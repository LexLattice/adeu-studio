from __future__ import annotations

import json
import os
import subprocess
import tempfile
import urllib.error
import urllib.request
from copy import deepcopy
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal, Protocol

from urm_runtime.normalization import extract_artifact_candidate, normalize_exec_line

from .hashing import sha256_text

BackendApi = Literal["responses", "chat", "codex_exec"]
ResponseMode = Literal["json_schema", "json_object"]
DEFAULT_OPENAI_HTTP_TIMEOUT_SECONDS = 60.0
DEFAULT_CODEX_EXEC_TIMEOUT_SECONDS = 120.0
CODEX_DEFAULT_MODEL_LABEL = "codex-cli-default"


def _env_timeout_seconds(name: str, default: float) -> float:
    raw_value = os.environ.get(name, "").strip()
    if not raw_value:
        return default
    try:
        value = float(raw_value)
    except ValueError as exc:
        raise RuntimeError(f"{name} must be a number") from exc
    if value <= 0:
        raise RuntimeError(f"{name} must be > 0")
    return value


OPENAI_HTTP_TIMEOUT_SECONDS = _env_timeout_seconds(
    "ADEU_OPENAI_HTTP_TIMEOUT_SECONDS",
    DEFAULT_OPENAI_HTTP_TIMEOUT_SECONDS,
)
CODEX_EXEC_TIMEOUT_SECONDS = _env_timeout_seconds(
    "ADEU_CODEX_EXEC_TIMEOUT_SECONDS",
    DEFAULT_CODEX_EXEC_TIMEOUT_SECONDS,
)

_SCHEMA_MAP_KEYS = {
    "$defs",
    "definitions",
    "properties",
    "patternProperties",
    "dependentSchemas",
}
_SCHEMA_SINGLE_KEYS = {
    "additionalProperties",
    "additionalItems",
    "items",
    "contains",
    "propertyNames",
    "unevaluatedProperties",
    "unevaluatedItems",
    "not",
    "if",
    "then",
    "else",
}
_SCHEMA_LIST_KEYS = {
    "allOf",
    "anyOf",
    "oneOf",
    "prefixItems",
}
_ANY_JSON_TYPED_SCHEMA: dict[str, Any] = {
    "anyOf": [
        {"type": "object"},
        {"type": "array"},
        {"type": "string"},
        {"type": "number"},
        {"type": "integer"},
        {"type": "boolean"},
        {"type": "null"},
    ]
}


@dataclass(frozen=True)
class BackendMeta:
    api: BackendApi
    model: str
    request_id: str | None = None
    usage: dict[str, Any] | None = None
    response_mode: ResponseMode | None = None


@dataclass(frozen=True)
class BackendResult:
    provider_meta: BackendMeta
    parsed_json: dict[str, Any] | None
    raw_prompt: str | None
    raw_text: str | None
    error: str | None = None
    prompt_hash: str | None = None
    response_hash: str | None = None


class OpenAIBackend(Protocol):
    def generate_ir_json(
        self,
        *,
        system_prompt: str,
        user_prompt: str,
        json_schema: dict[str, Any],
        model: str,
        temperature: float | None,
        extra: dict[str, Any] | None = None,
    ) -> BackendResult: ...


@dataclass(frozen=True)
class _HttpResult:
    data: dict[str, Any]
    raw_body: str
    request_id: str | None


@dataclass(frozen=True)
class _BackendHttpError(Exception):
    status_code: int
    detail: str

    def __str__(self) -> str:
        return f"HTTP {self.status_code}: {self.detail}"


def _json_type_for_python_value(value: Any) -> str:
    if value is None:
        return "null"
    if isinstance(value, bool):
        return "boolean"
    if isinstance(value, int):
        return "integer"
    if isinstance(value, float):
        return "number"
    if isinstance(value, str):
        return "string"
    if isinstance(value, list):
        return "array"
    if isinstance(value, dict):
        return "object"
    return "string"


def _ensure_typed_schema_for_codex(schema: dict[str, Any]) -> dict[str, Any]:
    if "type" in schema or "$ref" in schema:
        return schema

    if "properties" in schema or "additionalProperties" in schema:
        schema["type"] = "object"
        return schema
    if "items" in schema:
        schema["type"] = "array"
        return schema

    enum_values = schema.get("enum")
    if isinstance(enum_values, list) and enum_values:
        inferred = {_json_type_for_python_value(item) for item in enum_values}
        if len(inferred) == 1:
            schema["type"] = inferred.pop()
            return schema

    if "const" in schema:
        schema["type"] = _json_type_for_python_value(schema["const"])
        return schema

    if any(key in schema for key in ("anyOf", "oneOf", "allOf", "not", "if", "then", "else")):
        return schema

    # Preserve permissive `{}` semantics while keeping a typed schema node.
    if not schema:
        schema.update(deepcopy(_ANY_JSON_TYPED_SCHEMA))
        return schema

    # Codex schema validator rejects untyped nodes. Keep behavior stable for
    # non-empty untyped nodes by using a conservative scalar fallback.
    schema["type"] = "string"
    return schema


def _normalize_schema_for_codex_output(schema: dict[str, Any]) -> dict[str, Any]:
    normalized = deepcopy(schema)

    def _walk(node: Any, *, schema_position: bool) -> Any:
        if isinstance(node, list):
            return [
                _walk(item, schema_position=schema_position)
                for item in node
            ]
        if not isinstance(node, dict):
            return node

        for key, value in list(node.items()):
            if schema_position and key in _SCHEMA_MAP_KEYS and isinstance(value, dict):
                node[key] = {
                    sub_key: _walk(sub_value, schema_position=True)
                    for sub_key, sub_value in value.items()
                }
                continue
            if schema_position and key in _SCHEMA_SINGLE_KEYS:
                node[key] = _walk(value, schema_position=True)
                continue
            if schema_position and key in _SCHEMA_LIST_KEYS and isinstance(value, list):
                node[key] = [_walk(item, schema_position=True) for item in value]
                continue
            node[key] = _walk(value, schema_position=False)

        if not schema_position:
            return node

        node = _ensure_typed_schema_for_codex(node)

        properties = node.get("properties")
        if isinstance(properties, dict):
            required_raw = node.get("required")
            required_list = (
                [item for item in required_raw if isinstance(item, str)]
                if isinstance(required_raw, list)
                else []
            )
            required_set = set(required_list)
            for prop_name, prop_schema in properties.items():
                if not isinstance(prop_schema, dict):
                    continue
                if prop_name not in required_set:
                    required_list.append(prop_name)
                    required_set.add(prop_name)
            node["required"] = required_list
        return node

    return _walk(normalized, schema_position=True)


def _request_json(*, url: str, payload: dict[str, Any], api_key: str) -> _HttpResult:
    payload_text = json.dumps(payload, ensure_ascii=False)
    req = urllib.request.Request(
        url,
        data=payload_text.encode("utf-8"),
        headers={
            "authorization": f"Bearer {api_key}",
            "content-type": "application/json",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(
            req,
            timeout=OPENAI_HTTP_TIMEOUT_SECONDS,
        ) as resp:  # noqa: S310 (trusted host)
            raw_body = resp.read().decode("utf-8")
            request_id = resp.headers.get("x-request-id")
    except urllib.error.HTTPError as e:
        detail = e.read().decode("utf-8", errors="replace")
        raise _BackendHttpError(status_code=e.code, detail=detail) from e
    except urllib.error.URLError as e:
        raise RuntimeError(f"OpenAI request failed: {e}") from e

    try:
        data = json.loads(raw_body)
    except json.JSONDecodeError as e:
        raise RuntimeError(f"OpenAI response is not valid JSON: {e}") from e

    if not isinstance(data, dict):
        raise RuntimeError("OpenAI response JSON must be an object")
    return _HttpResult(data=data, raw_body=raw_body, request_id=request_id)


def _strict_json_object(*, text: str, api: BackendApi) -> tuple[dict[str, Any] | None, str | None]:
    if not isinstance(text, str) or not text.strip():
        return None, f"{api} response missing JSON text"
    try:
        parsed = json.loads(text)
    except json.JSONDecodeError as e:
        return None, f"{api} output is not valid JSON: {e}"
    if not isinstance(parsed, dict):
        return None, f"{api} output JSON must be an object"
    return parsed, None


def _extract_responses_text(data: dict[str, Any]) -> str | None:
    output_text = data.get("output_text")
    if isinstance(output_text, str) and output_text.strip():
        return output_text

    output = data.get("output")
    if not isinstance(output, list):
        return None

    for item in output:
        if not isinstance(item, dict):
            continue
        content = item.get("content")
        if not isinstance(content, list):
            continue
        for block in content:
            if not isinstance(block, dict):
                continue
            text = block.get("text")
            if isinstance(text, str) and text.strip():
                return text
    return None


def _extract_chat_text(data: dict[str, Any]) -> str | None:
    choices = data.get("choices")
    if not isinstance(choices, list) or not choices:
        return None
    first = choices[0]
    if not isinstance(first, dict):
        return None
    message = first.get("message")
    if not isinstance(message, dict):
        return None
    content = message.get("content")
    if isinstance(content, str) and content.strip():
        return content
    return None


def _is_chat_json_schema_unsupported(err: _BackendHttpError) -> bool:
    if err.status_code not in {400, 404, 422}:
        return False
    lowered = err.detail.lower()
    return "json_schema" in lowered or "response_format" in lowered


class ResponsesBackend:
    def __init__(self, *, api_key: str, base_url: str):
        self._api_key = api_key
        self._base_url = base_url.rstrip("/")

    def generate_ir_json(
        self,
        *,
        system_prompt: str,
        user_prompt: str,
        json_schema: dict[str, Any],
        model: str,
        temperature: float | None,
        extra: dict[str, Any] | None = None,
    ) -> BackendResult:
        payload: dict[str, Any] = {
            "model": model,
            "input": [
                {"role": "system", "content": [{"type": "input_text", "text": system_prompt}]},
                {"role": "user", "content": [{"type": "input_text", "text": user_prompt}]},
            ],
            "text": {
                "format": {
                    "type": "json_schema",
                    "name": "adeu_ir",
                    "schema": json_schema,
                    "strict": True,
                }
            },
        }
        if temperature is not None:
            payload["temperature"] = temperature
        if extra:
            payload.update(extra)

        payload_text = json.dumps(payload, sort_keys=True, ensure_ascii=False)
        prompt_hash = sha256_text(payload_text)
        try:
            result = _request_json(
                url=f"{self._base_url}/responses",
                payload=payload,
                api_key=self._api_key,
            )
        except _BackendHttpError as e:
            return BackendResult(
                provider_meta=BackendMeta(
                    api="responses",
                    model=model,
                    response_mode="json_schema",
                ),
                parsed_json=None,
                raw_prompt=payload_text,
                raw_text=None,
                error=f"OpenAI responses error: {e}",
                prompt_hash=prompt_hash,
                response_hash=None,
            )
        except RuntimeError as e:
            return BackendResult(
                provider_meta=BackendMeta(
                    api="responses",
                    model=model,
                    response_mode="json_schema",
                ),
                parsed_json=None,
                raw_prompt=payload_text,
                raw_text=None,
                error=str(e),
                prompt_hash=prompt_hash,
                response_hash=None,
            )

        raw_text = _extract_responses_text(result.data)
        if raw_text is None:
            return BackendResult(
                provider_meta=BackendMeta(
                    api="responses",
                    model=model,
                    request_id=result.request_id,
                    usage=result.data.get("usage")
                    if isinstance(result.data.get("usage"), dict)
                    else None,
                    response_mode="json_schema",
                ),
                parsed_json=None,
                raw_prompt=payload_text,
                raw_text=None,
                error="responses output missing text payload",
                prompt_hash=prompt_hash,
                response_hash=None,
            )

        parsed_json, parse_error = _strict_json_object(text=raw_text, api="responses")
        response_hash = sha256_text(raw_text)
        return BackendResult(
            provider_meta=BackendMeta(
                api="responses",
                model=model,
                request_id=result.request_id,
                usage=(
                    result.data.get("usage")
                    if isinstance(result.data.get("usage"), dict)
                    else None
                ),
                response_mode="json_schema",
            ),
            parsed_json=parsed_json,
            raw_prompt=payload_text,
            raw_text=raw_text,
            error=parse_error,
            prompt_hash=prompt_hash,
            response_hash=response_hash,
        )


class ChatCompletionsBackend:
    def __init__(self, *, api_key: str, base_url: str):
        self._api_key = api_key
        self._base_url = base_url.rstrip("/")

    def _build_payload(
        self,
        *,
        system_prompt: str,
        user_prompt: str,
        model: str,
        temperature: float | None,
        response_mode: ResponseMode,
        json_schema: dict[str, Any],
        extra: dict[str, Any] | None,
    ) -> tuple[dict[str, Any], str, str]:
        response_format: dict[str, Any]
        if response_mode == "json_schema":
            response_format = {
                "type": "json_schema",
                "json_schema": {
                    "name": "adeu_ir",
                    "schema": json_schema,
                    "strict": True,
                },
            }
        else:
            response_format = {"type": "json_object"}

        payload: dict[str, Any] = {
            "model": model,
            "messages": [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ],
            "response_format": response_format,
        }
        if temperature is not None:
            payload["temperature"] = temperature
        if extra:
            payload.update(extra)

        payload_text = json.dumps(payload, sort_keys=True, ensure_ascii=False)
        prompt_hash = sha256_text(payload_text)
        return payload, payload_text, prompt_hash

    def _chat_call(
        self,
        *,
        system_prompt: str,
        user_prompt: str,
        model: str,
        temperature: float | None,
        response_mode: ResponseMode,
        json_schema: dict[str, Any],
        extra: dict[str, Any] | None,
    ) -> BackendResult:
        payload, payload_text, prompt_hash = self._build_payload(
            system_prompt=system_prompt,
            user_prompt=user_prompt,
            model=model,
            temperature=temperature,
            response_mode=response_mode,
            json_schema=json_schema,
            extra=extra,
        )
        result = _request_json(
            url=f"{self._base_url}/chat/completions",
            payload=payload,
            api_key=self._api_key,
        )

        raw_text = _extract_chat_text(result.data)
        if raw_text is None:
            return BackendResult(
                provider_meta=BackendMeta(
                    api="chat",
                    model=model,
                    request_id=result.request_id,
                    usage=result.data.get("usage")
                    if isinstance(result.data.get("usage"), dict)
                    else None,
                    response_mode=response_mode,
                ),
                parsed_json=None,
                raw_prompt=payload_text,
                raw_text=None,
                error="chat completion missing message.content",
                prompt_hash=prompt_hash,
                response_hash=None,
            )

        parsed_json, parse_error = _strict_json_object(text=raw_text, api="chat")
        response_hash = sha256_text(raw_text)
        return BackendResult(
            provider_meta=BackendMeta(
                api="chat",
                model=model,
                request_id=result.request_id,
                usage=(
                    result.data.get("usage")
                    if isinstance(result.data.get("usage"), dict)
                    else None
                ),
                response_mode=response_mode,
            ),
            parsed_json=parsed_json,
            raw_prompt=payload_text,
            raw_text=raw_text,
            error=parse_error,
            prompt_hash=prompt_hash,
            response_hash=response_hash,
        )

    def generate_ir_json(
        self,
        *,
        system_prompt: str,
        user_prompt: str,
        json_schema: dict[str, Any],
        model: str,
        temperature: float | None,
        extra: dict[str, Any] | None = None,
    ) -> BackendResult:
        _, schema_payload_text, schema_prompt_hash = self._build_payload(
            system_prompt=system_prompt,
            user_prompt=user_prompt,
            model=model,
            temperature=temperature,
            response_mode="json_schema",
            json_schema=json_schema,
            extra=extra,
        )
        try:
            return self._chat_call(
                system_prompt=system_prompt,
                user_prompt=user_prompt,
                model=model,
                temperature=temperature,
                response_mode="json_schema",
                json_schema=json_schema,
                extra=extra,
            )
        except _BackendHttpError as e:
            if not _is_chat_json_schema_unsupported(e):
                return BackendResult(
                    provider_meta=BackendMeta(api="chat", model=model, response_mode="json_schema"),
                    parsed_json=None,
                    raw_prompt=schema_payload_text,
                    raw_text=None,
                    error=f"OpenAI chat error: {e}",
                    prompt_hash=schema_prompt_hash,
                    response_hash=None,
                )
        except RuntimeError as e:
            return BackendResult(
                provider_meta=BackendMeta(api="chat", model=model, response_mode="json_schema"),
                parsed_json=None,
                raw_prompt=schema_payload_text,
                raw_text=None,
                error=str(e),
                prompt_hash=schema_prompt_hash,
                response_hash=None,
            )

        # Only fallback when json_schema is unsupported for this chat mode.
        _, object_payload_text, object_prompt_hash = self._build_payload(
            system_prompt=system_prompt,
            user_prompt=user_prompt,
            model=model,
            temperature=temperature,
            response_mode="json_object",
            json_schema=json_schema,
            extra=extra,
        )
        try:
            return self._chat_call(
                system_prompt=system_prompt,
                user_prompt=user_prompt,
                model=model,
                temperature=temperature,
                response_mode="json_object",
                json_schema=json_schema,
                extra=extra,
            )
        except _BackendHttpError as e:
            return BackendResult(
                provider_meta=BackendMeta(api="chat", model=model, response_mode="json_object"),
                parsed_json=None,
                raw_prompt=object_payload_text,
                raw_text=None,
                error=f"OpenAI chat fallback error: {e}",
                prompt_hash=object_prompt_hash,
                response_hash=None,
            )
        except RuntimeError as e:
            return BackendResult(
                provider_meta=BackendMeta(api="chat", model=model, response_mode="json_object"),
                parsed_json=None,
                raw_prompt=object_payload_text,
                raw_text=None,
                error=str(e),
                prompt_hash=object_prompt_hash,
                response_hash=None,
            )


class CodexExecBackend:
    def __init__(self, *, codex_bin: str):
        self._codex_bin = codex_bin

    def _build_prompt(self, *, system_prompt: str, user_prompt: str) -> str:
        return (
            "SYSTEM:\n"
            f"{system_prompt}\n\n"
            "USER:\n"
            f"{user_prompt}\n\n"
            "Return only a single JSON object that matches the output schema."
        )

    def _build_command(
        self,
        *,
        prompt: str,
        schema_path: str,
        model: str,
    ) -> list[str]:
        command = [
            self._codex_bin,
            "exec",
            "--json",
            "--sandbox",
            "read-only",
            "--output-schema",
            schema_path,
        ]
        if model and model != CODEX_DEFAULT_MODEL_LABEL:
            command.extend(["--model", model])
        command.append(prompt)
        return command

    def generate_ir_json(
        self,
        *,
        system_prompt: str,
        user_prompt: str,
        json_schema: dict[str, Any],
        model: str,
        temperature: float | None,
        extra: dict[str, Any] | None = None,
    ) -> BackendResult:
        del temperature
        del extra

        prompt = self._build_prompt(system_prompt=system_prompt, user_prompt=user_prompt)
        codex_schema = _normalize_schema_for_codex_output(json_schema)
        payload_text = json.dumps(
            {
                "api": "codex_exec",
                "model": model,
                "prompt": prompt,
                "schema": codex_schema,
            },
            sort_keys=True,
            ensure_ascii=False,
        )
        prompt_hash = sha256_text(payload_text)

        schema_path: str | None = None
        try:
            with tempfile.NamedTemporaryFile(
                mode="w",
                encoding="utf-8",
                suffix=".json",
                delete=False,
            ) as schema_file:
                schema_file.write(json.dumps(codex_schema, sort_keys=True, ensure_ascii=False))
                schema_path = schema_file.name
        except OSError as exc:
            return BackendResult(
                provider_meta=BackendMeta(
                    api="codex_exec",
                    model=model,
                    response_mode="json_schema",
                ),
                parsed_json=None,
                raw_prompt=payload_text,
                raw_text=None,
                error=f"failed to write codex output schema file: {exc}",
                prompt_hash=prompt_hash,
                response_hash=None,
            )

        try:
            command = self._build_command(prompt=prompt, schema_path=schema_path, model=model)
            completed = subprocess.run(
                command,
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=CODEX_EXEC_TIMEOUT_SECONDS,
                check=False,
            )
        except FileNotFoundError:
            return BackendResult(
                provider_meta=BackendMeta(
                    api="codex_exec",
                    model=model,
                    response_mode="json_schema",
                ),
                parsed_json=None,
                raw_prompt=payload_text,
                raw_text=None,
                error=f"codex executable not found: {self._codex_bin}",
                prompt_hash=prompt_hash,
                response_hash=None,
            )
        except subprocess.TimeoutExpired:
            return BackendResult(
                provider_meta=BackendMeta(
                    api="codex_exec",
                    model=model,
                    response_mode="json_schema",
                ),
                parsed_json=None,
                raw_prompt=payload_text,
                raw_text=None,
                error=f"codex exec timed out after {CODEX_EXEC_TIMEOUT_SECONDS} seconds",
                prompt_hash=prompt_hash,
                response_hash=None,
            )
        except OSError as exc:
            return BackendResult(
                provider_meta=BackendMeta(
                    api="codex_exec",
                    model=model,
                    response_mode="json_schema",
                ),
                parsed_json=None,
                raw_prompt=payload_text,
                raw_text=None,
                error=f"codex exec failed to start: {exc}",
                prompt_hash=prompt_hash,
                response_hash=None,
            )
        finally:
            if schema_path is not None:
                Path(schema_path).unlink(missing_ok=True)

        raw_lines = completed.stdout.splitlines()
        events = []
        for index, line in enumerate(raw_lines):
            if not line.strip():
                continue
            events.append(
                normalize_exec_line(
                    seq=index + 1,
                    raw_line=line,
                    stream_id="provider:codex_exec",
                    run_id="provider.codex_exec",
                    role="pipeline_worker",
                    endpoint="proposer.codex_exec",
                )
            )

        artifact_candidate = extract_artifact_candidate(events)
        stderr_text = completed.stderr.strip()
        if completed.returncode != 0:
            detail = stderr_text or (completed.stdout.strip() or "unknown error")
            return BackendResult(
                provider_meta=BackendMeta(
                    api="codex_exec",
                    model=model,
                    response_mode="json_schema",
                ),
                parsed_json=None,
                raw_prompt=payload_text,
                raw_text=completed.stdout.strip() or None,
                error=f"Codex exec error (exit {completed.returncode}): {detail}",
                prompt_hash=prompt_hash,
                response_hash=None,
            )

        if artifact_candidate is None:
            return BackendResult(
                provider_meta=BackendMeta(
                    api="codex_exec",
                    model=model,
                    response_mode="json_schema",
                ),
                parsed_json=None,
                raw_prompt=payload_text,
                raw_text=completed.stdout.strip() or None,
                error="codex output missing artifact candidate",
                prompt_hash=prompt_hash,
                response_hash=None,
            )

        parse_error: str | None = None
        parsed_json: dict[str, Any] | None = None
        raw_text: str | None = None
        if isinstance(artifact_candidate, dict):
            parsed_json = artifact_candidate
            raw_text = json.dumps(artifact_candidate, sort_keys=True, ensure_ascii=False)
        elif isinstance(artifact_candidate, str):
            parsed_json, parse_error = _strict_json_object(
                text=artifact_candidate,
                api="codex_exec",
            )
            raw_text = artifact_candidate
        else:
            parse_error = "codex output JSON must be an object"
            raw_text = json.dumps({"value": artifact_candidate}, sort_keys=True, ensure_ascii=False)

        response_hash = sha256_text(raw_text) if raw_text is not None else None
        return BackendResult(
            provider_meta=BackendMeta(api="codex_exec", model=model, response_mode="json_schema"),
            parsed_json=parsed_json,
            raw_prompt=payload_text,
            raw_text=raw_text,
            error=parse_error,
            prompt_hash=prompt_hash,
            response_hash=response_hash,
        )


def build_openai_backend(*, api: BackendApi, api_key: str, base_url: str) -> OpenAIBackend:
    if api == "responses":
        return ResponsesBackend(api_key=api_key, base_url=base_url)
    if api == "chat":
        return ChatCompletionsBackend(api_key=api_key, base_url=base_url)
    raise ValueError(f"Unsupported ADEU_OPENAI_API value: {api!r}")


def build_codex_exec_backend(*, codex_bin: str) -> OpenAIBackend:
    return CodexExecBackend(codex_bin=codex_bin)
