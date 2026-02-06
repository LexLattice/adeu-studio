from __future__ import annotations

import hashlib
import json
import urllib.error
import urllib.request
from dataclasses import dataclass
from typing import Any, Literal, Protocol

BackendApi = Literal["responses", "chat"]
ResponseMode = Literal["json_schema", "json_object"]


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


def _hash_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


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
        with urllib.request.urlopen(req, timeout=60) as resp:  # noqa: S310 (trusted host)
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
        prompt_hash = _hash_text(payload_text)
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
        response_hash = _hash_text(raw_text)
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
        prompt_hash = _hash_text(payload_text)
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
        response_hash = _hash_text(raw_text)
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
                    raw_prompt=None,
                    raw_text=None,
                    error=f"OpenAI chat error: {e}",
                    prompt_hash=None,
                    response_hash=None,
                )
        except RuntimeError as e:
            return BackendResult(
                provider_meta=BackendMeta(api="chat", model=model, response_mode="json_schema"),
                parsed_json=None,
                raw_prompt=None,
                raw_text=None,
                error=str(e),
                prompt_hash=None,
                response_hash=None,
            )

        # Only fallback when json_schema is unsupported for this chat mode.
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
                raw_prompt=None,
                raw_text=None,
                error=f"OpenAI chat fallback error: {e}",
                prompt_hash=None,
                response_hash=None,
            )
        except RuntimeError as e:
            return BackendResult(
                provider_meta=BackendMeta(api="chat", model=model, response_mode="json_object"),
                parsed_json=None,
                raw_prompt=None,
                raw_text=None,
                error=str(e),
                prompt_hash=None,
                response_hash=None,
            )


def build_openai_backend(*, api: BackendApi, api_key: str, base_url: str) -> OpenAIBackend:
    if api == "responses":
        return ResponsesBackend(api_key=api_key, base_url=base_url)
    if api == "chat":
        return ChatCompletionsBackend(api_key=api_key, base_url=base_url)
    raise ValueError(f"Unsupported ADEU_OPENAI_API value: {api!r}")
