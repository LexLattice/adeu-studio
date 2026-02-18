from __future__ import annotations

from typing import Any

import adeu_api.openai_backends as backends


def _schema() -> dict[str, Any]:
    return {"type": "object", "properties": {"x": {"type": "string"}}, "required": ["x"]}


def test_chat_backend_nonfallback_error_keeps_prompt_metadata(monkeypatch) -> None:
    backend = backends.ChatCompletionsBackend(api_key="test", base_url="https://api.openai.com/v1")

    def fake_request_json(*, url: str, payload: dict[str, Any], api_key: str) -> Any:
        raise backends._BackendHttpError(status_code=500, detail="upstream failed")

    monkeypatch.setattr(backends, "_request_json", fake_request_json)

    result = backend.generate_ir_json(
        system_prompt="system",
        user_prompt="user",
        json_schema=_schema(),
        model="gpt-5.2",
        temperature=0.3,
        extra=None,
    )

    assert result.error is not None
    assert "OpenAI chat error" in result.error
    assert result.raw_prompt is not None
    assert result.prompt_hash is not None


def test_chat_backend_fallback_error_keeps_fallback_prompt_metadata(monkeypatch) -> None:
    backend = backends.ChatCompletionsBackend(api_key="test", base_url="https://api.openai.com/v1")
    calls = 0

    def fake_request_json(*, url: str, payload: dict[str, Any], api_key: str) -> Any:
        nonlocal calls
        calls += 1
        if calls == 1:
            raise backends._BackendHttpError(
                status_code=400,
                detail="response_format json_schema unsupported",
            )
        raise backends._BackendHttpError(status_code=500, detail="fallback failed")

    monkeypatch.setattr(backends, "_request_json", fake_request_json)

    result = backend.generate_ir_json(
        system_prompt="system",
        user_prompt="user",
        json_schema=_schema(),
        model="gpt-5.2",
        temperature=0.3,
        extra=None,
    )

    assert calls == 2
    assert result.error is not None
    assert "fallback error" in result.error
    assert result.raw_prompt is not None
    assert '"json_object"' in result.raw_prompt
    assert result.prompt_hash is not None


def test_request_json_uses_configured_timeout(monkeypatch) -> None:
    captured_timeout: float | None = None

    class _FakeResponse:
        headers: dict[str, str] = {}

        def __enter__(self) -> _FakeResponse:
            return self

        def __exit__(self, exc_type, exc, tb) -> bool:
            return False

        def read(self) -> bytes:
            return b"{}"

    def fake_urlopen(_req: object, timeout: float) -> _FakeResponse:
        nonlocal captured_timeout
        captured_timeout = timeout
        return _FakeResponse()

    monkeypatch.setattr(backends.urllib.request, "urlopen", fake_urlopen)
    monkeypatch.setattr(backends, "OPENAI_HTTP_TIMEOUT_SECONDS", 12.5)

    backends._request_json(
        url="https://api.openai.com/v1/responses",
        payload={"model": "gpt-5.2"},
        api_key="test-key",
    )

    assert captured_timeout == 12.5


def test_codex_exec_backend_extracts_agent_message_json_object(monkeypatch) -> None:
    backend = backends.CodexExecBackend(codex_bin="/tmp/fake-codex")
    stdout = "\n".join(
        [
            '{"type":"thread.started","thread_id":"thread-1"}',
            '{"type":"turn.started"}',
            '{"type":"item.completed","item":{"id":"item_1","type":"agent_message","text":"{\\"x\\":\\"ok\\"}"}}',
            '{"type":"turn.completed","usage":{"input_tokens":1,"output_tokens":1}}',
        ]
    )

    def fake_run(*args, **kwargs):
        del args, kwargs
        return backends.subprocess.CompletedProcess(
            args=["codex", "exec"],
            returncode=0,
            stdout=stdout,
            stderr="",
        )

    monkeypatch.setattr(backends.subprocess, "run", fake_run)

    result = backend.generate_ir_json(
        system_prompt="system",
        user_prompt="user",
        json_schema=_schema(),
        model="codex-cli-default",
        temperature=None,
        extra=None,
    )

    assert result.error is None
    assert result.parsed_json == {"x": "ok"}
    assert result.provider_meta.api == "codex_exec"


def test_codex_schema_normalization_requires_all_object_properties() -> None:
    schema = {
        "type": "object",
        "properties": {
            "required_field": {"type": "string"},
            "optional_field": {"type": "integer"},
            "already_nullable": {"anyOf": [{"type": "number"}, {"type": "null"}]},
            "any_value": {"anyOf": [{}, {"type": "null"}]},
            "nested": {
                "type": "object",
                "properties": {
                    "inner_required": {"type": "string"},
                    "inner_optional": {"type": "boolean"},
                },
                "required": ["inner_required"],
            },
            "subject": {
                "oneOf": [{"$ref": "#/$defs/DocRef"}, {"$ref": "#/$defs/TextRef"}],
                "discriminator": {
                    "mapping": {
                        "doc": "#/$defs/DocRef",
                        "text": "#/$defs/TextRef",
                    },
                    "propertyName": "ref_type",
                },
            },
        },
        "required": ["required_field"],
    }

    normalized = backends._normalize_schema_for_codex_output(schema)

    assert normalized["required"] == [
        "required_field",
        "optional_field",
        "already_nullable",
        "any_value",
        "nested",
        "subject",
    ]
    assert normalized["properties"]["optional_field"] == {"type": "integer"}
    assert normalized["properties"]["already_nullable"] == {
        "anyOf": [{"type": "number"}, {"type": "null"}]
    }
    any_value = normalized["properties"]["any_value"]["anyOf"]
    assert isinstance(any_value, list)
    first_branch = any_value[0]
    assert isinstance(first_branch, dict)
    first_branch_anyof = first_branch.get("anyOf")
    assert isinstance(first_branch_anyof, list)
    assert {"type": "object"} in first_branch_anyof
    assert {"type": "array"} in first_branch_anyof
    assert {"type": "string"} in first_branch_anyof
    assert {"type": "number"} in first_branch_anyof
    assert {"type": "integer"} in first_branch_anyof
    assert {"type": "boolean"} in first_branch_anyof
    assert {"type": "null"} in first_branch_anyof
    assert {"type": "null"} in any_value
    nested = normalized["properties"]["nested"]
    assert nested["required"] == ["inner_required", "inner_optional"]
    assert nested["properties"]["inner_optional"] == {"type": "boolean"}
    subject = normalized["properties"]["subject"]
    discriminator = subject["oneOf"]
    assert discriminator == [{"$ref": "#/$defs/DocRef"}, {"$ref": "#/$defs/TextRef"}]
    mapping = subject["discriminator"]["mapping"]
    assert mapping == {
        "doc": "#/$defs/DocRef",
        "text": "#/$defs/TextRef",
    }


def test_codex_schema_normalization_keeps_optional_fields_non_nullable_by_default() -> None:
    schema = {
        "type": "object",
        "properties": {
            "schema_version": {"type": "string"},
            "items": {"type": "array", "items": {"type": "string"}},
        },
        "required": [],
    }

    normalized = backends._normalize_schema_for_codex_output(schema)

    assert normalized["required"] == ["schema_version", "items"]
    assert normalized["properties"]["schema_version"] == {"type": "string"}
    assert normalized["properties"]["items"] == {"type": "array", "items": {"type": "string"}}
