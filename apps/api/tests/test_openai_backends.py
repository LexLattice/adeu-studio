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
