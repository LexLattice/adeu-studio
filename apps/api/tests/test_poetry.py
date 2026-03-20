from __future__ import annotations

from typing import Any

import adeu_api.openai_backends as backends
import adeu_api.poetry as poetry
import pytest


class _FixedBackend:
    def __init__(
        self,
        *,
        payload: dict[str, Any] | None = None,
        error: str | None = None,
    ) -> None:
        self._payload = payload
        self._error = error

    def generate_ir_json(
        self,
        *,
        system_prompt: str,
        user_prompt: str,
        json_schema: dict[str, Any],
        model: str,
        temperature: float | None,
        extra: dict[str, Any] | None = None,
    ) -> backends.BackendResult:
        del system_prompt, user_prompt, json_schema, model, temperature, extra
        return backends.BackendResult(
            provider_meta=backends.BackendMeta(api="codex_exec", model="gpt-5.3-codex"),
            parsed_json=self._payload,
            raw_prompt=None,
            raw_text=None,
            error=self._error,
        )


def test_parse_llm_output_rejects_line_count_mismatch() -> None:
    with pytest.raises(ValueError, match="exactly 3 entries"):
        poetry._parse_llm_output(
            {"title": "Draft", "lines": ["one", "two"], "devices": ["imagery"]},
            expected_lines=3,
        )


def test_write_poem_codex_passes_skip_git_repo_check(monkeypatch) -> None:
    captured: dict[str, Any] = {}

    def fake_build_codex_exec_backend(
        *,
        codex_bin: str,
        skip_git_repo_check: bool,
    ) -> _FixedBackend:
        captured["codex_bin"] = codex_bin
        captured["skip_git_repo_check"] = skip_git_repo_check
        return _FixedBackend(
            payload={
                "title": "Harbor",
                "lines": ["First line", "Second line", "Third line"],
                "devices": ["imagery"],
            }
        )

    monkeypatch.setattr(poetry, "build_codex_exec_backend", fake_build_codex_exec_backend)
    monkeypatch.setattr(poetry, "codex_bin", lambda: "/tmp/fake-codex")
    monkeypatch.setattr(poetry, "codex_model", lambda: "gpt-5.3-codex")

    artifact = poetry.write_poem(
        provider="codex",
        form="haiku",
        skip_git_repo_check=True,
    )

    assert captured == {
        "codex_bin": "/tmp/fake-codex",
        "skip_git_repo_check": True,
    }
    assert artifact.title == "Harbor"
    assert artifact.lines == ("First line", "Second line", "Third line")
    assert artifact.source == "llm"


def test_write_poem_codex_fails_closed_on_malformed_output(monkeypatch) -> None:
    monkeypatch.setattr(
        poetry,
        "build_codex_exec_backend",
        lambda *, codex_bin, skip_git_repo_check: _FixedBackend(
            payload={
                "title": "Broken",
                "lines": ["Only one", "Only two"],
                "devices": ["imagery"],
            }
        ),
    )
    monkeypatch.setattr(poetry, "codex_bin", lambda: "/tmp/fake-codex")
    monkeypatch.setattr(poetry, "codex_model", lambda: "gpt-5.3-codex")

    with pytest.raises(RuntimeError, match="exactly 3 entries"):
        poetry.write_poem(provider="codex", form="haiku")


def test_write_poem_auto_falls_back_on_malformed_output(monkeypatch) -> None:
    monkeypatch.setattr(
        poetry,
        "build_openai_backend",
        lambda *, api, api_key, base_url: _FixedBackend(
            payload={
                "title": "Broken",
                "lines": ["Only one", "Only two"],
                "devices": ["imagery"],
            }
        ),
    )
    monkeypatch.setattr(poetry, "openai_api", lambda: "responses")
    monkeypatch.setattr(poetry, "openai_api_key", lambda: "test-key")
    monkeypatch.setattr(poetry, "openai_base_url", lambda: "https://api.test/v1")
    monkeypatch.setattr(poetry, "openai_model", lambda: "gpt-5.4-mini")
    monkeypatch.setattr(poetry, "openai_temperature", lambda: 0.2)

    artifact = poetry.write_poem(provider="auto", form="haiku")

    assert artifact.source == "template"
    assert artifact.provider_request == "fallback"
    assert len(artifact.lines) == 3
