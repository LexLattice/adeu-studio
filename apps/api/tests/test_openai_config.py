from __future__ import annotations

import pytest
from adeu_api.openai_config import DEFAULT_OPENAI_TEMPERATURE, openai_temperature


def test_openai_temperature_defaults_when_unset(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delenv("ADEU_OPENAI_TEMPERATURE", raising=False)
    assert openai_temperature() == DEFAULT_OPENAI_TEMPERATURE


def test_openai_temperature_parse_error_includes_bad_value(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("ADEU_OPENAI_TEMPERATURE", "abc")
    with pytest.raises(RuntimeError, match=r"must be a number, but got 'abc'"):
        openai_temperature()


def test_openai_temperature_range_error_includes_bad_value(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("ADEU_OPENAI_TEMPERATURE", "3.5")
    with pytest.raises(RuntimeError, match=r"must be between 0.0 and 2.0, but got 3.5"):
        openai_temperature()
