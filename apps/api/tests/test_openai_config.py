from __future__ import annotations

import pytest
from adeu_api.openai_config import (
    DEFAULT_OPENAI_MAX_CANDIDATES,
    DEFAULT_OPENAI_MAX_REPAIRS,
    DEFAULT_OPENAI_TEMPERATURE,
    openai_default_max_candidates,
    openai_default_max_repairs,
    openai_temperature,
)


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


def test_openai_default_max_candidates_defaults_when_unset(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.delenv("ADEU_OPENAI_DEFAULT_MAX_CANDIDATES", raising=False)
    assert openai_default_max_candidates() == DEFAULT_OPENAI_MAX_CANDIDATES


def test_openai_default_max_repairs_defaults_when_unset(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.delenv("ADEU_OPENAI_DEFAULT_MAX_REPAIRS", raising=False)
    assert openai_default_max_repairs() == DEFAULT_OPENAI_MAX_REPAIRS


def test_openai_default_max_candidates_parse_error_includes_bad_value(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("ADEU_OPENAI_DEFAULT_MAX_CANDIDATES", "abc")
    with pytest.raises(RuntimeError, match=r"must be an integer, but got 'abc'"):
        openai_default_max_candidates()


def test_openai_default_max_repairs_range_error_includes_bad_value(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("ADEU_OPENAI_DEFAULT_MAX_REPAIRS", "99")
    with pytest.raises(RuntimeError, match=r"must be between 0 and 10, but got 99"):
        openai_default_max_repairs()
