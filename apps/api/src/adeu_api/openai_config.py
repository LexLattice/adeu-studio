from __future__ import annotations

import os
from typing import cast

from .openai_backends import BackendApi

DEFAULT_OPENAI_MODEL = "gpt-5.2"
DEFAULT_OPENAI_API: BackendApi = "responses"
DEFAULT_OPENAI_TEMPERATURE = 0.3
MIN_OPENAI_TEMPERATURE = 0.0
MAX_OPENAI_TEMPERATURE = 2.0


def env_flag(name: str) -> bool:
    return os.environ.get(name, "").strip() == "1"


def openai_api_key() -> str | None:
    return os.environ.get("OPENAI_API_KEY") or os.environ.get("ADEU_OPENAI_API_KEY")


def openai_model() -> str:
    return os.environ.get("ADEU_OPENAI_MODEL", DEFAULT_OPENAI_MODEL).strip() or DEFAULT_OPENAI_MODEL


def openai_api() -> BackendApi:
    value = os.environ.get("ADEU_OPENAI_API", DEFAULT_OPENAI_API).strip().lower()
    if value in {"responses", "chat"}:
        return cast(BackendApi, value)
    raise RuntimeError("ADEU_OPENAI_API must be one of: responses, chat")


def openai_base_url() -> str:
    return os.environ.get("ADEU_OPENAI_BASE_URL", "https://api.openai.com/v1").rstrip("/")


def openai_temperature() -> float:
    raw = os.environ.get("ADEU_OPENAI_TEMPERATURE", "").strip()
    if not raw:
        return DEFAULT_OPENAI_TEMPERATURE
    try:
        value = float(raw)
    except ValueError as exc:
        raise RuntimeError(
            f"ADEU_OPENAI_TEMPERATURE must be a number, but got {raw!r}"
        ) from exc
    if value < MIN_OPENAI_TEMPERATURE or value > MAX_OPENAI_TEMPERATURE:
        raise RuntimeError(
            "ADEU_OPENAI_TEMPERATURE must be between "
            f"{MIN_OPENAI_TEMPERATURE} and {MAX_OPENAI_TEMPERATURE}, but got {value}"
        )
    return value
