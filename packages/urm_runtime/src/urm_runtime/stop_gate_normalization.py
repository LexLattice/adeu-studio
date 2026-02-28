from __future__ import annotations

from collections.abc import Mapping
from typing import Any


def strip_created_at_recursive(value: Any) -> Any:
    if isinstance(value, Mapping):
        normalized: dict[str, Any] = {}
        for raw_key in sorted(value.keys(), key=lambda item: str(item)):
            key = str(raw_key)
            if key == "created_at":
                continue
            normalized[key] = strip_created_at_recursive(value[raw_key])
        return normalized
    if isinstance(value, list):
        return [strip_created_at_recursive(item) for item in value]
    return value

