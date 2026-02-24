from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping
from typing import Any


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def canonical_json(value: object) -> str:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def sha256_canonical_json(value: object) -> str:
    return sha256_text(canonical_json(value))


def strip_created_at_recursive(value: Any) -> Any:
    if isinstance(value, Mapping):
        normalized: dict[str, Any] = {}
        for key in sorted(str(item) for item in value.keys()):
            if key == "created_at":
                continue
            normalized[key] = strip_created_at_recursive(value[key])
        return normalized
    if isinstance(value, list):
        return [strip_created_at_recursive(item) for item in value]
    return value
