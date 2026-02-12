from __future__ import annotations

import hashlib
import json
from typing import Any


def canonical_json(value: Any) -> str:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    )


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def sha256_canonical_json(value: Any) -> str:
    return sha256_text(canonical_json(value))


def action_hash(*, action_kind: str, action_payload: dict[str, Any]) -> str:
    return sha256_canonical_json(
        {
            "action_kind": action_kind,
            "action_payload": action_payload,
        }
    )
