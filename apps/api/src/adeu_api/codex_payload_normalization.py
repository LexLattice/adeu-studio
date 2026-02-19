from __future__ import annotations

from copy import deepcopy
from typing import Any

_TRANSPORT_WRAPPER_KEYS = ("final_output", "artifact", "output", "result")
_MAX_UNWRAP_DEPTH = 8


def normalize_codex_transport_payload(payload: dict[str, Any]) -> dict[str, Any]:
    """Normalize codex transport wrappers into a direct candidate object."""

    current = payload
    for _ in range(_MAX_UNWRAP_DEPTH):
        if len(current) != 1:
            break
        wrapper_key, wrapper_value = next(iter(current.items()))
        if wrapper_key not in _TRANSPORT_WRAPPER_KEYS:
            break
        if not isinstance(wrapper_value, dict):
            break
        current = wrapper_value
    return deepcopy(current)
