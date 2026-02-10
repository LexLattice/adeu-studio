from __future__ import annotations

import json
from datetime import datetime, timezone
from json import JSONDecodeError
from typing import Any

from .models import NormalizedEvent


def normalize_exec_line(*, seq: int, raw_line: str) -> NormalizedEvent:
    timestamp = datetime.now(tz=timezone.utc)
    stripped = raw_line.rstrip("\n")
    try:
        parsed = json.loads(stripped)
    except JSONDecodeError as exc:
        return NormalizedEvent(
            seq=seq,
            ts=timestamp,
            source="worker_exec",
            event_kind="parse_error",
            payload={"error": str(exc)},
            raw_line=stripped,
        )

    if isinstance(parsed, dict):
        event_kind = str(parsed.get("type") or parsed.get("event") or "unknown_event")
        payload = parsed
    else:
        event_kind = "unknown_event"
        payload = {"value": parsed}
    return NormalizedEvent(
        seq=seq,
        ts=timestamp,
        source="worker_exec",
        event_kind=event_kind,
        payload=payload,
        raw_line=stripped,
    )


def extract_artifact_candidate(events: list[NormalizedEvent]) -> Any | None:
    for event in reversed(events):
        payload: dict[str, Any] = event.payload
        if "final_output" in payload:
            return payload["final_output"]
        if "artifact" in payload:
            return payload["artifact"]
        if "output" in payload:
            return payload["output"]
        if "result" in payload:
            return payload["result"]
    return None
