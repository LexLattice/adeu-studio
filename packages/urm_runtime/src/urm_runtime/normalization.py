from __future__ import annotations

import json
from datetime import datetime, timezone
from importlib.metadata import PackageNotFoundError, version
from json import JSONDecodeError
from typing import Any, Literal

from .models import NormalizedEvent

try:
    URM_RUNTIME_VERSION = version("urm-runtime")
except PackageNotFoundError:
    URM_RUNTIME_VERSION = "0.0.0"


def _normalize_line(
    *,
    seq: int,
    raw_line: str,
    source_component: Literal["worker_exec", "copilot_app_server"],
    stream_id: str,
    context: dict[str, Any],
) -> NormalizedEvent:
    timestamp = datetime.now(tz=timezone.utc)
    stripped = raw_line.rstrip("\n")
    source = {
        "component": source_component,
        "version": URM_RUNTIME_VERSION,
        "provider": "codex",
    }
    try:
        parsed = json.loads(stripped)
    except JSONDecodeError as exc:
        return NormalizedEvent(
            event="PROVIDER_PARSE_ERROR",
            stream_id=stream_id,
            seq=seq,
            ts=timestamp,
            source=source,
            context=context,
            detail={"error": str(exc)},
            event_kind="parse_error",
            payload={"error": str(exc)},
            raw_line=stripped,
        )

    if isinstance(parsed, dict):
        event_kind = str(
            parsed.get("type")
            or parsed.get("event")
            or parsed.get("method")
            or "unknown_event"
        )
        payload = parsed
        detail: dict[str, Any] = {
            "provider_event": event_kind,
            "payload": payload,
        }
    else:
        event_kind = "unknown_event"
        payload = {"value": parsed}
        detail = {
            "provider_event": event_kind,
            "payload": payload,
        }
    return NormalizedEvent(
        event="PROVIDER_EVENT",
        stream_id=stream_id,
        seq=seq,
        ts=timestamp,
        source=source,
        context=context,
        detail=detail,
        event_kind=event_kind,
        payload=payload,
        raw_line=stripped,
    )


def build_internal_event(
    *,
    seq: int,
    event: str,
    stream_id: str,
    source_component: str,
    context: dict[str, Any],
    detail: dict[str, Any],
    event_kind: str | None = None,
    payload: dict[str, Any] | None = None,
) -> NormalizedEvent:
    return NormalizedEvent(
        event=event,
        stream_id=stream_id,
        seq=seq,
        ts=datetime.now(tz=timezone.utc),
        source={
            "component": source_component,
            "version": URM_RUNTIME_VERSION,
            "provider": "codex",
        },
        context=context,
        detail=detail,
        event_kind=event_kind or event,
        payload=payload if payload is not None else detail,
        raw_line=None,
    )


def normalize_exec_line(
    *,
    seq: int,
    raw_line: str,
    stream_id: str,
    run_id: str,
    role: str,
    endpoint: str,
) -> NormalizedEvent:
    return _normalize_line(
        seq=seq,
        raw_line=raw_line,
        source_component="worker_exec",
        stream_id=stream_id,
        context={
            "run_id": run_id,
            "role": role,
            "endpoint": endpoint,
        },
    )


def normalize_app_server_line(
    *,
    seq: int,
    raw_line: str,
    stream_id: str,
    session_id: str,
    role: str,
    endpoint: str,
) -> NormalizedEvent:
    return _normalize_line(
        seq=seq,
        raw_line=raw_line,
        source_component="copilot_app_server",
        stream_id=stream_id,
        context={
            "session_id": session_id,
            "role": role,
            "endpoint": endpoint,
        },
    )


def extract_artifact_candidate(events: list[NormalizedEvent]) -> Any | None:
    for event in reversed(events):
        payload: dict[str, Any] = {}
        detail_payload = event.detail.get("payload")
        if isinstance(detail_payload, dict):
            payload = detail_payload
        elif isinstance(event.payload, dict):
            payload = event.payload
        if "final_output" in payload:
            return payload["final_output"]
        if "artifact" in payload:
            return payload["artifact"]
        if "output" in payload:
            return payload["output"]
        if "result" in payload:
            return payload["result"]
    return None
