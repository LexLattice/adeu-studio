from __future__ import annotations

import json
import re
from datetime import datetime, timezone
from importlib.metadata import PackageNotFoundError, version
from json import JSONDecodeError
from typing import Any, Literal

from .models import NormalizedEvent

try:
    URM_RUNTIME_VERSION = version("urm-runtime")
except PackageNotFoundError:
    URM_RUNTIME_VERSION = "0.0.0"

_ANSI_ESCAPE_RE = re.compile(r"\x1b\[[0-9;]*m")
_ROLLOUT_MISSING_PATH_RE = re.compile(
    r".*codex_core::rollout::list.*state db missing rollout path for thread\s+([0-9a-f\-]+)",
    re.IGNORECASE,
)
_MARKDOWN_JSON_FENCE_RE = re.compile(
    r"```(?:json)?\s*(?P<body>.*?)```",
    re.IGNORECASE | re.DOTALL,
)


def _strip_ansi(text: str) -> str:
    return _ANSI_ESCAPE_RE.sub("", text)


def _provider_log_payload(raw_line: str) -> dict[str, Any] | None:
    normalized = _strip_ansi(raw_line).strip()
    if not normalized:
        return None
    rollout_match = _ROLLOUT_MISSING_PATH_RE.match(normalized)
    if rollout_match is None:
        return None
    return {
        "provider_log_kind": "rollout_state_db_missing_path",
        "severity": "error",
        "thread_id": rollout_match.group(1),
        "message": normalized,
    }


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
        provider_log = _provider_log_payload(stripped)
        if provider_log is not None:
            return NormalizedEvent(
                event="PROVIDER_LOG",
                stream_id=stream_id,
                seq=seq,
                ts=timestamp,
                source=source,
                context=context,
                detail=provider_log,
                event_kind="provider_log",
                payload=provider_log,
                raw_line=stripped,
            )
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


def _coerce_json_object(value: Any) -> dict[str, Any] | None:
    if isinstance(value, dict):
        return value
    if not isinstance(value, str):
        return None
    candidate = value.strip()
    if not candidate:
        return None
    try:
        parsed = json.loads(candidate)
    except JSONDecodeError:
        return None
    if isinstance(parsed, dict):
        return parsed
    return None


def _extract_json_object_from_text(text: str) -> dict[str, Any] | None:
    candidate = text.strip()
    if not candidate:
        return None

    direct = _coerce_json_object(candidate)
    if direct is not None:
        return direct

    for match in _MARKDOWN_JSON_FENCE_RE.finditer(candidate):
        body = match.group("body").strip()
        parsed = _coerce_json_object(body)
        if parsed is not None:
            return parsed

    start = candidate.find("{")
    end = candidate.rfind("}")
    if start != -1 and end > start:
        inner = candidate[start : end + 1]
        parsed = _coerce_json_object(inner)
        if parsed is not None:
            return parsed
    return None


def _extract_candidate_from_item_payload(payload: dict[str, Any]) -> Any | None:
    item = payload.get("item")
    if not isinstance(item, dict):
        return None
    item_type = item.get("type")
    if item_type not in {"agent_message", "assistant_message", "message"}:
        return None

    text_candidates: list[str] = []
    text = item.get("text")
    if isinstance(text, str):
        text_candidates.append(text)
    content = item.get("content")
    if isinstance(content, list):
        for block in content:
            if not isinstance(block, dict):
                continue
            block_text = block.get("text")
            if isinstance(block_text, str):
                text_candidates.append(block_text)
    for candidate_text in reversed(text_candidates):
        parsed = _extract_json_object_from_text(candidate_text)
        if parsed is not None:
            return parsed
    return None


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
        item_candidate = _extract_candidate_from_item_payload(payload)
        if item_candidate is not None:
            return item_candidate
    return None
