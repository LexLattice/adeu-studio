from __future__ import annotations

import os
import threading
from collections.abc import Iterator
from datetime import datetime, timezone
from typing import Literal

from fastapi import APIRouter, HTTPException, Query
from fastapi.responses import StreamingResponse
from urm_runtime.config import URMRuntimeConfig
from urm_runtime.copilot import URMCopilotManager
from urm_runtime.errors import URMError
from urm_runtime.hashing import canonical_json
from urm_runtime.models import (
    CopilotModeRequest,
    CopilotSessionResponse,
    CopilotSessionSendRequest,
    CopilotSessionStartRequest,
    CopilotStopRequest,
)

router = APIRouter(prefix="/urm", tags=["urm"])

_MANAGER_LOCK = threading.Lock()
_MANAGER: URMCopilotManager | None = None
_MANAGER_ENV_KEY: tuple[str, str] | None = None


def _manager_env_key() -> tuple[str, str]:
    return (
        os.environ.get("ADEU_API_DB_PATH", ""),
        os.environ.get("ADEU_CODEX_BIN", "codex"),
    )


def _to_http_exception(error: URMError) -> HTTPException:
    return HTTPException(status_code=error.status_code, detail=error.detail.model_dump(mode="json"))


def _get_manager() -> URMCopilotManager:
    global _MANAGER, _MANAGER_ENV_KEY
    key = _manager_env_key()
    with _MANAGER_LOCK:
        if _MANAGER is None or _MANAGER_ENV_KEY != key:
            if _MANAGER is not None:
                _MANAGER.shutdown()
            _MANAGER = URMCopilotManager(config=URMRuntimeConfig.from_env())
            _MANAGER_ENV_KEY = key
        return _MANAGER


def _reset_manager_for_tests() -> None:
    global _MANAGER, _MANAGER_ENV_KEY
    with _MANAGER_LOCK:
        if _MANAGER is not None:
            _MANAGER.shutdown()
        _MANAGER = None
        _MANAGER_ENV_KEY = None


@router.post("/copilot/start", response_model=CopilotSessionResponse)
def urm_copilot_start_endpoint(request: CopilotSessionStartRequest) -> CopilotSessionResponse:
    manager = _get_manager()
    try:
        return manager.start_session(request)
    except URMError as exc:
        raise _to_http_exception(exc) from exc


@router.post("/copilot/send", response_model=CopilotSessionResponse)
def urm_copilot_send_endpoint(request: CopilotSessionSendRequest) -> CopilotSessionResponse:
    manager = _get_manager()
    try:
        return manager.send(request)
    except URMError as exc:
        raise _to_http_exception(exc) from exc


@router.post("/copilot/stop", response_model=CopilotSessionResponse)
def urm_copilot_stop_endpoint(request: CopilotStopRequest) -> CopilotSessionResponse:
    manager = _get_manager()
    try:
        return manager.stop(request)
    except URMError as exc:
        raise _to_http_exception(exc) from exc


@router.post("/copilot/mode", response_model=CopilotSessionResponse)
def urm_copilot_mode_endpoint(request: CopilotModeRequest) -> CopilotSessionResponse:
    manager = _get_manager()
    try:
        return manager.set_mode(request)
    except URMError as exc:
        raise _to_http_exception(exc) from exc


def _sse_frame(event_type: str, payload: dict[str, object]) -> str:
    return f"event: {event_type}\ndata: {canonical_json(payload)}\n\n"


@router.get("/copilot/events")
def urm_copilot_events_endpoint(
    *,
    session_id: str = Query(min_length=1),
    after_seq: int = Query(default=0, ge=0),
    provider: Literal["codex"] = Query(default="codex"),
    max_events: int | None = Query(default=None, ge=1),
) -> StreamingResponse:
    del provider
    manager = _get_manager()

    def _stream() -> Iterator[str]:
        next_seq = after_seq
        emitted = 0
        while True:
            try:
                events, status = manager.iter_events(session_id=session_id, after_seq=next_seq)
            except URMError as exc:
                yield _sse_frame(
                    "session_status",
                    {
                        "session_id": session_id,
                        "status": "failed",
                        "error": exc.detail.model_dump(mode="json"),
                    },
                )
                return

            if events:
                for event in events:
                    next_seq = max(next_seq, event.seq)
                    emitted += 1
                    yield _sse_frame("codex_event", event.model_dump(mode="json"))
                    if max_events is not None and emitted >= max_events:
                        return
                continue

            if status in {"stopped", "failed"}:
                yield _sse_frame(
                    "session_status",
                    {
                        "session_id": session_id,
                        "status": status,
                        "last_seq": next_seq,
                    },
                )
                return

            yield _sse_frame(
                "heartbeat",
                {"session_id": session_id, "ts": datetime.now(tz=timezone.utc).isoformat()},
            )

    return StreamingResponse(_stream(), media_type="text/event-stream")
