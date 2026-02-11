from __future__ import annotations

import os
import threading
from collections.abc import Iterator
from datetime import datetime, timezone
from typing import Literal, cast

from fastapi import APIRouter, HTTPException, Query
from fastapi.responses import StreamingResponse
from urm_domain_adeu import ADEUDomainTools
from urm_runtime.capability_policy import authorize_action
from urm_runtime.config import URMRuntimeConfig
from urm_runtime.copilot import URMCopilotManager
from urm_runtime.errors import URMError
from urm_runtime.hashing import canonical_json
from urm_runtime.models import (
    ApprovalIssueRequest,
    ApprovalIssueResponse,
    ApprovalRevokeRequest,
    ApprovalRevokeResponse,
    CopilotModeRequest,
    CopilotSessionResponse,
    CopilotSessionSendRequest,
    CopilotSessionStartRequest,
    CopilotStopRequest,
    ToolCallRequest,
    ToolCallResponse,
    WorkerCancelRequest,
    WorkerCancelResponse,
    WorkerRunRequest,
    WorkerRunResult,
)
from urm_runtime.storage import db_path_from_config, get_copilot_session, transaction
from urm_runtime.worker import CodexExecWorkerRunner

router = APIRouter(prefix="/urm", tags=["urm"])

_MANAGER_LOCK = threading.Lock()
_MANAGER: URMCopilotManager | None = None
_WORKER_RUNNER: CodexExecWorkerRunner | None = None
_DOMAIN_TOOLS: ADEUDomainTools | None = None
_MANAGER_ENV_KEY: tuple[str, str] | None = None


def _manager_env_key() -> tuple[str, str]:
    return (
        os.environ.get("ADEU_API_DB_PATH", ""),
        os.environ.get("ADEU_CODEX_BIN", "codex"),
    )


def _to_http_exception(error: URMError) -> HTTPException:
    return HTTPException(status_code=error.status_code, detail=error.detail.model_dump(mode="json"))


def _get_manager() -> URMCopilotManager:
    return _get_runtime_components()[0]


def _get_worker_runner() -> CodexExecWorkerRunner:
    return _get_runtime_components()[1]


def _get_domain_tools() -> ADEUDomainTools:
    return _get_runtime_components()[2]


def _get_runtime_components() -> tuple[URMCopilotManager, CodexExecWorkerRunner, ADEUDomainTools]:
    global _MANAGER, _WORKER_RUNNER, _DOMAIN_TOOLS, _MANAGER_ENV_KEY
    key = _manager_env_key()
    with _MANAGER_LOCK:
        if _MANAGER is None or _MANAGER_ENV_KEY != key:
            if _MANAGER is not None:
                _MANAGER.shutdown()
            config = URMRuntimeConfig.from_env()
            _MANAGER = URMCopilotManager(config=config)
            _WORKER_RUNNER = CodexExecWorkerRunner(config=config)
            _DOMAIN_TOOLS = ADEUDomainTools(config=config, worker_runner=_WORKER_RUNNER)
            _MANAGER_ENV_KEY = key
        assert _MANAGER is not None, "URMCopilotManager should be initialized"
        assert _WORKER_RUNNER is not None, "CodexExecWorkerRunner should be initialized"
        assert _DOMAIN_TOOLS is not None, "ADEUDomainTools should be initialized"
        return (_MANAGER, _WORKER_RUNNER, _DOMAIN_TOOLS)


def _reset_manager_for_tests() -> None:
    global _MANAGER, _WORKER_RUNNER, _DOMAIN_TOOLS, _MANAGER_ENV_KEY
    with _MANAGER_LOCK:
        if _MANAGER is not None:
            _MANAGER.shutdown()
        _MANAGER = None
        _WORKER_RUNNER = None
        _DOMAIN_TOOLS = None
        _MANAGER_ENV_KEY = None


def _resolve_tool_policy_action(request: ToolCallRequest) -> str:
    if request.tool_name != "urm.set_mode":
        return request.tool_name
    writes_allowed = request.arguments.get("writes_allowed")
    if not isinstance(writes_allowed, bool):
        raise URMError(
            code="URM_POLICY_DENIED",
            message="writes_allowed must be a boolean",
            context={"tool_name": request.tool_name},
        )
    return "urm.set_mode.enable_writes" if writes_allowed else "urm.set_mode.disable_writes"


def _load_session_writes_allowed(session_id: str | None) -> bool:
    if session_id is None:
        return False
    config = URMRuntimeConfig.from_env()
    with transaction(db_path=db_path_from_config(config)) as con:
        row = get_copilot_session(con=con, copilot_session_id=session_id)
    if row is None:
        return False
    return row.writes_allowed


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


@router.post("/approval/issue", response_model=ApprovalIssueResponse)
def urm_approval_issue_endpoint(request: ApprovalIssueRequest) -> ApprovalIssueResponse:
    manager = _get_manager()
    try:
        return manager.issue_approval(
            session_id=request.session_id,
            action_kind=request.action_kind,
            action_payload=request.action_payload,
            expires_in_secs=request.expires_in_secs,
        )
    except URMError as exc:
        raise _to_http_exception(exc) from exc


@router.post("/approval/revoke", response_model=ApprovalRevokeResponse)
def urm_approval_revoke_endpoint(request: ApprovalRevokeRequest) -> ApprovalRevokeResponse:
    manager = _get_manager()
    try:
        return manager.revoke_approval(approval_id=request.approval_id)
    except URMError as exc:
        raise _to_http_exception(exc) from exc


@router.post("/worker/run", response_model=WorkerRunResult)
def urm_worker_run_endpoint(request: WorkerRunRequest) -> WorkerRunResult:
    runner = _get_worker_runner()
    try:
        return runner.run(request)
    except URMError as exc:
        raise _to_http_exception(exc) from exc


@router.post("/worker/{worker_id}/cancel", response_model=WorkerCancelResponse)
def urm_worker_cancel_endpoint(
    worker_id: str,
    request: WorkerCancelRequest,
) -> WorkerCancelResponse:
    if request.provider != "codex":
        raise _to_http_exception(
            URMError(
                code="URM_POLICY_DENIED",
                message="unsupported provider",
                context={"provider": request.provider},
            )
        )
    runner = _get_worker_runner()
    try:
        return runner.cancel(worker_id=worker_id)
    except URMError as exc:
        raise _to_http_exception(exc) from exc


@router.post("/tools/call", response_model=ToolCallResponse)
def urm_tool_call_endpoint(request: ToolCallRequest) -> ToolCallResponse:
    if request.provider != "codex":
        raise _to_http_exception(
            URMError(
                code="URM_POLICY_DENIED",
                message="unsupported provider",
                context={"provider": request.provider},
            )
        )

    try:
        action = _resolve_tool_policy_action(request)
        session_writes_allowed = _load_session_writes_allowed(request.session_id)
        authorize_action(
            role=request.role,
            action=action,
            writes_allowed=session_writes_allowed,
            approval_provided=bool(request.approval_id),
        )
    except URMError as exc:
        raise _to_http_exception(exc) from exc

    try:
        if request.tool_name == "urm.set_mode":
            if request.session_id is None:
                raise URMError(
                    code="URM_POLICY_DENIED",
                    message="session_id is required for urm.set_mode",
                    context={"tool_name": request.tool_name},
                )
            writes_allowed = action == "urm.set_mode.enable_writes"
            manager = _get_manager()
            mode_response = manager.set_mode(
                CopilotModeRequest(
                    provider="codex",
                    session_id=request.session_id,
                    writes_allowed=writes_allowed,
                    approval_id=request.approval_id,
                )
            )
            return ToolCallResponse(
                tool_name=request.tool_name,
                warrant="observed",
                result=mode_response.model_dump(mode="json"),
            )

        tools = _get_domain_tools()
        result, warrant = tools.call_tool(
            tool_name=request.tool_name,
            arguments=request.arguments,
        )
        return ToolCallResponse(
            tool_name=request.tool_name,
            warrant=cast(
                Literal["observed", "derived", "checked", "hypothesis", "unknown"],
                warrant,
            ),
            result=result,
        )
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
                    yield _sse_frame(
                        "codex_event",
                        event.model_dump(mode="json", by_alias=True),
                    )
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
