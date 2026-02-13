from __future__ import annotations

import os
import threading
from collections.abc import Iterator
from datetime import datetime, timezone
from typing import Any, Literal, cast

from fastapi import APIRouter, HTTPException, Query
from fastapi.responses import StreamingResponse
from urm_domain_adeu import ADEUDomainTools
from urm_domain_digest import DigestDomainTools
from urm_domain_paper import PaperDomainTools
from urm_runtime.capability_policy import (
    PolicyEvalEventCallback,
    PolicyEvalEventName,
    authorize_action,
    load_capability_policy,
)
from urm_runtime.config import URMRuntimeConfig
from urm_runtime.copilot import URMCopilotManager
from urm_runtime.domain_registry import DomainToolRegistry
from urm_runtime.errors import URMError
from urm_runtime.hashing import action_hash as compute_action_hash
from urm_runtime.hashing import canonical_json
from urm_runtime.models import (
    AgentCancelRequest,
    AgentCancelResponse,
    AgentSpawnRequest,
    AgentSpawnResponse,
    ApprovalIssueRequest,
    ApprovalIssueResponse,
    ApprovalRevokeRequest,
    ApprovalRevokeResponse,
    ConnectorSnapshotCreateRequest,
    ConnectorSnapshotResponse,
    CopilotModeRequest,
    CopilotSessionResponse,
    CopilotSessionSendRequest,
    CopilotSessionStartRequest,
    CopilotSteerRequest,
    CopilotSteerResponse,
    CopilotStopRequest,
    PolicyProfileCurrentResponse,
    PolicyProfileListResponse,
    PolicyProfileSelectRequest,
    PolicyProfileSelectResponse,
    ToolCallRequest,
    ToolCallResponse,
    WorkerCancelRequest,
    WorkerCancelResponse,
    WorkerRunRequest,
    WorkerRunResult,
)
from urm_runtime.storage import (
    ApprovalRow,
    db_path_from_config,
    get_approval,
    get_copilot_session,
    transaction,
)
from urm_runtime.worker import CodexExecWorkerRunner

router = APIRouter(prefix="/urm", tags=["urm"])

_MANAGER_LOCK = threading.Lock()
_MANAGER: URMCopilotManager | None = None
_WORKER_RUNNER: CodexExecWorkerRunner | None = None
_DOMAIN_REGISTRY: DomainToolRegistry | None = None
_MANAGER_ENV_KEY: tuple[str, str] | None = None


def _manager_env_key() -> tuple[str, str]:
    return (
        os.environ.get("ADEU_API_DB_PATH", ""),
        os.environ.get("ADEU_CODEX_BIN", "codex"),
    )


def _to_http_exception(error: URMError) -> HTTPException:
    return HTTPException(status_code=error.status_code, detail=error.detail.model_dump(mode="json"))


def _require_codex_provider(provider: str) -> None:
    if provider != "codex":
        raise _to_http_exception(
            URMError(
                code="URM_POLICY_DENIED",
                message="unsupported provider",
                context={"provider": provider},
            )
        )


def _get_manager() -> URMCopilotManager:
    return _get_runtime_components()[0]


def _get_worker_runner() -> CodexExecWorkerRunner:
    return _get_runtime_components()[1]


def _get_domain_registry() -> DomainToolRegistry:
    return _get_runtime_components()[2]


def _get_runtime_components() -> tuple[
    URMCopilotManager,
    CodexExecWorkerRunner,
    DomainToolRegistry,
]:
    global _MANAGER, _WORKER_RUNNER, _DOMAIN_REGISTRY, _MANAGER_ENV_KEY
    key = _manager_env_key()
    with _MANAGER_LOCK:
        if _MANAGER is None or _MANAGER_ENV_KEY != key:
            if _MANAGER is not None:
                _MANAGER.shutdown()
            config = URMRuntimeConfig.from_env()
            _MANAGER = URMCopilotManager(config=config)
            _WORKER_RUNNER = CodexExecWorkerRunner(config=config)
            _DOMAIN_REGISTRY = DomainToolRegistry.build(
                tool_packs=[
                    ADEUDomainTools(config=config, worker_runner=_WORKER_RUNNER),
                    DigestDomainTools(),
                    PaperDomainTools(),
                ]
            )
            _MANAGER_ENV_KEY = key
        assert _MANAGER is not None, "URMCopilotManager should be initialized"
        assert _WORKER_RUNNER is not None, "CodexExecWorkerRunner should be initialized"
        assert _DOMAIN_REGISTRY is not None, "DomainToolRegistry should be initialized"
        return (_MANAGER, _WORKER_RUNNER, _DOMAIN_REGISTRY)


def _reset_manager_for_tests() -> None:
    global _MANAGER, _WORKER_RUNNER, _DOMAIN_REGISTRY, _MANAGER_ENV_KEY
    with _MANAGER_LOCK:
        if _MANAGER is not None:
            _MANAGER.shutdown()
        _MANAGER = None
        _WORKER_RUNNER = None
        _DOMAIN_REGISTRY = None
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


def _resolve_steer_policy_action() -> str:
    return "urm.turn.steer"


def _resolve_spawn_policy_action() -> str:
    return "urm.agent.spawn"


def _resolve_cancel_policy_action() -> str:
    return "urm.agent.cancel"


def _resolve_connector_snapshot_create_policy_action() -> str:
    return "urm.connectors.snapshot.create"


def _resolve_connector_snapshot_get_policy_action() -> str:
    return "urm.connectors.snapshot.get"


def _load_session_writes_allowed(session_id: str | None) -> bool:
    writes_allowed, _ = _load_session_access_state(session_id)
    return writes_allowed


def _load_session_access_state(session_id: str | None) -> tuple[bool, bool]:
    if session_id is None:
        return (False, False)
    manager = _get_manager()
    with transaction(db_path=db_path_from_config(manager.config)) as con:
        row = get_copilot_session(con=con, copilot_session_id=session_id)
    if row is None:
        return (False, False)
    return (row.writes_allowed, row.status in {"starting", "running"})


def _parse_db_timestamp(value: str) -> datetime:
    text = value.strip()
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    parsed = datetime.fromisoformat(text)
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed.astimezone(timezone.utc)


def _resolve_approval_precheck(
    *,
    session_id: str | None,
    approval_id: str | None,
    action: str,
    action_payload: dict[str, object],
) -> tuple[bool, bool, bool]:
    if approval_id is None:
        return (False, False, False)
    if session_id is None:
        raise URMError(
            code="URM_APPROVAL_INVALID",
            message="approval requires session context",
            context={"action": action},
        )
    manager = _get_manager()
    with transaction(db_path=db_path_from_config(manager.config)) as con:
        approval: ApprovalRow | None = get_approval(con=con, approval_id=approval_id)
    if approval is None:
        raise URMError(
            code="URM_APPROVAL_INVALID",
            message="approval not found",
            context={"approval_id": approval_id, "action": action},
        )
    if approval.copilot_session_id != session_id:
        raise URMError(
            code="URM_APPROVAL_INVALID",
            message="approval does not belong to this session",
            context={"approval_id": approval_id, "session_id": session_id},
        )
    expected_hash = compute_action_hash(action_kind=action, action_payload=action_payload)
    if approval.action_kind != action or approval.action_hash != expected_hash:
        raise URMError(
            code="URM_APPROVAL_INVALID",
            message="approval action does not match request action",
            context={"approval_id": approval_id, "action": action},
        )
    if approval.revoked_at is not None or approval.consumed_at is not None:
        raise URMError(
            code="URM_APPROVAL_INVALID",
            message="approval is no longer usable",
            context={"approval_id": approval_id, "action": action},
        )
    expires_at = _parse_db_timestamp(approval.expires_at)
    now = datetime.now(tz=timezone.utc)
    if now > expires_at:
        raise URMError(
            code="URM_APPROVAL_EXPIRED",
            message="approval expired",
            context={"approval_id": approval_id, "action": action},
        )
    return (True, True, True)


def _policy_event_emitter(*, session_id: str | None) -> PolicyEvalEventCallback:
    manager = _get_manager()

    def _emit(event_name: PolicyEvalEventName, detail: dict[str, Any]) -> None:
        manager.record_policy_eval_event(
            session_id=session_id,
            event_kind=event_name,
            detail=detail,
        )

    return _emit


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


@router.post("/copilot/steer", response_model=CopilotSteerResponse)
def urm_copilot_steer_endpoint(request: CopilotSteerRequest) -> CopilotSteerResponse:
    _require_codex_provider(request.provider)
    manager = _get_manager()
    try:
        session_writes_allowed, session_active = _load_session_access_state(request.session_id)
        _ = authorize_action(
            role="copilot",
            action=_resolve_steer_policy_action(),
            writes_allowed=session_writes_allowed,
            approval_provided=False,
            action_payload={
                "target_turn_id": request.target_turn_id,
                "use_last_turn": request.use_last_turn,
                "steer_intent_class": request.steer_intent_class,
                "text": request.text,
            },
            session_active=session_active,
            emit_policy_event=_policy_event_emitter(session_id=request.session_id),
        )
        return manager.steer(request)
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


@router.get("/policy/profile/list", response_model=PolicyProfileListResponse)
def urm_policy_profile_list_endpoint(
    *,
    provider: Literal["codex"] = Query(default="codex"),
) -> PolicyProfileListResponse:
    _require_codex_provider(provider)
    manager = _get_manager()
    return manager.list_profiles()


@router.get("/policy/profile/current", response_model=PolicyProfileCurrentResponse)
def urm_policy_profile_current_endpoint(
    *,
    session_id: str = Query(min_length=1),
    provider: Literal["codex"] = Query(default="codex"),
) -> PolicyProfileCurrentResponse:
    _require_codex_provider(provider)
    manager = _get_manager()
    try:
        return manager.current_profile(session_id=session_id)
    except URMError as exc:
        raise _to_http_exception(exc) from exc


@router.post("/policy/profile/select", response_model=PolicyProfileSelectResponse)
def urm_policy_profile_select_endpoint(
    request: PolicyProfileSelectRequest,
) -> PolicyProfileSelectResponse:
    _require_codex_provider(request.provider)
    manager = _get_manager()
    try:
        return manager.select_profile(request)
    except URMError as exc:
        raise _to_http_exception(exc) from exc


@router.post("/agent/spawn", response_model=AgentSpawnResponse)
def urm_agent_spawn_endpoint(request: AgentSpawnRequest) -> AgentSpawnResponse:
    _require_codex_provider(request.provider)
    manager = _get_manager()
    try:
        session_writes_allowed, session_active = _load_session_access_state(request.session_id)
        decision = authorize_action(
            role="copilot",
            action=_resolve_spawn_policy_action(),
            writes_allowed=session_writes_allowed,
            approval_provided=False,
            action_payload={
                "target_turn_id": request.target_turn_id,
                "use_last_turn": request.use_last_turn,
                "prompt": request.prompt,
            },
            session_active=session_active,
            emit_policy_event=_policy_event_emitter(session_id=request.session_id),
        )
        policy_trace = decision.policy_decision
        capability_policy = load_capability_policy()
        role_caps = sorted(capability_policy.role_capabilities.get("copilot", frozenset()))
        return manager.spawn_child(
            request,
            inherited_policy_hash=policy_trace.policy_hash,
            capabilities_allowed=role_caps,
        )
    except URMError as exc:
        raise _to_http_exception(exc) from exc


@router.post("/agent/{child_id}/cancel", response_model=AgentCancelResponse)
def urm_agent_cancel_endpoint(child_id: str, request: AgentCancelRequest) -> AgentCancelResponse:
    _require_codex_provider(request.provider)
    manager = _get_manager()
    try:
        parent_session_id = manager.child_parent_session_id(child_id=child_id)
        session_writes_allowed, session_active = _load_session_access_state(parent_session_id)
        _ = authorize_action(
            role="copilot",
            action=_resolve_cancel_policy_action(),
            writes_allowed=session_writes_allowed,
            approval_provided=False,
            action_payload={"child_id": child_id},
            session_active=session_active,
            emit_policy_event=_policy_event_emitter(session_id=parent_session_id),
        )
        return manager.cancel_child(child_id=child_id, request=request)
    except URMError as exc:
        raise _to_http_exception(exc) from exc


@router.post("/connectors/snapshot", response_model=ConnectorSnapshotResponse)
def urm_connector_snapshot_create_endpoint(
    request: ConnectorSnapshotCreateRequest,
) -> ConnectorSnapshotResponse:
    _require_codex_provider(request.provider)
    manager = _get_manager()
    try:
        session_writes_allowed, session_active = _load_session_access_state(request.session_id)
        _ = authorize_action(
            role="copilot",
            action=_resolve_connector_snapshot_create_policy_action(),
            writes_allowed=session_writes_allowed,
            approval_provided=False,
            action_payload={
                "requested_capability_snapshot_id": request.requested_capability_snapshot_id,
                "min_acceptable_ts": (
                    request.min_acceptable_ts.isoformat()
                    if request.min_acceptable_ts is not None
                    else None
                ),
            },
            session_active=session_active,
            emit_policy_event=_policy_event_emitter(session_id=request.session_id),
        )
        return manager.create_connector_snapshot(request)
    except URMError as exc:
        raise _to_http_exception(exc) from exc


@router.get("/connectors/snapshot/{snapshot_id}", response_model=ConnectorSnapshotResponse)
def urm_connector_snapshot_get_endpoint(
    snapshot_id: str,
    *,
    session_id: str,
    provider: str = "codex",
    requested_capability_snapshot_id: str | None = None,
    min_acceptable_ts: datetime | None = None,
) -> ConnectorSnapshotResponse:
    _require_codex_provider(provider)
    manager = _get_manager()
    try:
        session_writes_allowed, session_active = _load_session_access_state(session_id)
        _ = authorize_action(
            role="copilot",
            action=_resolve_connector_snapshot_get_policy_action(),
            writes_allowed=session_writes_allowed,
            approval_provided=False,
            action_payload={
                "snapshot_id": snapshot_id,
                "requested_capability_snapshot_id": requested_capability_snapshot_id,
                "min_acceptable_ts": (
                    min_acceptable_ts.isoformat() if min_acceptable_ts is not None else None
                ),
            },
            session_active=session_active,
            emit_policy_event=_policy_event_emitter(session_id=session_id),
        )
        return manager.get_connector_snapshot(
            snapshot_id=snapshot_id,
            session_id=session_id,
            provider=provider,
            requested_capability_snapshot_id=requested_capability_snapshot_id,
            min_acceptable_ts=min_acceptable_ts,
        )
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
    _require_codex_provider(request.provider)
    runner = _get_worker_runner()
    try:
        return runner.cancel(worker_id=worker_id)
    except URMError as exc:
        raise _to_http_exception(exc) from exc


@router.post("/tools/call", response_model=ToolCallResponse)
def urm_tool_call_endpoint(request: ToolCallRequest) -> ToolCallResponse:
    _require_codex_provider(request.provider)

    try:
        action = _resolve_tool_policy_action(request)
        session_writes_allowed, session_active = _load_session_access_state(request.session_id)
        approval_valid, approval_unexpired, approval_unused = _resolve_approval_precheck(
            session_id=request.session_id,
            approval_id=request.approval_id,
            action=action,
            action_payload=request.arguments,
        )
        decision = authorize_action(
            role=request.role,
            action=action,
            writes_allowed=session_writes_allowed,
            approval_provided=bool(request.approval_id),
            action_payload=request.arguments,
            approval_valid=approval_valid,
            approval_unexpired=approval_unexpired,
            approval_unused=approval_unused,
            session_active=session_active,
            emit_policy_event=_policy_event_emitter(session_id=request.session_id),
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
                policy_trace=decision.policy_decision.model_dump(mode="json"),
            )

        domain_registry = _get_domain_registry()
        result, warrant = domain_registry.call_tool(
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
            policy_trace=decision.policy_decision.model_dump(mode="json"),
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
