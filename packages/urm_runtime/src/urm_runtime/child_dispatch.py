from __future__ import annotations

import sqlite3
import threading
import uuid
from datetime import datetime, timezone
from typing import Any

from .errors import URMError
from .evidence import EvidenceFileWriter
from .hashing import sha256_canonical_json
from .models import AgentSpawnRequest, AgentSpawnResponse
from .storage import (
    IdempotencyPayloadConflict,
    lease_dispatch_token,
    persist_idempotency_response,
    persist_worker_run_start,
    reserve_request_idempotency,
    set_dispatch_token_phase,
    transaction,
    update_worker_run_status,
    upsert_dispatch_token_queued,
)


def _fail_queued_child_unlocked(
    *,
    manager: Any,
    parent_session_id: str,
    child: Any,
    error_code: str,
    error_message: str,
    reason: str,
) -> None:
    child.status = "failed"
    child.error_code = error_code
    child.error_message = error_message
    child.ended_at = datetime.now(tz=timezone.utc).isoformat()
    child.dispatch_phase = "terminal"
    manager._record_child_event(
        child=child,
        event_kind="WORKER_FAIL",
        payload={
            "worker_id": child.child_id,
            "status": "failed",
            "error_code": child.error_code,
            "code": child.error_code,
            "reason": reason,
        },
    )
    manager._record_parent_or_audit_event(
        parent_session_id=parent_session_id,
        event_kind="WORKER_FAIL",
        payload={
            "worker_id": child.child_id,
            "status": "failed",
            "error_code": child.error_code,
            "dispatch_seq": child.dispatch_seq,
            "lease_id": child.lease_id,
            "parent_stream_id": child.parent_stream_id,
            "parent_seq": child.parent_seq,
            "child_id": child.child_id,
            "phase": child.dispatch_phase,
        },
        endpoint="urm.agent.spawn",
    )
    manager._persist_child_terminal_state(child=child)


def start_child_execution_thread_unlocked(
    *,
    manager: Any,
    parent_session_id: str,
    child: Any,
) -> None:
    if manager._is_child_queue_v2_enabled():
        try:
            with transaction(db_path=manager.config.db_path) as con:
                token = lease_dispatch_token(con=con, child_id=child.child_id)
        except sqlite3.IntegrityError as exc:
            raise URMError(
                code="URM_DISPATCH_LEASE_CONFLICT",
                message="scheduler dispatch lease conflict",
                context={
                    "child_id": child.child_id,
                    "session_id": parent_session_id,
                },
            ) from exc
        except RuntimeError as exc:
            raise URMError(
                code="URM_SCHEDULER_REPLAY_ORDER_INVALID",
                message="scheduler dispatch token missing",
                context={
                    "child_id": child.child_id,
                    "session_id": parent_session_id,
                },
            ) from exc
        child.queue_seq = token.queue_seq
        child.dispatch_seq = token.dispatch_seq
        child.lease_id = token.worker_run_id
        child.parent_seq = token.parent_seq
        child.dispatch_phase = token.phase
    child.status = "running"
    if manager._is_child_queue_v2_enabled():
        child.dispatch_phase = "started"
    manager._record_child_event(
        child=child,
        event_kind="WORKER_START",
        payload={
            "worker_id": child.child_id,
            "status": "running",
            "queue_seq": child.queue_seq,
            "dispatch_seq": child.dispatch_seq,
            "lease_id": child.lease_id,
        },
    )
    with transaction(db_path=manager.config.db_path) as con:
        update_worker_run_status(
            con=con,
            worker_id=child.child_id,
            status="running",
            error_code=None,
            error_message=None,
            result_json=manager._child_worker_result_json(child=child),
        )
        if manager._is_child_queue_v2_enabled():
            token = set_dispatch_token_phase(
                con=con,
                child_id=child.child_id,
                phase="started",
            )
            child.dispatch_phase = token.phase
    thread = threading.Thread(
        target=manager._run_child_workflow_v2,
        kwargs={"child_id": child.child_id, "parent_session_id": parent_session_id},
        daemon=True,
        name=f"urm-child-{child.child_id}",
    )
    manager._child_run_threads[child.child_id] = thread
    thread.start()


def dispatch_child_queue_unlocked(*, manager: Any, parent_session_id: str) -> None:
    while True:
        children = [
            manager._child_runs[child_id]
            for child_id in manager._children_by_parent.get(parent_session_id, set())
            if child_id in manager._child_runs
        ]
        running_count = sum(1 for child in children if child.status == "running")
        if running_count >= manager._max_active_children_per_parent():
            return
        queued = sorted(
            (child for child in children if child.status == "queued"),
            key=lambda child: child.queue_seq,
        )
        if not queued:
            return
        next_child = queued[0]
        runtime = manager._sessions.get(parent_session_id)
        if runtime is None or runtime.status not in {"starting", "running"}:
            _fail_queued_child_unlocked(
                manager=manager,
                parent_session_id=parent_session_id,
                child=next_child,
                error_code="URM_CHILD_TERMINATED_ON_RESTART",
                error_message="parent session unavailable during queue dispatch",
                reason="parent_session_unavailable",
            )
            continue
        try:
            start_child_execution_thread_unlocked(
                manager=manager,
                parent_session_id=parent_session_id,
                child=next_child,
            )
        except URMError as exc:
            _fail_queued_child_unlocked(
                manager=manager,
                parent_session_id=parent_session_id,
                child=next_child,
                error_code=exc.detail.code,
                error_message=exc.detail.message,
                reason="dispatch_start_failed",
            )
            continue


def spawn_child_v2(
    *,
    manager: Any,
    request: AgentSpawnRequest,
    inherited_policy_hash: str | None,
    capabilities_allowed: list[str],
    child_runtime_cls: type[Any],
    max_child_depth: int,
    spawn_endpoint_name: str,
) -> AgentSpawnResponse:
    payload_hash = sha256_canonical_json(request.idempotency_payload())
    with manager._lock:
        runtime = manager._sessions.get(request.session_id)
        if runtime is None:
            raise URMError(
                code="URM_NOT_FOUND",
                message="copilot session not found",
                status_code=404,
                context={"session_id": request.session_id},
            )
        manager._enforce_session_duration_unlocked(runtime=runtime)
        with transaction(db_path=manager.config.db_path) as con:
            child_id = uuid.uuid4().hex
            try:
                reservation = reserve_request_idempotency(
                    con=con,
                    endpoint_name=spawn_endpoint_name,
                    client_request_id=request.client_request_id,
                    payload_hash=payload_hash,
                    resource_id=child_id,
                )
            except IdempotencyPayloadConflict as exc:
                raise URMError(
                    code="URM_IDEMPOTENCY_KEY_CONFLICT",
                    message="client_request_id already used with a different payload",
                    status_code=409,
                    context={
                        "client_request_id": request.client_request_id,
                        "stored_payload_hash": exc.stored_payload_hash,
                        "incoming_payload_hash": exc.incoming_payload_hash,
                    },
                ) from exc
            if reservation.replay:
                replay = AgentSpawnResponse.model_validate(reservation.response_json or {})
                return replay.model_copy(update={"idempotent_replay": True})
            child_id = reservation.resource_id
        active_or_queued_children = [
            child_id
            for child_id in manager._children_by_parent.get(request.session_id, set())
            if manager._child_runs.get(child_id) is not None
            and manager._child_runs[child_id].status in {"queued", "running"}
        ]
        if len(active_or_queued_children) >= manager._max_children_per_parent():
            raise URMError(
                code="URM_CHILD_QUEUE_LIMIT_EXCEEDED",
                message="child queue limit exceeded for parent session",
                context={
                    "session_id": request.session_id,
                    "max_children": manager._max_children_per_parent(),
                },
            )
        if max_child_depth < 1:
            raise URMError(
                code="URM_CHILD_DEPTH_EXCEEDED",
                message="child depth limit exceeded",
                context={"session_id": request.session_id, "max_depth": max_child_depth},
            )

        selected_profile = manager._resolve_profile(runtime.profile_id)
        if request.profile_id is not None:
            try:
                selected_profile = manager._resolve_profile(request.profile_id)
            except URMError as exc:
                manager._record_parent_or_audit_event(
                    parent_session_id=request.session_id,
                    event_kind="PROFILE_DENIED",
                    payload={
                        "profile_id": request.profile_id,
                        "scope": "run",
                        "reason": exc.detail.message,
                    },
                )
                raise
            manager._record_parent_or_audit_event(
                parent_session_id=request.session_id,
                event_kind="PROFILE_SELECTED",
                payload={
                    "profile_id": selected_profile.profile_id,
                    "profile_version": selected_profile.profile_version,
                    "policy_hash": manager._resolve_active_policy_hash_for_profile(
                        profile=selected_profile
                    ),
                    "scope": "run",
                    "child_id": child_id,
                },
            )

        target_turn_id = manager._resolve_turn_target(
            runtime=runtime,
            target_turn_id=request.target_turn_id,
            use_last_turn=request.use_last_turn,
        )
        manager._bootstrap_runtime(runtime=runtime)
        if runtime.thread_id is None:
            raise URMError(
                code="URM_CHILD_SPAWN_FAILED",
                message="copilot thread is not initialized",
                context={"session_id": request.session_id},
            )

        raw_path = manager._raw_jsonl_path_for_child(child_id)
        events_path = manager._urm_events_path_for_child(child_id)
        raw_rel_path = manager._relative_path(raw_path)
        events_rel_path = manager._relative_path(events_path)
        parent_stream_id = f"copilot:{request.session_id}"
        parent_seq_anchor = runtime.last_seq + 1
        try:
            with transaction(db_path=manager.config.db_path) as con:
                token = upsert_dispatch_token_queued(
                    con=con,
                    child_id=child_id,
                    parent_session_id=request.session_id,
                    parent_stream_id=parent_stream_id,
                    parent_seq=parent_seq_anchor,
                    worker_run_id=child_id,
                )
        except sqlite3.IntegrityError as exc:
            raise URMError(
                code="URM_DISPATCH_LEASE_CONFLICT",
                message="scheduler token persistence conflict",
                context={
                    "session_id": request.session_id,
                    "child_id": child_id,
                },
            ) from exc
        except RuntimeError as exc:
            raise URMError(
                code="URM_SCHEDULER_REPLAY_ORDER_INVALID",
                message="scheduler token persistence failed",
                context={
                    "session_id": request.session_id,
                    "child_id": child_id,
                },
            ) from exc
        child = child_runtime_cls(
            child_id=child_id,
            parent_session_id=request.session_id,
            parent_turn_id=target_turn_id,
            parent_stream_id=parent_stream_id,
            child_stream_id=f"child:{child_id}",
            started_at=datetime.now(tz=timezone.utc).isoformat(),
            events_writer=EvidenceFileWriter(
                path=events_path,
                max_line_bytes=manager.config.max_line_bytes,
                max_file_bytes=manager.config.max_evidence_file_bytes,
            ),
            raw_writer=EvidenceFileWriter(
                path=raw_path,
                max_line_bytes=manager.config.max_line_bytes,
                max_file_bytes=manager.config.max_evidence_file_bytes,
            ),
            raw_jsonl_path=raw_rel_path,
            urm_events_path=events_rel_path,
            status="queued",
            parent_seq=token.parent_seq,
            queue_seq=token.queue_seq,
            lease_id=token.worker_run_id,
            dispatch_phase=token.phase,
            prompt=request.prompt,
            budget_snapshot=manager._child_budget_snapshot(runtime=runtime),
            inherited_policy_hash=inherited_policy_hash,
            capabilities_allowed=sorted(capabilities_allowed),
            profile_id=selected_profile.profile_id,
            profile_version=selected_profile.profile_version,
        )
        manager._child_runs[child_id] = child
        manager._children_by_parent.setdefault(request.session_id, set()).add(child_id)
        manager._record_parent_or_audit_event(
            parent_session_id=request.session_id,
            event_kind="TOOL_CALL_START",
            payload={
                "tool_name": "spawn_agent",
                "child_id": child_id,
                "target_turn_id": target_turn_id,
                "budget_snapshot": child.budget_snapshot,
                "inherited_policy_hash": inherited_policy_hash,
                "profile_id": child.profile_id,
                "profile_version": child.profile_version,
                "queue_seq": child.queue_seq,
                "parent_stream_id": child.parent_stream_id,
                "parent_seq": child.parent_seq,
            },
        )
        manager._record_child_event(
            child=child,
            event_kind="WORKER_START",
            payload={
                "worker_id": child_id,
                "status": "queued",
                "queue_seq": child.queue_seq,
                "dispatch_seq": child.dispatch_seq,
                "lease_id": child.lease_id,
            },
        )
        with transaction(db_path=manager.config.db_path) as con:
            persist_worker_run_start(
                con=con,
                worker_id=child.child_id,
                role="copilot_child",
                provider="codex",
                template_id="urm.agent.spawn",
                template_version="v2",
                schema_version="urm.child-run.v1",
                domain_pack_id="urm_domain_adeu",
                domain_pack_version="v0",
                raw_jsonl_path=child.raw_jsonl_path,
                status="queued",
                result_json=manager._child_worker_result_json(child=child),
            )
        dispatch_child_queue_unlocked(manager=manager, parent_session_id=request.session_id)
        response_model = AgentSpawnResponse(
            child_id=child.child_id,
            parent_session_id=child.parent_session_id,
            status=child.status,
            parent_stream_id=child.parent_stream_id,
            child_stream_id=child.child_stream_id,
            target_turn_id=child.parent_turn_id,
            queue_seq=child.queue_seq,
            profile_id=child.profile_id,
            profile_version=child.profile_version,
            idempotent_replay=False,
            error=None,
            budget_snapshot=child.budget_snapshot,
            inherited_policy_hash=child.inherited_policy_hash,
        )
        with transaction(db_path=manager.config.db_path) as con:
            persist_idempotency_response(
                con=con,
                endpoint_name=spawn_endpoint_name,
                client_request_id=request.client_request_id,
                response_json=response_model.model_dump(mode="json"),
            )
        return response_model
