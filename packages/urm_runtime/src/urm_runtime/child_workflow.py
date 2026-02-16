from __future__ import annotations

from datetime import datetime, timezone
from typing import Any

from .errors import URMError


def run_child_workflow_v2(
    *,
    manager: Any,
    child_id: str,
    parent_session_id: str,
) -> None:
    try:
        with manager._lock:
            child = manager._child_runs.get(child_id)
            runtime = manager._sessions.get(parent_session_id)
            if child is None:
                return
            if runtime is None or runtime.status not in {"starting", "running"}:
                child.status = "failed"
                child.error_code = "URM_CHILD_TERMINATED_ON_RESTART"
                child.error_message = "parent session unavailable"
                child.ended_at = datetime.now(tz=timezone.utc).isoformat()
                child.dispatch_phase = "terminal"
                manager._record_child_event(
                    child=child,
                    event_kind="WORKER_FAIL",
                    payload={
                        "worker_id": child.child_id,
                        "status": "failed",
                        "error_code": child.error_code,
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
                return
            manager._bootstrap_runtime(runtime=runtime)
            if runtime.thread_id is None:
                raise URMError(
                    code="URM_CHILD_SPAWN_FAILED",
                    message="copilot thread is not initialized",
                    context={"session_id": parent_session_id},
                )
            prompt = child.prompt
            target_turn_id = child.parent_turn_id
            parent_thread_id = runtime.thread_id

        def _child_call(method: str, params: dict[str, Any]) -> dict[str, Any]:
            with manager._lock:
                current = manager._child_runs.get(child_id)
                if current is None:
                    raise URMError(
                        code="URM_CHILD_SPAWN_FAILED",
                        message="child run missing",
                        context={"child_id": child_id},
                    )
                if current.status == "cancelled":
                    raise URMError(
                        code="URM_CHILD_CANCELLED",
                        message="child run cancelled",
                        context={"child_id": child_id},
                    )
                manager._enforce_child_budget_unlocked(child=current)
                current.solver_calls_observed += 1
            response = manager._send_jsonrpc_and_wait(
                runtime=runtime,
                method=method,
                params=params,
                timeout_secs=10.0,
            )
            token_usage = manager._extract_authoritative_token_usage(response=response)
            with manager._lock:
                current = manager._child_runs.get(child_id)
                if current is None:
                    raise URMError(
                        code="URM_CHILD_SPAWN_FAILED",
                        message="child run missing",
                        context={"child_id": child_id},
                    )
                if current.status == "cancelled":
                    raise URMError(
                        code="URM_CHILD_CANCELLED",
                        message="child run cancelled",
                        context={"child_id": child_id},
                    )
                if token_usage is not None:
                    current.token_usage_observed = token_usage
                    current.token_usage_unobserved = False
                manager._enforce_child_budget_unlocked(child=current)
                manager._record_child_event(
                    child=current,
                    event_kind="TOOL_CALL_PASS",
                    payload={"tool_name": method, "status": "completed"},
                )
            return response

        spawn_response = _child_call(
            "spawn_agent",
            {"threadId": parent_thread_id, "turnId": target_turn_id},
        )
        result = spawn_response.get("result", {})
        child_thread_id = (
            result.get("newThreadId") or result.get("receiverThreadId") or result.get("threadId")
        )
        if not isinstance(child_thread_id, str) or not child_thread_id:
            child_thread_id = f"child-thread:{child_id}"
        with manager._lock:
            current = manager._child_runs.get(child_id)
            if current is None:
                return
            current.child_thread_id = child_thread_id
        _child_call(
            "send_input",
            {
                "threadId": parent_thread_id,
                "receiverThreadId": child_thread_id,
                "prompt": prompt,
            },
        )
        _child_call(
            "wait",
            {
                "threadId": parent_thread_id,
                "receiverThreadId": child_thread_id,
            },
        )
        _child_call(
            "close_agent",
            {
                "threadId": parent_thread_id,
                "receiverThreadId": child_thread_id,
            },
        )
        with manager._lock:
            current = manager._child_runs.get(child_id)
            if current is None:
                return
            if current.status != "cancelled":
                current.status = "completed"
                current.ended_at = datetime.now(tz=timezone.utc).isoformat()
                current.dispatch_phase = "terminal"
                manager._record_child_event(
                    child=current,
                    event_kind="WORKER_PASS",
                    payload={"worker_id": child_id, "status": "completed"},
                )
                manager._record_parent_or_audit_event(
                    parent_session_id=parent_session_id,
                    event_kind="TOOL_CALL_PASS",
                    payload={
                        "tool_name": "spawn_agent",
                        "child_id": child_id,
                        "status": "completed",
                    },
                )
            manager._persist_child_terminal_state(child=current)
    except URMError as exc:
        with manager._lock:
            current = manager._child_runs.get(child_id)
            if current is None:
                return
            if current.status != "cancelled":
                manager._handle_child_spawn_failure_unlocked(
                    child=current,
                    parent_session_id=parent_session_id,
                    exc=exc,
                )
            manager._persist_child_terminal_state(child=current)
    finally:
        with manager._lock:
            manager._child_run_threads.pop(child_id, None)
            manager._dispatch_child_queue_unlocked(parent_session_id=parent_session_id)
