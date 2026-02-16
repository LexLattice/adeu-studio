from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .evidence import EvidenceFileWriter
from .normalization import build_internal_event
from .storage import (
    get_dispatch_token_for_child,
    list_active_copilot_child_runs,
    persist_worker_run_end,
    set_dispatch_token_phase,
    transaction,
)


def _metadata_str(metadata: dict[str, Any], key: str) -> str | None:
    value = metadata.get(key)
    if isinstance(value, str) and value:
        return value
    return None


def _metadata_int(metadata: dict[str, Any], key: str) -> int | None:
    value = metadata.get(key)
    if isinstance(value, int):
        return value
    return None


@dataclass(frozen=True)
class _RecoveryFields:
    child_stream_id: str
    parent_session_id: str | None
    parent_stream_id: str | None
    parent_seq: int | None
    dispatch_seq: int | None
    lease_id: str
    phase: str
    started_observed: bool


def _resolve_recovery_fields(
    *,
    worker_id: str,
    metadata: dict[str, Any],
    token: Any | None,
) -> _RecoveryFields:
    child_stream_id = _metadata_str(metadata, "child_stream_id") or f"child:{worker_id}"
    parent_session_id = (
        token.parent_session_id
        if token is not None
        else _metadata_str(metadata, "parent_session_id")
    )
    parent_stream_id = (
        token.parent_stream_id if token is not None else _metadata_str(metadata, "parent_stream_id")
    )
    parent_seq = token.parent_seq if token is not None else _metadata_int(metadata, "parent_seq")
    dispatch_seq = (
        token.dispatch_seq if token is not None else _metadata_int(metadata, "dispatch_seq")
    )
    lease_id = (
        token.worker_run_id
        if token is not None
        else (_metadata_str(metadata, "lease_id") or worker_id)
    )
    phase = token.phase if token is not None else (_metadata_str(metadata, "phase") or "queued")
    started_observed = token is not None and token.phase in {"started", "terminal"}
    return _RecoveryFields(
        child_stream_id=child_stream_id,
        parent_session_id=parent_session_id,
        parent_stream_id=parent_stream_id,
        parent_seq=parent_seq,
        dispatch_seq=dispatch_seq,
        lease_id=lease_id,
        phase=phase,
        started_observed=started_observed,
    )


def _recovery_order_key(*, metadata: dict[str, Any], token: Any | None) -> tuple[str, int, int]:
    parent_session_id = (
        token.parent_session_id
        if token is not None
        else (_metadata_str(metadata, "parent_session_id") or "")
    )
    dispatch_seq = (
        token.dispatch_seq
        if token is not None and token.dispatch_seq is not None
        else (_metadata_int(metadata, "dispatch_seq") or 2**62)
    )
    queue_seq = (
        token.queue_seq if token is not None else (_metadata_int(metadata, "queue_seq") or 2**62)
    )
    return (parent_session_id, int(dispatch_seq), int(queue_seq))


def recover_stale_child_runs(*, manager: Any, logger: Any) -> None:
    if not manager._is_child_queue_v2_enabled():
        return
    recovery_rows: list[tuple[str, int, int, str, Any, dict[str, Any], Any | None]] = []
    with transaction(db_path=manager.config.db_path) as con:
        stale_rows = list_active_copilot_child_runs(con=con)
        if not stale_rows:
            return
        for row in stale_rows:
            metadata = row.result_json if isinstance(row.result_json, dict) else {}
            token = get_dispatch_token_for_child(con=con, child_id=row.worker_id)
            parent_session_id, dispatch_seq, queue_seq = _recovery_order_key(
                metadata=metadata,
                token=token,
            )
            recovery_rows.append(
                (
                    parent_session_id,
                    dispatch_seq,
                    queue_seq,
                    row.worker_id,
                    row,
                    metadata,
                    token,
                )
            )
    recovery_rows.sort(key=lambda item: (item[0], item[1], item[2], item[3]))
    for _, _, _, _, row, metadata, token in recovery_rows:
        fields = _resolve_recovery_fields(
            worker_id=row.worker_id,
            metadata=metadata,
            token=token,
        )
        if fields.started_observed:
            recovery_code = "URM_CHILD_TERMINATED_ON_RESTART"
            recovery_reason = "restart_terminated"
            recovery_message = "child run terminated during API restart"
        else:
            recovery_code = "URM_SCHEDULER_LEASE_ORPHANED"
            recovery_reason = "lease_orphaned"
            recovery_message = "orphan lease terminated during API restart"
        detail_payload: dict[str, Any] = {
            "worker_id": row.worker_id,
            "status": "failed",
            "error_code": recovery_code,
            "code": recovery_code,
            "reason": recovery_reason,
            "dispatch_seq": fields.dispatch_seq,
            "lease_id": fields.lease_id,
            "parent_stream_id": fields.parent_stream_id,
            "parent_seq": fields.parent_seq,
            "child_id": row.worker_id,
            "phase": fields.phase,
        }
        raw_events_path = _metadata_str(metadata, "urm_events_path")
        if raw_events_path is not None:
            try:
                events_path = manager._resolve_urm_events_path(raw_events_path)
            except Exception:
                events_path = None
        else:
            events_path = None
        if events_path is not None:
            manager._repair_trailing_partial_ndjson(path=events_path)
            writer = EvidenceFileWriter(
                path=events_path,
                max_line_bytes=manager.config.max_line_bytes,
                max_file_bytes=manager.config.max_evidence_file_bytes,
            )
            seq = manager._next_seq_for_event_file(path=events_path)
            event = build_internal_event(
                seq=seq,
                event="WORKER_FAIL",
                stream_id=fields.child_stream_id,
                source_component="urm_copilot_manager",
                context={
                    "session_id": fields.parent_session_id,
                    "run_id": row.worker_id,
                    "role": "copilot",
                    "endpoint": "urm.agent.spawn",
                },
                detail=detail_payload,
            )
            writer.write_json_line(event.model_dump(mode="json", by_alias=True))
            writer.close()
        if isinstance(fields.parent_session_id, str) and fields.parent_session_id:
            manager._record_parent_or_audit_event(
                parent_session_id=fields.parent_session_id,
                event_kind="WORKER_FAIL",
                payload=detail_payload,
                endpoint="urm.agent.spawn",
            )
        with transaction(db_path=manager.config.db_path) as con:
            persist_worker_run_end(
                con=con,
                worker_id=row.worker_id,
                status="failed",
                exit_code=None,
                error_code=recovery_code,
                error_message=recovery_message,
                result_json={
                    **metadata,
                    "status": "failed",
                    "error": {
                        "code": recovery_code,
                        "message": recovery_message,
                    },
                    "restart_reason": recovery_reason,
                    "dispatch_seq": fields.dispatch_seq,
                    "lease_id": fields.lease_id,
                    "parent_stream_id": fields.parent_stream_id,
                    "parent_seq": fields.parent_seq,
                    "phase": fields.phase,
                },
            )
            if token is not None:
                try:
                    set_dispatch_token_phase(
                        con=con,
                        child_id=row.worker_id,
                        phase="terminal",
                    )
                except RuntimeError as exc:
                    logger.warning(
                        "failed to mark restart-recovered dispatch token terminal: child_id=%s",
                        row.worker_id,
                        exc_info=exc,
                    )
