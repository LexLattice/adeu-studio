from __future__ import annotations

import json
import threading
import time
import uuid
from collections import deque
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Literal

from .app_server import CodexAppServerHost
from .config import URMRuntimeConfig
from .errors import (
    ApprovalError,
    ApprovalExpiredError,
    ApprovalNotFoundError,
    URMError,
)
from .evidence import EvidenceFileLimitExceeded, EvidenceFileWriter
from .hashing import action_hash as compute_action_hash
from .hashing import sha256_canonical_json
from .models import (
    ApprovalIssueResponse,
    ApprovalRevokeResponse,
    CopilotModeRequest,
    CopilotSessionResponse,
    CopilotSessionSendRequest,
    CopilotSessionStartRequest,
    CopilotStopRequest,
    NormalizedEvent,
)
from .normalization import build_internal_event, normalize_app_server_line
from .probe import CodexCapabilityProbeResult, run_and_persist_capability_probe
from .retention import run_evidence_retention_gc
from .storage import (
    CopilotSessionRow,
    consume_approval,
    create_approval,
    get_approval,
    get_copilot_session,
    mark_running_sessions_terminated,
    persist_copilot_session_start,
    persist_evidence_record,
    persist_idempotency_response,
    reserve_request_idempotency,
    revoke_approval,
    set_copilot_writes_allowed,
    transaction,
    update_copilot_session_last_seq,
    update_copilot_session_pid,
    update_copilot_session_status,
)

COPILOT_START_ENDPOINT = "urm.copilot.start"
COPILOT_SEND_ENDPOINT = "urm.copilot.send"
HEARTBEAT_SECS = 10
COPILOT_BUFFER_MAX = 20_000


@dataclass
class CopilotSessionRuntime:
    session_id: str
    host: CodexAppServerHost
    raw_writer: EvidenceFileWriter
    events_writer: EvidenceFileWriter
    raw_jsonl_path: str
    urm_events_path: str
    started_at: str
    last_seq: int = 0
    status: Literal["starting", "running", "stopped", "failed"] = "starting"
    ended_at: str | None = None
    error_code: str | None = None
    error_message: str | None = None
    thread_id: str | None = None
    initialized: bool = False
    cwd: str | None = None
    buffer: deque[NormalizedEvent] = field(default_factory=lambda: deque(maxlen=COPILOT_BUFFER_MAX))
    condition: threading.Condition = field(default_factory=threading.Condition)


class URMCopilotManager:
    def __init__(
        self,
        *,
        config: URMRuntimeConfig | None = None,
        probe: CodexCapabilityProbeResult | None = None,
    ) -> None:
        self.config = config or URMRuntimeConfig.from_env()
        self._probe = probe or run_and_persist_capability_probe(config=self.config)
        self._sessions: dict[str, CopilotSessionRuntime] = {}
        self._active_session_id: str | None = None
        self._lock = threading.RLock()
        self._recover_terminated_sessions()

    @property
    def probe(self) -> CodexCapabilityProbeResult:
        return self._probe

    def _recover_terminated_sessions(self) -> None:
        with transaction(db_path=self.config.db_path) as con:
            mark_running_sessions_terminated(
                con=con,
                error_code="URM_CODEX_SESSION_TERMINATED",
                error_message="session terminated during API restart",
                terminal_status="stopped",
            )

    def _raw_jsonl_path_for_session(self, session_id: str) -> Path:
        path = self.config.evidence_root / "copilot" / session_id / "codex_raw.ndjson"
        path.parent.mkdir(parents=True, exist_ok=True)
        return path

    def _urm_events_path_for_session(self, session_id: str) -> Path:
        path = self.config.evidence_root / "copilot" / session_id / "urm_events.ndjson"
        path.parent.mkdir(parents=True, exist_ok=True)
        return path

    def _relative_path(self, path: Path) -> str:
        try:
            return str(path.relative_to(self.config.var_root))
        except ValueError:
            return str(path)

    def _resolve_raw_path(self, raw_jsonl_path: str) -> Path:
        path = Path(raw_jsonl_path)
        if path.is_absolute():
            raise URMError(
                code="URM_CODEX_SSE_REPLAY_FAILED",
                message="raw evidence path must be relative",
                context={"raw_jsonl_path": raw_jsonl_path},
            )
        resolved = (self.config.var_root / path).resolve()
        root = self.config.evidence_root.resolve()
        if not resolved.is_relative_to(root):
            raise URMError(
                code="URM_CODEX_SSE_REPLAY_FAILED",
                message="raw evidence path escapes evidence root",
                context={"raw_jsonl_path": raw_jsonl_path},
            )
        return resolved

    def _resolve_urm_events_path(self, urm_events_path: str) -> Path:
        path = Path(urm_events_path)
        if path.is_absolute():
            raise URMError(
                code="URM_CODEX_SSE_REPLAY_FAILED",
                message="urm events path must be relative",
                context={"urm_events_path": urm_events_path},
            )
        resolved = (self.config.var_root / path).resolve()
        root = self.config.evidence_root.resolve()
        if not resolved.is_relative_to(root):
            raise URMError(
                code="URM_CODEX_SSE_REPLAY_FAILED",
                message="urm events path escapes evidence root",
                context={"urm_events_path": urm_events_path},
            )
        return resolved

    def _record_event_line(self, *, runtime: CopilotSessionRuntime, raw_line: str) -> None:
        with runtime.condition:
            runtime.last_seq += 1
            seq = runtime.last_seq
            try:
                line = raw_line if raw_line.endswith("\n") else raw_line + "\n"
                runtime.raw_writer.write_raw_line(line)
                event = normalize_app_server_line(
                    seq=seq,
                    raw_line=raw_line,
                    stream_id=f"copilot:{runtime.session_id}",
                    session_id=runtime.session_id,
                    role="copilot",
                    endpoint="urm.copilot.events",
                )
                runtime.events_writer.write_json_line(
                    event.model_dump(mode="json", by_alias=True)
                )
            except (EvidenceFileLimitExceeded, ValueError) as exc:
                runtime.error_code = "URM_CODEX_SESSION_LIMIT_EXCEEDED"
                runtime.error_message = str(exc)
                runtime.status = "failed"
                runtime.ended_at = datetime.now(tz=timezone.utc).isoformat()
                runtime.condition.notify_all()
                runtime.host.stop()
                runtime.raw_writer.close()
                runtime.events_writer.close()
                return
            runtime.buffer.append(event)
            runtime.condition.notify_all()

        try:
            with transaction(db_path=self.config.db_path) as con:
                update_copilot_session_last_seq(
                    con=con,
                    copilot_session_id=runtime.session_id,
                    last_seq=runtime.last_seq,
                )
        except Exception as exc:
            runtime.error_code = "URM_DB_TX_FAILED"
            runtime.error_message = f"failed to persist copilot event seq: {exc}"
            runtime.status = "failed"
            runtime.ended_at = datetime.now(tz=timezone.utc).isoformat()
            with runtime.condition:
                runtime.condition.notify_all()
            runtime.host.stop()
            runtime.raw_writer.close()
            runtime.events_writer.close()
            with self._lock:
                self._sessions.pop(runtime.session_id, None)
                if self._active_session_id == runtime.session_id:
                    self._active_session_id = None
            try:
                self._persist_terminal_state(runtime=runtime)
            except Exception:
                # Best-effort only; the session is already force-stopped in memory.
                pass

    def _record_internal_event(
        self,
        *,
        runtime: CopilotSessionRuntime,
        event_kind: str,
        payload: dict[str, Any],
    ) -> None:
        with runtime.condition:
            runtime.last_seq += 1
            seq = runtime.last_seq
            event = build_internal_event(
                seq=seq,
                event=event_kind,
                stream_id=f"copilot:{runtime.session_id}",
                source_component="urm_copilot_manager",
                context={
                    "session_id": runtime.session_id,
                    "role": "copilot",
                    "endpoint": "urm.copilot.events",
                },
                detail=payload,
            )
            try:
                runtime.events_writer.write_json_line(
                    event.model_dump(mode="json", by_alias=True)
                )
            except (EvidenceFileLimitExceeded, ValueError) as exc:
                runtime.error_code = "URM_CODEX_SESSION_LIMIT_EXCEEDED"
                runtime.error_message = str(exc)
                runtime.status = "failed"
                runtime.ended_at = datetime.now(tz=timezone.utc).isoformat()
                runtime.condition.notify_all()
                runtime.host.stop()
                runtime.raw_writer.close()
                runtime.events_writer.close()
                return
            runtime.buffer.append(event)
            runtime.condition.notify_all()

        try:
            with transaction(db_path=self.config.db_path) as con:
                update_copilot_session_last_seq(
                    con=con,
                    copilot_session_id=runtime.session_id,
                    last_seq=runtime.last_seq,
                )
        except Exception:
            # Best-effort update only for internal events.
            pass

    def record_policy_eval_event(
        self,
        *,
        session_id: str | None,
        event_kind: Literal["POLICY_EVAL_START", "POLICY_EVAL_PASS", "POLICY_DENIED"],
        detail: dict[str, Any],
    ) -> None:
        if not session_id:
            return
        with self._lock:
            runtime = self._sessions.get(session_id)
            if runtime is None:
                return
            self._record_internal_event(
                runtime=runtime,
                event_kind=event_kind,
                payload=detail,
            )

    def _wait_for_response(
        self,
        *,
        runtime: CopilotSessionRuntime,
        request_id: str,
        timeout_secs: float = 10.0,
    ) -> dict[str, Any]:
        deadline = time.monotonic() + timeout_secs
        with runtime.condition:
            while True:
                for event in reversed(runtime.buffer):
                    payload = event.payload
                    if not isinstance(payload, dict):
                        continue
                    if payload.get("id") != request_id:
                        continue
                    if "result" in payload or "error" in payload:
                        return payload

                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    break
                runtime.condition.wait(timeout=min(remaining, 0.5))

        raise URMError(
            code="URM_CODEX_START_FAILED",
            message="timed out waiting for app-server response",
            context={"request_id": request_id, "timeout_secs": timeout_secs},
        )

    def _send_jsonrpc_and_wait(
        self,
        *,
        runtime: CopilotSessionRuntime,
        method: str,
        params: dict[str, Any],
        timeout_secs: float = 10.0,
    ) -> dict[str, Any]:
        request_id = uuid.uuid4().hex
        request_payload: dict[str, Any] = {
            "id": request_id,
            "method": method,
            "params": params,
        }
        line = runtime.host.send(request_payload)
        self._record_event_line(runtime=runtime, raw_line=line)
        response = self._wait_for_response(
            runtime=runtime,
            request_id=request_id,
            timeout_secs=timeout_secs,
        )
        if "error" in response:
            raise URMError(
                code="URM_CODEX_START_FAILED",
                message=f"app-server returned error for {method}",
                context={"method": method, "error": response.get("error")},
            )
        return response

    def _bootstrap_runtime(self, *, runtime: CopilotSessionRuntime) -> None:
        if runtime.initialized and runtime.thread_id:
            return

        self._send_jsonrpc_and_wait(
            runtime=runtime,
            method="initialize",
            params={
                "clientInfo": {
                    "name": "adeu-copilot",
                    "version": "0.1.0",
                },
                "capabilities": {"experimentalApi": True},
            },
        )

        thread_start_params: dict[str, Any] = {
            "approvalPolicy": "never",
            "sandbox": "read-only",
        }
        if runtime.cwd:
            thread_start_params["cwd"] = runtime.cwd

        thread_response = self._send_jsonrpc_and_wait(
            runtime=runtime,
            method="thread/start",
            params=thread_start_params,
        )
        thread_id = thread_response.get("result", {}).get("thread", {}).get("id")
        if not isinstance(thread_id, str) or not thread_id:
            raise URMError(
                code="URM_CODEX_START_FAILED",
                message="thread/start response missing thread id",
                context={"response": thread_response},
            )

        runtime.thread_id = thread_id
        runtime.initialized = True
        self._record_internal_event(
            runtime=runtime,
            event_kind="SESSION_READY",
            payload={"status": "running", "thread_id": thread_id},
        )

    def _send_user_message(self, *, runtime: CopilotSessionRuntime, text: str) -> None:
        self._bootstrap_runtime(runtime=runtime)
        if runtime.thread_id is None:
            raise URMError(
                code="URM_CODEX_START_FAILED",
                message="missing copilot thread id after bootstrap",
            )
        line = runtime.host.send(
            {
                "id": uuid.uuid4().hex,
                "method": "turn/start",
                "params": {
                    "threadId": runtime.thread_id,
                    "approvalPolicy": "never",
                    "input": [{"type": "text", "text": text}],
                },
            }
        )
        self._record_event_line(runtime=runtime, raw_line=line)

    def _persist_terminal_state(self, *, runtime: CopilotSessionRuntime) -> None:
        status = runtime.status
        ended_at = runtime.ended_at or datetime.now(tz=timezone.utc).isoformat()
        runtime.ended_at = ended_at
        error_json = (
            {"code": runtime.error_code, "message": runtime.error_message}
            if runtime.error_code and runtime.error_message
            else None
        )
        with transaction(db_path=self.config.db_path) as con:
            update_copilot_session_status(
                con=con,
                copilot_session_id=runtime.session_id,
                status=status,
                error_code=runtime.error_code,
                error_message=runtime.error_message,
                ended=True,
            )
            persist_evidence_record(
                con=con,
                source="codex_app_server",
                role="copilot",
                worker_id=None,
                copilot_session_id=runtime.session_id,
                template_id=None,
                started_at=runtime.started_at,
                ended_at=ended_at,
                raw_jsonl_path=runtime.raw_jsonl_path,
                status=status,
                error_json=error_json,
                metadata_json={
                    "last_seq": runtime.last_seq,
                    "urm_events_path": runtime.urm_events_path,
                },
            )

    def _stop_runtime(
        self,
        *,
        runtime: CopilotSessionRuntime,
        reason: str,
    ) -> CopilotSessionResponse:
        exit_code = runtime.host.stop()
        if runtime.status not in {"failed", "stopped"}:
            runtime.status = "stopped"
        runtime.ended_at = datetime.now(tz=timezone.utc).isoformat()
        terminal_event = "SESSION_FAIL" if runtime.status == "failed" else "SESSION_STOP"
        self._record_internal_event(
            runtime=runtime,
            event_kind=terminal_event,
            payload={
                "status": runtime.status,
                "reason": reason,
                "method": "terminate_then_kill_if_needed",
                "exit_code": exit_code,
            },
        )
        runtime.raw_writer.close()
        runtime.events_writer.close()
        with runtime.condition:
            runtime.condition.notify_all()
        self._persist_terminal_state(runtime=runtime)
        return CopilotSessionResponse(
            session_id=runtime.session_id,
            status=runtime.status,
            app_server_unavailable=self._probe.app_server_unavailable,
            idempotent_replay=False,
        )

    def _action_hash(self, *, action_kind: str, action_payload: dict[str, Any]) -> str:
        return compute_action_hash(action_kind=action_kind, action_payload=action_payload)

    def _consume_approval_unlocked(
        self,
        *,
        session_id: str,
        approval_id: str | None,
        action_kind: str,
        action_payload: dict[str, Any],
    ) -> str:
        if not approval_id:
            raise URMError(
                code="URM_APPROVAL_REQUIRED",
                message="approval is required for this action",
                context={"action_kind": action_kind},
            )
        action_hash = self._action_hash(action_kind=action_kind, action_payload=action_payload)
        with transaction(db_path=self.config.db_path) as con:
            approval = get_approval(con=con, approval_id=approval_id)
            if approval is None:
                raise URMError(
                    code="URM_APPROVAL_INVALID",
                    message="approval not found",
                    context={"approval_id": approval_id},
                )
            if approval.copilot_session_id != session_id:
                raise URMError(
                    code="URM_APPROVAL_INVALID",
                    message="approval does not belong to this session",
                    context={"approval_id": approval_id, "session_id": session_id},
                )
            try:
                consume_approval(
                    con=con,
                    approval_id=approval_id,
                    action_kind=action_kind,
                    action_hash=action_hash,
                    consumed_by_evidence_id=None,
                )
            except ApprovalNotFoundError as exc:
                raise URMError(
                    code="URM_APPROVAL_INVALID",
                    message="approval not found",
                    context={"approval_id": approval_id},
                ) from exc
            except ApprovalExpiredError as exc:
                raise URMError(
                    code="URM_APPROVAL_EXPIRED",
                    message="approval expired",
                    context={"approval_id": approval_id},
                ) from exc
            except ApprovalError as exc:
                raise URMError(
                    code="URM_APPROVAL_INVALID",
                    message="approval invalid",
                    context={"approval_id": approval_id, "reason": exc.__class__.__name__},
                ) from exc

        runtime = self._sessions.get(session_id)
        if runtime is not None:
            self._record_internal_event(
                runtime=runtime,
                event_kind="APPROVAL_CONSUMED",
                payload={"approval_id": approval_id, "action_kind": action_kind},
            )
        return action_hash

    def issue_approval(
        self,
        *,
        session_id: str,
        action_kind: str,
        action_payload: dict[str, Any],
        expires_in_secs: int | None,
    ) -> ApprovalIssueResponse:
        with self._lock:
            runtime = self._sessions.get(session_id)
            if runtime is None:
                raise URMError(
                    code="URM_NOT_FOUND",
                    message="copilot session not found",
                    status_code=404,
                    context={"session_id": session_id},
                )
            ttl = expires_in_secs if expires_in_secs is not None else self.config.approval_ttl_secs
            ttl = max(1, min(ttl, self.config.approval_ttl_secs))
            expires_at = datetime.now(tz=timezone.utc) + timedelta(seconds=ttl)
            action_hash = self._action_hash(action_kind=action_kind, action_payload=action_payload)
            with transaction(db_path=self.config.db_path) as con:
                approval_id = create_approval(
                    con=con,
                    action_kind=action_kind,
                    action_hash=action_hash,
                    expires_at=expires_at.isoformat(),
                    copilot_session_id=session_id,
                    granted_by_user=True,
                )
            self._record_internal_event(
                runtime=runtime,
                event_kind="APPROVAL_ISSUED",
                payload={
                    "approval_id": approval_id,
                    "action_kind": action_kind,
                    "expires_at": expires_at.isoformat(),
                },
            )
            return ApprovalIssueResponse(
                approval_id=approval_id,
                session_id=session_id,
                action_kind=action_kind,
                action_hash=action_hash,
                expires_at=expires_at,
            )

    def revoke_approval(self, *, approval_id: str) -> ApprovalRevokeResponse:
        with self._lock:
            with transaction(db_path=self.config.db_path) as con:
                approval = get_approval(con=con, approval_id=approval_id)
                if approval is None:
                    raise URMError(
                        code="URM_NOT_FOUND",
                        message="approval not found",
                        status_code=404,
                        context={"approval_id": approval_id},
                    )
                revoked = revoke_approval(con=con, approval_id=approval_id)
            runtime = (
                self._sessions.get(approval.copilot_session_id)
                if approval.copilot_session_id is not None
                else None
            )
            if runtime is not None and revoked:
                self._record_internal_event(
                    runtime=runtime,
                    event_kind="APPROVAL_REVOKED",
                    payload={
                        "approval_id": approval_id,
                        "action_kind": approval.action_kind,
                    },
                )
            return ApprovalRevokeResponse(
                approval_id=approval_id,
                revoked=True,
                idempotent_replay=not revoked,
            )

    def start_session(self, request: CopilotSessionStartRequest) -> CopilotSessionResponse:
        if request.provider != "codex":
            raise URMError(
                code="URM_POLICY_DENIED",
                message="unsupported provider",
                context={"provider": request.provider},
            )
        if self._probe.app_server_unavailable:
            raise URMError(
                code="URM_CODEX_APP_SERVER_UNAVAILABLE",
                message="codex app-server unavailable; worker-only mode",
                context={"app_server_unavailable": True},
            )

        run_evidence_retention_gc(config=self.config)

        payload_hash = sha256_canonical_json(request.idempotency_payload())
        with self._lock:
            new_session_id = uuid.uuid4().hex
            with transaction(db_path=self.config.db_path) as con:
                try:
                    reservation = reserve_request_idempotency(
                        con=con,
                        endpoint_name=COPILOT_START_ENDPOINT,
                        client_request_id=request.client_request_id,
                        payload_hash=payload_hash,
                        resource_id=new_session_id,
                    )
                except ValueError as exc:
                    raise URMError(
                        code="URM_IDEMPOTENCY_KEY_CONFLICT",
                        message="client_request_id already used with a different payload",
                        status_code=409,
                        context={"client_request_id": request.client_request_id},
                    ) from exc
                if reservation.replay:
                    replay = CopilotSessionResponse.model_validate(reservation.response_json or {})
                    return replay.model_copy(update={"idempotent_replay": True})
                session_id = reservation.resource_id

            if self._active_session_id is not None:
                prior = self._sessions.get(self._active_session_id)
                if prior is not None:
                    self._stop_runtime(runtime=prior, reason="superseded")
                    self._sessions.pop(prior.session_id, None)
                self._active_session_id = None

            raw_path = self._raw_jsonl_path_for_session(session_id)
            events_path = self._urm_events_path_for_session(session_id)
            raw_rel_path = self._relative_path(raw_path)
            events_rel_path = self._relative_path(events_path)
            raw_writer = EvidenceFileWriter(
                path=raw_path,
                max_line_bytes=self.config.max_line_bytes,
                max_file_bytes=self.config.max_evidence_file_bytes,
            )
            events_writer = EvidenceFileWriter(
                path=events_path,
                max_line_bytes=self.config.max_line_bytes,
                max_file_bytes=self.config.max_evidence_file_bytes,
            )
            runtime = CopilotSessionRuntime(
                session_id=session_id,
                host=CodexAppServerHost(
                    config=self.config,
                    on_line=lambda line: self._record_event_line(runtime=runtime, raw_line=line),
                ),
                raw_writer=raw_writer,
                events_writer=events_writer,
                raw_jsonl_path=raw_rel_path,
                urm_events_path=events_rel_path,
                started_at=datetime.now(tz=timezone.utc).isoformat(),
                cwd=request.cwd,
            )

            with transaction(db_path=self.config.db_path) as con:
                persist_copilot_session_start(
                    con=con,
                    copilot_session_id=session_id,
                    role="copilot",
                    status="starting",
                    codex_version=self._probe.codex_version,
                    capability_probe_id=self._probe.probe_id,
                    pid=None,
                    bin_path=self.config.codex_bin,
                    raw_jsonl_path=raw_rel_path,
                )
            try:
                runtime.host.start(cwd=request.cwd)
            except URMError as exc:
                runtime.status = "failed"
                runtime.error_code = exc.detail.code
                runtime.error_message = exc.detail.message
                runtime.ended_at = datetime.now(tz=timezone.utc).isoformat()
                self._record_internal_event(
                    runtime=runtime,
                    event_kind="SESSION_FAIL",
                    payload={
                        "status": "failed",
                        "code": runtime.error_code,
                        "message": runtime.error_message,
                    },
                )
                raw_writer.close()
                events_writer.close()
                self._persist_terminal_state(runtime=runtime)
                response = CopilotSessionResponse(
                    session_id=session_id,
                    status="failed",
                    app_server_unavailable=True,
                    idempotent_replay=False,
                )
                with transaction(db_path=self.config.db_path) as con:
                    persist_idempotency_response(
                        con=con,
                        endpoint_name=COPILOT_START_ENDPOINT,
                        client_request_id=request.client_request_id,
                        response_json=response.model_dump(mode="json"),
                    )
                return response

            runtime.status = "running"
            self._sessions[session_id] = runtime
            self._active_session_id = session_id
            self._record_internal_event(
                runtime=runtime,
                event_kind="SESSION_START",
                payload={"status": "running"},
            )
            with transaction(db_path=self.config.db_path) as con:
                update_copilot_session_pid(
                    con=con,
                    copilot_session_id=session_id,
                    pid=runtime.host.pid,
                )
                update_copilot_session_status(
                    con=con,
                    copilot_session_id=session_id,
                    status="running",
                )
            response = CopilotSessionResponse(
                session_id=session_id,
                status="running",
                app_server_unavailable=False,
                idempotent_replay=False,
            )
            with transaction(db_path=self.config.db_path) as con:
                persist_idempotency_response(
                    con=con,
                    endpoint_name=COPILOT_START_ENDPOINT,
                    client_request_id=request.client_request_id,
                    response_json=response.model_dump(mode="json"),
                )
            return response

    def send(self, request: CopilotSessionSendRequest) -> CopilotSessionResponse:
        payload_hash = sha256_canonical_json(request.idempotency_payload())
        with self._lock:
            runtime = self._sessions.get(request.session_id)
            if runtime is None:
                raise URMError(
                    code="URM_NOT_FOUND",
                    message="copilot session not found",
                    status_code=404,
                    context={"session_id": request.session_id},
                )
            self._enforce_session_duration_unlocked(runtime=runtime)
            with transaction(db_path=self.config.db_path) as con:
                try:
                    reservation = reserve_request_idempotency(
                        con=con,
                        endpoint_name=COPILOT_SEND_ENDPOINT,
                        client_request_id=request.client_request_id,
                        payload_hash=payload_hash,
                        resource_id=request.session_id,
                    )
                except ValueError as exc:
                    raise URMError(
                        code="URM_IDEMPOTENCY_KEY_CONFLICT",
                        message="client_request_id already used with a different payload",
                        status_code=409,
                        context={"client_request_id": request.client_request_id},
                    ) from exc
                if reservation.replay:
                    replay = CopilotSessionResponse.model_validate(reservation.response_json or {})
                    return replay.model_copy(update={"idempotent_replay": True})

            if request.message.get("method") == "copilot.user_message":
                params = request.message.get("params")
                text = params.get("text") if isinstance(params, dict) else None
                if not isinstance(text, str) or not text.strip():
                    raise URMError(
                        code="URM_POLICY_DENIED",
                        message="copilot.user_message requires non-empty params.text",
                        status_code=400,
                    )
                self._send_user_message(runtime=runtime, text=text)
            else:
                line = runtime.host.send(request.message)
                self._record_event_line(runtime=runtime, raw_line=line)
            response = CopilotSessionResponse(
                session_id=request.session_id,
                status=runtime.status,  # type: ignore[arg-type]
                app_server_unavailable=self._probe.app_server_unavailable,
                idempotent_replay=False,
            )
            with transaction(db_path=self.config.db_path) as con:
                persist_idempotency_response(
                    con=con,
                    endpoint_name=COPILOT_SEND_ENDPOINT,
                    client_request_id=request.client_request_id,
                    response_json=response.model_dump(mode="json"),
                )
            return response

    def stop(self, request: CopilotStopRequest) -> CopilotSessionResponse:
        with self._lock:
            runtime = self._sessions.get(request.session_id)
            if runtime is None:
                with transaction(db_path=self.config.db_path) as con:
                    row = get_copilot_session(con=con, copilot_session_id=request.session_id)
                if row is None:
                    raise URMError(
                        code="URM_NOT_FOUND",
                        message="copilot session not found",
                        status_code=404,
                        context={"session_id": request.session_id},
                    )
                return CopilotSessionResponse(
                    session_id=request.session_id,
                    status=row.status,  # type: ignore[arg-type]
                    app_server_unavailable=self._probe.app_server_unavailable,
                    idempotent_replay=True,
                )
            response = self._stop_runtime(runtime=runtime, reason="user_stop")
            self._sessions.pop(request.session_id, None)
            if self._active_session_id == request.session_id:
                self._active_session_id = None
            return response

    def set_mode(self, request: CopilotModeRequest) -> CopilotSessionResponse:
        with self._lock:
            runtime = self._sessions.get(request.session_id)
            if runtime is None:
                raise URMError(
                    code="URM_NOT_FOUND",
                    message="copilot session not found",
                    status_code=404,
                    context={"session_id": request.session_id},
                )
            self._enforce_session_duration_unlocked(runtime=runtime)

            if request.writes_allowed:
                self._consume_approval_unlocked(
                    session_id=request.session_id,
                    approval_id=request.approval_id,
                    action_kind="urm.set_mode.enable_writes",
                    action_payload={"writes_allowed": True},
                )

            with transaction(db_path=self.config.db_path) as con:
                set_copilot_writes_allowed(
                    con=con,
                    copilot_session_id=request.session_id,
                    writes_allowed=request.writes_allowed,
                )
            self._record_internal_event(
                runtime=runtime,
                event_kind="MODE_CHANGED",
                payload={"writes_allowed": request.writes_allowed},
            )
            return CopilotSessionResponse(
                session_id=request.session_id,
                status=runtime.status,  # type: ignore[arg-type]
                app_server_unavailable=self._probe.app_server_unavailable,
                idempotent_replay=False,
            )

    def shutdown(self) -> None:
        with self._lock:
            session_ids = list(self._sessions)
            for session_id in session_ids:
                runtime = self._sessions.get(session_id)
                if runtime is None:
                    continue
                self._stop_runtime(runtime=runtime, reason="server_shutdown")
                self._sessions.pop(session_id, None)
            self._active_session_id = None

    def _enforce_session_duration_unlocked(self, *, runtime: CopilotSessionRuntime) -> None:
        if runtime.status not in {"starting", "running"}:
            return
        started = datetime.fromisoformat(runtime.started_at)
        elapsed = datetime.now(tz=timezone.utc) - started
        if elapsed.total_seconds() <= self.config.max_session_duration_secs:
            return
        runtime.status = "failed"
        runtime.error_code = "URM_CODEX_SESSION_LIMIT_EXCEEDED"
        runtime.error_message = (
            f"copilot session exceeded {self.config.max_session_duration_secs} seconds"
        )
        self._stop_runtime(runtime=runtime, reason="session_duration_exceeded")
        self._sessions.pop(runtime.session_id, None)
        if self._active_session_id == runtime.session_id:
            self._active_session_id = None

    def _replay_events_from_file(
        self,
        *,
        row: CopilotSessionRow,
        after_seq: int,
    ) -> list[NormalizedEvent]:
        if row.raw_jsonl_path is None:
            return []
        raw_path = self._resolve_raw_path(row.raw_jsonl_path)
        events_rel_path: str
        raw_rel = Path(row.raw_jsonl_path)
        events_rel_path = str(raw_rel.with_name("urm_events.ndjson"))
        events_path = self._resolve_urm_events_path(events_rel_path)

        events: list[NormalizedEvent] = []
        if events_path.exists():
            with events_path.open("r", encoding="utf-8", errors="replace") as handle:
                for line in handle:
                    try:
                        parsed = json.loads(line)
                        event = NormalizedEvent.model_validate(parsed)
                    except (json.JSONDecodeError, ValueError):
                        continue
                    if event.seq <= after_seq:
                        continue
                    events.append(event)
                    if len(events) >= self.config.max_replay_events:
                        break
            return events

        if not raw_path.exists():
            return []
        with raw_path.open("r", encoding="utf-8", errors="replace") as handle:
            seq = 0
            for line in handle:
                seq += 1
                if seq <= after_seq:
                    continue
                events.append(
                    normalize_app_server_line(
                        seq=seq,
                        raw_line=line,
                        stream_id=f"copilot:{row.copilot_session_id}",
                        session_id=row.copilot_session_id,
                        role=row.role,
                        endpoint="urm.copilot.events",
                    )
                )
                if len(events) >= self.config.max_replay_events:
                    break
        return events

    def iter_events(self, *, session_id: str, after_seq: int) -> tuple[list[NormalizedEvent], str]:
        with self._lock:
            runtime = self._sessions.get(session_id)
            if runtime is not None:
                self._enforce_session_duration_unlocked(runtime=runtime)
        if runtime is None:
            with transaction(db_path=self.config.db_path) as con:
                row = get_copilot_session(con=con, copilot_session_id=session_id)
            if row is None:
                raise URMError(
                    code="URM_NOT_FOUND",
                    message="copilot session not found",
                    status_code=404,
                    context={"session_id": session_id},
                )
            return self._replay_events_from_file(row=row, after_seq=after_seq), row.status

        with runtime.condition:
            if runtime.last_seq <= after_seq and runtime.status in {"starting", "running"}:
                runtime.condition.wait(timeout=HEARTBEAT_SECS)
            events = [event for event in runtime.buffer if event.seq > after_seq]
            status = runtime.status
        return events, status
