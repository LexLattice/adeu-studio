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
from .instruction_policy import compute_policy_hash, load_instruction_policy
from .models import (
    AgentCancelRequest,
    AgentCancelResponse,
    AgentSpawnRequest,
    AgentSpawnResponse,
    ApprovalIssueResponse,
    ApprovalRevokeResponse,
    CopilotModeRequest,
    CopilotSessionResponse,
    CopilotSessionSendRequest,
    CopilotSessionStartRequest,
    CopilotSteerRequest,
    CopilotSteerResponse,
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
COPILOT_STEER_ENDPOINT = "urm.copilot.steer"
AGENT_SPAWN_ENDPOINT = "urm.agent.spawn"
AGENT_CANCEL_ENDPOINT = "urm.agent.cancel"
HEARTBEAT_SECS = 10
COPILOT_BUFFER_MAX = 20_000
MAX_STEER_PER_TURN = 5
MAX_CHILD_DEPTH = 1
MAX_CHILDREN_PER_PARENT = 1
PROFILE_VERSION = "profile.v1"
SUPPORTED_PROFILE_IDS = frozenset({"safe_mode", "default", "experimental"})


@dataclass
class ChildAgentRuntime:
    child_id: str
    parent_session_id: str
    parent_turn_id: str
    parent_stream_id: str
    child_stream_id: str
    started_at: str
    events_writer: EvidenceFileWriter
    raw_writer: EvidenceFileWriter
    raw_jsonl_path: str
    urm_events_path: str
    status: Literal["running", "completed", "failed", "cancelled"] = "running"
    ended_at: str | None = None
    error_code: str | None = None
    error_message: str | None = None
    child_thread_id: str | None = None
    last_seq: int = 0
    budget_snapshot: dict[str, int] = field(default_factory=dict)
    inherited_policy_hash: str | None = None
    capabilities_allowed: list[str] = field(default_factory=list)
    profile_id: str = "default"
    profile_version: str = PROFILE_VERSION
    persisted: bool = False


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
    active_turn_id: str | None = None
    last_turn_id: str | None = None
    steer_counts_by_turn: dict[str, int] = field(default_factory=dict)
    profile_id: str = "default"
    profile_version: str = PROFILE_VERSION
    profile_policy_hash: str | None = None


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
        self._child_runs: dict[str, ChildAgentRuntime] = {}
        self._children_by_parent: dict[str, set[str]] = {}
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

    def _raw_jsonl_path_for_child(self, child_id: str) -> Path:
        path = self.config.evidence_root / "agent" / child_id / "codex_raw.ndjson"
        path.parent.mkdir(parents=True, exist_ok=True)
        return path

    def _urm_events_path_for_child(self, child_id: str) -> Path:
        path = self.config.evidence_root / "agent" / child_id / "urm_events.ndjson"
        path.parent.mkdir(parents=True, exist_ok=True)
        return path

    def _audit_events_path_for_session(self, session_id: str) -> Path:
        path = self.config.evidence_root / "audit" / session_id / "urm_events.ndjson"
        path.parent.mkdir(parents=True, exist_ok=True)
        return path

    def _relative_path(self, path: Path) -> str:
        try:
            return str(path.relative_to(self.config.var_root))
        except ValueError:
            return str(path)

    def _validate_profile_id(self, profile_id: str) -> str:
        normalized = profile_id.strip()
        if normalized not in SUPPORTED_PROFILE_IDS:
            raise URMError(
                code="URM_POLICY_PROFILE_NOT_FOUND",
                message="profile is not supported",
                context={
                    "profile_id": profile_id,
                    "supported_profile_ids": sorted(SUPPORTED_PROFILE_IDS),
                },
            )
        return normalized

    def _current_profile_policy_hash(self) -> str:
        return compute_policy_hash(load_instruction_policy())

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

    def _update_turn_state_from_payload(
        self,
        *,
        runtime: CopilotSessionRuntime,
        payload: dict[str, Any],
    ) -> None:
        method = payload.get("method")
        if method == "turn/started":
            params = payload.get("params")
            if isinstance(params, dict):
                turn = params.get("turn")
                if isinstance(turn, dict):
                    turn_id = turn.get("id")
                    if isinstance(turn_id, str) and turn_id:
                        runtime.active_turn_id = turn_id
                        runtime.last_turn_id = turn_id
                        runtime.steer_counts_by_turn.setdefault(turn_id, 0)
            return
        if method == "turn/completed":
            params = payload.get("params")
            if isinstance(params, dict):
                turn = params.get("turn")
                if isinstance(turn, dict):
                    turn_id = turn.get("id")
                    if isinstance(turn_id, str) and turn_id:
                        runtime.last_turn_id = turn_id
                        if runtime.active_turn_id == turn_id:
                            runtime.active_turn_id = None
            return

        result = payload.get("result")
        if not isinstance(result, dict):
            return
        turn = result.get("turn")
        if not isinstance(turn, dict):
            return
        turn_id = turn.get("id")
        status = turn.get("status")
        if not isinstance(turn_id, str) or not turn_id:
            return
        runtime.last_turn_id = turn_id
        runtime.steer_counts_by_turn.setdefault(turn_id, 0)
        if status == "inProgress":
            runtime.active_turn_id = turn_id
        elif status in {"completed", "interrupted", "failed"} and runtime.active_turn_id == turn_id:
            runtime.active_turn_id = None

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
            if isinstance(event.payload, dict):
                self._update_turn_state_from_payload(runtime=runtime, payload=event.payload)
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

    def _record_child_event(
        self,
        *,
        child: ChildAgentRuntime,
        event_kind: str,
        payload: dict[str, Any],
        endpoint: str = "urm.agent.spawn",
    ) -> None:
        child.last_seq += 1
        event = build_internal_event(
            seq=child.last_seq,
            event=event_kind,
            stream_id=child.child_stream_id,
            source_component="urm_copilot_manager",
            context={
                "session_id": child.parent_session_id,
                "run_id": child.child_id,
                "role": "copilot",
                "endpoint": endpoint,
            },
            detail=payload,
        )
        child.events_writer.write_json_line(event.model_dump(mode="json", by_alias=True))

    def _next_seq_for_event_file(self, *, path: Path) -> int:
        if not path.exists():
            return 1
        last_seq = 0
        try:
            with path.open("r", encoding="utf-8", errors="replace") as handle:
                for line in handle:
                    try:
                        payload = json.loads(line)
                    except json.JSONDecodeError:
                        continue
                    if isinstance(payload, dict):
                        seq = payload.get("seq")
                        if isinstance(seq, int) and seq > last_seq:
                            last_seq = seq
        except OSError:
            return 1
        return last_seq + 1

    def _record_parent_or_audit_event(
        self,
        *,
        parent_session_id: str,
        event_kind: str,
        payload: dict[str, Any],
        endpoint: str = "urm.agent.spawn",
    ) -> None:
        runtime = self._sessions.get(parent_session_id)
        if runtime is not None and runtime.status in {"starting", "running"}:
            self._record_internal_event(
                runtime=runtime,
                event_kind=event_kind,
                payload=payload,
            )
            return

        audit_path = self._audit_events_path_for_session(parent_session_id)
        writer = EvidenceFileWriter(
            path=audit_path,
            max_line_bytes=self.config.max_line_bytes,
            max_file_bytes=self.config.max_evidence_file_bytes,
        )
        seq = self._next_seq_for_event_file(path=audit_path)
        event = build_internal_event(
            seq=seq,
            event=event_kind,
            stream_id=f"urm_audit:{parent_session_id}",
            source_component="urm_copilot_manager",
            context={
                "session_id": parent_session_id,
                "role": "copilot",
                "endpoint": endpoint,
            },
            detail=payload,
        )
        writer.write_json_line(event.model_dump(mode="json", by_alias=True))
        writer.close()

    def _persist_child_terminal_state(self, *, child: ChildAgentRuntime) -> None:
        if child.persisted:
            return
        ended_at = child.ended_at or datetime.now(tz=timezone.utc).isoformat()
        child.ended_at = ended_at
        error_json = (
            {"code": child.error_code, "message": child.error_message}
            if child.error_code and child.error_message
            else None
        )
        child.events_writer.close()
        child.raw_writer.close()
        with transaction(db_path=self.config.db_path) as con:
            persist_evidence_record(
                con=con,
                source="codex_app_server",
                role="copilot_child",
                worker_id=None,
                copilot_session_id=child.parent_session_id,
                template_id="urm.agent.spawn",
                started_at=child.started_at,
                ended_at=ended_at,
                raw_jsonl_path=child.urm_events_path,
                status=child.status,
                error_json=error_json,
                metadata_json={
                    "stream_id": child.child_stream_id,
                    "parent_stream_id": child.parent_stream_id,
                    "parent_turn_id": child.parent_turn_id,
                    "child_thread_id": child.child_thread_id,
                    "budget_snapshot": child.budget_snapshot,
                    "inherited_policy_hash": child.inherited_policy_hash,
                    "capabilities_allowed": child.capabilities_allowed,
                    "profile_id": child.profile_id,
                    "profile_version": child.profile_version,
                },
            )
        child.persisted = True

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
                    "profile_id": runtime.profile_id,
                    "profile_version": runtime.profile_version,
                    "profile_policy_hash": runtime.profile_policy_hash,
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
            profile_id=runtime.profile_id,
            profile_version=runtime.profile_version,
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
        profile_id = self._validate_profile_id(request.profile_id)
        profile_policy_hash = self._current_profile_policy_hash()

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
                profile_id=profile_id,
                profile_version=PROFILE_VERSION,
                profile_policy_hash=profile_policy_hash,
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
                    profile_id=runtime.profile_id,
                    profile_version=runtime.profile_version,
                    profile_policy_hash=runtime.profile_policy_hash,
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
                    profile_id=runtime.profile_id,
                    profile_version=runtime.profile_version,
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
            self._record_internal_event(
                runtime=runtime,
                event_kind="PROFILE_SELECTED",
                payload={
                    "profile_id": runtime.profile_id,
                    "profile_version": runtime.profile_version,
                    "policy_hash": runtime.profile_policy_hash,
                    "scope": "session",
                },
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
                profile_id=runtime.profile_id,
                profile_version=runtime.profile_version,
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
                profile_id=runtime.profile_id,
                profile_version=runtime.profile_version,
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
                    profile_id=row.profile_id,
                    profile_version=row.profile_version,
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
                profile_id=runtime.profile_id,
                profile_version=runtime.profile_version,
                app_server_unavailable=self._probe.app_server_unavailable,
                idempotent_replay=False,
            )

    def _resolve_turn_target(
        self,
        *,
        runtime: CopilotSessionRuntime,
        target_turn_id: str | None,
        use_last_turn: bool,
    ) -> str:
        if target_turn_id:
            return target_turn_id
        if not use_last_turn:
            raise URMError(
                code="URM_STEER_DENIED",
                message="target_turn_id is required when use_last_turn is false",
                context={"session_id": runtime.session_id},
            )
        if runtime.active_turn_id:
            return runtime.active_turn_id
        raise URMError(
            code="URM_STEER_DENIED",
            message="unable to resolve active last_turn deterministically",
            context={"session_id": runtime.session_id},
        )

    def _remaining_parent_duration_secs(self, *, runtime: CopilotSessionRuntime) -> int:
        started = datetime.fromisoformat(runtime.started_at)
        elapsed = datetime.now(tz=timezone.utc) - started
        remaining = self.config.max_session_duration_secs - int(elapsed.total_seconds())
        return max(0, remaining)

    def _child_budget_snapshot(self, *, runtime: CopilotSessionRuntime) -> dict[str, int]:
        remaining_parent = self._remaining_parent_duration_secs(runtime=runtime)
        return {
            "max_solver_calls": 40,
            "max_duration_secs": min(300, remaining_parent),
            "max_token_budget": 20_000,
            "remaining_parent_duration_secs": remaining_parent,
        }

    def child_parent_session_id(self, *, child_id: str) -> str | None:
        with self._lock:
            child = self._child_runs.get(child_id)
            return child.parent_session_id if child is not None else None

    def steer(self, request: CopilotSteerRequest) -> CopilotSteerResponse:
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
                        endpoint_name=COPILOT_STEER_ENDPOINT,
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
                    replay = CopilotSteerResponse.model_validate(reservation.response_json or {})
                    return replay.model_copy(update={"idempotent_replay": True})

            self._bootstrap_runtime(runtime=runtime)
            target_turn_id = self._resolve_turn_target(
                runtime=runtime,
                target_turn_id=request.target_turn_id,
                use_last_turn=request.use_last_turn,
            )
            steer_count = runtime.steer_counts_by_turn.get(target_turn_id, 0)
            if steer_count >= MAX_STEER_PER_TURN:
                raise URMError(
                    code="URM_STEER_DENIED",
                    message="steer rate limit exceeded for turn",
                    context={
                        "session_id": request.session_id,
                        "target_turn_id": target_turn_id,
                        "max_steer_per_turn": MAX_STEER_PER_TURN,
                    },
                )
            if runtime.thread_id is None:
                raise URMError(
                    code="URM_STEER_DENIED",
                    message="copilot thread is not initialized",
                    context={"session_id": request.session_id},
                )
            request_id = uuid.uuid4().hex
            try:
                line = runtime.host.send(
                    {
                        "id": request_id,
                        "method": "turn/steer",
                        "params": {
                            "threadId": runtime.thread_id,
                            "input": [{"type": "text", "text": request.text}],
                            "expectedTurnId": target_turn_id,
                        },
                    }
                )
                self._record_event_line(runtime=runtime, raw_line=line)
                response = self._wait_for_response(
                    runtime=runtime,
                    request_id=request_id,
                    timeout_secs=10.0,
                )
                if "error" in response:
                    raise URMError(
                        code="URM_STEER_DENIED",
                        message="turn/steer was rejected by app-server",
                        context={
                            "session_id": request.session_id,
                            "target_turn_id": target_turn_id,
                            "error": response.get("error"),
                        },
                    )
            except URMError as exc:
                if exc.detail.code != "URM_STEER_DENIED":
                    raise URMError(
                        code="URM_STEER_DENIED",
                        message="turn/steer failed",
                        context={
                            "session_id": request.session_id,
                            "target_turn_id": target_turn_id,
                            "reason": exc.detail.message,
                        },
                    ) from exc
                raise

            accepted_turn_id = response.get("result", {}).get("turnId")
            if not isinstance(accepted_turn_id, str) or not accepted_turn_id:
                accepted_turn_id = target_turn_id
            runtime.active_turn_id = accepted_turn_id
            runtime.last_turn_id = accepted_turn_id
            runtime.steer_counts_by_turn[accepted_turn_id] = (
                runtime.steer_counts_by_turn.get(accepted_turn_id, 0) + 1
            )
            steer_payload_hash = sha256_canonical_json(
                {
                    "steer_intent_class": request.steer_intent_class,
                    "text": request.text,
                }
            )
            self._record_internal_event(
                runtime=runtime,
                event_kind="STEER_APPLIED",
                payload={
                    "target_turn_id": target_turn_id,
                    "accepted_turn_id": accepted_turn_id,
                    "steer_intent_class": request.steer_intent_class,
                    "steer_payload_hash": steer_payload_hash,
                },
            )
            response_model = CopilotSteerResponse(
                session_id=request.session_id,
                status=runtime.status,
                target_turn_id=target_turn_id,
                accepted_turn_id=accepted_turn_id,
                idempotent_replay=False,
            )
            with transaction(db_path=self.config.db_path) as con:
                persist_idempotency_response(
                    con=con,
                    endpoint_name=COPILOT_STEER_ENDPOINT,
                    client_request_id=request.client_request_id,
                    response_json=response_model.model_dump(mode="json"),
                )
            return response_model

    def spawn_child(
        self,
        request: AgentSpawnRequest,
        *,
        inherited_policy_hash: str | None,
        capabilities_allowed: list[str],
    ) -> AgentSpawnResponse:
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
            running_children = [
                child_id
                for child_id in self._children_by_parent.get(request.session_id, set())
                if self._child_runs.get(child_id) is not None
                and self._child_runs[child_id].status == "running"
            ]
            if len(running_children) >= MAX_CHILDREN_PER_PARENT:
                raise URMError(
                    code="URM_CHILD_LIMIT_EXCEEDED",
                    message="child agent limit exceeded for parent session",
                    context={
                        "session_id": request.session_id,
                        "max_children": MAX_CHILDREN_PER_PARENT,
                    },
                )
            if MAX_CHILD_DEPTH < 1:
                raise URMError(
                    code="URM_CHILD_DEPTH_EXCEEDED",
                    message="child depth limit exceeded",
                    context={"session_id": request.session_id, "max_depth": MAX_CHILD_DEPTH},
                )
            with transaction(db_path=self.config.db_path) as con:
                child_id = uuid.uuid4().hex
                try:
                    reservation = reserve_request_idempotency(
                        con=con,
                        endpoint_name=AGENT_SPAWN_ENDPOINT,
                        client_request_id=request.client_request_id,
                        payload_hash=payload_hash,
                        resource_id=child_id,
                    )
                except ValueError as exc:
                    raise URMError(
                        code="URM_IDEMPOTENCY_KEY_CONFLICT",
                        message="client_request_id already used with a different payload",
                        status_code=409,
                        context={"client_request_id": request.client_request_id},
                    ) from exc
                if reservation.replay:
                    replay = AgentSpawnResponse.model_validate(reservation.response_json or {})
                    return replay.model_copy(update={"idempotent_replay": True})
                child_id = reservation.resource_id

            selected_profile_id = runtime.profile_id
            if request.profile_id is not None:
                try:
                    selected_profile_id = self._validate_profile_id(request.profile_id)
                except URMError as exc:
                    self._record_parent_or_audit_event(
                        parent_session_id=request.session_id,
                        event_kind="PROFILE_DENIED",
                        payload={
                            "profile_id": request.profile_id,
                            "scope": "run",
                            "reason": exc.detail.message,
                        },
                    )
                    raise
                self._record_parent_or_audit_event(
                    parent_session_id=request.session_id,
                    event_kind="PROFILE_SELECTED",
                    payload={
                        "profile_id": selected_profile_id,
                        "profile_version": runtime.profile_version,
                        "scope": "run",
                        "child_id": child_id,
                    },
                )

            target_turn_id = self._resolve_turn_target(
                runtime=runtime,
                target_turn_id=request.target_turn_id,
                use_last_turn=request.use_last_turn,
            )
            self._bootstrap_runtime(runtime=runtime)
            if runtime.thread_id is None:
                raise URMError(
                    code="URM_CHILD_SPAWN_FAILED",
                    message="copilot thread is not initialized",
                    context={"session_id": request.session_id},
                )

            raw_path = self._raw_jsonl_path_for_child(child_id)
            events_path = self._urm_events_path_for_child(child_id)
            raw_rel_path = self._relative_path(raw_path)
            events_rel_path = self._relative_path(events_path)
            child = ChildAgentRuntime(
                child_id=child_id,
                parent_session_id=request.session_id,
                parent_turn_id=target_turn_id,
                parent_stream_id=f"copilot:{request.session_id}",
                child_stream_id=f"child:{child_id}",
                started_at=datetime.now(tz=timezone.utc).isoformat(),
                events_writer=EvidenceFileWriter(
                    path=events_path,
                    max_line_bytes=self.config.max_line_bytes,
                    max_file_bytes=self.config.max_evidence_file_bytes,
                ),
                raw_writer=EvidenceFileWriter(
                    path=raw_path,
                    max_line_bytes=self.config.max_line_bytes,
                    max_file_bytes=self.config.max_evidence_file_bytes,
                ),
                raw_jsonl_path=raw_rel_path,
                urm_events_path=events_rel_path,
                budget_snapshot=self._child_budget_snapshot(runtime=runtime),
                inherited_policy_hash=inherited_policy_hash,
                capabilities_allowed=sorted(capabilities_allowed),
                profile_id=selected_profile_id,
                profile_version=runtime.profile_version,
            )
            self._child_runs[child_id] = child
            self._children_by_parent.setdefault(request.session_id, set()).add(child_id)
            self._record_parent_or_audit_event(
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
                },
            )
            self._record_child_event(
                child=child,
                event_kind="WORKER_START",
                payload={"worker_id": child_id, "status": "running"},
            )

            def _child_call(method: str, params: dict[str, Any]) -> dict[str, Any]:
                response = self._send_jsonrpc_and_wait(
                    runtime=runtime,
                    method=method,
                    params=params,
                    timeout_secs=10.0,
                )
                self._record_child_event(
                    child=child,
                    event_kind="TOOL_CALL_PASS",
                    payload={"tool_name": method, "status": "completed"},
                )
                return response

            try:
                spawn_response = _child_call(
                    "spawn_agent",
                    {"threadId": runtime.thread_id, "turnId": target_turn_id},
                )
                result = spawn_response.get("result", {})
                child_thread_id = (
                    result.get("newThreadId")
                    or result.get("receiverThreadId")
                    or result.get("threadId")
                )
                if not isinstance(child_thread_id, str) or not child_thread_id:
                    child_thread_id = f"child-thread:{child_id}"
                child.child_thread_id = child_thread_id
                _child_call(
                    "send_input",
                    {
                        "threadId": runtime.thread_id,
                        "receiverThreadId": child_thread_id,
                        "prompt": request.prompt,
                    },
                )
                _child_call(
                    "wait",
                    {
                        "threadId": runtime.thread_id,
                        "receiverThreadId": child_thread_id,
                    },
                )
                _child_call(
                    "close_agent",
                    {
                        "threadId": runtime.thread_id,
                        "receiverThreadId": child_thread_id,
                    },
                )
                child.status = "completed"
                child.ended_at = datetime.now(tz=timezone.utc).isoformat()
                self._record_child_event(
                    child=child,
                    event_kind="WORKER_PASS",
                    payload={"worker_id": child_id, "status": "completed"},
                )
                self._record_parent_or_audit_event(
                    parent_session_id=request.session_id,
                    event_kind="TOOL_CALL_PASS",
                    payload={
                        "tool_name": "spawn_agent",
                        "child_id": child_id,
                        "status": "completed",
                    },
                )
            except URMError as exc:
                child.status = "failed"
                child.error_code = "URM_CHILD_SPAWN_FAILED"
                child.error_message = exc.detail.message
                child.ended_at = datetime.now(tz=timezone.utc).isoformat()
                self._record_child_event(
                    child=child,
                    event_kind="WORKER_FAIL",
                    payload={
                        "worker_id": child_id,
                        "status": "failed",
                        "error_code": child.error_code,
                    },
                )
                self._record_parent_or_audit_event(
                    parent_session_id=request.session_id,
                    event_kind="TOOL_CALL_FAIL",
                    payload={
                        "tool_name": "spawn_agent",
                        "child_id": child_id,
                        "error_code": child.error_code,
                        "reason": exc.detail.message,
                    },
                )
            self._persist_child_terminal_state(child=child)
            response_model = AgentSpawnResponse(
                child_id=child.child_id,
                parent_session_id=child.parent_session_id,
                status=child.status,
                parent_stream_id=child.parent_stream_id,
                child_stream_id=child.child_stream_id,
                target_turn_id=child.parent_turn_id,
                profile_id=child.profile_id,
                profile_version=child.profile_version,
                idempotent_replay=False,
                error=(
                    {"code": child.error_code, "message": child.error_message}
                    if child.error_code and child.error_message
                    else None
                ),
                budget_snapshot=child.budget_snapshot,
                inherited_policy_hash=child.inherited_policy_hash,
            )
            with transaction(db_path=self.config.db_path) as con:
                persist_idempotency_response(
                    con=con,
                    endpoint_name=AGENT_SPAWN_ENDPOINT,
                    client_request_id=request.client_request_id,
                    response_json=response_model.model_dump(mode="json"),
                )
            return response_model

    def cancel_child(self, *, child_id: str, request: AgentCancelRequest) -> AgentCancelResponse:
        payload_hash = sha256_canonical_json(
            {"child_id": child_id, **request.idempotency_payload()}
        )
        with self._lock:
            with transaction(db_path=self.config.db_path) as con:
                try:
                    reservation = reserve_request_idempotency(
                        con=con,
                        endpoint_name=AGENT_CANCEL_ENDPOINT,
                        client_request_id=request.client_request_id,
                        payload_hash=payload_hash,
                        resource_id=child_id,
                    )
                except ValueError as exc:
                    raise URMError(
                        code="URM_IDEMPOTENCY_KEY_CONFLICT",
                        message="client_request_id already used with a different payload",
                        status_code=409,
                        context={"client_request_id": request.client_request_id},
                    ) from exc
                if reservation.replay:
                    replay = AgentCancelResponse.model_validate(reservation.response_json or {})
                    return replay.model_copy(update={"idempotent_replay": True})

            child = self._child_runs.get(child_id)
            if child is None:
                raise URMError(
                    code="URM_NOT_FOUND",
                    message="child agent not found",
                    status_code=404,
                    context={"child_id": child_id},
                )
            if child.status in {"completed", "failed", "cancelled"}:
                self._record_parent_or_audit_event(
                    parent_session_id=child.parent_session_id,
                    event_kind="WORKER_CANCEL",
                    payload={
                        "worker_id": child_id,
                        "status": child.status,
                        "error_code": "URM_CHILD_CANCEL_ALREADY_TERMINAL",
                    },
                    endpoint="urm.agent.cancel",
                )
                response_model = AgentCancelResponse(
                    child_id=child_id,
                    status=child.status,
                    idempotent_replay=True,
                    error={
                        "code": "URM_CHILD_CANCEL_ALREADY_TERMINAL",
                        "message": "child agent already terminal",
                    },
                )
            else:
                child.status = "cancelled"
                child.ended_at = datetime.now(tz=timezone.utc).isoformat()
                self._record_child_event(
                    child=child,
                    event_kind="WORKER_CANCEL",
                    payload={"worker_id": child_id, "status": "cancelled"},
                    endpoint="urm.agent.cancel",
                )
                self._record_parent_or_audit_event(
                    parent_session_id=child.parent_session_id,
                    event_kind="WORKER_CANCEL",
                    payload={"worker_id": child_id, "status": "cancelled"},
                    endpoint="urm.agent.cancel",
                )
                self._persist_child_terminal_state(child=child)
                response_model = AgentCancelResponse(
                    child_id=child_id,
                    status="cancelled",
                    idempotent_replay=False,
                    error=None,
                )

            with transaction(db_path=self.config.db_path) as con:
                persist_idempotency_response(
                    con=con,
                    endpoint_name=AGENT_CANCEL_ENDPOINT,
                    client_request_id=request.client_request_id,
                    response_json=response_model.model_dump(mode="json"),
                )
            return response_model

    def shutdown(self) -> None:
        with self._lock:
            child_ids = list(self._child_runs)
            for child_id in child_ids:
                child = self._child_runs.get(child_id)
                if child is None:
                    continue
                if child.status == "running":
                    child.status = "cancelled"
                    child.ended_at = datetime.now(tz=timezone.utc).isoformat()
                    try:
                        self._record_child_event(
                            child=child,
                            event_kind="WORKER_CANCEL",
                            payload={"worker_id": child_id, "status": "cancelled"},
                            endpoint="urm.agent.cancel",
                        )
                    except Exception:
                        pass
                self._persist_child_terminal_state(child=child)
                self._child_runs.pop(child_id, None)
            self._children_by_parent.clear()
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
