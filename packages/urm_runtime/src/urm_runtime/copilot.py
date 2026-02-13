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
from .hashing import canonical_json, sha256_canonical_json
from .models import (
    AgentCancelRequest,
    AgentCancelResponse,
    AgentSpawnRequest,
    AgentSpawnResponse,
    ApprovalIssueResponse,
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
    NormalizedEvent,
    PolicyActivationResponse,
    PolicyActiveResponse,
    PolicyProfileCurrentResponse,
    PolicyProfileDescriptor,
    PolicyProfileListResponse,
    PolicyProfileSelectRequest,
    PolicyProfileSelectResponse,
    PolicyRollbackRequest,
    PolicyRolloutRequest,
)
from .normalization import build_internal_event, normalize_app_server_line
from .policy_governance import (
    POLICY_ROLLBACK_ENDPOINT,
    POLICY_ROLLOUT_ENDPOINT,
    apply_policy_activation,
    resolve_active_policy_state,
)
from .probe import CodexCapabilityProbeResult, run_and_persist_capability_probe
from .profile_registry import (
    PolicyProfileEntry,
    PolicyProfileRegistry,
    load_policy_profile_registry,
)
from .retention import run_evidence_retention_gc
from .storage import (
    CopilotSessionRow,
    consume_approval,
    create_approval,
    get_approval,
    get_connector_snapshot,
    get_copilot_session,
    list_active_copilot_child_runs,
    mark_running_sessions_terminated,
    persist_connector_snapshot,
    persist_copilot_session_start,
    persist_evidence_record,
    persist_idempotency_response,
    persist_worker_run_end,
    persist_worker_run_start,
    reserve_request_idempotency,
    revoke_approval,
    set_copilot_writes_allowed,
    transaction,
    update_copilot_session_last_seq,
    update_copilot_session_pid,
    update_copilot_session_profile,
    update_copilot_session_status,
    update_worker_run_status,
)

COPILOT_START_ENDPOINT = "urm.copilot.start"
COPILOT_SEND_ENDPOINT = "urm.copilot.send"
COPILOT_STEER_ENDPOINT = "urm.copilot.steer"
AGENT_SPAWN_ENDPOINT = "urm.agent.spawn"
AGENT_CANCEL_ENDPOINT = "urm.agent.cancel"
CONNECTOR_SNAPSHOT_CREATE_ENDPOINT = "urm.connectors.snapshot.create"
HEARTBEAT_SECS = 10
COPILOT_BUFFER_MAX = 20_000
MAX_STEER_PER_TURN = 5
MAX_CHILD_DEPTH = 1
MAX_CHILDREN_PER_PARENT = 2
MAX_ACTIVE_CHILDREN_PER_PARENT = 1
PROFILE_VERSION = "profile.v1"
POLICY_PROFILE_SELECT_ENDPOINT = "urm.policy.profile.select"


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
    status: Literal["queued", "running", "completed", "failed", "cancelled"] = "queued"
    ended_at: str | None = None
    error_code: str | None = None
    error_message: str | None = None
    child_thread_id: str | None = None
    last_seq: int = 0
    queue_seq: int = 0
    prompt: str = ""
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
        self._profile_registry: PolicyProfileRegistry = load_policy_profile_registry()
        self._profiles_by_id: dict[str, PolicyProfileEntry] = {
            profile.profile_id: profile for profile in self._profile_registry.sorted_profiles()
        }
        self._sessions: dict[str, CopilotSessionRuntime] = {}
        self._child_runs: dict[str, ChildAgentRuntime] = {}
        self._children_by_parent: dict[str, set[str]] = {}
        self._child_run_threads: dict[str, threading.Thread] = {}
        self._child_queue_seq_by_parent: dict[str, int] = {}
        self._active_session_id: str | None = None
        self._lock = threading.RLock()
        self._recover_terminated_sessions()
        self._recover_stale_child_runs()

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

    def _is_child_queue_v2_enabled(self) -> bool:
        return self.config.child_queue_mode == "v2"

    def _max_children_per_parent(self) -> int:
        if self._is_child_queue_v2_enabled():
            return MAX_CHILDREN_PER_PARENT
        return 1

    def _max_active_children_per_parent(self) -> int:
        if self._is_child_queue_v2_enabled():
            return MAX_ACTIVE_CHILDREN_PER_PARENT
        return 1

    def _recover_stale_child_runs(self) -> None:
        if not self._is_child_queue_v2_enabled():
            return
        with transaction(db_path=self.config.db_path) as con:
            stale_rows = list_active_copilot_child_runs(con=con)
        if not stale_rows:
            return
        for row in stale_rows:
            metadata = row.result_json if isinstance(row.result_json, dict) else {}
            child_stream_id = metadata.get("child_stream_id")
            if not isinstance(child_stream_id, str) or not child_stream_id:
                child_stream_id = f"child:{row.worker_id}"
            raw_events_path = metadata.get("urm_events_path")
            if isinstance(raw_events_path, str):
                try:
                    events_path = self._resolve_urm_events_path(raw_events_path)
                except URMError:
                    events_path = None
            else:
                events_path = None
            if events_path is not None:
                writer = EvidenceFileWriter(
                    path=events_path,
                    max_line_bytes=self.config.max_line_bytes,
                    max_file_bytes=self.config.max_evidence_file_bytes,
                )
                seq = self._next_seq_for_event_file(path=events_path)
                event = build_internal_event(
                    seq=seq,
                    event="WORKER_FAIL",
                    stream_id=child_stream_id,
                    source_component="urm_copilot_manager",
                    context={
                        "session_id": metadata.get("parent_session_id"),
                        "run_id": row.worker_id,
                        "role": "copilot",
                        "endpoint": "urm.agent.spawn",
                    },
                    detail={
                        "worker_id": row.worker_id,
                        "status": "failed",
                        "error_code": "URM_CHILD_TERMINATED_ON_RESTART",
                    },
                )
                writer.write_json_line(event.model_dump(mode="json", by_alias=True))
                writer.close()
            parent_session_id = metadata.get("parent_session_id")
            if isinstance(parent_session_id, str) and parent_session_id:
                self._record_parent_or_audit_event(
                    parent_session_id=parent_session_id,
                    event_kind="WORKER_FAIL",
                    payload={
                        "worker_id": row.worker_id,
                        "status": "failed",
                        "error_code": "URM_CHILD_TERMINATED_ON_RESTART",
                    },
                    endpoint="urm.agent.spawn",
                )
            with transaction(db_path=self.config.db_path) as con:
                persist_worker_run_end(
                    con=con,
                    worker_id=row.worker_id,
                    status="failed",
                    exit_code=None,
                    error_code="URM_CHILD_TERMINATED_ON_RESTART",
                    error_message="child run terminated during API restart",
                    result_json={
                        **metadata,
                        "status": "failed",
                        "error": {
                            "code": "URM_CHILD_TERMINATED_ON_RESTART",
                            "message": "child run terminated during API restart",
                        },
                    },
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

    def _connector_snapshot_path(self, snapshot_id: str) -> Path:
        path = self.config.evidence_root / "connectors" / f"{snapshot_id}.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        return path

    def _relative_path(self, path: Path) -> str:
        try:
            return str(path.relative_to(self.config.var_root))
        except ValueError:
            return str(path)

    def _resolve_profile(self, profile_id: str) -> PolicyProfileEntry:
        normalized = profile_id.strip()
        profile = self._profiles_by_id.get(normalized)
        if profile is None:
            raise URMError(
                code="URM_POLICY_PROFILE_NOT_FOUND",
                message="profile is not defined in registry",
                context={
                    "profile_id": profile_id,
                    "supported_profile_ids": sorted(self._profiles_by_id),
                },
            )
        return profile

    def _resolve_active_policy_hash_for_profile(self, *, profile: PolicyProfileEntry) -> str:
        active_state = resolve_active_policy_state(
            config=self.config,
            registry=self._profile_registry,
            profile_id=profile.profile_id,
        )
        return active_state.policy_hash

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
            persist_worker_run_end(
                con=con,
                worker_id=child.child_id,
                status=child.status,
                exit_code=None,
                error_code=child.error_code,
                error_message=child.error_message,
                result_json=self._child_worker_result_json(child=child),
            )
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
        profile = self._resolve_profile(request.profile_id)
        profile_id = profile.profile_id
        profile_policy_hash = self._resolve_active_policy_hash_for_profile(profile=profile)

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
                profile_version=profile.profile_version,
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

    def list_profiles(self) -> PolicyProfileListResponse:
        profiles = [
            PolicyProfileDescriptor(
                profile_id=profile.profile_id,
                profile_version=profile.profile_version,
                default_policy_hash=profile.default_policy_hash,
                allowed_policy_hashes=list(profile.allowed_policy_hashes),
                policy_ref=profile.policy_ref,
            )
            for profile in self._profile_registry.sorted_profiles()
        ]
        return PolicyProfileListResponse(profiles=profiles)

    def _build_current_profile_response(
        self,
        *,
        session_id: str,
        profile_id: str,
        profile_policy_hash: str | None,
    ) -> PolicyProfileCurrentResponse:
        profile = self._resolve_profile(profile_id)
        policy_hash = profile_policy_hash or self._resolve_active_policy_hash_for_profile(
            profile=profile
        )
        return PolicyProfileCurrentResponse(
            session_id=session_id,
            profile_id=profile.profile_id,
            profile_version=profile.profile_version,
            policy_hash=policy_hash,
        )

    def current_profile(self, *, session_id: str) -> PolicyProfileCurrentResponse:
        with self._lock:
            runtime = self._sessions.get(session_id)
            if runtime is not None:
                return self._build_current_profile_response(
                    session_id=session_id,
                    profile_id=runtime.profile_id,
                    profile_policy_hash=runtime.profile_policy_hash,
                )
        with transaction(db_path=self.config.db_path) as con:
            row = get_copilot_session(con=con, copilot_session_id=session_id)
        if row is None:
            raise URMError(
                code="URM_NOT_FOUND",
                message="copilot session not found",
                status_code=404,
                context={"session_id": session_id},
            )
        return self._build_current_profile_response(
            session_id=session_id,
            profile_id=row.profile_id,
            profile_policy_hash=row.profile_policy_hash,
        )

    def select_profile(self, request: PolicyProfileSelectRequest) -> PolicyProfileSelectResponse:
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
            with transaction(db_path=self.config.db_path) as con:
                try:
                    reservation = reserve_request_idempotency(
                        con=con,
                        endpoint_name=POLICY_PROFILE_SELECT_ENDPOINT,
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
                    replay = PolicyProfileSelectResponse.model_validate(
                        reservation.response_json or {}
                    )
                    return replay.model_copy(update={"idempotent_replay": True})

            try:
                profile = self._resolve_profile(request.profile_id)
            except URMError as exc:
                self._record_internal_event(
                    runtime=runtime,
                    event_kind="PROFILE_DENIED",
                    payload={
                        "profile_id": request.profile_id,
                        "scope": "session",
                        "reason": exc.detail.message,
                    },
                )
                raise

            runtime.profile_id = profile.profile_id
            runtime.profile_version = profile.profile_version
            runtime.profile_policy_hash = self._resolve_active_policy_hash_for_profile(
                profile=profile
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
                update_copilot_session_profile(
                    con=con,
                    copilot_session_id=request.session_id,
                    profile_id=runtime.profile_id,
                    profile_version=runtime.profile_version,
                    profile_policy_hash=runtime.profile_policy_hash,
                )
            response = PolicyProfileSelectResponse(
                session_id=request.session_id,
                profile_id=runtime.profile_id,
                profile_version=runtime.profile_version,
                policy_hash=runtime.profile_policy_hash or profile.default_policy_hash,
                idempotent_replay=False,
            )
            with transaction(db_path=self.config.db_path) as con:
                persist_idempotency_response(
                    con=con,
                    endpoint_name=POLICY_PROFILE_SELECT_ENDPOINT,
                    client_request_id=request.client_request_id,
                    response_json=response.model_dump(mode="json"),
                )
            return response

    def policy_active(self, *, profile_id: str) -> PolicyActiveResponse:
        active_state = resolve_active_policy_state(
            config=self.config,
            registry=self._profile_registry,
            profile_id=profile_id,
        )
        return PolicyActiveResponse(
            profile_id=active_state.profile_id,
            profile_version=active_state.profile_version,
            policy_hash=active_state.policy_hash,
            source=active_state.source,
            activation_seq=active_state.activation_seq,
            action=active_state.action,
            activation_ts=active_state.activation_ts,
            client_request_id=active_state.client_request_id,
            prev_policy_hash=active_state.prev_policy_hash,
        )

    def _apply_policy_activation_request(
        self,
        *,
        request: PolicyRolloutRequest | PolicyRollbackRequest,
        endpoint_name: str,
        action: Literal["rollout", "rollback"],
    ) -> PolicyActivationResponse:
        activation_ts = request.activation_ts or datetime.now(tz=timezone.utc).strftime(
            "%Y-%m-%dT%H:%M:%SZ"
        )
        with self._lock:
            result = apply_policy_activation(
                config=self.config,
                registry=self._profile_registry,
                endpoint_name=endpoint_name,
                action=action,
                client_request_id=request.client_request_id,
                profile_id=request.profile_id,
                target_policy_hash=request.target_policy_hash,
                activation_ts=activation_ts,
                request_payload=request.idempotency_payload(),
            )
        return PolicyActivationResponse(
            profile_id=result.profile_id,
            profile_version=result.profile_version,
            action=result.action,
            target_policy_hash=result.target_policy_hash,
            prev_policy_hash=result.prev_policy_hash,
            activation_seq=result.activation_seq,
            activation_ts=result.activation_ts,
            request_payload_hash=result.request_payload_hash,
            idempotent_replay=result.idempotent_replay,
        )

    def policy_rollout(self, request: PolicyRolloutRequest) -> PolicyActivationResponse:
        return self._apply_policy_activation_request(
            request=request,
            endpoint_name=POLICY_ROLLOUT_ENDPOINT,
            action="rollout",
        )

    def policy_rollback(self, request: PolicyRollbackRequest) -> PolicyActivationResponse:
        return self._apply_policy_activation_request(
            request=request,
            endpoint_name=POLICY_ROLLBACK_ENDPOINT,
            action="rollback",
        )

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

    def _normalize_connectors(self, *, raw_connectors: Any) -> list[dict[str, Any]]:
        if not isinstance(raw_connectors, list):
            return []
        normalized_with_keys: list[tuple[tuple[str, str, str], dict[str, Any]]] = []
        seen: set[str] = set()
        for item in raw_connectors:
            if not isinstance(item, dict):
                continue
            try:
                normalized = json.loads(canonical_json(item))
            except (TypeError, ValueError):
                continue
            if not isinstance(normalized, dict):
                continue
            connector_hash = sha256_canonical_json(normalized)
            if connector_hash in seen:
                continue
            seen.add(connector_hash)
            connector_id = normalized.get("id")
            connector_name = normalized.get("name")
            key = (
                str(connector_id) if connector_id is not None else "",
                str(connector_name) if connector_name is not None else "",
                connector_hash,
            )
            normalized_with_keys.append((key, normalized))
        normalized_with_keys.sort(key=lambda pair: pair[0])
        return [item for _, item in normalized_with_keys]

    def _extract_app_list(self, *, response: dict[str, Any]) -> list[dict[str, Any]]:
        result = response.get("result")
        if isinstance(result, dict):
            apps = result.get("apps")
            if isinstance(apps, list):
                return self._normalize_connectors(raw_connectors=apps)
            connectors = result.get("connectors")
            if isinstance(connectors, list):
                return self._normalize_connectors(raw_connectors=connectors)
        if isinstance(result, list):
            return self._normalize_connectors(raw_connectors=result)
        return []

    def _capability_snapshot_id(self) -> str:
        return self._probe.probe_id

    def create_connector_snapshot(
        self,
        request: ConnectorSnapshotCreateRequest,
    ) -> ConnectorSnapshotResponse:
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
            capability_snapshot_id = self._capability_snapshot_id()
            if (
                request.requested_capability_snapshot_id is not None
                and request.requested_capability_snapshot_id != capability_snapshot_id
            ):
                raise URMError(
                    code="URM_CONNECTOR_SNAPSHOT_STALE",
                    message="requested capability snapshot id does not match active snapshot",
                    context={
                        "requested_capability_snapshot_id": (
                            request.requested_capability_snapshot_id
                        ),
                        "capability_snapshot_id": capability_snapshot_id,
                    },
                )
            now = datetime.now(tz=timezone.utc)
            min_acceptable_ts = request.min_acceptable_ts
            if min_acceptable_ts is not None and min_acceptable_ts.tzinfo is None:
                min_acceptable_ts = min_acceptable_ts.replace(tzinfo=timezone.utc)
            if min_acceptable_ts is not None and now < min_acceptable_ts:
                raise URMError(
                    code="URM_CONNECTOR_SNAPSHOT_STALE",
                    message="snapshot creation time precedes requested minimum timestamp",
                    context={
                        "min_acceptable_ts": min_acceptable_ts.isoformat(),
                    },
                )
            with transaction(db_path=self.config.db_path) as con:
                snapshot_id = uuid.uuid4().hex
                try:
                    reservation = reserve_request_idempotency(
                        con=con,
                        endpoint_name=CONNECTOR_SNAPSHOT_CREATE_ENDPOINT,
                        client_request_id=request.client_request_id,
                        payload_hash=payload_hash,
                        resource_id=snapshot_id,
                    )
                except ValueError as exc:
                    raise URMError(
                        code="URM_IDEMPOTENCY_KEY_CONFLICT",
                        message="client_request_id already used with a different payload",
                        status_code=409,
                        context={"client_request_id": request.client_request_id},
                    ) from exc
                if reservation.replay:
                    replay = ConnectorSnapshotResponse.model_validate(
                        reservation.response_json or {}
                    )
                    return replay.model_copy(update={"idempotent_replay": True})
                snapshot_id = reservation.resource_id

            self._bootstrap_runtime(runtime=runtime)
            try:
                app_list_response = self._send_jsonrpc_and_wait(
                    runtime=runtime,
                    method="app/list",
                    params={},
                    timeout_secs=10.0,
                )
            except URMError as exc:
                raise URMError(
                    code="URM_CAPABILITY_MISSING",
                    message="connector discovery capability is unavailable",
                    context={"reason": exc.detail.message},
                ) from exc

            connectors = self._extract_app_list(response=app_list_response)
            connector_snapshot_hash = sha256_canonical_json(connectors)
            artifact_path = self._connector_snapshot_path(snapshot_id)
            artifact_rel_path = self._relative_path(artifact_path)
            with transaction(db_path=self.config.db_path) as con:
                created_at = persist_connector_snapshot(
                    con=con,
                    snapshot_id=snapshot_id,
                    session_id=request.session_id,
                    provider=request.provider,
                    capability_snapshot_id=capability_snapshot_id,
                    connector_snapshot_hash=connector_snapshot_hash,
                    connectors=connectors,
                    artifact_path=artifact_rel_path,
                )
            artifact_payload = {
                "schema": "connector_snapshot@1",
                "snapshot_id": snapshot_id,
                "session_id": request.session_id,
                "provider": request.provider,
                "capability_snapshot_id": capability_snapshot_id,
                "connector_snapshot_hash": connector_snapshot_hash,
                "created_at": created_at,
                "connectors": connectors,
            }
            artifact_path.write_text(
                canonical_json(artifact_payload) + "\n",
                encoding="utf-8",
            )
            self._record_internal_event(
                runtime=runtime,
                event_kind="EVIDENCE_WRITTEN",
                payload={
                    "evidence_id": snapshot_id,
                    "path": artifact_rel_path,
                },
            )
            response_model = ConnectorSnapshotResponse(
                snapshot_id=snapshot_id,
                session_id=request.session_id,
                provider=request.provider,
                capability_snapshot_id=capability_snapshot_id,
                connector_snapshot_hash=connector_snapshot_hash,
                created_at=datetime.fromisoformat(created_at),
                connectors=connectors,
                idempotent_replay=False,
            )
            with transaction(db_path=self.config.db_path) as con:
                persist_idempotency_response(
                    con=con,
                    endpoint_name=CONNECTOR_SNAPSHOT_CREATE_ENDPOINT,
                    client_request_id=request.client_request_id,
                    response_json=response_model.model_dump(mode="json"),
                )
            return response_model

    def get_connector_snapshot(
        self,
        *,
        snapshot_id: str,
        session_id: str,
        provider: str,
        requested_capability_snapshot_id: str | None = None,
        min_acceptable_ts: datetime | None = None,
    ) -> ConnectorSnapshotResponse:
        with self._lock:
            with transaction(db_path=self.config.db_path) as con:
                row = get_connector_snapshot(con=con, snapshot_id=snapshot_id)
            if row is None:
                raise URMError(
                    code="URM_CONNECTOR_SNAPSHOT_NOT_FOUND",
                    message="connector snapshot not found",
                    status_code=404,
                    context={"snapshot_id": snapshot_id},
                )
            if row.session_id != session_id:
                raise URMError(
                    code="URM_POLICY_DENIED",
                    message="session is not authorized for this connector snapshot",
                    context={"snapshot_id": snapshot_id, "session_id": session_id},
                )
            if row.provider != provider:
                raise URMError(
                    code="URM_CONNECTOR_SNAPSHOT_STALE",
                    message="connector snapshot provider mismatch",
                    context={
                        "snapshot_id": snapshot_id,
                        "snapshot_provider": row.provider,
                        "requested_provider": provider,
                    },
                )
            if (
                requested_capability_snapshot_id is not None
                and requested_capability_snapshot_id != row.capability_snapshot_id
            ):
                raise URMError(
                    code="URM_CONNECTOR_SNAPSHOT_STALE",
                    message="connector snapshot capability snapshot mismatch",
                    context={
                        "snapshot_id": snapshot_id,
                        "capability_snapshot_id": row.capability_snapshot_id,
                        "requested_capability_snapshot_id": requested_capability_snapshot_id,
                    },
                )
            created_at = datetime.fromisoformat(row.created_at)
            if created_at.tzinfo is None:
                created_at = created_at.replace(tzinfo=timezone.utc)
            normalized_min_ts = min_acceptable_ts
            if normalized_min_ts is not None and normalized_min_ts.tzinfo is None:
                normalized_min_ts = normalized_min_ts.replace(tzinfo=timezone.utc)
            if normalized_min_ts is not None and created_at < normalized_min_ts:
                raise URMError(
                    code="URM_CONNECTOR_SNAPSHOT_STALE",
                    message="connector snapshot is older than min_acceptable_ts",
                    context={
                        "snapshot_id": snapshot_id,
                        "created_at": created_at.isoformat(),
                        "min_acceptable_ts": normalized_min_ts.isoformat(),
                    },
                )
            return ConnectorSnapshotResponse(
                snapshot_id=row.snapshot_id,
                session_id=row.session_id,
                provider=row.provider,
                capability_snapshot_id=row.capability_snapshot_id,
                connector_snapshot_hash=row.connector_snapshot_hash,
                created_at=created_at,
                connectors=row.connectors,
                idempotent_replay=False,
            )

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
        if self._is_child_queue_v2_enabled():
            return self._spawn_child_v2(
                request,
                inherited_policy_hash=inherited_policy_hash,
                capabilities_allowed=capabilities_allowed,
            )
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
            if len(running_children) >= self._max_children_per_parent():
                raise URMError(
                    code="URM_CHILD_LIMIT_EXCEEDED",
                    message="child agent limit exceeded for parent session",
                    context={
                        "session_id": request.session_id,
                        "max_children": self._max_children_per_parent(),
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

            selected_profile = self._resolve_profile(runtime.profile_id)
            if request.profile_id is not None:
                try:
                    selected_profile = self._resolve_profile(request.profile_id)
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
                        "profile_id": selected_profile.profile_id,
                        "profile_version": selected_profile.profile_version,
                        "policy_hash": self._resolve_active_policy_hash_for_profile(
                            profile=selected_profile
                        ),
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
                profile_id=selected_profile.profile_id,
                profile_version=selected_profile.profile_version,
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

    def _next_child_queue_seq_unlocked(self, *, parent_session_id: str) -> int:
        next_seq = self._child_queue_seq_by_parent.get(parent_session_id, 0) + 1
        self._child_queue_seq_by_parent[parent_session_id] = next_seq
        return next_seq

    def _child_worker_result_json(self, *, child: ChildAgentRuntime) -> dict[str, Any]:
        return {
            "child_id": child.child_id,
            "parent_session_id": child.parent_session_id,
            "parent_stream_id": child.parent_stream_id,
            "child_stream_id": child.child_stream_id,
            "parent_turn_id": child.parent_turn_id,
            "child_thread_id": child.child_thread_id,
            "status": child.status,
            "error": (
                {"code": child.error_code, "message": child.error_message}
                if child.error_code and child.error_message
                else None
            ),
            "profile_id": child.profile_id,
            "profile_version": child.profile_version,
            "budget_snapshot": child.budget_snapshot,
            "inherited_policy_hash": child.inherited_policy_hash,
            "capabilities_allowed": child.capabilities_allowed,
            "queue_seq": child.queue_seq,
            "raw_jsonl_path": child.raw_jsonl_path,
            "urm_events_path": child.urm_events_path,
        }

    def _start_child_execution_thread_unlocked(
        self,
        *,
        parent_session_id: str,
        child: ChildAgentRuntime,
    ) -> None:
        child.status = "running"
        self._record_child_event(
            child=child,
            event_kind="WORKER_START",
            payload={
                "worker_id": child.child_id,
                "status": "running",
                "queue_seq": child.queue_seq,
            },
        )
        with transaction(db_path=self.config.db_path) as con:
            update_worker_run_status(
                con=con,
                worker_id=child.child_id,
                status="running",
                error_code=None,
                error_message=None,
                result_json=self._child_worker_result_json(child=child),
            )
        thread = threading.Thread(
            target=self._run_child_workflow_v2,
            kwargs={"child_id": child.child_id, "parent_session_id": parent_session_id},
            daemon=True,
            name=f"urm-child-{child.child_id}",
        )
        self._child_run_threads[child.child_id] = thread
        thread.start()

    def _dispatch_child_queue_unlocked(self, *, parent_session_id: str) -> None:
        children = [
            self._child_runs[child_id]
            for child_id in self._children_by_parent.get(parent_session_id, set())
            if child_id in self._child_runs
        ]
        running_count = sum(1 for child in children if child.status == "running")
        if running_count >= self._max_active_children_per_parent():
            return
        queued = sorted(
            (child for child in children if child.status == "queued"),
            key=lambda child: (child.queue_seq, child.child_id),
        )
        if not queued:
            return
        next_child = queued[0]
        runtime = self._sessions.get(parent_session_id)
        if runtime is None or runtime.status not in {"starting", "running"}:
            next_child.status = "failed"
            next_child.error_code = "URM_CHILD_TERMINATED_ON_RESTART"
            next_child.error_message = "parent session unavailable during queue dispatch"
            next_child.ended_at = datetime.now(tz=timezone.utc).isoformat()
            self._record_child_event(
                child=next_child,
                event_kind="WORKER_FAIL",
                payload={
                    "worker_id": next_child.child_id,
                    "status": "failed",
                    "error_code": next_child.error_code,
                },
            )
            self._record_parent_or_audit_event(
                parent_session_id=parent_session_id,
                event_kind="WORKER_FAIL",
                payload={
                    "worker_id": next_child.child_id,
                    "status": "failed",
                    "error_code": next_child.error_code,
                },
                endpoint="urm.agent.spawn",
            )
            self._persist_child_terminal_state(child=next_child)
            return
        self._start_child_execution_thread_unlocked(
            parent_session_id=parent_session_id,
            child=next_child,
        )

    def _run_child_workflow_v2(self, *, child_id: str, parent_session_id: str) -> None:
        try:
            with self._lock:
                child = self._child_runs.get(child_id)
                runtime = self._sessions.get(parent_session_id)
                if child is None:
                    return
                if runtime is None or runtime.status not in {"starting", "running"}:
                    child.status = "failed"
                    child.error_code = "URM_CHILD_TERMINATED_ON_RESTART"
                    child.error_message = "parent session unavailable"
                    child.ended_at = datetime.now(tz=timezone.utc).isoformat()
                    self._record_child_event(
                        child=child,
                        event_kind="WORKER_FAIL",
                        payload={
                            "worker_id": child.child_id,
                            "status": "failed",
                            "error_code": child.error_code,
                        },
                    )
                    self._record_parent_or_audit_event(
                        parent_session_id=parent_session_id,
                        event_kind="WORKER_FAIL",
                        payload={
                            "worker_id": child.child_id,
                            "status": "failed",
                            "error_code": child.error_code,
                        },
                        endpoint="urm.agent.spawn",
                    )
                    self._persist_child_terminal_state(child=child)
                    return
                self._bootstrap_runtime(runtime=runtime)
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
                with self._lock:
                    current = self._child_runs.get(child_id)
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
                response = self._send_jsonrpc_and_wait(
                    runtime=runtime,
                    method=method,
                    params=params,
                    timeout_secs=10.0,
                )
                with self._lock:
                    current = self._child_runs.get(child_id)
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
                    self._record_child_event(
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
                result.get("newThreadId")
                or result.get("receiverThreadId")
                or result.get("threadId")
            )
            if not isinstance(child_thread_id, str) or not child_thread_id:
                child_thread_id = f"child-thread:{child_id}"
            with self._lock:
                current = self._child_runs.get(child_id)
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
            with self._lock:
                current = self._child_runs.get(child_id)
                if current is None:
                    return
                if current.status != "cancelled":
                    current.status = "completed"
                    current.ended_at = datetime.now(tz=timezone.utc).isoformat()
                    self._record_child_event(
                        child=current,
                        event_kind="WORKER_PASS",
                        payload={"worker_id": child_id, "status": "completed"},
                    )
                    self._record_parent_or_audit_event(
                        parent_session_id=parent_session_id,
                        event_kind="TOOL_CALL_PASS",
                        payload={
                            "tool_name": "spawn_agent",
                            "child_id": child_id,
                            "status": "completed",
                        },
                    )
                self._persist_child_terminal_state(child=current)
        except URMError as exc:
            with self._lock:
                current = self._child_runs.get(child_id)
                if current is None:
                    return
                if current.status != "cancelled":
                    current.status = "failed"
                    current.error_code = (
                        exc.detail.code
                        if exc.detail.code.startswith("URM_CHILD_")
                        else "URM_CHILD_SPAWN_FAILED"
                    )
                    current.error_message = exc.detail.message
                    current.ended_at = datetime.now(tz=timezone.utc).isoformat()
                    self._record_child_event(
                        child=current,
                        event_kind="WORKER_FAIL",
                        payload={
                            "worker_id": child_id,
                            "status": "failed",
                            "error_code": current.error_code,
                        },
                    )
                    self._record_parent_or_audit_event(
                        parent_session_id=parent_session_id,
                        event_kind="TOOL_CALL_FAIL",
                        payload={
                            "tool_name": "spawn_agent",
                            "child_id": child_id,
                            "error_code": current.error_code,
                            "reason": current.error_message,
                        },
                    )
                self._persist_child_terminal_state(child=current)
        finally:
            with self._lock:
                self._child_run_threads.pop(child_id, None)
                self._dispatch_child_queue_unlocked(parent_session_id=parent_session_id)

    def _spawn_child_v2(
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
            active_or_queued_children = [
                child_id
                for child_id in self._children_by_parent.get(request.session_id, set())
                if self._child_runs.get(child_id) is not None
                and self._child_runs[child_id].status in {"queued", "running"}
            ]
            if len(active_or_queued_children) >= self._max_children_per_parent():
                raise URMError(
                    code="URM_CHILD_QUEUE_LIMIT_EXCEEDED",
                    message="child queue limit exceeded for parent session",
                    context={
                        "session_id": request.session_id,
                        "max_children": self._max_children_per_parent(),
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

            selected_profile = self._resolve_profile(runtime.profile_id)
            if request.profile_id is not None:
                try:
                    selected_profile = self._resolve_profile(request.profile_id)
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
                        "profile_id": selected_profile.profile_id,
                        "profile_version": selected_profile.profile_version,
                        "policy_hash": self._resolve_active_policy_hash_for_profile(
                            profile=selected_profile
                        ),
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
            queue_seq = self._next_child_queue_seq_unlocked(parent_session_id=request.session_id)
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
                status="queued",
                queue_seq=queue_seq,
                prompt=request.prompt,
                budget_snapshot=self._child_budget_snapshot(runtime=runtime),
                inherited_policy_hash=inherited_policy_hash,
                capabilities_allowed=sorted(capabilities_allowed),
                profile_id=selected_profile.profile_id,
                profile_version=selected_profile.profile_version,
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
                    "queue_seq": child.queue_seq,
                },
            )
            self._record_child_event(
                child=child,
                event_kind="WORKER_START",
                payload={
                    "worker_id": child_id,
                    "status": "queued",
                    "queue_seq": child.queue_seq,
                },
            )
            with transaction(db_path=self.config.db_path) as con:
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
                    result_json=self._child_worker_result_json(child=child),
                )
            self._dispatch_child_queue_unlocked(parent_session_id=request.session_id)
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
                error=None,
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
                if self._is_child_queue_v2_enabled():
                    self._dispatch_child_queue_unlocked(parent_session_id=child.parent_session_id)
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
                if child.status in {"running", "queued"}:
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
                self._child_run_threads.pop(child_id, None)
            self._children_by_parent.clear()
            self._child_queue_seq_by_parent.clear()
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
