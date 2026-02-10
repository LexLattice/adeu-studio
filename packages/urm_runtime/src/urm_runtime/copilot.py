from __future__ import annotations

import threading
import uuid
from collections import deque
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from .app_server import CodexAppServerHost
from .config import URMRuntimeConfig
from .errors import URMError
from .evidence import EvidenceFileLimitExceeded, EvidenceFileWriter
from .hashing import sha256_canonical_json
from .models import (
    CopilotModeRequest,
    CopilotSessionResponse,
    CopilotSessionSendRequest,
    CopilotSessionStartRequest,
    CopilotStopRequest,
    NormalizedEvent,
)
from .normalization import normalize_app_server_line
from .probe import CodexCapabilityProbeResult, run_and_persist_capability_probe
from .storage import (
    CopilotSessionRow,
    get_copilot_session,
    persist_copilot_session_start,
    persist_evidence_record,
    persist_idempotency_response,
    reserve_request_idempotency,
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
    writer: EvidenceFileWriter
    raw_jsonl_path: str
    started_at: str
    last_seq: int = 0
    status: str = "starting"
    ended_at: str | None = None
    error_code: str | None = None
    error_message: str | None = None
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

    @property
    def probe(self) -> CodexCapabilityProbeResult:
        return self._probe

    def _raw_jsonl_path_for_session(self, session_id: str) -> Path:
        path = self.config.evidence_root / "copilot" / f"{session_id}.jsonl"
        path.parent.mkdir(parents=True, exist_ok=True)
        return path

    def _relative_path(self, path: Path) -> str:
        try:
            return str(path.relative_to(self.config.var_root))
        except ValueError:
            return str(path)

    def _resolve_raw_path(self, raw_jsonl_path: str) -> Path:
        path = Path(raw_jsonl_path)
        if not path.is_absolute():
            path = self.config.var_root / path
        return path.resolve()

    def _record_event_line(self, *, runtime: CopilotSessionRuntime, raw_line: str) -> None:
        with runtime.condition:
            runtime.last_seq += 1
            seq = runtime.last_seq
            try:
                line = raw_line if raw_line.endswith("\n") else raw_line + "\n"
                runtime.writer.write_raw_line(line)
            except (EvidenceFileLimitExceeded, ValueError) as exc:
                runtime.error_code = "URM_CODEX_SESSION_LIMIT_EXCEEDED"
                runtime.error_message = str(exc)
                runtime.status = "failed"
                runtime.ended_at = datetime.now(tz=timezone.utc).isoformat()
                runtime.condition.notify_all()
                runtime.host.stop()
                return
            event = normalize_app_server_line(seq=seq, raw_line=raw_line)
            runtime.buffer.append(event)
            runtime.condition.notify_all()

        with transaction(db_path=self.config.db_path) as con:
            update_copilot_session_last_seq(
                con=con,
                copilot_session_id=runtime.session_id,
                last_seq=runtime.last_seq,
            )

    def _record_internal_event(
        self,
        *,
        runtime: CopilotSessionRuntime,
        event_kind: str,
        payload: dict[str, Any],
    ) -> None:
        import json

        self._record_event_line(
            runtime=runtime,
            raw_line=json.dumps({"event": event_kind, **payload}),
        )

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
                metadata_json={"last_seq": runtime.last_seq},
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
        self._record_internal_event(
            runtime=runtime,
            event_kind="process_terminated",
            payload={"reason": reason, "exit_code": exit_code},
        )
        runtime.writer.close()
        with runtime.condition:
            runtime.condition.notify_all()
        self._persist_terminal_state(runtime=runtime)
        return CopilotSessionResponse(
            session_id=runtime.session_id,
            status=runtime.status,
            app_server_unavailable=self._probe.app_server_unavailable,
            idempotent_replay=False,
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
            raw_rel_path = self._relative_path(raw_path)
            writer = EvidenceFileWriter(
                path=raw_path,
                max_line_bytes=self.config.max_line_bytes,
                max_file_bytes=self.config.max_evidence_file_bytes,
            )
            runtime = CopilotSessionRuntime(
                session_id=session_id,
                host=CodexAppServerHost(
                    config=self.config,
                    on_line=lambda line: self._record_event_line(runtime=runtime, raw_line=line),
                ),
                writer=writer,
                raw_jsonl_path=raw_rel_path,
                started_at=datetime.now(tz=timezone.utc).isoformat(),
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
                writer.close()
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
            with transaction(db_path=self.config.db_path) as con:
                set_copilot_writes_allowed(
                    con=con,
                    copilot_session_id=request.session_id,
                    writes_allowed=request.writes_allowed,
                )
            self._record_internal_event(
                runtime=runtime,
                event_kind="mode_changed",
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

    def _replay_events_from_file(
        self,
        *,
        row: CopilotSessionRow,
        after_seq: int,
    ) -> list[NormalizedEvent]:
        if row.raw_jsonl_path is None:
            return []
        raw_path = self._resolve_raw_path(row.raw_jsonl_path)
        if not raw_path.exists():
            return []
        events: list[NormalizedEvent] = []
        with raw_path.open("r", encoding="utf-8", errors="replace") as handle:
            seq = 0
            for line in handle:
                seq += 1
                if seq <= after_seq:
                    continue
                events.append(normalize_app_server_line(seq=seq, raw_line=line))
                if len(events) >= self.config.max_replay_events:
                    break
        return events

    def iter_events(self, *, session_id: str, after_seq: int) -> tuple[list[NormalizedEvent], str]:
        with self._lock:
            runtime = self._sessions.get(session_id)
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
