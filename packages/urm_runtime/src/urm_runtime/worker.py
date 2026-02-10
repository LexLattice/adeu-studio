from __future__ import annotations

import json
import os
import subprocess
import threading
import time
import uuid
from datetime import datetime, timezone
from pathlib import Path

from .config import URMRuntimeConfig
from .errors import URMError
from .evidence import EvidenceFileLimitExceeded, EvidenceFileWriter
from .hashing import sha256_canonical_json
from .models import WorkerCancelResponse, WorkerRunRequest, WorkerRunResult
from .normalization import extract_artifact_candidate, normalize_exec_line
from .retention import run_evidence_retention_gc
from .roles import get_role_policy
from .storage import (
    count_running_worker_runs,
    db_path_from_config,
    get_worker_run,
    persist_evidence_record,
    persist_idempotency_response,
    persist_worker_run_end,
    persist_worker_run_start,
    reserve_worker_idempotency,
    transaction,
)

WORKER_RUN_ENDPOINT_NAME = "urm.worker.run"
WORKER_GRACE_SECS = 5
WORKER_CANCEL_WAIT_SECS = 6
_TERMINAL_WORKER_STATUSES = {"ok", "failed", "cancelled"}


class CodexExecWorkerRunner:
    def __init__(self, *, config: URMRuntimeConfig | None = None) -> None:
        self.config = config or URMRuntimeConfig.from_env()
        self._process_lock = threading.RLock()
        self._active_processes: dict[str, subprocess.Popen[str]] = {}
        self._cancel_requested: set[str] = set()

    def _build_command(self, request: WorkerRunRequest) -> list[str]:
        command = [
            self.config.codex_bin,
            "exec",
            "--json",
            "--sandbox",
            "read-only",
            "--ask-for-approval",
            "never",
        ]
        if request.output_schema_path:
            command.extend(["--output-schema", request.output_schema_path])
        command.append(request.prompt)
        return command

    def _build_subprocess_env(self) -> dict[str, str]:
        allowed_exact = {
            "PATH",
            "HOME",
            "USERPROFILE",
            "APPDATA",
            "LOCALAPPDATA",
            "XDG_CONFIG_HOME",
            "XDG_CACHE_HOME",
            "SYSTEMROOT",
            "WINDIR",
            "TMP",
            "TEMP",
            "TMPDIR",
            "COMSPEC",
            "PATHEXT",
            "PYTHONIOENCODING",
        }
        allowed_prefixes = (
            "FAKE_CODEX_",
            "CODEX_",
            "ADEU_CODEX_",
            "URM_",
        )
        env: dict[str, str] = {}
        for key, value in os.environ.items():
            if key in allowed_exact or any(key.startswith(prefix) for prefix in allowed_prefixes):
                env[key] = value
        env.setdefault("PYTHONIOENCODING", "utf-8")
        return env

    def _raw_jsonl_path_for_worker(self, worker_id: str) -> Path:
        path = self.config.evidence_root / "worker" / f"{worker_id}.jsonl"
        path.parent.mkdir(parents=True, exist_ok=True)
        return path

    def _terminate_process(self, process: subprocess.Popen[str]) -> None:
        if process.poll() is not None:
            return
        process.terminate()
        try:
            process.wait(timeout=WORKER_GRACE_SECS)
            return
        except subprocess.TimeoutExpired:
            pass
        process.kill()
        process.wait(timeout=WORKER_GRACE_SECS)

    def _set_process_running(
        self,
        *,
        worker_id: str,
        process: subprocess.Popen[str],
    ) -> None:
        with self._process_lock:
            self._active_processes[worker_id] = process

    def _clear_process_running(self, *, worker_id: str) -> None:
        with self._process_lock:
            self._active_processes.pop(worker_id, None)

    def _is_cancel_requested(self, *, worker_id: str) -> bool:
        with self._process_lock:
            return worker_id in self._cancel_requested

    def _clear_cancel_requested(self, *, worker_id: str) -> None:
        with self._process_lock:
            self._cancel_requested.discard(worker_id)

    def _load_worker_row(self, *, worker_id: str):
        db_path = db_path_from_config(self.config)
        with transaction(db_path=db_path) as con:
            return get_worker_run(con=con, worker_id=worker_id)

    def cancel(self, *, worker_id: str) -> WorkerCancelResponse:
        process: subprocess.Popen[str] | None = None
        was_running = False
        with self._process_lock:
            process = self._active_processes.get(worker_id)
            if process is not None and process.poll() is None:
                was_running = True
                self._cancel_requested.add(worker_id)
        if was_running and process is not None:
            self._terminate_process(process)

        deadline = time.monotonic() + WORKER_CANCEL_WAIT_SECS
        row = self._load_worker_row(worker_id=worker_id)
        while (
            row is not None
            and row.status == "running"
            and was_running
            and time.monotonic() < deadline
        ):
            time.sleep(0.05)
            row = self._load_worker_row(worker_id=worker_id)

        if row is None:
            raise URMError(
                code="URM_NOT_FOUND",
                message="worker run not found",
                status_code=404,
                context={"worker_id": worker_id},
            )
        if row.status == "running":
            return WorkerCancelResponse(
                worker_id=worker_id,
                status="running",
                idempotent_replay=False,
                error=None,
            )

        return WorkerCancelResponse(
            worker_id=worker_id,
            status=row.status,  # type: ignore[arg-type]
            idempotent_replay=not was_running,
            error=(
                {"code": row.error_code, "message": row.error_message}
                if row.error_code is not None and row.error_message is not None
                else None
            ),
        )

    def run(self, request: WorkerRunRequest) -> WorkerRunResult:
        if request.provider != "codex":
            raise URMError(
                code="URM_POLICY_DENIED",
                message="unsupported provider",
                context={"provider": request.provider},
            )

        try:
            role_policy = get_role_policy(request.role)
        except KeyError:
            raise URMError(
                code="URM_POLICY_DENIED",
                message="unknown role",
                context={"role": request.role},
            ) from None
        if role_policy.transport != "exec":
            raise URMError(
                code="URM_POLICY_DENIED",
                message="role does not allow worker exec transport",
                context={"role": request.role, "transport": role_policy.transport},
            )

        # Best-effort retention pass before allocating new evidence files.
        run_evidence_retention_gc(config=self.config)

        payload_hash = sha256_canonical_json(request.idempotency_payload())
        db_path = db_path_from_config(self.config)
        worker_id = uuid.uuid4().hex
        raw_path = self._raw_jsonl_path_for_worker(worker_id)
        try:
            raw_jsonl_rel_path = str(raw_path.relative_to(self.config.var_root))
        except ValueError:
            raw_jsonl_rel_path = str(raw_path)

        with transaction(db_path=db_path) as con:
            try:
                reservation = reserve_worker_idempotency(
                    con=con,
                    endpoint_name=WORKER_RUN_ENDPOINT_NAME,
                    client_request_id=request.client_request_id,
                    payload_hash=payload_hash,
                    worker_id=worker_id,
                )
            except ValueError as exc:
                raise URMError(
                    code="URM_IDEMPOTENCY_KEY_CONFLICT",
                    message="client_request_id already used with a different payload",
                    status_code=409,
                    context={"client_request_id": request.client_request_id},
                ) from exc
            if reservation.replay:
                replay = WorkerRunResult.model_validate(reservation.response_json or {})
                return replay.model_copy(update={"idempotent_replay": True})
            worker_id = reservation.resource_id
            running_count = count_running_worker_runs(con=con)
            if running_count >= self.config.max_concurrent_workers:
                raise URMError(
                    code="URM_WORKER_START_FAILED",
                    message="max concurrent worker limit reached",
                    context={
                        "running_workers": running_count,
                        "max_concurrent_workers": self.config.max_concurrent_workers,
                    },
                )
            raw_path = self._raw_jsonl_path_for_worker(worker_id)
            try:
                raw_jsonl_rel_path = str(raw_path.relative_to(self.config.var_root))
            except ValueError:
                raw_jsonl_rel_path = str(raw_path)
            persist_worker_run_start(
                con=con,
                worker_id=worker_id,
                role=request.role,
                provider=request.provider,
                template_id=request.template_id,
                template_version=request.template_version,
                schema_version=request.schema_version,
                domain_pack_id=request.domain_pack_id,
                domain_pack_version=request.domain_pack_version,
                raw_jsonl_path=raw_jsonl_rel_path,
            )

        command = self._build_command(request)
        started_at = datetime.now(tz=timezone.utc).isoformat()
        events = []
        parse_degraded = False
        status = "failed"
        error_code: str | None = None
        error_message: str | None = None
        exit_code: int | None = None

        with EvidenceFileWriter(
            path=raw_path,
            max_line_bytes=self.config.max_line_bytes,
            max_file_bytes=self.config.max_evidence_file_bytes,
        ) as writer:
            process: subprocess.Popen[str] | None = None
            try:
                process = subprocess.Popen(
                    command,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    encoding="utf-8",
                    errors="replace",
                    cwd=request.cwd,
                    env=self._build_subprocess_env(),
                )
                self._set_process_running(worker_id=worker_id, process=process)
            except FileNotFoundError as exc:
                error_code = "URM_CODEX_BIN_NOT_FOUND"
                error_message = f"codex executable not found: {self.config.codex_bin}"
                status = "failed"
                events.append(
                    normalize_exec_line(
                        seq=1,
                        raw_line=json.dumps(
                            {
                                "event": "worker_error",
                                "code": "URM_CODEX_BIN_NOT_FOUND",
                                "error": str(exc),
                            }
                        ),
                    )
                )
                process = None
            except OSError as exc:
                error_code = "URM_WORKER_START_FAILED"
                error_message = f"failed to start worker: {exc}"
                status = "failed"
                events.append(
                    normalize_exec_line(
                        seq=1,
                        raw_line=json.dumps(
                            {
                                "event": "worker_error",
                                "code": "URM_WORKER_START_FAILED",
                                "error": str(exc),
                            }
                        ),
                    )
                )
                process = None

            if process is not None:
                assert process.stdout is not None
                try:
                    seq = 0
                    for line in process.stdout:
                        seq += 1
                        writer.write_raw_line(line)
                        event = normalize_exec_line(seq=seq, raw_line=line)
                        if event.event_kind == "parse_error":
                            parse_degraded = True
                        events.append(event)
                except EvidenceFileLimitExceeded as exc:
                    error_code = "URM_WORKER_OUTPUT_LIMIT_EXCEEDED"
                    error_message = str(exc)
                    self._terminate_process(process)
                except Exception:
                    self._terminate_process(process)
                    raise

                try:
                    exit_code = process.wait(timeout=request.timeout_secs)
                except subprocess.TimeoutExpired:
                    self._terminate_process(process)
                    exit_code = process.returncode
                    error_code = "URM_WORKER_TIMEOUT"
                    error_message = f"worker timed out after {request.timeout_secs} seconds"
                finally:
                    self._clear_process_running(worker_id=worker_id)

                if self._is_cancel_requested(worker_id=worker_id):
                    status = "cancelled"
                    error_code = "URM_WORKER_CANCELLED"
                    error_message = "worker cancelled by user"
                elif error_code is None:
                    if exit_code == 0:
                        status = "ok"
                    else:
                        status = "failed"
                        error_code = "URM_WORKER_EXIT_NONZERO"
                        error_message = f"worker exited with code {exit_code}"
                else:
                    status = "failed"

                self._clear_cancel_requested(worker_id=worker_id)

        artifact_candidate = extract_artifact_candidate(events)
        ended_at = datetime.now(tz=timezone.utc).isoformat()
        metadata_json = {
            "normalized_event_count": len(events),
            "parse_degraded": parse_degraded,
        }
        error_json = (
            {"code": error_code, "message": error_message}
            if error_code is not None and error_message is not None
            else None
        )

        result = WorkerRunResult(
            worker_id=worker_id,
            status=status if status in _TERMINAL_WORKER_STATUSES else "failed",  # type: ignore[arg-type]
            exit_code=exit_code,
            evidence_id="",
            raw_jsonl_path=raw_jsonl_rel_path,
            normalized_event_count=len(events),
            artifact_candidate=artifact_candidate,
            parse_degraded=parse_degraded,
            error=error_json,
            idempotent_replay=False,
        )

        with transaction(db_path=db_path) as con:
            evidence_id = persist_evidence_record(
                con=con,
                source="codex_exec",
                role=request.role,
                worker_id=worker_id,
                copilot_session_id=None,
                template_id=request.template_id,
                started_at=started_at,
                ended_at=ended_at,
                raw_jsonl_path=raw_jsonl_rel_path,
                status=result.status,
                error_json=error_json,
                metadata_json=metadata_json,
            )
            result = result.model_copy(update={"evidence_id": evidence_id})
            persist_worker_run_end(
                con=con,
                worker_id=worker_id,
                status=result.status,
                exit_code=exit_code,
                error_code=error_code,
                error_message=error_message,
                result_json=result.model_dump(mode="json"),
            )
            persist_idempotency_response(
                con=con,
                endpoint_name=WORKER_RUN_ENDPOINT_NAME,
                client_request_id=request.client_request_id,
                response_json=result.model_dump(mode="json"),
            )

        if error_code is not None and error_message is not None:
            raise URMError(
                code=error_code,
                message=error_message,
                status_code=400,
                context={"worker_id": worker_id, "evidence_id": result.evidence_id},
            )
        return result
