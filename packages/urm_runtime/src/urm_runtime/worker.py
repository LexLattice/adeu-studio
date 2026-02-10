from __future__ import annotations

import subprocess
import uuid
from datetime import datetime, timezone
from pathlib import Path

from .config import URMRuntimeConfig
from .errors import URMError
from .evidence import EvidenceFileLimitExceeded, EvidenceFileWriter
from .hashing import sha256_canonical_json
from .models import WorkerRunRequest, WorkerRunResult
from .normalization import extract_artifact_candidate, normalize_exec_line
from .roles import get_role_policy
from .storage import (
    db_path_from_config,
    persist_evidence_record,
    persist_idempotency_response,
    persist_worker_run_end,
    persist_worker_run_start,
    reserve_worker_idempotency,
    transaction,
)

WORKER_RUN_ENDPOINT_NAME = "urm.worker.run"
WORKER_GRACE_SECS = 5


class CodexExecWorkerRunner:
    def __init__(self, *, config: URMRuntimeConfig | None = None) -> None:
        self.config = config or URMRuntimeConfig.from_env()

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
            worker_id = reservation.worker_id
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

        writer = EvidenceFileWriter(
            path=raw_path,
            max_line_bytes=self.config.max_line_bytes,
            max_file_bytes=self.config.max_evidence_file_bytes,
        )
        try:
            try:
                process = subprocess.Popen(
                    command,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    encoding="utf-8",
                    errors="replace",
                    cwd=request.cwd,
                )
            except FileNotFoundError as exc:
                error_code = "URM_CODEX_BIN_NOT_FOUND"
                error_message = f"codex executable not found: {self.config.codex_bin}"
                status = "failed"
                events.append(
                    normalize_exec_line(
                        seq=1,
                        raw_line=(
                            '{"event":"worker_error","code":"URM_CODEX_BIN_NOT_FOUND","error":"'
                            + str(exc).replace('"', "'")
                            + '"}'
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
                        raw_line=(
                            '{"event":"worker_error","code":"URM_WORKER_START_FAILED","error":"'
                            + str(exc).replace('"', "'")
                            + '"}'
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

                if error_code is None:
                    if exit_code == 0:
                        status = "ok"
                    else:
                        status = "failed"
                        error_code = "URM_WORKER_EXIT_NONZERO"
                        error_message = f"worker exited with code {exit_code}"
                else:
                    status = "failed"
        finally:
            writer.close()

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
            status=status,  # type: ignore[arg-type]
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
                status=status,
                error_json=error_json,
                metadata_json=metadata_json,
            )
            result = result.model_copy(update={"evidence_id": evidence_id})
            persist_worker_run_end(
                con=con,
                worker_id=worker_id,
                status=status,
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
