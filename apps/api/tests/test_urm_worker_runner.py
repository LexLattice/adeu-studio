from __future__ import annotations

import shutil
import sqlite3
import threading
import time
from pathlib import Path

import pytest
from urm_runtime.config import URMRuntimeConfig
from urm_runtime.errors import URMError
from urm_runtime.models import WorkerRunRequest
from urm_runtime.normalization import normalize_exec_line
from urm_runtime.worker import CodexExecWorkerRunner


def _runtime_config(
    *,
    tmp_path: Path,
    codex_bin: Path,
    max_concurrent_workers: int = 2,
    max_evidence_file_bytes: int = 200_000_000,
    retention_days: int = 14,
    max_total_evidence_bytes: int = 2_000_000_000,
) -> URMRuntimeConfig:
    var_root = tmp_path / "var"
    evidence_root = var_root / "evidence" / "codex"
    var_root.mkdir(parents=True, exist_ok=True)
    evidence_root.mkdir(parents=True, exist_ok=True)
    return URMRuntimeConfig(
        codex_bin=str(codex_bin),
        db_path=var_root / "adeu.sqlite3",
        var_root=var_root,
        evidence_root=evidence_root,
        max_line_bytes=1_000_000,
        max_evidence_file_bytes=max_evidence_file_bytes,
        max_session_duration_secs=6 * 60 * 60,
        max_concurrent_workers=max_concurrent_workers,
        max_replay_events=10_000,
        approval_ttl_secs=120,
        retention_days=retention_days,
        max_total_evidence_bytes=max_total_evidence_bytes,
    )


def _prepare_fake_codex(*, tmp_path: Path) -> Path:
    fixture = Path(__file__).resolve().parent / "fixtures" / "codex_exec" / "fake_codex.py"
    target = tmp_path / "fake_codex.py"
    shutil.copy2(fixture, target)
    target.chmod(0o755)
    return target


def _worker_request(
    *,
    client_request_id: str,
    role: str,
    prompt: str,
    output_schema_path: str | None = None,
) -> WorkerRunRequest:
    return WorkerRunRequest(
        client_request_id=client_request_id,
        role=role,
        prompt=prompt,
        output_schema_path=output_schema_path,
        template_id="adeu.workflow.pipeline_worker.v0",
        template_version="v0",
        schema_version="urm.workflow.v0",
        domain_pack_id="urm_domain_adeu",
        domain_pack_version="0.0.0",
    )


def test_worker_runner_persists_evidence_and_idempotent_replay(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    config = _runtime_config(tmp_path=tmp_path, codex_bin=codex_bin)
    fixture_path = Path(__file__).resolve().parent / "fixtures" / "codex_exec" / "success.jsonl"
    counter_path = tmp_path / "counter.txt"
    monkeypatch.setenv("FAKE_CODEX_JSONL_PATH", str(fixture_path))
    monkeypatch.setenv("FAKE_CODEX_CALL_COUNTER_PATH", str(counter_path))
    monkeypatch.setenv("FAKE_CODEX_EXIT_CODE", "0")

    runner = CodexExecWorkerRunner(config=config)
    request = _worker_request(
        client_request_id="req-1",
        role="pipeline_worker",
        prompt="demo prompt",
    )

    first = runner.run(request)
    second = runner.run(request)

    assert first.status == "ok"
    assert first.idempotent_replay is False
    assert first.worker_id == second.worker_id
    assert second.idempotent_replay is True
    assert first.artifact_candidate == {"artifact": {"kind": "demo", "value": 1}}

    raw_path = config.var_root / first.raw_jsonl_path
    assert raw_path.is_file()
    assert raw_path.name == "codex_raw.ndjson"
    assert first.urm_events_path is not None
    events_path = config.var_root / first.urm_events_path
    assert events_path.is_file()
    raw_payload = raw_path.read_text(encoding="utf-8")
    assert '"type":"message"' in raw_payload
    assert '"type":"result"' in raw_payload
    events_payload = events_path.read_text(encoding="utf-8")
    assert '"schema":"urm-events@1"' in events_payload

    with sqlite3.connect(config.db_path) as con:
        schema_row = con.execute(
            "SELECT schema_version FROM urm_schema_ledger ORDER BY schema_version ASC LIMIT 1"
        ).fetchone()
        assert schema_row == (1,)
        idempotency_row = con.execute(
            """
            SELECT response_json
            FROM urm_idempotency_key
            WHERE endpoint_name = ? AND client_request_id = ?
            """,
            ("urm.worker.run", "req-1"),
        ).fetchone()
        assert idempotency_row is not None
        evidence_row = con.execute(
            "SELECT evidence_id FROM urm_evidence_record WHERE worker_id = ?",
            (first.worker_id,),
        ).fetchone()
        assert evidence_row is not None

    calls = counter_path.read_text(encoding="utf-8").strip().splitlines()
    assert len(calls) == 1


def test_worker_runner_rejects_disallowed_role(tmp_path: Path) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    config = _runtime_config(tmp_path=tmp_path, codex_bin=codex_bin)
    runner = CodexExecWorkerRunner(config=config)

    with pytest.raises(URMError) as exc_info:
        runner.run(
            _worker_request(
                client_request_id="req-role",
                role="copilot",
                prompt="should fail",
            )
        )

    assert exc_info.value.detail.code == "URM_POLICY_DENIED"


def test_worker_runner_idempotency_conflict(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    config = _runtime_config(tmp_path=tmp_path, codex_bin=codex_bin)
    fixture_path = Path(__file__).resolve().parent / "fixtures" / "codex_exec" / "success.jsonl"
    monkeypatch.setenv("FAKE_CODEX_JSONL_PATH", str(fixture_path))
    monkeypatch.setenv("FAKE_CODEX_EXIT_CODE", "0")

    runner = CodexExecWorkerRunner(config=config)
    runner.run(
        _worker_request(
            client_request_id="req-conflict",
            role="pipeline_worker",
            prompt="first prompt",
        )
    )

    with pytest.raises(URMError) as exc_info:
        runner.run(
            _worker_request(
                client_request_id="req-conflict",
                role="pipeline_worker",
                prompt="second prompt",
            )
        )

    assert exc_info.value.status_code == 409
    assert exc_info.value.detail.code == "URM_IDEMPOTENCY_KEY_CONFLICT"


def test_worker_runner_marks_parse_degraded_nonfatal(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    config = _runtime_config(tmp_path=tmp_path, codex_bin=codex_bin)
    fixture_path = (
        Path(__file__).resolve().parent / "fixtures" / "codex_exec" / "unknown_and_malformed.jsonl"
    )
    monkeypatch.setenv("FAKE_CODEX_JSONL_PATH", str(fixture_path))
    monkeypatch.setenv("FAKE_CODEX_EXIT_CODE", "0")

    runner = CodexExecWorkerRunner(config=config)
    result = runner.run(
        _worker_request(
            client_request_id="req-parse",
            role="pipeline_worker",
            prompt="parse fixture",
        )
    )

    assert result.status == "ok"
    assert result.invalid_schema is False
    assert result.schema_validation_errors == []
    assert result.parse_degraded is True
    assert result.normalized_event_count == 5
    assert result.artifact_candidate == {"kind": "fallback"}


def test_normalize_exec_line_tolerates_unknown_and_parse_errors() -> None:
    unknown = normalize_exec_line(
        seq=1,
        raw_line='{"custom":"shape"}\n',
        stream_id="worker:test",
        run_id="test-run",
        role="pipeline_worker",
        endpoint="urm.worker.run",
    )
    malformed = normalize_exec_line(
        seq=2,
        raw_line="not-json\n",
        stream_id="worker:test",
        run_id="test-run",
        role="pipeline_worker",
        endpoint="urm.worker.run",
    )

    assert unknown.event_kind == "unknown_event"
    assert malformed.event_kind == "parse_error"


def test_worker_runner_cancel_is_idempotent(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    config = _runtime_config(tmp_path=tmp_path, codex_bin=codex_bin)
    fixture_path = Path(__file__).resolve().parent / "fixtures" / "codex_exec" / "success.jsonl"
    monkeypatch.setenv("FAKE_CODEX_JSONL_PATH", str(fixture_path))
    monkeypatch.setenv("FAKE_CODEX_EXIT_CODE", "0")
    monkeypatch.setenv("FAKE_CODEX_SLEEP_SECS", "4")

    runner = CodexExecWorkerRunner(config=config)
    request = _worker_request(
        client_request_id="req-cancel-1",
        role="pipeline_worker",
        prompt="cancel me",
    )
    run_error: dict[str, URMError] = {}

    def _run_worker() -> None:
        try:
            runner.run(request)
        except URMError as exc:
            run_error["error"] = exc

    thread = threading.Thread(target=_run_worker, daemon=True)
    thread.start()

    worker_id: str | None = None
    deadline = time.monotonic() + 5
    while time.monotonic() < deadline and worker_id is None:
        try:
            with sqlite3.connect(config.db_path) as con:
                row = con.execute(
                    """
                    SELECT resource_id
                    FROM urm_idempotency_key
                    WHERE endpoint_name = ? AND client_request_id = ?
                    """,
                    ("urm.worker.run", "req-cancel-1"),
                ).fetchone()
                if row is not None:
                    worker_id = str(row[0])
        except sqlite3.OperationalError:
            pass
        if worker_id is None:
            time.sleep(0.05)

    assert worker_id is not None
    first_cancel = runner.cancel(worker_id=worker_id)
    assert first_cancel.status in {"cancelled", "running"}
    assert first_cancel.idempotent_replay is False

    thread.join(timeout=10)
    assert not thread.is_alive()
    err = run_error.get("error")
    assert err is not None
    assert err.detail.code == "URM_WORKER_CANCELLED"

    second_cancel = runner.cancel(worker_id=worker_id)
    assert second_cancel.status == "cancelled"
    assert second_cancel.idempotent_replay is True


def test_worker_runner_enforces_max_concurrency(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    config = _runtime_config(
        tmp_path=tmp_path,
        codex_bin=codex_bin,
        max_concurrent_workers=1,
    )
    fixture_path = Path(__file__).resolve().parent / "fixtures" / "codex_exec" / "success.jsonl"
    monkeypatch.setenv("FAKE_CODEX_JSONL_PATH", str(fixture_path))
    monkeypatch.setenv("FAKE_CODEX_EXIT_CODE", "0")
    monkeypatch.setenv("FAKE_CODEX_SLEEP_SECS", "6")

    runner = CodexExecWorkerRunner(config=config)
    first_request = _worker_request(
        client_request_id="req-limit-1",
        role="pipeline_worker",
        prompt="hold lock",
    )
    second_request = _worker_request(
        client_request_id="req-limit-2",
        role="pipeline_worker",
        prompt="second worker",
    )
    first_error: dict[str, URMError] = {}

    def _run_first() -> None:
        try:
            runner.run(first_request)
        except URMError as exc:
            first_error["error"] = exc

    thread = threading.Thread(target=_run_first, daemon=True)
    thread.start()

    running_seen = False
    deadline = time.monotonic() + 5
    while time.monotonic() < deadline:
        count = 0
        try:
            with sqlite3.connect(config.db_path) as con:
                row = con.execute(
                    "SELECT COUNT(*) FROM urm_worker_run WHERE status = 'running'"
                ).fetchone()
                count = int(row[0]) if row is not None else 0
        except sqlite3.OperationalError:
            pass
        if count >= 1:
            running_seen = True
            break
        time.sleep(0.05)
    assert running_seen

    with pytest.raises(URMError) as exc_info:
        runner.run(second_request)
    assert exc_info.value.detail.code == "URM_WORKER_START_FAILED"
    assert exc_info.value.detail.context["max_concurrent_workers"] == 1

    with sqlite3.connect(config.db_path) as con:
        row = con.execute(
            """
            SELECT resource_id
            FROM urm_idempotency_key
            WHERE endpoint_name = ? AND client_request_id = ?
            """,
            ("urm.worker.run", "req-limit-1"),
        ).fetchone()
    assert row is not None
    worker_id = str(row[0])
    runner.cancel(worker_id=worker_id)
    thread.join(timeout=10)
    assert not thread.is_alive()
    assert first_error.get("error") is not None
    assert first_error["error"].detail.code == "URM_WORKER_CANCELLED"


def test_worker_runner_retention_preflight_purges_old_evidence(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    config = _runtime_config(
        tmp_path=tmp_path,
        codex_bin=codex_bin,
        max_total_evidence_bytes=1,
    )
    fixture_path = Path(__file__).resolve().parent / "fixtures" / "codex_exec" / "success.jsonl"
    monkeypatch.setenv("FAKE_CODEX_JSONL_PATH", str(fixture_path))
    monkeypatch.setenv("FAKE_CODEX_EXIT_CODE", "0")
    monkeypatch.delenv("FAKE_CODEX_SLEEP_SECS", raising=False)

    runner = CodexExecWorkerRunner(config=config)
    first = runner.run(
        _worker_request(
            client_request_id="req-retention-1",
            role="pipeline_worker",
            prompt="first",
        )
    )
    first_path = config.var_root / first.raw_jsonl_path
    assert first.urm_events_path is not None
    first_events_path = config.var_root / first.urm_events_path
    assert first_path.exists()
    assert first_events_path.exists()

    runner.run(
        _worker_request(
            client_request_id="req-retention-2",
            role="pipeline_worker",
            prompt="second",
        )
    )

    with sqlite3.connect(config.db_path) as con:
        row = con.execute(
            """
            SELECT purged_at, purge_reason, raw_jsonl_path
            FROM urm_evidence_record
            WHERE evidence_id = ?
            """,
            (first.evidence_id,),
        ).fetchone()
    assert row is not None
    assert row[0] is not None
    assert row[1] == "size_budget_exceeded"
    assert str(row[2]).startswith("__purged__/")
    assert not first_path.exists()
    assert not first_events_path.exists()


def test_worker_runner_output_schema_fallback_without_flag(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    config = _runtime_config(tmp_path=tmp_path, codex_bin=codex_bin)
    fixture_path = Path(__file__).resolve().parent / "fixtures" / "codex_exec" / "success.jsonl"
    schema_path = tmp_path / "output.schema.json"
    schema_path.write_text(
        """
{
  "type": "object",
  "required": ["artifact"],
  "properties": {
    "artifact": {
      "type": "object",
      "required": ["kind", "value"],
      "properties": {
        "kind": {"type": "string"},
        "value": {"type": "integer"}
      }
    }
  }
}
        """.strip(),
        encoding="utf-8",
    )
    monkeypatch.setenv("FAKE_CODEX_JSONL_PATH", str(fixture_path))
    monkeypatch.setenv("FAKE_CODEX_EXIT_CODE", "0")
    monkeypatch.setenv("FAKE_CODEX_EXEC_HELP_NO_OUTPUT_SCHEMA", "1")

    runner = CodexExecWorkerRunner(config=config)
    result = runner.run(
        _worker_request(
            client_request_id="req-schema-fallback-1",
            role="pipeline_worker",
            prompt="schema fallback",
            output_schema_path=str(schema_path),
        )
    )

    assert result.status == "ok"


def test_worker_runner_returns_structured_error_when_events_stream_hits_cap(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    config = _runtime_config(
        tmp_path=tmp_path,
        codex_bin=codex_bin,
        max_evidence_file_bytes=350,
    )
    fixture_path = Path(__file__).resolve().parent / "fixtures" / "codex_exec" / "success.jsonl"
    monkeypatch.setenv("FAKE_CODEX_JSONL_PATH", str(fixture_path))
    monkeypatch.setenv("FAKE_CODEX_EXIT_CODE", "0")

    runner = CodexExecWorkerRunner(config=config)

    with pytest.raises(URMError) as exc_info:
        runner.run(
            _worker_request(
                client_request_id="req-events-cap-1",
                role="pipeline_worker",
                prompt="cap envelope stream",
            )
        )

    assert exc_info.value.detail.code == "URM_WORKER_OUTPUT_LIMIT_EXCEEDED"


def test_worker_runner_marks_invalid_schema_with_errors(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    config = _runtime_config(tmp_path=tmp_path, codex_bin=codex_bin)
    fixture_path = Path(__file__).resolve().parent / "fixtures" / "codex_exec" / "success.jsonl"
    schema_path = tmp_path / "output.invalid.schema.json"
    schema_path.write_text(
        """
{
  "type": "object",
  "required": ["must_not_exist"]
}
        """.strip(),
        encoding="utf-8",
    )
    monkeypatch.setenv("FAKE_CODEX_JSONL_PATH", str(fixture_path))
    monkeypatch.setenv("FAKE_CODEX_EXIT_CODE", "0")
    monkeypatch.setenv("FAKE_CODEX_EXEC_HELP_NO_OUTPUT_SCHEMA", "1")

    runner = CodexExecWorkerRunner(config=config)
    result = runner.run(
        _worker_request(
            client_request_id="req-schema-fallback-2",
            role="pipeline_worker",
            prompt="schema invalid",
            output_schema_path=str(schema_path),
        )
    )

    assert result.status == "ok"
    assert result.invalid_schema is True
    assert result.schema_validation_errors


def test_worker_runner_omits_ask_for_approval_when_flag_unsupported(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    config = _runtime_config(tmp_path=tmp_path, codex_bin=codex_bin)
    fixture_path = Path(__file__).resolve().parent / "fixtures" / "codex_exec" / "success.jsonl"
    monkeypatch.setenv("FAKE_CODEX_JSONL_PATH", str(fixture_path))
    monkeypatch.setenv("FAKE_CODEX_EXIT_CODE", "0")
    monkeypatch.setenv("FAKE_CODEX_EXEC_HELP_NO_ASK_FOR_APPROVAL", "1")

    runner = CodexExecWorkerRunner(config=config)
    result = runner.run(
        _worker_request(
            client_request_id="req-no-ask-flag-1",
            role="pipeline_worker",
            prompt="run without ask-for-approval",
        )
    )

    assert result.status == "ok"
