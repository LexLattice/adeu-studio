from __future__ import annotations

import shutil
import sqlite3
from pathlib import Path

import pytest
from urm_runtime.config import URMRuntimeConfig
from urm_runtime.errors import URMError
from urm_runtime.models import WorkerRunRequest
from urm_runtime.normalization import normalize_exec_line
from urm_runtime.worker import CodexExecWorkerRunner


def _runtime_config(*, tmp_path: Path, codex_bin: Path) -> URMRuntimeConfig:
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
        max_evidence_file_bytes=200_000_000,
        max_session_duration_secs=6 * 60 * 60,
        max_concurrent_workers=2,
        approval_ttl_secs=120,
        retention_days=14,
        max_total_evidence_bytes=2_000_000_000,
    )


def _prepare_fake_codex(*, tmp_path: Path) -> Path:
    fixture = Path(__file__).resolve().parent / "fixtures" / "codex_exec" / "fake_codex.py"
    target = tmp_path / "fake_codex.py"
    shutil.copy2(fixture, target)
    target.chmod(0o755)
    return target


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
    request = WorkerRunRequest(
        client_request_id="req-1",
        role="pipeline_worker",
        prompt="demo prompt",
        template_id="demo_template",
        template_version="v1",
        schema_version="schema.v1",
        domain_pack_id="urm_domain_adeu",
        domain_pack_version="0.0.0",
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
    raw_payload = raw_path.read_text(encoding="utf-8")
    assert '"type":"message"' in raw_payload
    assert '"type":"result"' in raw_payload

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
            WorkerRunRequest(
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
        WorkerRunRequest(
            client_request_id="req-conflict",
            role="pipeline_worker",
            prompt="first prompt",
        )
    )

    with pytest.raises(URMError) as exc_info:
        runner.run(
            WorkerRunRequest(
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
        WorkerRunRequest(
            client_request_id="req-parse",
            role="pipeline_worker",
            prompt="parse fixture",
        )
    )

    assert result.status == "ok"
    assert result.parse_degraded is True
    assert result.normalized_event_count == 3
    assert result.artifact_candidate == {"kind": "fallback"}


def test_normalize_exec_line_tolerates_unknown_and_parse_errors() -> None:
    unknown = normalize_exec_line(seq=1, raw_line='{"custom":"shape"}\n')
    malformed = normalize_exec_line(seq=2, raw_line="not-json\n")

    assert unknown.event_kind == "unknown_event"
    assert malformed.event_kind == "parse_error"
