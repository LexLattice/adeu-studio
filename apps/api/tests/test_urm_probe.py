from __future__ import annotations

import shutil
import sqlite3
from pathlib import Path

import pytest
from urm_runtime.config import URMRuntimeConfig
from urm_runtime.probe import run_and_persist_capability_probe


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
        max_replay_events=10_000,
        approval_ttl_secs=120,
        retention_days=14,
        max_total_evidence_bytes=2_000_000_000,
    )


def _prepare_fake_codex(*, tmp_path: Path) -> Path:
    fixture = (
        Path(__file__).resolve().parent / "fixtures" / "codex_app_server" / "fake_codex.py"
    )
    target = tmp_path / "fake_codex_probe.py"
    shutil.copy2(fixture, target)
    target.chmod(0o755)
    return target


def test_probe_records_exec_and_app_server_smoke_success(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    config = _runtime_config(tmp_path=tmp_path, codex_bin=codex_bin)
    monkeypatch.delenv("FAKE_CODEX_EXEC_FAIL", raising=False)
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    monkeypatch.delenv("FAKE_CODEX_EXEC_HELP_NO_OUTPUT_SCHEMA", raising=False)

    result = run_and_persist_capability_probe(config=config)

    assert result.exec_available is True
    assert result.app_server_available is True
    assert result.output_schema_available is True
    assert result.details["exec_help_ok"] is True
    assert result.details["exec_smoke_ok"] is True
    assert result.artifact_path.exists()

    with sqlite3.connect(config.db_path) as con:
        row = con.execute(
            """
            SELECT exec_available, app_server_available, output_schema_available
            FROM urm_codex_capability_probe
            WHERE probe_id = ?
            """,
            (result.probe_id,),
        ).fetchone()
    assert row == (1, 1, 1)


def test_probe_exec_smoke_failure_is_reported_but_exec_stays_available(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    config = _runtime_config(tmp_path=tmp_path, codex_bin=codex_bin)
    monkeypatch.setenv("FAKE_CODEX_EXEC_FAIL", "1")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    monkeypatch.delenv("FAKE_CODEX_EXEC_HELP_NO_OUTPUT_SCHEMA", raising=False)

    result = run_and_persist_capability_probe(config=config)

    assert result.exec_available is True
    assert result.details["exec_help_ok"] is True
    assert result.details["exec_smoke_ok"] is False
    assert result.app_server_available is True


def test_probe_detects_missing_output_schema_flag(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    config = _runtime_config(tmp_path=tmp_path, codex_bin=codex_bin)
    monkeypatch.setenv("FAKE_CODEX_EXEC_HELP_NO_OUTPUT_SCHEMA", "1")
    monkeypatch.delenv("FAKE_CODEX_EXEC_FAIL", raising=False)
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)

    result = run_and_persist_capability_probe(config=config)

    assert result.exec_available is True
    assert result.output_schema_available is False
    assert result.details["exec_help_contains_output_schema"] is False


def test_probe_detects_missing_ask_for_approval_flag(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    config = _runtime_config(tmp_path=tmp_path, codex_bin=codex_bin)
    monkeypatch.setenv("FAKE_CODEX_EXEC_HELP_NO_ASK_FOR_APPROVAL", "1")
    monkeypatch.delenv("FAKE_CODEX_EXEC_FAIL", raising=False)
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)

    result = run_and_persist_capability_probe(config=config)

    assert result.exec_available is True
    assert result.details["exec_help_contains_ask_for_approval"] is False


def test_probe_accepts_silent_app_server_startup(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    config = _runtime_config(tmp_path=tmp_path, codex_bin=codex_bin)
    monkeypatch.setenv("FAKE_APP_SERVER_SILENT_READY", "1")
    monkeypatch.delenv("FAKE_CODEX_EXEC_FAIL", raising=False)

    result = run_and_persist_capability_probe(config=config)

    assert result.app_server_available is True
