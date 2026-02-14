from __future__ import annotations

import json
import sqlite3
from pathlib import Path

import adeu_api.main as api_main
import pytest
from adeu_api.main import (
    ArtifactCreateRequest,
    ArtifactValidatorRunsResponse,
    CheckRequest,
    check_variant,
    create_artifact_endpoint,
    list_artifact_validator_runs_endpoint,
)
from adeu_ir import AdeuIR
from adeu_kernel import KernelMode


def _sample_ir() -> AdeuIR:
    return AdeuIR.model_validate(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_validator_persist",
            "context": {
                "doc_id": "doc:test:validator",
                "jurisdiction": "US-CA",
                "time_eval": "2026-02-06T00:00:00Z",
            },
            "D_norm": {
                "statements": [
                    {
                        "id": "dn_keep_1",
                        "kind": "obligation",
                        "subject": {"ref_type": "text", "text": "Supplier"},
                        "action": {"verb": "deliver"},
                        "scope": {"jurisdiction": "US-CA", "time_about": {"kind": "unspecified"}},
                        "provenance": {
                            "doc_ref": "doc:test:validator#sec1",
                            "span": {"start": 0, "end": 20},
                        },
                    }
                ]
            },
        }
    )


def _fetch_validator_rows(db_path: Path) -> list[sqlite3.Row]:
    with sqlite3.connect(db_path) as con:
        con.row_factory = sqlite3.Row
        return con.execute(
            """
            SELECT artifact_id, backend, status, evidence_json, atom_map_json
            FROM validator_runs
            ORDER BY created_at ASC
            """
        ).fetchall()


def _table_count(db_path: Path, table: str) -> int:
    with sqlite3.connect(db_path) as con:
        row = con.execute(f"SELECT COUNT(*) FROM {table}").fetchone()
    return int(row[0]) if row is not None else 0


def test_check_endpoint_persists_validator_runs_when_flag_enabled(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_PERSIST_VALIDATOR_RUNS", "1")

    report = check_variant(CheckRequest(ir=_sample_ir(), mode=KernelMode.LAX))
    assert report.status in {"PASS", "WARN"}

    rows = _fetch_validator_rows(db_path)
    assert len(rows) == 1
    assert rows[0]["artifact_id"] is None
    assert rows[0]["backend"] == "z3"
    assert rows[0]["status"] == "SAT"

    evidence = json.loads(rows[0]["evidence_json"])
    atom_map = json.loads(rows[0]["atom_map_json"])
    assert evidence.get("unsat_core") == []
    assert atom_map == {}


def test_create_artifact_persists_validator_runs_with_artifact_id(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.delenv("ADEU_PERSIST_VALIDATOR_RUNS", raising=False)

    resp = create_artifact_endpoint(
        ArtifactCreateRequest(
            clause_text="Supplier shall deliver goods.",
            ir=_sample_ir(),
            mode=KernelMode.LAX,
        )
    )

    rows = _fetch_validator_rows(db_path)
    assert len(rows) == 1
    assert rows[0]["artifact_id"] == resp.artifact_id
    assert rows[0]["backend"] == "z3"
    assert rows[0]["status"] == "SAT"


def test_list_artifact_validator_runs_endpoint_returns_rows(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.delenv("ADEU_PERSIST_VALIDATOR_RUNS", raising=False)

    created = create_artifact_endpoint(
        ArtifactCreateRequest(
            clause_text="Supplier shall deliver goods.",
            ir=_sample_ir(),
            mode=KernelMode.LAX,
        )
    )

    resp: ArtifactValidatorRunsResponse = list_artifact_validator_runs_endpoint(created.artifact_id)
    assert len(resp.items) == 1
    run = resp.items[0]
    assert run.artifact_id == created.artifact_id
    assert run.backend == "z3"
    assert run.status == "SAT"
    assert run.evidence_json.get("unsat_core") == []
    assert run.atom_map_json == {}
    packet = run.validator_evidence_packet
    assert packet["schema"] == "validator_evidence_packet@1"
    assert packet["validator_run_id"] == run.run_id
    assert packet["status"] == run.status
    assert packet["request_hash"] == run.request_hash
    assert packet["formula_hash"] == run.formula_hash
    assert packet["evidence"]["unsat_core"] == []
    assert len(str(packet["evidence_packet_hash"])) == 64


def test_create_artifact_rolls_back_all_rows_when_proof_insert_fails(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.delenv("ADEU_PERSIST_VALIDATOR_RUNS", raising=False)

    def _explode_create_proof(*args, **kwargs):
        raise RuntimeError("synthetic-proof-insert-failure")

    monkeypatch.setattr(api_main, "create_proof_artifact", _explode_create_proof)

    with pytest.raises(RuntimeError, match="synthetic-proof-insert-failure"):
        create_artifact_endpoint(
            ArtifactCreateRequest(
                clause_text="Supplier shall deliver goods.",
                ir=_sample_ir(),
                mode=KernelMode.LAX,
            )
        )

    assert _table_count(db_path, "artifacts") == 0
    assert _table_count(db_path, "validator_runs") == 0
    assert _table_count(db_path, "proof_artifacts") == 0
