from __future__ import annotations

import json
import sqlite3
from pathlib import Path

from adeu_api.main import (
    ArtifactCreateRequest,
    CheckRequest,
    check_variant,
    create_artifact_endpoint,
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
    assert rows[0]["status"] == "UNSAT"

    evidence = json.loads(rows[0]["evidence_json"])
    atom_map = json.loads(rows[0]["atom_map_json"])
    assert "unsat_core" in evidence
    assert atom_map


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
    assert rows[0]["status"] == "UNSAT"
