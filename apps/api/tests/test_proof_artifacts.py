from __future__ import annotations

import sqlite3
from pathlib import Path

from adeu_api.main import (
    ArtifactCreateRequest,
    create_artifact_endpoint,
    list_artifact_proofs_endpoint,
)
from adeu_ir import AdeuIR
from adeu_kernel import KernelMode


def _sample_ir() -> AdeuIR:
    return AdeuIR.model_validate(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_proof_artifact_test",
            "context": {
                "doc_id": "doc:test:proof",
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
                            "doc_ref": "doc:test:proof#sec1",
                            "span": {"start": 0, "end": 20},
                        },
                    }
                ]
            },
        }
    )


def test_create_artifact_persists_mock_proof_artifact(monkeypatch, tmp_path: Path) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_PROOF_BACKEND", "mock")

    resp = create_artifact_endpoint(
        ArtifactCreateRequest(
            clause_text="Supplier shall deliver goods.",
            ir=_sample_ir(),
            mode=KernelMode.LAX,
        )
    )

    with sqlite3.connect(db_path) as con:
        con.row_factory = sqlite3.Row
        rows = con.execute(
            """
            SELECT artifact_id, backend, theorem_id, status, proof_hash
            FROM proof_artifacts
            ORDER BY created_at ASC
            """
        ).fetchall()

    assert len(rows) == 1
    assert rows[0]["artifact_id"] == resp.artifact_id
    assert rows[0]["backend"] == "mock"
    assert rows[0]["status"] == "proved"
    assert rows[0]["theorem_id"] == "ir_proof_artifact_test_artifact_consistency"
    assert isinstance(rows[0]["proof_hash"], str) and len(rows[0]["proof_hash"]) == 64


def test_list_artifact_proofs_returns_rows(monkeypatch, tmp_path: Path) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_PROOF_BACKEND", "mock")

    created = create_artifact_endpoint(
        ArtifactCreateRequest(
            clause_text="Supplier shall deliver goods.",
            ir=_sample_ir(),
            mode=KernelMode.LAX,
        )
    )

    resp = list_artifact_proofs_endpoint(created.artifact_id)
    assert len(resp.items) == 1
    item = resp.items[0]
    assert item.artifact_id == created.artifact_id
    assert item.proof.backend == "mock"
    assert item.proof.status == "proved"
    assert item.proof.theorem_id == "ir_proof_artifact_test_artifact_consistency"
