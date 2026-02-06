from __future__ import annotations

import json
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


def test_create_artifact_allows_multiple_same_ir_id_proof_rows(
    monkeypatch, tmp_path: Path
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_PROOF_BACKEND", "mock")

    create_artifact_endpoint(
        ArtifactCreateRequest(
            clause_text="Supplier shall deliver goods.",
            ir=_sample_ir(),
            mode=KernelMode.LAX,
        )
    )
    create_artifact_endpoint(
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
            SELECT proof_id, details_json
            FROM proof_artifacts
            ORDER BY created_at ASC
            """
        ).fetchall()

    assert len(rows) == 2
    assert len({row["proof_id"] for row in rows}) == 2
    backend_proof_ids: set[str] = set()
    for row in rows:
        details = json.loads(row["details_json"])
        backend_proof_id = details["backend_proof_id"]
        assert isinstance(backend_proof_id, str) and backend_proof_id.startswith("proof_")
        backend_proof_ids.add(backend_proof_id)
    assert len(backend_proof_ids) == 1


def test_create_artifact_failed_proof_uses_configured_backend(
    monkeypatch, tmp_path: Path
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_PROOF_BACKEND", "lean")
    monkeypatch.setenv("ADEU_LEAN_TIMEOUT_MS", "0")

    created = create_artifact_endpoint(
        ArtifactCreateRequest(
            clause_text="Supplier shall deliver goods.",
            ir=_sample_ir(),
            mode=KernelMode.LAX,
        )
    )

    with sqlite3.connect(db_path) as con:
        con.row_factory = sqlite3.Row
        row = con.execute(
            """
            SELECT artifact_id, backend, status, details_json
            FROM proof_artifacts
            ORDER BY created_at DESC
            LIMIT 1
            """
        ).fetchone()

    assert row is not None
    assert row["artifact_id"] == created.artifact_id
    assert row["backend"] == "lean"
    assert row["status"] == "failed"
    details = json.loads(row["details_json"])
    assert details["error"] == "ADEU_LEAN_TIMEOUT_MS must be a positive integer"
    assert isinstance(details["backend_proof_id"], str)
