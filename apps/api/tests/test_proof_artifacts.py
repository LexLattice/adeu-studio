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
            ORDER BY theorem_id ASC
            """
        ).fetchall()

    assert len(rows) == 3
    assert all(row["artifact_id"] == resp.artifact_id for row in rows)
    assert all(row["backend"] == "mock" for row in rows)
    assert all(row["status"] == "proved" for row in rows)
    theorem_ids = {row["theorem_id"] for row in rows}
    assert theorem_ids == {
        "ir_proof_artifact_test_conflict_soundness",
        "ir_proof_artifact_test_exception_gating",
        "ir_proof_artifact_test_pred_closed_world",
    }
    assert all(isinstance(row["proof_hash"], str) and len(row["proof_hash"]) == 64 for row in rows)


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
    assert len(resp.items) == 3
    theorem_ids_ordered = [item.proof.theorem_id for item in resp.items]
    assert theorem_ids_ordered == sorted(theorem_ids_ordered)
    theorem_ids = {item.proof.theorem_id for item in resp.items}
    assert theorem_ids == {
        "ir_proof_artifact_test_conflict_soundness",
        "ir_proof_artifact_test_exception_gating",
        "ir_proof_artifact_test_pred_closed_world",
    }
    assert all(item.artifact_id == created.artifact_id for item in resp.items)
    assert all(item.proof.backend == "mock" for item in resp.items)
    assert all(item.proof.status == "proved" for item in resp.items)
    assert all(item.proof_evidence_packet["schema"] == "proof_evidence@1" for item in resp.items)
    assert all(
        isinstance(item.proof_evidence_packet["proof_evidence_hash"], str)
        and len(str(item.proof_evidence_packet["proof_evidence_hash"])) == 64
        for item in resp.items
    )


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

    assert len(rows) == 6
    assert len({row["proof_id"] for row in rows}) == 6
    backend_proof_ids: set[str] = set()
    for row in rows:
        details = json.loads(row["details_json"])
        backend_proof_id = details["backend_proof_id"]
        assert isinstance(backend_proof_id, str) and backend_proof_id.startswith("proof_")
        assert details["semantics_version"] == "adeu.lean.core.v1"
        assert isinstance(details["inputs_hash"], str) and len(details["inputs_hash"]) == 64
        assert isinstance(details["theorem_src_hash"], str)
        assert len(details["theorem_src_hash"]) == 64
        assert isinstance(details["mapping_id"], str)
        assert len(details["mapping_id"]) == 64
        backend_proof_ids.add(backend_proof_id)
    assert len(backend_proof_ids) == 3


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
        rows = con.execute(
            """
            SELECT artifact_id, backend, status, details_json
            FROM proof_artifacts
            ORDER BY created_at ASC
            """
        ).fetchall()

    assert len(rows) == 3
    for row in rows:
        assert row["artifact_id"] == created.artifact_id
        assert row["backend"] == "lean"
        assert row["status"] == "failed"
        details = json.loads(row["details_json"])
        assert details["error"] == "ADEU_LEAN_TIMEOUT_MS must be a positive integer"
        assert details["error_code"] == "URM_PROOF_BACKEND_UNAVAILABLE"
        assert details["semantics_version"] == "adeu.lean.core.v1"
        assert isinstance(details["backend_proof_id"], str)
        assert isinstance(details["mapping_id"], str)
        assert len(details["mapping_id"]) == 64
