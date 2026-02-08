from __future__ import annotations

import hashlib
import sqlite3
from pathlib import Path

import adeu_api.main as api_main
from adeu_api.main import ArtifactCreateRequest, list_artifacts_endpoint
from adeu_ir import AdeuIR, ProofArtifact, ProofInput
from adeu_kernel import KernelMode


def _sample_ir() -> AdeuIR:
    return AdeuIR.model_validate(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_artifact_list_trust_test",
            "context": {
                "doc_id": "doc:test:artifact:list:trust",
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
                            "doc_ref": "doc:test:artifact:list:trust#sec1",
                            "span": {"start": 0, "end": 20},
                        },
                    }
                ]
            },
        }
    )


def _summary_for_artifact(artifact_id: str):
    rows = list_artifacts_endpoint(
        doc_id=None,
        status=None,
        created_after=None,
        created_before=None,
        limit=50,
        offset=0,
    ).items
    matches = [row for row in rows if row.artifact_id == artifact_id]
    assert len(matches) == 1
    return matches[0]


def test_artifact_list_includes_mock_trust_labels(monkeypatch, tmp_path: Path) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_PROOF_BACKEND", "mock")

    created = api_main.create_artifact_endpoint(
        ArtifactCreateRequest(
            clause_text="Supplier shall deliver goods.",
            ir=_sample_ir(),
            mode=KernelMode.LAX,
        )
    )
    summary = _summary_for_artifact(created.artifact_id)
    assert summary.solver_trust == "solver_backed"
    assert summary.proof_trust == "mock_backend_not_proof_checked"


def test_artifact_list_reports_no_required_proofs_when_rows_missing(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_PROOF_BACKEND", "mock")

    created = api_main.create_artifact_endpoint(
        ArtifactCreateRequest(
            clause_text="Supplier shall deliver goods.",
            ir=_sample_ir(),
            mode=KernelMode.LAX,
        )
    )
    with sqlite3.connect(db_path) as con:
        con.execute(
            """
            DELETE FROM proof_artifacts
            WHERE artifact_id = ? AND theorem_id LIKE ?
            """,
            (created.artifact_id, "%pred_closed_world"),
        )

    summary = _summary_for_artifact(created.artifact_id)
    assert summary.solver_trust == "solver_backed"
    assert summary.proof_trust == "no_required_proofs"


def test_artifact_list_promotes_proof_checked_for_lean_proved_required(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_PROOF_BACKEND", "lean")

    class _StubLeanBackend:
        def check(
            self,
            *,
            theorem_id: str,
            theorem_src: str,
            inputs: list[ProofInput],
        ) -> ProofArtifact:
            return ProofArtifact(
                proof_id=f"proof_{hashlib.sha256(theorem_id.encode('utf-8')).hexdigest()[:16]}",
                backend="lean",
                theorem_id=theorem_id,
                status="proved",
                proof_hash=hashlib.sha256(theorem_src.encode("utf-8")).hexdigest(),
                inputs=inputs,
                details={"mode": "stub-lean"},
            )

    monkeypatch.setattr(api_main, "build_proof_backend", lambda: _StubLeanBackend())

    created = api_main.create_artifact_endpoint(
        ArtifactCreateRequest(
            clause_text="Supplier shall deliver goods.",
            ir=_sample_ir(),
            mode=KernelMode.LAX,
        )
    )

    summary = _summary_for_artifact(created.artifact_id)
    assert summary.solver_trust == "proof_checked"
    assert summary.proof_trust == "lean_core_v1_proved"
