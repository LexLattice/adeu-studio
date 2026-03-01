from __future__ import annotations

import hashlib
import json
import sqlite3
from pathlib import Path

import adeu_api.main as api_main
import pytest
from adeu_api.main import ArtifactCreateRequest, create_artifact_endpoint, get_artifact_endpoint
from adeu_ir import AdeuIR, ProofArtifact, ProofInput
from adeu_kernel import KernelMode


def _sample_ir() -> AdeuIR:
    return AdeuIR.model_validate(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_artifact_trust_test",
            "context": {
                "doc_id": "doc:test:artifact:trust",
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
                            "doc_ref": "doc:test:artifact:trust#sec1",
                            "span": {"start": 0, "end": 20},
                        },
                    }
                ]
            },
        }
    )


def _insert_proof_row(
    *,
    db_path: Path,
    proof_id: str,
    artifact_id: str,
    created_at: str,
    theorem_id: str,
    obligation_kind: str,
    backend: str,
    status: str,
    semantics_version: str = "adeu.lean.core.v1",
) -> None:
    inputs_hash = hashlib.sha256(f"inputs::{theorem_id}".encode("utf-8")).hexdigest()
    theorem_src_hash = hashlib.sha256(f"src::{theorem_id}".encode("utf-8")).hexdigest()
    mapping_id = hashlib.sha256(
        json.dumps(
            {
                "theorem_id": theorem_id,
                "obligation_kind": obligation_kind,
                "inputs_hash": inputs_hash,
                "proof_semantics_version": semantics_version,
                "theorem_src_hash": theorem_src_hash,
            },
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()
    details = {
        "backend_proof_id": proof_id,
        "semantics_version": semantics_version,
        "obligation_kind": obligation_kind,
        "inputs_hash": inputs_hash,
        "theorem_src_hash": theorem_src_hash,
        "mapping_id": mapping_id,
    }
    with sqlite3.connect(db_path) as con:
        con.execute(
            """
            INSERT INTO proof_artifacts (
              proof_id, artifact_id, created_at, backend, theorem_id, status, proof_hash,
              inputs_json, details_json
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                proof_id,
                artifact_id,
                created_at,
                backend,
                theorem_id,
                status,
                hashlib.sha256(proof_id.encode("utf-8")).hexdigest(),
                json.dumps([], sort_keys=True),
                json.dumps(details, sort_keys=True),
            ),
        )


def test_artifact_trust_mock_backend_never_promotes(monkeypatch, tmp_path: Path) -> None:
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
    assert created.solver_trust == "solver_backed"
    assert created.proof_trust == "mock_backend_not_proof_checked"

    fetched = get_artifact_endpoint(created.artifact_id)
    assert fetched.solver_trust == "solver_backed"
    assert fetched.proof_trust == "mock_backend_not_proof_checked"


def test_artifact_trust_lean_failure_is_partial(monkeypatch, tmp_path: Path) -> None:
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
    assert created.solver_trust == "solver_backed"
    assert created.proof_trust == "lean_core_v1_partial_or_failed"


def test_artifact_trust_promotes_on_lean_proved_required_obligations(
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

    created = create_artifact_endpoint(
        ArtifactCreateRequest(
            clause_text="Supplier shall deliver goods.",
            ir=_sample_ir(),
            mode=KernelMode.LAX,
        )
    )
    assert created.solver_trust == "proof_checked"
    assert created.proof_trust == "lean_core_v1_proved"

    fetched = get_artifact_endpoint(created.artifact_id)
    assert fetched.solver_trust == "proof_checked"
    assert fetched.proof_trust == "lean_core_v1_proved"


def test_artifact_trust_requires_recomputable_proof_evidence_hash(
    monkeypatch: pytest.MonkeyPatch,
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
    original_packet_builder = api_main._proof_evidence_packet_from_row

    def _corrupt_hash(row):
        packet = original_packet_builder(row)
        packet["proof_evidence_hash"] = "0" * 64
        return packet

    monkeypatch.setattr(api_main, "_proof_evidence_packet_from_row", _corrupt_hash)

    created = create_artifact_endpoint(
        ArtifactCreateRequest(
            clause_text="Supplier shall deliver goods.",
            ir=_sample_ir(),
            mode=KernelMode.LAX,
        )
    )
    assert created.solver_trust == "solver_backed"
    assert created.proof_trust == "lean_core_v1_partial_or_failed"


def test_artifact_trust_requires_mapping_id_continuity(
    monkeypatch: pytest.MonkeyPatch,
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
    created = create_artifact_endpoint(
        ArtifactCreateRequest(
            clause_text="Supplier shall deliver goods.",
            ir=_sample_ir(),
            mode=KernelMode.LAX,
        )
    )
    assert created.solver_trust == "proof_checked"
    assert created.proof_trust == "lean_core_v1_proved"

    with sqlite3.connect(db_path) as con:
        con.row_factory = sqlite3.Row
        row = con.execute(
            """
            SELECT proof_id, details_json
            FROM proof_artifacts
            WHERE artifact_id = ? AND theorem_id LIKE ?
            ORDER BY created_at DESC
            LIMIT 1
            """,
            (created.artifact_id, "%pred_closed_world"),
        ).fetchone()
        assert row is not None
        details = json.loads(str(row["details_json"]))
        details["mapping_id"] = "0" * 64
        con.execute(
            "UPDATE proof_artifacts SET details_json = ? WHERE proof_id = ?",
            (json.dumps(details, sort_keys=True), str(row["proof_id"])),
        )

    fetched = get_artifact_endpoint(created.artifact_id)
    assert fetched.solver_trust == "solver_backed"
    assert fetched.proof_trust == "lean_core_v1_partial_or_failed"


def test_artifact_trust_requires_mapping_id_presence(
    monkeypatch: pytest.MonkeyPatch,
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
    created = create_artifact_endpoint(
        ArtifactCreateRequest(
            clause_text="Supplier shall deliver goods.",
            ir=_sample_ir(),
            mode=KernelMode.LAX,
        )
    )
    assert created.solver_trust == "proof_checked"
    assert created.proof_trust == "lean_core_v1_proved"

    with sqlite3.connect(db_path) as con:
        con.row_factory = sqlite3.Row
        row = con.execute(
            """
            SELECT proof_id, details_json
            FROM proof_artifacts
            WHERE artifact_id = ? AND theorem_id LIKE ?
            ORDER BY created_at DESC, proof_id DESC
            LIMIT 1
            """,
            (created.artifact_id, "%pred_closed_world"),
        ).fetchone()
        assert row is not None
        details = json.loads(str(row["details_json"]))
        details.pop("mapping_id", None)
        con.execute(
            "UPDATE proof_artifacts SET details_json = ? WHERE proof_id = ?",
            (json.dumps(details, sort_keys=True), str(row["proof_id"])),
        )

    fetched = get_artifact_endpoint(created.artifact_id)
    assert fetched.solver_trust == "solver_backed"
    assert fetched.proof_trust == "lean_core_v1_partial_or_failed"


def test_artifact_trust_requires_unique_mapping_id_per_required_obligation(
    monkeypatch: pytest.MonkeyPatch,
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
    created = create_artifact_endpoint(
        ArtifactCreateRequest(
            clause_text="Supplier shall deliver goods.",
            ir=_sample_ir(),
            mode=KernelMode.LAX,
        )
    )
    assert created.solver_trust == "proof_checked"
    assert created.proof_trust == "lean_core_v1_proved"

    with sqlite3.connect(db_path) as con:
        con.row_factory = sqlite3.Row
        pred_row = con.execute(
            """
            SELECT details_json
            FROM proof_artifacts
            WHERE artifact_id = ? AND theorem_id LIKE ?
            ORDER BY created_at DESC, proof_id DESC
            LIMIT 1
            """,
            (created.artifact_id, "%pred_closed_world"),
        ).fetchone()
        conflict_row = con.execute(
            """
            SELECT proof_id, details_json
            FROM proof_artifacts
            WHERE artifact_id = ? AND theorem_id LIKE ?
            ORDER BY created_at DESC, proof_id DESC
            LIMIT 1
            """,
            (created.artifact_id, "%conflict_soundness"),
        ).fetchone()
        assert pred_row is not None
        assert conflict_row is not None
        pred_details = json.loads(str(pred_row["details_json"]))
        conflict_details = json.loads(str(conflict_row["details_json"]))
        conflict_details["mapping_id"] = pred_details["mapping_id"]
        con.execute(
            "UPDATE proof_artifacts SET details_json = ? WHERE proof_id = ?",
            (json.dumps(conflict_details, sort_keys=True), str(conflict_row["proof_id"])),
        )

    fetched = get_artifact_endpoint(created.artifact_id)
    assert fetched.solver_trust == "solver_backed"
    assert fetched.proof_trust == "lean_core_v1_partial_or_failed"


def test_artifact_trust_reraises_unexpected_proof_packet_value_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def _raise_unexpected(_: list[object]) -> list[dict[str, object]]:
        raise ValueError("unexpected packet error", "URM_UNEXPECTED_PACKET_ERROR")

    monkeypatch.setattr(api_main, "_proof_evidence_packets_from_rows", _raise_unexpected)

    with pytest.raises(ValueError, match="unexpected packet error"):
        api_main._artifact_trust_labels(validator_runs=[], proof_rows=[])


def test_artifact_trust_missing_required_rows_is_no_required(
    monkeypatch,
    tmp_path: Path,
) -> None:
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
    with sqlite3.connect(db_path) as con:
        con.execute(
            """
            DELETE FROM proof_artifacts
            WHERE artifact_id = ? AND theorem_id LIKE ?
            """,
            (created.artifact_id, "%pred_closed_world"),
        )

    fetched = get_artifact_endpoint(created.artifact_id)
    assert fetched.solver_trust == "solver_backed"
    assert fetched.proof_trust == "no_required_proofs"


def test_artifact_trust_duplicate_rows_use_latest_created_then_proof_id(
    monkeypatch,
    tmp_path: Path,
) -> None:
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

    # Later rows override baseline mock rows.
    _insert_proof_row(
        db_path=db_path,
        proof_id="proof_conflict_001",
        artifact_id=created.artifact_id,
        created_at="9999-01-01T00:00:00+00:00",
        theorem_id="manual_conflict_001",
        obligation_kind="conflict_soundness",
        backend="lean",
        status="failed",
    )
    _insert_proof_row(
        db_path=db_path,
        proof_id="proof_conflict_999",
        artifact_id=created.artifact_id,
        created_at="9999-01-01T00:00:00+00:00",
        theorem_id="manual_conflict_999",
        obligation_kind="conflict_soundness",
        backend="lean",
        status="proved",
    )
    _insert_proof_row(
        db_path=db_path,
        proof_id="proof_pred_999",
        artifact_id=created.artifact_id,
        created_at="9999-01-01T00:00:00+00:00",
        theorem_id="manual_pred_999",
        obligation_kind="pred_closed_world",
        backend="lean",
        status="proved",
    )

    fetched = get_artifact_endpoint(created.artifact_id)
    assert fetched.solver_trust == "proof_checked"
    assert fetched.proof_trust == "lean_core_v1_proved"
