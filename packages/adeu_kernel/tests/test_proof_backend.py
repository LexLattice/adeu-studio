from __future__ import annotations

from adeu_ir import ProofInput
from adeu_kernel import (
    LeanCliProofBackend,
    MockProofBackend,
    build_adeu_core_proof_requests,
    build_proof_backend,
    build_proof_mapping_id,
    build_trivial_theorem_source,
)


def test_build_trivial_theorem_source_sanitizes_theorem_name() -> None:
    theorem = build_trivial_theorem_source(theorem_id="123 bad-id")
    assert "theorem t_123_bad_id : True := by" in theorem


def test_mock_proof_backend_is_deterministic() -> None:
    backend = MockProofBackend()
    theorem_id = "artifact_consistency"
    theorem_src = build_trivial_theorem_source(theorem_id=theorem_id)
    inputs = [ProofInput(object_id="dn1", json_path="/D_norm/statements/0", formula_hash="f1")]

    p1 = backend.check(theorem_id=theorem_id, theorem_src=theorem_src, inputs=inputs)
    p2 = backend.check(theorem_id=theorem_id, theorem_src=theorem_src, inputs=inputs)

    assert p1.status == "proved"
    assert p2.status == "proved"
    assert p1.proof_hash == p2.proof_hash
    assert p1.proof_id == p2.proof_id


def test_lean_cli_backend_reports_missing_binary_as_failed() -> None:
    backend = LeanCliProofBackend(lean_bin="/tmp/lean-not-installed", timeout_ms=1000)
    theorem_id = "artifact_consistency"
    theorem_src = build_trivial_theorem_source(theorem_id=theorem_id)

    result = backend.check(theorem_id=theorem_id, theorem_src=theorem_src, inputs=[])
    assert result.backend == "lean"
    assert result.status == "failed"
    assert "binary not found" in str(result.details.get("error", "")).lower()


def test_build_adeu_core_proof_requests_returns_three_obligations() -> None:
    requests = build_adeu_core_proof_requests(theorem_prefix="ir_sample", inputs=[])
    assert [request.obligation_kind for request in requests] == [
        "pred_closed_world",
        "exception_gating",
        "conflict_soundness",
    ]
    assert [request.theorem_id for request in requests] == [
        "ir_sample_pred_closed_world",
        "ir_sample_exception_gating",
        "ir_sample_conflict_soundness",
    ]


def test_build_proof_backend_accepts_lean_bin_alias(monkeypatch) -> None:
    monkeypatch.setenv("ADEU_PROOF_BACKEND", "lean")
    monkeypatch.delenv("ADEU_LEAN_BIN", raising=False)
    monkeypatch.setenv("LEAN_BIN", "/tmp/lean-alias")
    backend = build_proof_backend()
    assert isinstance(backend, LeanCliProofBackend)
    assert backend.lean_bin == "/tmp/lean-alias"


def test_build_proof_mapping_id_is_stable() -> None:
    left = build_proof_mapping_id(
        theorem_id="ir_sample_pred_closed_world",
        obligation_kind="pred_closed_world",
        inputs_hash="a" * 64,
        proof_semantics_version="adeu.lean.core.v1",
        theorem_src_hash="b" * 64,
    )
    right = build_proof_mapping_id(
        theorem_id="ir_sample_pred_closed_world",
        obligation_kind="pred_closed_world",
        inputs_hash="a" * 64,
        proof_semantics_version="adeu.lean.core.v1",
        theorem_src_hash="b" * 64,
    )
    assert left == right
    assert len(left) == 64
