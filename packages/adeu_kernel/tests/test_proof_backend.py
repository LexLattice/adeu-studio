from __future__ import annotations

from adeu_ir import ProofInput
from adeu_kernel import LeanCliProofBackend, MockProofBackend, build_trivial_theorem_source


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
