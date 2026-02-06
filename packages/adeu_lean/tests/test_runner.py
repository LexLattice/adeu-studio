from __future__ import annotations

from pathlib import Path

from adeu_ir import ProofInput
from adeu_lean import (
    DEFAULT_SEMANTICS_VERSION,
    OBLIGATION_KINDS,
    build_obligation_requests,
    run_lean_request,
)


def test_build_obligation_requests_is_deterministic() -> None:
    inputs = [ProofInput(object_id="dn1", json_path="/D_norm/statements/0", formula_hash="f1")]
    left = build_obligation_requests(theorem_prefix="ir_abc", inputs=inputs)
    right = build_obligation_requests(theorem_prefix="ir_abc", inputs=inputs)

    assert [request.theorem_id for request in left] == [request.theorem_id for request in right]
    assert [request.obligation_kind for request in left] == list(OBLIGATION_KINDS)
    assert left[0].semantics_version == DEFAULT_SEMANTICS_VERSION
    assert [request.theorem_src for request in left] == [request.theorem_src for request in right]
    assert all("inputs_hash" in request.metadata for request in left)
    assert all("theorem_src_hash" in request.metadata for request in left)


def test_run_lean_request_missing_binary_returns_failed() -> None:
    request = build_obligation_requests(theorem_prefix="ir_missing", inputs=[])[0]
    result = run_lean_request(
        request,
        timeout_ms=1000,
        lake_bin="/tmp/lake-not-installed",
        lean_bin="/tmp/lean-not-installed",
        project_root=Path(__file__).resolve().parents[1],
    )
    assert result.status == "failed"
    assert "binary not found" in str(result.details.get("error", "")).lower()
    assert len(result.proof_hash) == 64
