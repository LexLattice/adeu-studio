from __future__ import annotations

import json
from pathlib import Path

from adeu_api.adeu_concept_bridge import BRIDGE_MAPPING_VERSION, compute_mapping_hash
from adeu_api.main import AdeuAnalyzeConceptsRequest, analyze_adeu_as_concepts
from adeu_ir import AdeuIR
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode


def _fixture_ir(*, fixture: str, name: str) -> AdeuIR:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "fixtures" / fixture / "proposals" / name
    return AdeuIR.model_validate(json.loads(path.read_text(encoding="utf-8")))


def test_adeu_analyze_concepts_endpoint_returns_bridge_and_solver_lanes() -> None:
    ir = _fixture_ir(fixture="exception_priority_resolves_conflict", name="var2.json")

    resp = analyze_adeu_as_concepts(
        AdeuAnalyzeConceptsRequest(
            ir=ir,
            mode=KernelMode.LAX,
            include_validator_runs=True,
        )
    )

    assert resp.concept_ir.schema_version == "adeu.concepts.v0"
    assert resp.bridge_mapping_version == BRIDGE_MAPPING_VERSION
    assert resp.mapping_hash == compute_mapping_hash()
    assert len(resp.mapping_hash) == 64
    assert resp.mapping_trust == "derived_bridge"
    assert resp.solver_trust == "solver_backed"
    assert resp.proof_trust is None
    assert resp.bridge_manifest.entries
    assert resp.validator_runs is not None
    assert len(resp.validator_runs) == 1
