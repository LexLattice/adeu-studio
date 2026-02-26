from __future__ import annotations

import pytest
from adeu_core_ir import (
    AdeuCoreIRProposal,
    canonicalize_core_ir_proposal_payload,
)


def _minimal_payload() -> dict[str, object]:
    return {
        "schema": "adeu_core_ir_proposal@0.1",
        "client_request_id": "req-core-ir-proposer-1",
        "surface_id": "adeu_core_ir.propose",
        "provider": "mock",
        "core_ir_artifact_ref": "proposal:adeu_core_ir@0.1:1" + ("0" * 63),
        "lane_artifact_refs": [
            "proposal:adeu_lane_report@0.1:2" + ("0" * 63),
        ],
        "integrity_artifact_refs": [
            "proposal:adeu_integrity_cycle_policy@0.1:3" + ("0" * 63),
            "proposal:adeu_integrity_dangling_reference@0.1:4" + ("0" * 63),
        ],
        "not_produced_reasons": [],
        "summary": {
            "candidate_count": 1,
            "assertion_node_count": 5,
            "relation_edge_count": 4,
            "logic_tree_max_depth": 2,
            "lane_ref_count": 1,
            "integrity_ref_count": 2,
        },
    }


def test_core_ir_proposal_model_validate_minimal_payload() -> None:
    normalized = AdeuCoreIRProposal.model_validate(_minimal_payload())

    assert normalized.schema == "adeu_core_ir_proposal@0.1"
    assert normalized.surface_id == "adeu_core_ir.propose"
    assert normalized.provider == "mock"
    assert normalized.summary.integrity_ref_count == 2


def test_canonicalize_core_ir_proposal_payload_normalizes_valid_payload() -> None:
    canonical = canonicalize_core_ir_proposal_payload(_minimal_payload())

    assert canonical["schema"] == "adeu_core_ir_proposal@0.1"
    assert canonical["summary"]["lane_ref_count"] == 1


def test_core_ir_proposal_rejects_unsorted_integrity_refs() -> None:
    payload = _minimal_payload()
    payload["integrity_artifact_refs"] = list(reversed(payload["integrity_artifact_refs"]))  # type: ignore[index]

    with pytest.raises(ValueError, match="integrity_artifact_refs must be lexicographically sorted"):
        AdeuCoreIRProposal.model_validate(payload)


def test_core_ir_proposal_rejects_summary_ref_count_mismatch() -> None:
    payload = _minimal_payload()
    payload["summary"]["lane_ref_count"] = 2  # type: ignore[index]

    with pytest.raises(ValueError, match="summary.lane_ref_count must match lane_artifact_refs"):
        AdeuCoreIRProposal.model_validate(payload)
