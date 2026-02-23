from __future__ import annotations

import pytest
from adeu_core_ir import (
    AdeuSemanticsV4CandidatePacket,
    build_semantics_v4_candidate_comparison_id,
    canonicalize_semantics_v4_candidate_packet_payload,
)


def _minimal_payload() -> dict[str, object]:
    source_text_hash = "3d956a90a9f1433816149bcb70e300afdcca6d303bdc119cea8f0657222c32aa"
    core_ir_artifact_id = "core_ir.case_a_1"
    concept_artifact_id = "concept.case_a_1"
    trust_ref = (
        "artifact:adeu_trust_invariant_packet@0.1:"
        f"{source_text_hash}:{core_ir_artifact_id}:{concept_artifact_id}"
    )
    v3_ref = (
        "artifact:semantics_diagnostics@1:v3:"
        f"{source_text_hash}:{core_ir_artifact_id}:{concept_artifact_id}"
    )
    v4_ref = (
        "artifact:semantics_diagnostics@1:v4_candidate:"
        f"{source_text_hash}:{core_ir_artifact_id}:{concept_artifact_id}"
    )
    trust_invariant_packet_hash = (
        "3f0de140e2078c6f5492a3e6f9b06d0077d166da20c4c00da61152e85c51bb53"
    )
    baseline_semantics_hash = (
        "36c9e43763e7d92a353bbf0127e24d5fa67ac0eba6b9db3ce2a595b452d214d2"
    )
    candidate_semantics_hash = (
        "e6cc53eb491ea141b5c965a83358ed64f8693af9af33b2bfcd5f53b164f14cf6"
    )

    items = [
        {
            "comparison_code": "ASSURANCE_SET_CONTINUITY_REVIEW",
            "status": "compatible",
            "severity": "low",
            "justification_refs": [v3_ref, v4_ref],
            "message": "assurance sets are compatible",
        },
        {
            "comparison_code": "REQUEST_FORMULA_HASH_CONTINUITY_REVIEW",
            "status": "compatible",
            "severity": "low",
            "justification_refs": [v3_ref, v4_ref],
            "message": "request/formula hash tuples are compatible",
        },
        {
            "comparison_code": "STATUS_SET_CONTINUITY_REVIEW",
            "status": "compatible",
            "severity": "low",
            "justification_refs": [v3_ref, v4_ref],
            "message": "status sets are compatible",
        },
        {
            "comparison_code": "WITNESS_REF_STRUCTURE_REVIEW",
            "status": "compatible",
            "severity": "low",
            "justification_refs": [trust_ref, v3_ref, v4_ref],
            "message": "witness-ref structure is compatible",
        },
    ]

    for item in items:
        item["comparison_id"] = build_semantics_v4_candidate_comparison_id(
            comparison_code=item["comparison_code"],
            status=item["status"],
            severity=item["severity"],
            justification_refs=item["justification_refs"],
            expected_hash=None,
            observed_hash=None,
        )

    items.sort(key=lambda item: (item["comparison_code"], item["comparison_id"]))

    return {
        "schema": "adeu_semantics_v4_candidate_packet@0.1",
        "source_text_hash": source_text_hash,
        "core_ir_artifact_id": core_ir_artifact_id,
        "concept_artifact_id": concept_artifact_id,
        "trust_invariant_packet_hash": trust_invariant_packet_hash,
        "baseline_semantics_hash": baseline_semantics_hash,
        "candidate_semantics_hash": candidate_semantics_hash,
        "comparison_summary": {
            "total_comparisons": 4,
            "compatible_checks": 4,
            "drift_checks": 0,
            "counts_by_code": {
                "ASSURANCE_SET_CONTINUITY_REVIEW": 1,
                "REQUEST_FORMULA_HASH_CONTINUITY_REVIEW": 1,
                "STATUS_SET_CONTINUITY_REVIEW": 1,
                "WITNESS_REF_STRUCTURE_REVIEW": 1,
            },
            "counts_by_severity": {"low": 4},
            "counts_by_status": {"compatible": 4},
        },
        "comparison_items": items,
    }


def test_semantics_v4_candidate_packet_model_validate_minimal_payload() -> None:
    normalized = AdeuSemanticsV4CandidatePacket.model_validate(_minimal_payload())

    assert normalized.schema == "adeu_semantics_v4_candidate_packet@0.1"
    assert normalized.comparison_summary.total_comparisons == 4
    assert [item.comparison_code for item in normalized.comparison_items] == [
        "ASSURANCE_SET_CONTINUITY_REVIEW",
        "REQUEST_FORMULA_HASH_CONTINUITY_REVIEW",
        "STATUS_SET_CONTINUITY_REVIEW",
        "WITNESS_REF_STRUCTURE_REVIEW",
    ]


def test_canonicalize_semantics_v4_candidate_packet_payload_normalizes_valid_payload() -> None:
    canonical = canonicalize_semantics_v4_candidate_packet_payload(_minimal_payload())

    assert canonical["schema"] == "adeu_semantics_v4_candidate_packet@0.1"
    assert canonical["comparison_summary"]["counts_by_status"] == {"compatible": 4}


def test_semantics_v4_candidate_packet_rejects_hash_fields_for_compatible_item() -> None:
    payload = _minimal_payload()
    item = payload["comparison_items"][0]  # type: ignore[index]
    item["expected_hash"] = "0" * 64  # type: ignore[index]

    with pytest.raises(ValueError):
        AdeuSemanticsV4CandidatePacket.model_validate(payload)
