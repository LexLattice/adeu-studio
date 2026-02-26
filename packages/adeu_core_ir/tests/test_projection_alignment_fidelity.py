from __future__ import annotations

import pytest
from adeu_core_ir import (
    MAX_MATCHED_NODES_PER_SOURCE,
    AdeuProjectionAlignmentFidelity,
    AdeuProjectionAlignmentFidelityInput,
    build_projection_alignment_fidelity_id,
    canonicalize_projection_alignment_fidelity_input_payload,
    canonicalize_projection_alignment_fidelity_payload,
)


def _source_text_hash() -> str:
    return "3d956a90a9f1433816149bcb70e300afdcca6d303bdc119cea8f0657222c32aa"


def _justification_refs() -> list[str]:
    source_text_hash = _source_text_hash()
    return [
        f"artifact:adeu_projection_alignment@0.1:{source_text_hash}",
        f"artifact:adeu_projection_alignment_fidelity_input@0.1:{source_text_hash}",
    ]


def _minimal_input_payload() -> dict[str, object]:
    return {
        "schema": "adeu_projection_alignment_fidelity_input@0.1",
        "source_text_hash": _source_text_hash(),
        "matched_nodes": [
            {
                "match_id": "match_a",
                "projection_label_text": "alpha",
                "extraction_label_text": "alpha",
                "projection_span": {"start": 0, "end": 5},
                "extraction_span": {"start": 0, "end": 5},
                "projection_score_milli": 900,
                "extraction_score_milli": 890,
            }
        ],
    }


def _minimal_packet_payload() -> dict[str, object]:
    justification_refs = _justification_refs()
    items = [
        {
            "fidelity_code": "label_text_mismatch",
            "status": "compatible",
            "severity": "low",
            "justification_refs": justification_refs,
            "message": "label-text continuity check",
        },
        {
            "fidelity_code": "score_mismatch",
            "status": "drift",
            "severity": "medium",
            "justification_refs": justification_refs,
            "expected_hash": "2" * 64,
            "observed_hash": "3" * 64,
            "message": "score continuity check",
        },
        {
            "fidelity_code": "span_mismatch",
            "status": "drift",
            "severity": "high",
            "justification_refs": justification_refs,
            "expected_hash": "4" * 64,
            "observed_hash": "5" * 64,
            "message": "span continuity check",
        },
    ]

    for item in items:
        item["fidelity_id"] = build_projection_alignment_fidelity_id(
            fidelity_code=item["fidelity_code"],
            status=item["status"],
            severity=item["severity"],
            justification_refs=item["justification_refs"],
            expected_hash=item.get("expected_hash"),
            observed_hash=item.get("observed_hash"),
        )

    items.sort(key=lambda item: (item["fidelity_code"], item["fidelity_id"]))

    return {
        "schema": "adeu_projection_alignment_fidelity@0.1",
        "source_text_hash": _source_text_hash(),
        "projection_alignment_hash": "6" * 64,
        "fidelity_input_hash": "7" * 64,
        "fidelity_summary": {
            "total_checks": 3,
            "compatible_checks": 1,
            "drift_checks": 2,
            "counts_by_code": {
                "label_text_mismatch": 1,
                "score_mismatch": 1,
                "span_mismatch": 1,
            },
            "counts_by_status": {
                "compatible": 1,
                "drift": 2,
            },
            "counts_by_severity": {
                "high": 1,
                "low": 1,
                "medium": 1,
            },
        },
        "fidelity_items": items,
    }


def test_projection_alignment_fidelity_input_model_validate_minimal_payload() -> None:
    normalized = AdeuProjectionAlignmentFidelityInput.model_validate(_minimal_input_payload())

    assert normalized.schema == "adeu_projection_alignment_fidelity_input@0.1"
    assert normalized.source_text_hash == _source_text_hash()
    assert len(normalized.matched_nodes) == 1
    assert normalized.matched_nodes[0].match_id == "match_a"


def test_canonicalize_projection_alignment_fidelity_input_payload_normalizes_valid_payload() -> (
    None
):
    canonical = canonicalize_projection_alignment_fidelity_input_payload(_minimal_input_payload())

    assert canonical["schema"] == "adeu_projection_alignment_fidelity_input@0.1"
    assert canonical["matched_nodes"][0]["projection_score_milli"] == 900


def test_projection_alignment_fidelity_input_rejects_duplicate_match_id() -> None:
    payload = _minimal_input_payload()
    payload["matched_nodes"] = [
        payload["matched_nodes"][0],  # type: ignore[index]
        payload["matched_nodes"][0],  # type: ignore[index]
    ]

    with pytest.raises(ValueError, match="duplicate match_id"):
        AdeuProjectionAlignmentFidelityInput.model_validate(payload)


def test_projection_alignment_fidelity_input_rejects_volume_cap_exceeded() -> None:
    node = _minimal_input_payload()["matched_nodes"][0]  # type: ignore[index]
    payload = {
        "schema": "adeu_projection_alignment_fidelity_input@0.1",
        "source_text_hash": _source_text_hash(),
        "matched_nodes": [
            {
                **node,
                "match_id": f"match_{idx:04d}",
            }
            for idx in range(MAX_MATCHED_NODES_PER_SOURCE + 1)
        ],
    }

    with pytest.raises(ValueError, match="max_matched_nodes_per_source"):
        AdeuProjectionAlignmentFidelityInput.model_validate(payload)


def test_projection_alignment_fidelity_packet_model_validate_minimal_payload() -> None:
    normalized = AdeuProjectionAlignmentFidelity.model_validate(_minimal_packet_payload())

    assert normalized.schema == "adeu_projection_alignment_fidelity@0.1"
    assert normalized.fidelity_summary.total_checks == 3
    assert [item.fidelity_code for item in normalized.fidelity_items] == [
        "label_text_mismatch",
        "score_mismatch",
        "span_mismatch",
    ]


def test_canonicalize_projection_alignment_fidelity_payload_normalizes_valid_payload() -> None:
    canonical = canonicalize_projection_alignment_fidelity_payload(_minimal_packet_payload())

    assert canonical["schema"] == "adeu_projection_alignment_fidelity@0.1"
    assert canonical["fidelity_summary"]["counts_by_status"] == {
        "compatible": 1,
        "drift": 2,
    }


def test_projection_alignment_fidelity_packet_rejects_hash_fields_for_compatible_item() -> None:
    payload = _minimal_packet_payload()
    payload["fidelity_items"][0]["expected_hash"] = "0" * 64  # type: ignore[index]

    with pytest.raises(ValueError, match="compatible fidelity items must omit"):
        AdeuProjectionAlignmentFidelity.model_validate(payload)
