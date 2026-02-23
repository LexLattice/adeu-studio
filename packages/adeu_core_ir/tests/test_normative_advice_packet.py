from __future__ import annotations

import hashlib
import json

import pytest
from adeu_core_ir import (
    AdeuNormativeAdvicePacket,
    canonicalize_normative_advice_packet_payload,
)


def _advice_id(
    *,
    advice_code: str,
    concept_refs: list[str],
    core_ir_refs: list[str],
    justification_refs: list[str],
) -> str:
    payload = {
        "advice_code": advice_code,
        "concept_refs": concept_refs,
        "core_ir_refs": core_ir_refs,
        "justification_refs": justification_refs,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()[:16]


def _minimal_payload() -> dict[str, object]:
    concept_refs = ["amb1"]
    core_ir_refs: list[str] = []
    justification_refs = ["coherence_issue:af1ba710c9f6e5c8"]
    return {
        "schema": "adeu_normative_advice_packet@0.1",
        "source_text_hash": "3d956a90a9f1433816149bcb70e300afdcca6d303bdc119cea8f0657222c32aa",
        "core_ir_artifact_id": "core_ir.case_a_1",
        "concept_artifact_id": "concept.case_a_1",
        "bridge_manifest_hash": "3f0de140e2078c6f5492a3e6f9b06d0077d166da20c4c00da61152e85c51bb53",
        "advice_summary": {
            "total_advice": 1,
            "counts_by_code": {"MAPPING_GAP_REVIEW": 1},
            "counts_by_priority": {"medium": 1},
        },
        "advice_items": [
            {
                "advice_id": _advice_id(
                    advice_code="MAPPING_GAP_REVIEW",
                    concept_refs=concept_refs,
                    core_ir_refs=core_ir_refs,
                    justification_refs=justification_refs,
                ),
                "advice_code": "MAPPING_GAP_REVIEW",
                "priority": "medium",
                "concept_refs": concept_refs,
                "core_ir_refs": core_ir_refs,
                "justification_refs": justification_refs,
                "message": (
                    "review unmapped concept/core-ir coverage and reconcile missing mappings"
                ),
            }
        ],
    }


def test_normative_advice_packet_model_validate_minimal_payload() -> None:
    normalized = AdeuNormativeAdvicePacket.model_validate(_minimal_payload())

    assert normalized.schema == "adeu_normative_advice_packet@0.1"
    assert normalized.advice_summary.total_advice == 1
    assert normalized.advice_items[0].advice_code == "MAPPING_GAP_REVIEW"
    assert normalized.advice_items[0].justification_refs == [
        "coherence_issue:af1ba710c9f6e5c8"
    ]


def test_canonicalize_normative_advice_packet_payload_normalizes_valid_payload() -> None:
    canonical = canonicalize_normative_advice_packet_payload(_minimal_payload())
    assert canonical["schema"] == "adeu_normative_advice_packet@0.1"
    assert canonical["advice_summary"]["counts_by_code"] == {"MAPPING_GAP_REVIEW": 1}
    assert canonical["advice_summary"]["counts_by_priority"] == {"medium": 1}


def test_normative_advice_packet_rejects_invalid_justification_ref() -> None:
    payload = _minimal_payload()
    payload["advice_items"][0]["justification_refs"] = ["issue:af1ba710c9f6e5c8"]  # type: ignore[index]
    with pytest.raises(ValueError):
        AdeuNormativeAdvicePacket.model_validate(payload)


def test_normative_advice_packet_rejects_priority_mismatch() -> None:
    payload = _minimal_payload()
    payload["advice_items"][0]["priority"] = "high"  # type: ignore[index]
    with pytest.raises(ValueError):
        AdeuNormativeAdvicePacket.model_validate(payload)
