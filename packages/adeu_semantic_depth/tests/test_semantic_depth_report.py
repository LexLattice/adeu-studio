from __future__ import annotations

from adeu_concepts import ConceptIR
from adeu_semantic_depth import (
    SEMANTIC_DEPTH_CONFIDENCE_INVALID_CODE,
    SEMANTIC_DEPTH_INVALID_REF_CODE,
    SEMANTIC_DEPTH_SCHEMA,
    SemanticDepthError,
    build_semantic_depth_report,
    build_semantic_depth_report_from_concept_pair,
    semantic_depth_hash,
    validate_semantic_depth_report,
)


def _left_ir() -> ConceptIR:
    return ConceptIR.model_validate(
        {
            "schema_version": "adeu.concepts.v0",
            "concept_id": "concept_left",
            "context": {"doc_id": "doc:left"},
            "terms": [{"id": "term_pay", "label": "Payment"}],
            "senses": [{"id": "sense_pay", "term_id": "term_pay", "gloss": "pay within 5 days"}],
            "claims": [{"id": "claim_a", "sense_id": "sense_pay", "text": "must pay in 5 days"}],
            "links": [
                {
                    "id": "link_a",
                    "kind": "incompatibility",
                    "src_sense_id": "sense_pay",
                    "dst_sense_id": "sense_pay",
                }
            ],
        }
    )


def _right_ir() -> ConceptIR:
    return ConceptIR.model_validate(
        {
            "schema_version": "adeu.concepts.v0",
            "concept_id": "concept_right",
            "context": {"doc_id": "doc:right"},
            "terms": [{"id": "term_pay", "label": "Payment"}],
            "senses": [{"id": "sense_pay", "term_id": "term_pay", "gloss": "pay within 10 days"}],
            "claims": [{"id": "claim_b", "sense_id": "sense_pay", "text": "must pay in 10 days"}],
            "links": [
                {
                    "id": "link_b",
                    "kind": "commitment",
                    "src_sense_id": "sense_pay",
                    "dst_sense_id": "sense_pay",
                }
            ],
        }
    )


def test_build_semantic_depth_report_from_concept_pair_is_deterministic() -> None:
    packet = build_semantic_depth_report_from_concept_pair(
        left_ir=_left_ir(),
        right_ir=_right_ir(),
        input_artifact_refs=["artifact:z", "artifact:a"],
    )

    assert packet["schema"] == SEMANTIC_DEPTH_SCHEMA
    assert packet["input_artifact_refs"] == ["artifact:a", "artifact:z"]
    assert len(packet["conflict_items"]) >= 1
    assert packet["conflict_items"] == sorted(
        packet["conflict_items"],
        key=lambda item: str(item["conflict_id"]),
    )
    validate_semantic_depth_report(packet)


def test_semantic_depth_hash_excludes_nonsemantic_fields() -> None:
    common = {
        "input_artifact_refs": ["artifact:a", "artifact:b"],
        "conflict_items": [
            {
                "conflict_key": {
                    "kind": "status_flip",
                    "subject_ref": {"ref_type": "doc", "doc_ref": "doc:a"},
                    "object_ref": {"ref_type": "doc", "doc_ref": "doc:b"},
                }
            }
        ],
    }
    first = build_semantic_depth_report(
        **common,
        nonsemantic_fields={"client_request_id": "req-a"},
    )
    second = build_semantic_depth_report(
        **common,
        nonsemantic_fields={"client_request_id": "req-b"},
    )

    assert first["semantic_depth_hash"] == second["semantic_depth_hash"]


def test_validate_semantic_depth_report_rejects_invalid_ref() -> None:
    packet = build_semantic_depth_report(
        input_artifact_refs=["artifact:a", "artifact:b"],
        conflict_items=[],
    )
    packet["input_artifact_refs"] = ["bad:ref", "artifact:b"]

    try:
        validate_semantic_depth_report(packet)
        assert False, "expected invalid ref failure"
    except SemanticDepthError as exc:
        assert exc.code == SEMANTIC_DEPTH_INVALID_REF_CODE


def test_build_semantic_depth_report_rejects_priority_override() -> None:
    try:
        build_semantic_depth_report(
            input_artifact_refs=["artifact:a", "artifact:b"],
            conflict_items=[
                {
                    "conflict_key": {
                        "kind": "status_flip",
                        "subject_ref": {"ref_type": "doc", "doc_ref": "doc:a"},
                        "object_ref": {"ref_type": "doc", "doc_ref": "doc:b"},
                    },
                    "provenance": {
                        "priority": 1,
                        "confidence_milli": 900,
                        "evidence_kind": "status_flip",
                        "source_ref_ids": ["artifact:a", "artifact:b"],
                    },
                }
            ],
        )
        assert False, "expected priority mapping failure"
    except SemanticDepthError as exc:
        assert "frozen kind->priority mapping" in str(exc)


def test_validate_semantic_depth_report_rejects_rank_override() -> None:
    conflict_items = [
        {
            "conflict_key": {
                "kind": "status_flip",
                "subject_ref": {"ref_type": "doc", "doc_ref": "doc:a"},
                "object_ref": {"ref_type": "doc", "doc_ref": "doc:b"},
            },
            "provenance": {
                "evidence_kind": "status_flip",
                "source_ref_ids": ["artifact:a", "artifact:b"],
            },
        },
        {
            "conflict_key": {
                "kind": "claim_text_conflict",
                "subject_ref": {"ref_type": "doc", "doc_ref": "doc:a"},
                "object_ref": {"ref_type": "doc", "doc_ref": "doc:b"},
            },
            "provenance": {
                "evidence_kind": "claim_text_conflict",
                "source_ref_ids": ["artifact:a", "artifact:b"],
            },
        },
    ]
    packet = build_semantic_depth_report(
        input_artifact_refs=["artifact:a", "artifact:b"],
        conflict_items=conflict_items,
    )
    packet["ranked_conflict_ids"] = list(reversed(packet["ranked_conflict_ids"]))
    packet["semantic_depth_hash"] = semantic_depth_hash(packet)

    try:
        validate_semantic_depth_report(packet)
        assert False, "expected ranked_conflict_ids ordering failure"
    except SemanticDepthError as exc:
        assert "deterministic objective/tie-break ordering" in str(exc)


def test_build_semantic_depth_report_rejects_non_frozen_ranking_version() -> None:
    try:
        build_semantic_depth_report(
            input_artifact_refs=["artifact:a", "artifact:b"],
            conflict_items=[],
            ranking_objective_version="semantic_depth.rank.v2",
        )
        assert False, "expected frozen ranking_objective_version validation failure"
    except SemanticDepthError as exc:
        assert "ranking_objective_version must be semantic_depth.rank.v1" in str(exc)


def test_validate_semantic_depth_report_rejects_non_frozen_tie_break_version() -> None:
    packet = build_semantic_depth_report(
        input_artifact_refs=["artifact:a", "artifact:b"],
        conflict_items=[],
    )
    packet["ranking_tie_break_version"] = "semantic_depth.tie_break.v2"
    packet["semantic_depth_hash"] = semantic_depth_hash(packet)

    try:
        validate_semantic_depth_report(packet)
        assert False, "expected frozen ranking_tie_break_version validation failure"
    except SemanticDepthError as exc:
        assert "ranking_tie_break_version must be semantic_depth.tie_break.v1" in str(exc)


def test_build_semantic_depth_report_accepts_rational_confidence_conversion() -> None:
    packet = build_semantic_depth_report(
        input_artifact_refs=["artifact:a", "artifact:b"],
        conflict_items=[
            {
                "conflict_key": {
                    "kind": "status_flip",
                    "subject_ref": {"ref_type": "doc", "doc_ref": "doc:a"},
                    "object_ref": {"ref_type": "doc", "doc_ref": "doc:b"},
                },
                "provenance": {
                    "evidence_kind": "status_flip",
                    "source_ref_ids": ["artifact:a", "artifact:b"],
                    "confidence_ratio_num": 1,
                    "confidence_ratio_denom": 2,
                },
            }
        ],
    )
    assert packet["conflict_items"][0]["provenance"]["confidence_milli"] == 500
    assert "confidence_ratio_num" not in packet["conflict_items"][0]["provenance"]
    assert "confidence_ratio_denom" not in packet["conflict_items"][0]["provenance"]


def test_build_semantic_depth_report_rejects_invalid_rational_confidence() -> None:
    try:
        build_semantic_depth_report(
            input_artifact_refs=["artifact:a", "artifact:b"],
            conflict_items=[
                {
                    "conflict_key": {
                        "kind": "status_flip",
                        "subject_ref": {"ref_type": "doc", "doc_ref": "doc:a"},
                        "object_ref": {"ref_type": "doc", "doc_ref": "doc:b"},
                    },
                    "provenance": {
                        "evidence_kind": "status_flip",
                        "source_ref_ids": ["artifact:a", "artifact:b"],
                        "confidence_ratio_num": 1,
                        "confidence_ratio_denom": 0,
                    },
                }
            ],
        )
        assert False, "expected confidence ratio denominator failure"
    except SemanticDepthError as exc:
        assert exc.code == SEMANTIC_DEPTH_CONFIDENCE_INVALID_CODE
