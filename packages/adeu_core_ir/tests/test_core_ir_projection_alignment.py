from __future__ import annotations

import pytest
from adeu_core_ir import (
    AdeuProjectionAlignment,
    build_projection_alignment,
    canonicalize_core_ir_payload,
    canonicalize_projection_alignment_payload,
)


def _projection_payload() -> dict[str, object]:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-align-a",
        "nodes": [
            {"id": "o_concept_1", "layer": "O", "kind": "Concept", "label": "delegation"},
            {
                "id": "e_claim_1",
                "layer": "E",
                "kind": "Claim",
                "text": "AI agents can delegate tasks",
                "spans": [{"start": 0, "end": 10}],
            },
            {"id": "d_policy_1", "layer": "D", "kind": "Policy", "label": "verify-before-act"},
            {"id": "u_goal_1", "layer": "U", "kind": "Goal", "label": "maintain trust"},
        ],
        "edges": [
            {"type": "about", "from": "e_claim_1", "to": "o_concept_1"},
        ],
    }
    return canonicalize_core_ir_payload(payload)


def _extraction_payload() -> dict[str, object]:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-align-a",
        "nodes": [
            {"id": "o_concept_x", "layer": "O", "kind": "Concept", "label": "delegation"},
            {
                "id": "e_claim_x",
                "layer": "E",
                "kind": "Claim",
                "text": "AI agents can delegate tasks",
                "spans": [{"start": 0, "end": 10}],
            },
            {"id": "d_norm_x", "layer": "D", "kind": "Norm", "label": "verify-before-act"},
            {"id": "u_metric_x", "layer": "U", "kind": "Metric", "label": "latency reduction"},
        ],
        "edges": [
            {"type": "defines", "from": "e_claim_x", "to": "o_concept_x"},
        ],
    }
    return canonicalize_core_ir_payload(payload)


def test_build_projection_alignment_detects_expected_issue_kinds() -> None:
    alignment = build_projection_alignment(
        projection=_projection_payload(),
        extraction=_extraction_payload(),
    )
    assert alignment.schema == "adeu_projection_alignment@0.1"
    assert alignment.source_text_hash == "hash-align-a"
    assert alignment.summary.total_issues == 4
    assert alignment.summary.missing_in_projection == 1
    assert alignment.summary.missing_in_extraction == 1
    assert alignment.summary.kind_mismatch == 1
    assert alignment.summary.edge_type_mismatch == 1

    kinds = [issue.kind for issue in alignment.issues]
    assert kinds == sorted(kinds)
    assert set(kinds) == {
        "missing_in_projection",
        "missing_in_extraction",
        "kind_mismatch",
        "edge_type_mismatch",
    }


def test_build_projection_alignment_requires_matching_source_text_hash() -> None:
    extraction = _extraction_payload()
    extraction["source_text_hash"] = "hash-align-b"
    with pytest.raises(ValueError, match="source_text_hash must match"):
        build_projection_alignment(
            projection=_projection_payload(),
            extraction=extraction,
        )


def test_projection_alignment_rejects_unsorted_issues() -> None:
    payload = {
        "schema": "adeu_projection_alignment@0.1",
        "source_text_hash": "hash-align-a",
        "summary": {
            "total_issues": 2,
            "missing_in_projection": 1,
            "missing_in_extraction": 1,
            "kind_mismatch": 0,
            "edge_type_mismatch": 0,
        },
        "issues": [
            {
                "kind": "missing_in_projection",
                "subject_id": "z",
                "related_id": "",
            },
            {
                "kind": "missing_in_extraction",
                "subject_id": "a",
                "related_id": "",
            },
        ],
    }
    with pytest.raises(ValueError, match="issues must be sorted"):
        AdeuProjectionAlignment.model_validate(payload)


def test_projection_alignment_related_id_defaults_to_empty_string() -> None:
    payload = {
        "schema": "adeu_projection_alignment@0.1",
        "source_text_hash": "hash-align-a",
        "summary": {
            "total_issues": 1,
            "missing_in_projection": 1,
            "missing_in_extraction": 0,
            "kind_mismatch": 0,
            "edge_type_mismatch": 0,
        },
        "issues": [
            {
                "kind": "missing_in_projection",
                "subject_id": "a",
            }
        ],
    }
    model = AdeuProjectionAlignment.model_validate(payload)
    assert model.issues[0].related_id == ""


def test_projection_alignment_payload_canonicalization_is_deterministic() -> None:
    alignment_a = build_projection_alignment(
        projection=_projection_payload(),
        extraction=_extraction_payload(),
    )
    alignment_b = build_projection_alignment(
        projection=_projection_payload(),
        extraction=_extraction_payload(),
    )
    assert canonicalize_projection_alignment_payload(
        alignment_a
    ) == canonicalize_projection_alignment_payload(alignment_b)


def test_projection_alignment_reports_subset_edge_type_deltas_as_missing() -> None:
    projection = _projection_payload()
    projection["edges"] = [
        {"type": "about", "from": "e_claim_1", "to": "o_concept_1"},
        {"type": "defines", "from": "e_claim_1", "to": "o_concept_1"},
    ]

    extraction = _projection_payload()
    extraction["edges"] = [
        {"type": "about", "from": "e_claim_1", "to": "o_concept_1"},
    ]

    alignment = build_projection_alignment(
        projection=projection,
        extraction=extraction,
    )

    assert alignment.summary.edge_type_mismatch == 0
    assert alignment.summary.missing_in_extraction == 1
    assert alignment.summary.missing_in_projection == 0
    assert [
        issue.kind for issue in alignment.issues
    ] == [
        "missing_in_extraction",
    ]
    assert alignment.issues[0].subject_id.endswith(
        "edge:defines:node:E:ai agents can delegate tasks->node:O:delegation"
    )
