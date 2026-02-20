from __future__ import annotations

import pytest
from adeu_core_ir import (
    AdeuIntegrityDanglingReference,
    build_integrity_dangling_reference_diagnostics,
    canonicalize_core_ir_payload,
    canonicalize_integrity_dangling_reference_payload,
)


def _valid_core_ir_payload() -> dict[str, object]:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-d1-valid",
        "nodes": [
            {"id": "o_concept_1", "layer": "O", "kind": "Concept", "label": "delegation"},
            {
                "id": "e_claim_1",
                "layer": "E",
                "kind": "Claim",
                "text": "AI agents can delegate tasks",
                "spans": [{"start": 0, "end": 10}],
            },
        ],
        "edges": [
            {"type": "about", "from": "e_claim_1", "to": "o_concept_1"},
        ],
    }
    return canonicalize_core_ir_payload(payload)


def test_dangling_reference_diagnostics_empty_for_valid_core_ir() -> None:
    diagnostics = build_integrity_dangling_reference_diagnostics(_valid_core_ir_payload())
    assert diagnostics.schema == "adeu_integrity_dangling_reference@0.1"
    assert diagnostics.source_text_hash == "hash-d1-valid"
    assert diagnostics.summary.total_issues == 0
    assert diagnostics.summary.missing_node_reference == 0
    assert diagnostics.summary.missing_edge_endpoint == 0
    assert diagnostics.issues == []


def test_dangling_reference_diagnostics_detect_missing_node_references() -> None:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-d1-missing-nodes",
        "nodes": [
            {"id": "e_claim_1"},
            {"id": "o_concept_1"},
        ],
        "edges": [
            {"type": "about", "from": "e_claim_1", "to": "o_missing"},
            {"type": "about", "from": "e_missing", "to": "o_concept_1"},
            {"type": "about", "from": "e_missing", "to": "o_missing"},
        ],
    }

    diagnostics = build_integrity_dangling_reference_diagnostics(payload)

    assert diagnostics.summary.total_issues == 4
    assert diagnostics.summary.missing_node_reference == 4
    assert diagnostics.summary.missing_edge_endpoint == 0
    assert [
        (issue.kind, issue.subject_id, issue.related_id) for issue in diagnostics.issues
    ] == [
        ("missing_node_reference", "edge:about:e_claim_1->o_missing", "o_missing"),
        ("missing_node_reference", "edge:about:e_missing->o_concept_1", "e_missing"),
        ("missing_node_reference", "edge:about:e_missing->o_missing", "e_missing"),
        ("missing_node_reference", "edge:about:e_missing->o_missing", "o_missing"),
    ]


def test_dangling_reference_diagnostics_detect_missing_endpoints_with_placeholders() -> None:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-d1-missing-endpoints",
        "nodes": [
            {"id": "e1"},
            {"id": "o1"},
        ],
        "edges": [
            {"type": None, "from": None, "to": "o1"},
            {"type": None, "from": "e1", "to": None},
        ],
    }

    diagnostics = build_integrity_dangling_reference_diagnostics(payload)

    assert diagnostics.summary.total_issues == 2
    assert diagnostics.summary.missing_node_reference == 0
    assert diagnostics.summary.missing_edge_endpoint == 2
    assert [
        (issue.kind, issue.subject_id, issue.related_id) for issue in diagnostics.issues
    ] == [
        (
            "missing_edge_endpoint",
            "edge:_MISSING_:_MISSING_->o1",
            "endpoint:from",
        ),
        (
            "missing_edge_endpoint",
            "edge:_MISSING_:e1->_MISSING_",
            "endpoint:to",
        ),
    ]


def test_dangling_reference_model_rejects_unsorted_issues() -> None:
    payload = {
        "schema": "adeu_integrity_dangling_reference@0.1",
        "source_text_hash": "hash-d1-a",
        "summary": {
            "total_issues": 2,
            "missing_node_reference": 2,
            "missing_edge_endpoint": 0,
        },
        "issues": [
            {
                "kind": "missing_node_reference",
                "subject_id": "edge:about:z->a",
                "related_id": "z",
            },
            {
                "kind": "missing_node_reference",
                "subject_id": "edge:about:a->z",
                "related_id": "a",
            },
        ],
    }
    with pytest.raises(ValueError, match="issues must be sorted"):
        AdeuIntegrityDanglingReference.model_validate(payload)


def test_dangling_reference_payload_canonicalization_is_deterministic() -> None:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-d1-deterministic",
        "nodes": [{"id": "e1"}],
        "edges": [{"type": "about", "from": "e1", "to": "o_missing"}],
    }
    diagnostics_a = build_integrity_dangling_reference_diagnostics(payload)
    diagnostics_b = build_integrity_dangling_reference_diagnostics(payload)
    assert canonicalize_integrity_dangling_reference_payload(
        diagnostics_a
    ) == canonicalize_integrity_dangling_reference_payload(diagnostics_b)


def test_dangling_reference_requires_source_text_hash() -> None:
    with pytest.raises(ValueError, match="source_text_hash must be a non-empty string"):
        build_integrity_dangling_reference_diagnostics(
            {
                "schema": "adeu_core_ir@0.1",
                "nodes": [],
                "edges": [],
            }
        )
