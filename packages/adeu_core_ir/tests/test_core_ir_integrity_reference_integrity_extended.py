from __future__ import annotations

import adeu_core_ir.integrity_reference_integrity_extended as ref_integrity_module
import pytest
from adeu_core_ir import (
    AdeuIntegrityReferenceIntegrityExtended,
    build_integrity_reference_integrity_extended_diagnostics,
    canonicalize_core_ir_payload,
    canonicalize_integrity_reference_integrity_extended_payload,
)


def _valid_core_ir_payload() -> dict[str, object]:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-e1-valid",
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


def test_reference_integrity_extended_diagnostics_empty_for_valid_core_ir() -> None:
    diagnostics = build_integrity_reference_integrity_extended_diagnostics(_valid_core_ir_payload())
    assert diagnostics.schema == "adeu_integrity_reference_integrity_extended@0.1"
    assert diagnostics.source_text_hash == "hash-e1-valid"
    assert diagnostics.summary.total_issues == 0
    assert diagnostics.summary.edge_type_constraint_violation == 0
    assert diagnostics.summary.duplicate_edge_identity == 0
    assert diagnostics.issues == []


def test_reference_integrity_extended_diagnostics_detect_edge_type_violations() -> None:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-e1-type-violations",
        "nodes": [
            {"id": "e1", "layer": "E", "kind": "Claim"},
            {"id": "o1", "layer": "O", "kind": "Concept"},
        ],
        "edges": [
            {"type": "about", "from": "o1", "to": "e1"},
            {"type": "depends_on", "from": "e1", "to": "o1"},
            {"type": "about", "from": "e1", "to": "o_missing"},
            {"type": "about", "from": "e_missing", "to": "o1"},
        ],
    }

    diagnostics = build_integrity_reference_integrity_extended_diagnostics(payload)

    assert diagnostics.summary.total_issues == 2
    assert diagnostics.summary.edge_type_constraint_violation == 2
    assert diagnostics.summary.duplicate_edge_identity == 0
    assert [
        (issue.kind, issue.subject_id, issue.related_id) for issue in diagnostics.issues
    ] == [
        ("edge_type_constraint_violation", "edge:about:o1->e1", "type_constraint"),
        ("edge_type_constraint_violation", "edge:depends_on:e1->o1", "type_constraint"),
    ]


def test_reference_integrity_extended_diagnostics_emit_one_duplicate_issue_per_key() -> None:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-e1-duplicates",
        "nodes": [
            {"id": "e1", "layer": "E", "kind": "Claim"},
            {"id": "o1", "layer": "O", "kind": "Concept"},
            {"id": "o2", "layer": "O", "kind": "Concept"},
        ],
        "edges": [
            {"type": "about", "from": "e1", "to": "o1"},
            {"type": "about", "from": "e1", "to": "o1"},
            {"type": "about", "from": "e1", "to": "o1"},
            {"type": "about", "from": "e1", "to": "o2"},
            {"type": "about", "from": "e1", "to": "o2"},
        ],
    }

    diagnostics = build_integrity_reference_integrity_extended_diagnostics(payload)

    assert diagnostics.summary.total_issues == 2
    assert diagnostics.summary.edge_type_constraint_violation == 0
    assert diagnostics.summary.duplicate_edge_identity == 2
    assert [
        (issue.kind, issue.subject_id, issue.related_id, issue.details)
        for issue in diagnostics.issues
    ] == [
        (
            "duplicate_edge_identity",
            "edge:about:e1->o1",
            "duplicate_edge_identity",
            {"duplicate_count": 3},
        ),
        (
            "duplicate_edge_identity",
            "edge:about:e1->o2",
            "duplicate_edge_identity",
            {"duplicate_count": 2},
        ),
    ]


def test_reference_integrity_extended_model_rejects_unsorted_issues() -> None:
    payload = {
        "schema": "adeu_integrity_reference_integrity_extended@0.1",
        "source_text_hash": "hash-e1-unsorted",
        "summary": {
            "total_issues": 2,
            "edge_type_constraint_violation": 2,
            "duplicate_edge_identity": 0,
        },
        "issues": [
            {
                "kind": "edge_type_constraint_violation",
                "subject_id": "edge:depends_on:z->a",
                "related_id": "type_constraint",
            },
            {
                "kind": "edge_type_constraint_violation",
                "subject_id": "edge:about:a->z",
                "related_id": "type_constraint",
            },
        ],
    }
    with pytest.raises(ValueError, match="issues must be sorted"):
        AdeuIntegrityReferenceIntegrityExtended.model_validate(payload)


def test_reference_integrity_extended_diagnostics_fail_closed_on_issue_cap(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-e1-cap",
        "nodes": [
            {"id": "e1", "layer": "E", "kind": "Claim"},
            {"id": "o1", "layer": "O", "kind": "Concept"},
            {"id": "o2", "layer": "O", "kind": "Concept"},
        ],
        "edges": [
            {"type": "about", "from": "e1", "to": "o1"},
            {"type": "about", "from": "e1", "to": "o1"},
            {"type": "depends_on", "from": "e1", "to": "o1"},
            {"type": "depends_on", "from": "e1", "to": "o2"},
        ],
    }
    monkeypatch.setattr(ref_integrity_module, "_MAX_EMITTED_ISSUES", 1)
    with pytest.raises(ValueError, match="URM_ADEU_INTEGRITY_FIXTURE_INVALID"):
        build_integrity_reference_integrity_extended_diagnostics(payload)


def test_reference_integrity_extended_payload_canonicalization_is_deterministic() -> None:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-e1-deterministic",
        "nodes": [
            {"id": "e1", "layer": "E", "kind": "Claim"},
            {"id": "o1", "layer": "O", "kind": "Concept"},
        ],
        "edges": [
            {"type": "depends_on", "from": "e1", "to": "o1"},
            {"type": "depends_on", "from": "e1", "to": "o1"},
        ],
    }
    diagnostics_a = build_integrity_reference_integrity_extended_diagnostics(payload)
    diagnostics_b = build_integrity_reference_integrity_extended_diagnostics(payload)
    assert canonicalize_integrity_reference_integrity_extended_payload(
        diagnostics_a
    ) == canonicalize_integrity_reference_integrity_extended_payload(diagnostics_b)


def test_reference_integrity_extended_requires_source_text_hash() -> None:
    with pytest.raises(ValueError, match="source_text_hash must be a non-empty string"):
        build_integrity_reference_integrity_extended_diagnostics(
            {
                "schema": "adeu_core_ir@0.1",
                "nodes": [],
                "edges": [],
            }
        )
