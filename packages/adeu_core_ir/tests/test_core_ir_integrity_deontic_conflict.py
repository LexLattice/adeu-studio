from __future__ import annotations

import adeu_core_ir.integrity_deontic_conflict as deontic_conflict_module
import pytest
from adeu_core_ir import (
    AdeuIntegrityDeonticConflict,
    build_integrity_deontic_conflict_diagnostics,
    canonicalize_core_ir_payload,
    canonicalize_integrity_deontic_conflict_payload,
)


def _deontic_payload() -> dict[str, object]:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-d3-conflicts",
        "nodes": [
            {
                "id": "d_exception_1",
                "layer": "D",
                "kind": "Exception",
                "label": "unless emergency override applies",
            },
            {
                "id": "d_forbidden_1",
                "layer": "D",
                "kind": "Norm",
                "label": "Agents must not enable API access by default",
                "modality": "forbidden",
                "target": " API   ACCESS ",
                "condition": "none",
                "priority": 7,
            },
            {
                "id": "d_obligatory_1",
                "layer": "D",
                "kind": "Norm",
                "label": "Agents must enable api access during setup",
                "modality": "obligatory",
                "target": "api access",
                "condition": "always",
                "priority": 2,
            },
            {
                "id": "d_permitted_1",
                "layer": "D",
                "kind": "Policy",
                "label": "Agents may enable API access",
                "modality": "permitted",
                "target": "api access",
                "condition": "always",
            },
            {
                "id": "d_forbidden_2",
                "layer": "D",
                "kind": "Norm",
                "label": "Agents must not enable API access outside audits",
                "modality": "forbidden",
                "target": "api access",
                "condition": "if audited",
            },
        ],
        "edges": [
            {"type": "excepts", "from": "d_exception_1", "to": "d_forbidden_1"},
        ],
    }
    return canonicalize_core_ir_payload(payload)


def test_deontic_conflict_diagnostics_detect_minimal_conflicts() -> None:
    diagnostics = build_integrity_deontic_conflict_diagnostics(_deontic_payload())

    assert diagnostics.schema == "adeu_integrity_deontic_conflict@0.1"
    assert diagnostics.source_text_hash == "hash-d3-conflicts"
    assert diagnostics.summary.total_conflicts == 1
    assert diagnostics.summary.deontic_conflict == 1
    assert [
        (conflict.kind, conflict.primary_id, conflict.related_id)
        for conflict in diagnostics.conflicts
    ] == [("deontic_conflict", "d_forbidden_1", "d_obligatory_1")]
    assert diagnostics.conflicts[0].details == {
        "normalized_target": "api access",
        "normalized_condition": "",
        "primary_modality": "forbidden",
        "related_modality": "obligatory",
        "primary_priority": 7,
        "related_priority": 2,
    }


def test_deontic_conflict_diagnostics_returns_empty_when_no_matching_pairs() -> None:
    payload = canonicalize_core_ir_payload(
        {
            "schema": "adeu_core_ir@0.1",
            "source_text_hash": "hash-d3-empty",
            "nodes": [
                {
                    "id": "d_forbidden_1",
                    "layer": "D",
                    "kind": "Norm",
                    "label": "forbidden statement",
                    "modality": "forbidden",
                    "target": "",
                    "condition": "always",
                },
                {
                    "id": "d_obligatory_1",
                    "layer": "D",
                    "kind": "Norm",
                    "label": "obligatory statement",
                    "modality": "obligatory",
                    "target": "api access",
                    "condition": "if audited",
                },
            ],
            "edges": [],
        }
    )
    diagnostics = build_integrity_deontic_conflict_diagnostics(payload)
    assert diagnostics.summary.total_conflicts == 0
    assert diagnostics.summary.deontic_conflict == 0
    assert diagnostics.conflicts == []


def test_deontic_conflict_model_rejects_unsorted_conflicts() -> None:
    payload = {
        "schema": "adeu_integrity_deontic_conflict@0.1",
        "source_text_hash": "hash-d3-unsorted",
        "summary": {
            "total_conflicts": 2,
            "deontic_conflict": 2,
        },
        "conflicts": [
            {
                "kind": "deontic_conflict",
                "primary_id": "d2",
                "related_id": "d3",
            },
            {
                "kind": "deontic_conflict",
                "primary_id": "d1",
                "related_id": "d2",
            },
        ],
    }
    with pytest.raises(ValueError, match="conflicts must be sorted"):
        AdeuIntegrityDeonticConflict.model_validate(payload)


def test_deontic_conflict_payload_canonicalization_is_deterministic() -> None:
    diagnostics_a = build_integrity_deontic_conflict_diagnostics(_deontic_payload())
    diagnostics_b = build_integrity_deontic_conflict_diagnostics(_deontic_payload())
    assert canonicalize_integrity_deontic_conflict_payload(
        diagnostics_a
    ) == canonicalize_integrity_deontic_conflict_payload(diagnostics_b)


def test_deontic_conflict_diagnostics_fail_closed_when_conflict_cap_is_exceeded(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    payload = canonicalize_core_ir_payload(
        {
            "schema": "adeu_core_ir@0.1",
            "source_text_hash": "hash-d3-cap",
            "nodes": [
                {
                    "id": "d_forbidden_1",
                    "layer": "D",
                    "kind": "Norm",
                    "label": "forbidden one",
                    "modality": "forbidden",
                    "target": "api access",
                    "condition": "always",
                },
                {
                    "id": "d_obligatory_1",
                    "layer": "D",
                    "kind": "Norm",
                    "label": "obligatory one",
                    "modality": "obligatory",
                    "target": "api access",
                    "condition": "none",
                },
                {
                    "id": "d_obligatory_2",
                    "layer": "D",
                    "kind": "Norm",
                    "label": "obligatory two",
                    "modality": "obligatory",
                    "target": "api access",
                    "condition": "",
                },
            ],
            "edges": [],
        }
    )
    monkeypatch.setattr(deontic_conflict_module, "_MAX_EMITTED_CONFLICTS", 1)
    with pytest.raises(ValueError, match="URM_ADEU_INTEGRITY_FIXTURE_INVALID"):
        build_integrity_deontic_conflict_diagnostics(payload)
