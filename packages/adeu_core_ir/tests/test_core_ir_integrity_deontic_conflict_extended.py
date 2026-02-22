from __future__ import annotations

import adeu_core_ir.integrity_deontic_conflict_extended as deontic_conflict_extended_module
import pytest
from adeu_core_ir import (
    AdeuIntegrityDeonticConflictExtended,
    build_integrity_deontic_conflict_extended_diagnostics,
    canonicalize_core_ir_payload,
    canonicalize_integrity_deontic_conflict_extended_payload,
)


def _deontic_extended_payload() -> dict[str, object]:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-e3-extended-conflicts",
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
                "label": "Agents must enable API access during setup",
                "modality": "obligatory",
                "target": "api access",
                "condition": "always",
                "priority": 2,
            },
            {
                "id": "d_permitted_1",
                "layer": "D",
                "kind": "Policy",
                "label": "Agents may enable API access during setup",
                "modality": "permitted",
                "target": "api access",
                "condition": "",
                "priority": 1,
            },
        ],
        "edges": [
            {"type": "excepts", "from": "d_exception_1", "to": "d_forbidden_1"},
        ],
    }
    return canonicalize_core_ir_payload(payload)


def test_deontic_conflict_extended_detects_conflicts_and_tension() -> None:
    diagnostics = build_integrity_deontic_conflict_extended_diagnostics(_deontic_extended_payload())

    assert diagnostics.schema == "adeu_integrity_deontic_conflict_extended@0.1"
    assert diagnostics.source_text_hash == "hash-e3-extended-conflicts"
    assert diagnostics.summary.total_conflicts == 2
    assert diagnostics.summary.deontic_conflict == 1
    assert diagnostics.summary.deontic_tension == 1
    conflict_entries = [
        (conflict.kind, conflict.primary_id, conflict.related_id)
        for conflict in diagnostics.conflicts
    ]
    assert conflict_entries == [
        ("deontic_conflict", "d_forbidden_1", "d_obligatory_1"),
        ("deontic_tension", "d_forbidden_1", "d_permitted_1"),
    ]
    assert diagnostics.conflicts[0].details == {
        "normalized_target": "api access",
        "normalized_condition": "",
        "primary_modality": "forbidden",
        "related_modality": "obligatory",
        "primary_priority": 7,
        "related_priority": 2,
    }
    assert diagnostics.conflicts[1].details == {
        "normalized_target": "api access",
        "normalized_condition": "",
        "primary_modality": "forbidden",
        "related_modality": "permitted",
        "primary_priority": 7,
        "related_priority": 1,
    }


def test_deontic_conflict_extended_defers_obligatory_permitted_pair() -> None:
    payload = canonicalize_core_ir_payload(
        {
            "schema": "adeu_core_ir@0.1",
            "source_text_hash": "hash-e3-extended-deferred",
            "nodes": [
                {
                    "id": "d_obligatory_1",
                    "layer": "D",
                    "kind": "Norm",
                    "label": "obligatory statement",
                    "modality": "obligatory",
                    "target": "api access",
                    "condition": "always",
                },
                {
                    "id": "d_permitted_1",
                    "layer": "D",
                    "kind": "Policy",
                    "label": "permitted statement",
                    "modality": "permitted",
                    "target": "api access",
                    "condition": "none",
                },
            ],
            "edges": [],
        }
    )
    diagnostics = build_integrity_deontic_conflict_extended_diagnostics(payload)
    assert diagnostics.summary.total_conflicts == 0
    assert diagnostics.summary.deontic_conflict == 0
    assert diagnostics.summary.deontic_tension == 0
    assert diagnostics.conflicts == []


def test_deontic_conflict_extended_model_rejects_unsorted_conflicts() -> None:
    payload = {
        "schema": "adeu_integrity_deontic_conflict_extended@0.1",
        "source_text_hash": "hash-e3-extended-unsorted",
        "summary": {
            "total_conflicts": 2,
            "deontic_conflict": 1,
            "deontic_tension": 1,
        },
        "conflicts": [
            {
                "kind": "deontic_tension",
                "primary_id": "d_forbidden_2",
                "related_id": "d_permitted_2",
            },
            {
                "kind": "deontic_conflict",
                "primary_id": "d_forbidden_1",
                "related_id": "d_obligatory_1",
            },
        ],
    }
    with pytest.raises(ValueError, match="conflicts must be sorted"):
        AdeuIntegrityDeonticConflictExtended.model_validate(payload)


def test_deontic_conflict_extended_payload_canonicalization_is_deterministic() -> None:
    diagnostics_a = build_integrity_deontic_conflict_extended_diagnostics(
        _deontic_extended_payload()
    )
    diagnostics_b = build_integrity_deontic_conflict_extended_diagnostics(
        _deontic_extended_payload()
    )
    assert canonicalize_integrity_deontic_conflict_extended_payload(
        diagnostics_a
    ) == canonicalize_integrity_deontic_conflict_extended_payload(diagnostics_b)


def test_deontic_conflict_extended_diagnostics_fail_closed_when_cap_is_exceeded(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    payload = canonicalize_core_ir_payload(
        {
            "schema": "adeu_core_ir@0.1",
            "source_text_hash": "hash-e3-extended-cap",
            "nodes": [
                {
                    "id": "d_forbidden_1",
                    "layer": "D",
                    "kind": "Norm",
                    "label": "forbidden statement",
                    "modality": "forbidden",
                    "target": "api access",
                    "condition": "always",
                },
                {
                    "id": "d_obligatory_1",
                    "layer": "D",
                    "kind": "Norm",
                    "label": "obligatory statement",
                    "modality": "obligatory",
                    "target": "api access",
                    "condition": "none",
                },
                {
                    "id": "d_permitted_1",
                    "layer": "D",
                    "kind": "Policy",
                    "label": "permitted statement",
                    "modality": "permitted",
                    "target": "api access",
                    "condition": "",
                },
            ],
            "edges": [],
        }
    )
    monkeypatch.setattr(deontic_conflict_extended_module, "_MAX_EMITTED_CONFLICTS", 1)
    with pytest.raises(ValueError, match="URM_ADEU_INTEGRITY_FIXTURE_INVALID"):
        build_integrity_deontic_conflict_extended_diagnostics(payload)


def test_deontic_conflict_extended_requires_source_text_hash() -> None:
    with pytest.raises(ValueError, match="source_text_hash must be a non-empty string"):
        build_integrity_deontic_conflict_extended_diagnostics(
            {
                "schema": "adeu_core_ir@0.1",
                "nodes": [],
                "edges": [],
            }
        )
