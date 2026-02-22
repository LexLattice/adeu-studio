from __future__ import annotations

import adeu_core_ir.integrity_cycle_policy_extended as cycle_policy_extended_module
import pytest
from adeu_core_ir import (
    AdeuIntegrityCyclePolicyExtended,
    build_integrity_cycle_policy_extended_diagnostics,
    canonicalize_core_ir_payload,
    canonicalize_integrity_cycle_policy_extended_payload,
)


def _e_layer_cyclic_payload() -> dict[str, object]:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-e2-extended-e-cycles",
        "nodes": [
            {"id": "o1", "layer": "O", "kind": "Concept", "label": "governance"},
            {"id": "c1", "layer": "E", "kind": "Claim", "text": "c1", "spans": []},
            {"id": "c2", "layer": "E", "kind": "Claim", "text": "c2", "spans": []},
            {"id": "c3", "layer": "E", "kind": "Claim", "text": "c3", "spans": []},
        ],
        "edges": [
            {"type": "about", "from": "c1", "to": "o1"},
            {"type": "depends_on", "from": "c1", "to": "c1"},
            {"type": "depends_on", "from": "c1", "to": "c2"},
            {"type": "depends_on", "from": "c2", "to": "c3"},
            {"type": "depends_on", "from": "c3", "to": "c1"},
        ],
    }
    return canonicalize_core_ir_payload(payload)


def test_cycle_policy_extended_preserves_v16_e_layer_cycle_semantics() -> None:
    diagnostics = build_integrity_cycle_policy_extended_diagnostics(_e_layer_cyclic_payload())

    assert diagnostics.schema == "adeu_integrity_cycle_policy_extended@0.1"
    assert diagnostics.source_text_hash == "hash-e2-extended-e-cycles"
    assert diagnostics.summary.total_cycles == 2
    assert diagnostics.summary.self_cycle == 1
    assert diagnostics.summary.multi_node_cycle == 1
    assert diagnostics.summary.dependency_loop == 0
    assert diagnostics.summary.exception_loop == 0
    cycle_entries = [
        (entry.kind, entry.cycle_signature, entry.node_ids) for entry in diagnostics.cycles
    ]
    assert cycle_entries == [
        ("multi_node_cycle", "cycle:c1->c2->c3", ["c1", "c2", "c3"]),
        ("self_cycle", "cycle:c1", ["c1"]),
    ]


def test_cycle_policy_extended_detects_dependency_and_exception_loops_from_bypass_payload() -> None:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-e2-extended-bypass",
        "nodes": [
            {"id": "d_exception_1", "layer": "D", "kind": "Exception", "label": "exception"},
            {"id": "d_norm_1", "layer": "D", "kind": "Norm", "label": "norm"},
            {"id": "d_policy_1", "layer": "D", "kind": "Policy", "label": "policy"},
        ],
        "edges": [
            {"type": "depends_on", "from": "d_norm_1", "to": "d_policy_1"},
            {"type": "depends_on", "from": "d_policy_1", "to": "d_norm_1"},
            {"type": "excepts", "from": "d_exception_1", "to": "d_norm_1"},
            {"type": "depends_on", "from": "d_norm_1", "to": "d_exception_1"},
        ],
    }

    diagnostics = build_integrity_cycle_policy_extended_diagnostics(payload)

    assert diagnostics.summary.total_cycles == 2
    assert diagnostics.summary.self_cycle == 0
    assert diagnostics.summary.multi_node_cycle == 0
    assert diagnostics.summary.dependency_loop == 1
    assert diagnostics.summary.exception_loop == 1
    cycle_entries = [
        (entry.kind, entry.cycle_signature, entry.node_ids) for entry in diagnostics.cycles
    ]
    assert cycle_entries == [
        ("dependency_loop", "cycle:d_norm_1->d_policy_1", ["d_norm_1", "d_policy_1"]),
        ("exception_loop", "cycle:d_exception_1->d_norm_1", ["d_exception_1", "d_norm_1"]),
    ]


def test_cycle_policy_extended_d_scope_ignores_cross_layer_edges() -> None:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-e2-extended-cross-layer",
        "nodes": [
            {"id": "d_norm_1", "layer": "D", "kind": "Norm", "label": "norm"},
            {"id": "d_policy_1", "layer": "D", "kind": "Policy", "label": "policy"},
            {"id": "e_claim_1", "layer": "E", "kind": "Claim", "text": "c1", "spans": []},
        ],
        "edges": [
            {"type": "depends_on", "from": "d_norm_1", "to": "e_claim_1"},
            {"type": "depends_on", "from": "e_claim_1", "to": "d_norm_1"},
            {"type": "excepts", "from": "d_policy_1", "to": "e_claim_1"},
        ],
    }

    diagnostics = build_integrity_cycle_policy_extended_diagnostics(payload)

    assert diagnostics.summary.total_cycles == 0
    assert diagnostics.summary.self_cycle == 0
    assert diagnostics.summary.multi_node_cycle == 0
    assert diagnostics.summary.dependency_loop == 0
    assert diagnostics.summary.exception_loop == 0
    assert diagnostics.cycles == []


def test_cycle_policy_extended_model_rejects_unsorted_cycles() -> None:
    payload = {
        "schema": "adeu_integrity_cycle_policy_extended@0.1",
        "source_text_hash": "hash-e2-extended-unsorted",
        "summary": {
            "total_cycles": 2,
            "self_cycle": 0,
            "multi_node_cycle": 0,
            "dependency_loop": 1,
            "exception_loop": 1,
        },
        "cycles": [
            {
                "kind": "exception_loop",
                "cycle_signature": "cycle:d_exception_2->d_norm_2",
                "node_ids": ["d_exception_2", "d_norm_2"],
            },
            {
                "kind": "dependency_loop",
                "cycle_signature": "cycle:d_norm_1->d_policy_1",
                "node_ids": ["d_norm_1", "d_policy_1"],
            },
        ],
    }
    with pytest.raises(ValueError, match="cycles must be sorted by \\(kind, cycle_signature\\)"):
        AdeuIntegrityCyclePolicyExtended.model_validate(payload)


def test_cycle_policy_extended_diagnostics_fail_closed_when_cycle_cap_is_exceeded(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-e2-extended-cap",
        "nodes": [
            {"id": "c1", "layer": "E", "kind": "Claim", "text": "c1", "spans": []},
            {"id": "c2", "layer": "E", "kind": "Claim", "text": "c2", "spans": []},
            {"id": "d1", "layer": "D", "kind": "Norm", "label": "d1"},
            {"id": "d2", "layer": "D", "kind": "Policy", "label": "d2"},
        ],
        "edges": [
            {"type": "depends_on", "from": "c1", "to": "c2"},
            {"type": "depends_on", "from": "c2", "to": "c1"},
            {"type": "depends_on", "from": "d1", "to": "d2"},
            {"type": "depends_on", "from": "d2", "to": "d1"},
        ],
    }
    monkeypatch.setattr(cycle_policy_extended_module, "_MAX_EMITTED_CYCLES", 1)
    with pytest.raises(ValueError, match="URM_ADEU_INTEGRITY_FIXTURE_INVALID"):
        build_integrity_cycle_policy_extended_diagnostics(payload)


def test_cycle_policy_extended_payload_canonicalization_is_deterministic() -> None:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-e2-extended-deterministic",
        "nodes": [
            {"id": "d1", "layer": "D", "kind": "Norm", "label": "d1"},
            {"id": "d2", "layer": "D", "kind": "Policy", "label": "d2"},
        ],
        "edges": [
            {"type": "depends_on", "from": "d1", "to": "d2"},
            {"type": "depends_on", "from": "d2", "to": "d1"},
        ],
    }
    diagnostics_a = build_integrity_cycle_policy_extended_diagnostics(payload)
    diagnostics_b = build_integrity_cycle_policy_extended_diagnostics(payload)
    assert canonicalize_integrity_cycle_policy_extended_payload(
        diagnostics_a
    ) == canonicalize_integrity_cycle_policy_extended_payload(diagnostics_b)


def test_cycle_policy_extended_requires_source_text_hash() -> None:
    with pytest.raises(ValueError, match="source_text_hash must be a non-empty string"):
        build_integrity_cycle_policy_extended_diagnostics(
            {
                "schema": "adeu_core_ir@0.1",
                "nodes": [],
                "edges": [],
            }
        )
