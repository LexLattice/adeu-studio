from __future__ import annotations

import adeu_core_ir.integrity_cycle_policy as cycle_policy_module
import pytest
from adeu_core_ir import (
    AdeuIntegrityCyclePolicy,
    build_integrity_cycle_policy_diagnostics,
    canonicalize_core_ir_payload,
    canonicalize_integrity_cycle_policy_payload,
)


def _acyclic_payload() -> dict[str, object]:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-d2-acyclic",
        "nodes": [
            {"id": "o1", "layer": "O", "kind": "Concept", "label": "alignment"},
            {
                "id": "c1",
                "layer": "E",
                "kind": "Claim",
                "text": "A depends on B",
                "spans": [],
            },
            {
                "id": "c2",
                "layer": "E",
                "kind": "Claim",
                "text": "B depends on evidence",
                "spans": [],
            },
            {
                "id": "e1",
                "layer": "E",
                "kind": "Evidence",
                "text": "Benchmark reference",
                "spans": [],
            },
        ],
        "edges": [
            {"type": "about", "from": "c1", "to": "o1"},
            {"type": "depends_on", "from": "c1", "to": "c2"},
            {"type": "depends_on", "from": "c2", "to": "e1"},
        ],
    }
    return canonicalize_core_ir_payload(payload)


def _cyclic_payload() -> dict[str, object]:
    payload = {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-d2-cycles",
        "nodes": [
            {"id": "o1", "layer": "O", "kind": "Concept", "label": "governance"},
            {
                "id": "c1",
                "layer": "E",
                "kind": "Claim",
                "text": "C1 depends on itself and C2",
                "spans": [],
            },
            {
                "id": "c2",
                "layer": "E",
                "kind": "Claim",
                "text": "C2 depends on C3",
                "spans": [],
            },
            {
                "id": "c3",
                "layer": "E",
                "kind": "Claim",
                "text": "C3 depends on C1",
                "spans": [],
            },
            {
                "id": "e1",
                "layer": "E",
                "kind": "Evidence",
                "text": "Reference evidence",
                "spans": [],
            },
        ],
        "edges": [
            {"type": "about", "from": "c1", "to": "o1"},
            {"type": "depends_on", "from": "c1", "to": "c1"},
            {"type": "depends_on", "from": "c1", "to": "c2"},
            {"type": "depends_on", "from": "c2", "to": "c3"},
            {"type": "depends_on", "from": "c3", "to": "c1"},
            {"type": "depends_on", "from": "c3", "to": "e1"},
            {"type": "refutes", "from": "c2", "to": "c1"},
        ],
    }
    return canonicalize_core_ir_payload(payload)


def test_cycle_policy_diagnostics_empty_for_acyclic_depends_on_graph() -> None:
    diagnostics = build_integrity_cycle_policy_diagnostics(_acyclic_payload())
    assert diagnostics.schema == "adeu_integrity_cycle_policy@0.1"
    assert diagnostics.source_text_hash == "hash-d2-acyclic"
    assert diagnostics.summary.total_cycles == 0
    assert diagnostics.summary.self_cycle == 0
    assert diagnostics.summary.multi_node_cycle == 0
    assert diagnostics.cycles == []


def test_cycle_policy_diagnostics_detect_self_and_multi_node_cycles() -> None:
    diagnostics = build_integrity_cycle_policy_diagnostics(_cyclic_payload())

    assert diagnostics.summary.total_cycles == 2
    assert diagnostics.summary.self_cycle == 1
    assert diagnostics.summary.multi_node_cycle == 1
    assert [
        (cycle.kind, cycle.cycle_signature, cycle.node_ids) for cycle in diagnostics.cycles
    ] == [
        ("self_cycle", "cycle:c1", ["c1"]),
        ("multi_node_cycle", "cycle:c1->c2->c3", ["c1", "c2", "c3"]),
    ]


def test_cycle_policy_diagnostics_deduplicates_equivalent_cycle_discoveries() -> None:
    payload = canonicalize_core_ir_payload(
        {
            "schema": "adeu_core_ir@0.1",
            "source_text_hash": "hash-d2-dedup",
            "nodes": [
                {
                    "id": "c1",
                    "layer": "E",
                    "kind": "Claim",
                    "text": "c1",
                    "spans": [],
                },
                {
                    "id": "c2",
                    "layer": "E",
                    "kind": "Claim",
                    "text": "c2",
                    "spans": [],
                },
            ],
            "edges": [
                {"type": "depends_on", "from": "c1", "to": "c2"},
                {"type": "depends_on", "from": "c2", "to": "c1"},
            ],
        }
    )

    diagnostics = build_integrity_cycle_policy_diagnostics(payload)
    assert diagnostics.summary.total_cycles == 1
    assert diagnostics.summary.self_cycle == 0
    assert diagnostics.summary.multi_node_cycle == 1
    assert [
        (cycle.kind, cycle.cycle_signature, cycle.node_ids) for cycle in diagnostics.cycles
    ] == [("multi_node_cycle", "cycle:c1->c2", ["c1", "c2"])]


def test_cycle_policy_model_rejects_unsorted_cycles() -> None:
    payload = {
        "schema": "adeu_integrity_cycle_policy@0.1",
        "source_text_hash": "hash-d2-unsorted",
        "summary": {
            "total_cycles": 2,
            "self_cycle": 2,
            "multi_node_cycle": 0,
        },
        "cycles": [
            {"kind": "self_cycle", "cycle_signature": "cycle:c2", "node_ids": ["c2"]},
            {"kind": "self_cycle", "cycle_signature": "cycle:c1", "node_ids": ["c1"]},
        ],
    }
    with pytest.raises(ValueError, match="cycles must be sorted by cycle_signature"):
        AdeuIntegrityCyclePolicy.model_validate(payload)


def test_cycle_policy_payload_canonicalization_is_deterministic() -> None:
    diagnostics_a = build_integrity_cycle_policy_diagnostics(_cyclic_payload())
    diagnostics_b = build_integrity_cycle_policy_diagnostics(_cyclic_payload())

    assert canonicalize_integrity_cycle_policy_payload(
        diagnostics_a
    ) == canonicalize_integrity_cycle_policy_payload(diagnostics_b)


def test_cycle_policy_diagnostics_fail_closed_when_cycle_cap_is_exceeded(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(cycle_policy_module, "_MAX_EMITTED_CYCLES", 1)
    with pytest.raises(ValueError, match="URM_ADEU_INTEGRITY_FIXTURE_INVALID"):
        build_integrity_cycle_policy_diagnostics(_cyclic_payload())
