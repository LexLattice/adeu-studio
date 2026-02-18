from __future__ import annotations

import pytest
from adeu_core_ir import AdeuCoreIR, canonicalize_core_ir_payload


def _valid_payload() -> dict:
    return {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "abc123",
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
            {"type": "gates", "from": "d_policy_1", "to": "e_claim_1"},
            {"type": "serves_goal", "from": "d_policy_1", "to": "u_goal_1"},
        ],
    }


def test_valid_core_ir_contract_passes() -> None:
    ir = AdeuCoreIR.model_validate(_valid_payload())
    assert ir.schema == "adeu_core_ir@0.1"
    assert len(ir.nodes) == 4
    assert len(ir.edges) == 3


def test_rejects_unsorted_nodes() -> None:
    payload = _valid_payload()
    payload["nodes"] = [payload["nodes"][1], payload["nodes"][0], *payload["nodes"][2:]]
    with pytest.raises(ValueError, match="nodes must be sorted"):
        AdeuCoreIR.model_validate(payload)


def test_rejects_unsorted_edges() -> None:
    payload = _valid_payload()
    payload["edges"] = [payload["edges"][2], payload["edges"][0], payload["edges"][1]]
    with pytest.raises(ValueError, match="edges must be sorted"):
        AdeuCoreIR.model_validate(payload)


def test_rejects_duplicate_node_ids() -> None:
    payload = _valid_payload()
    payload["nodes"] = [payload["nodes"][0], dict(payload["nodes"][0]), *payload["nodes"][1:]]
    with pytest.raises(ValueError, match="duplicate node id"):
        AdeuCoreIR.model_validate(payload)


def test_rejects_duplicate_edge_identity() -> None:
    payload = _valid_payload()
    payload["edges"] = [payload["edges"][0], dict(payload["edges"][0]), *payload["edges"][1:]]
    with pytest.raises(ValueError, match="duplicate edge identity"):
        AdeuCoreIR.model_validate(payload)


def test_rejects_edge_typing_violation() -> None:
    payload = _valid_payload()
    payload["edges"][0] = {"type": "about", "from": "o_concept_1", "to": "e_claim_1"}
    with pytest.raises(ValueError, match="edge typing violation"):
        AdeuCoreIR.model_validate(payload)


def test_canonicalize_payload_sorts_and_dedupes_edges() -> None:
    payload = _valid_payload()
    payload["nodes"] = [
        payload["nodes"][2],
        payload["nodes"][1],
        payload["nodes"][0],
        payload["nodes"][3],
    ]
    payload["edges"] = [
        payload["edges"][2],
        payload["edges"][0],
        payload["edges"][1],
        payload["edges"][0],
    ]

    canonical = canonicalize_core_ir_payload(payload)
    ir = AdeuCoreIR.model_validate(canonical)

    assert [node["id"] for node in canonical["nodes"]] == [
        "o_concept_1",
        "e_claim_1",
        "d_policy_1",
        "u_goal_1",
    ]
    assert len(canonical["edges"]) == 3
    assert [edge["type"] for edge in canonical["edges"]] == ["about", "gates", "serves_goal"]
    assert ir.edges[0].identity == ("about", "e_claim_1", "o_concept_1")
