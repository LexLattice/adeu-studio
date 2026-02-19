from __future__ import annotations

import pytest
from adeu_core_ir import (
    AdeuCoreIR,
    apply_claim_ledger_scores,
    assert_claim_ledger_recompute_match,
    build_core_ir_from_source_text,
)


def _payload() -> dict:
    return {
        "schema": "adeu_core_ir@0.1",
        "source_text_hash": "hash-a",
        "nodes": [
            {"id": "o1", "layer": "O", "kind": "Concept", "label": "trust"},
            {
                "id": "c1",
                "layer": "E",
                "kind": "Claim",
                "text": "AI systems improve trust.",
                "confidence": 0.8,
                "spans": [{"start": 0, "end": 25}],
            },
            {
                "id": "c2",
                "layer": "E",
                "kind": "Claim",
                "text": "Trust can decline.",
                "spans": [],
            },
            {
                "id": "e1",
                "layer": "E",
                "kind": "Evidence",
                "text": "Benchmark report",
                "spans": [],
            },
            {
                "id": "q1",
                "layer": "E",
                "kind": "Question",
                "text": "Under what conditions?",
                "spans": [],
            },
        ],
        "edges": [
            {"type": "about", "from": "c1", "to": "o1"},
            {"type": "about", "from": "c2", "to": "o1"},
            {"type": "depends_on", "from": "c1", "to": "c2"},
            {"type": "depends_on", "from": "c1", "to": "q1"},
            {"type": "refutes", "from": "c2", "to": "c1"},
            {"type": "supports", "from": "e1", "to": "c1"},
        ],
    }


def test_apply_claim_ledger_scores_computes_frozen_formula() -> None:
    ir = apply_claim_ledger_scores(_payload())

    c1 = next(node for node in ir.nodes if node.id == "c1")
    c2 = next(node for node in ir.nodes if node.id == "c2")

    assert c1.ledger_version == "adeu.sbr.v0_1"
    assert c1.s_milli == 600
    assert c1.b_milli == 800
    assert c1.r_milli == 200
    assert c1.s == "0.600"
    assert c1.b == "0.800"
    assert c1.r == "0.200"

    assert c2.ledger_version == "adeu.sbr.v0_1"
    assert c2.s_milli == 0
    assert c2.b_milli == 0
    assert c2.r_milli == 0
    assert c2.s == "0.000"
    assert c2.b == "0.000"
    assert c2.r == "0.000"


def test_apply_claim_ledger_scores_without_display_fields() -> None:
    ir = apply_claim_ledger_scores(_payload(), include_display_fields=False)
    c1 = next(node for node in ir.nodes if node.id == "c1")
    assert c1.s is None
    assert c1.b is None
    assert c1.r is None
    assert c1.s_milli == 600
    assert c1.b_milli == 800
    assert c1.r_milli == 200


def test_claim_ledger_recompute_match_passes_for_scored_ir() -> None:
    scored = apply_claim_ledger_scores(_payload())
    assert_claim_ledger_recompute_match(scored)


def test_claim_ledger_recompute_match_allows_missing_display_fields() -> None:
    scored = apply_claim_ledger_scores(_payload(), include_display_fields=False)
    assert_claim_ledger_recompute_match(scored)


def test_claim_ledger_recompute_mismatch_fails_closed() -> None:
    scored = apply_claim_ledger_scores(_payload())
    payload = scored.model_dump(mode="json", by_alias=True, exclude_none=True)
    for node in payload["nodes"]:
        if node.get("id") == "c1":
            node["R_milli"] = 999
            node["R"] = "0.999"
            break
    tampered = AdeuCoreIR.model_validate(payload)

    with pytest.raises(ValueError, match="URM_ADEU_CORE_LEDGER_RECOMPUTE_MISMATCH"):
        assert_claim_ledger_recompute_match(tampered)


def test_build_pipeline_applies_claim_ledger_by_default() -> None:
    ir = build_core_ir_from_source_text("AI systems must provide evidence. This improves trust.")
    claim = next(node for node in ir.nodes if node.layer == "E" and node.kind == "Claim")
    assert claim.ledger_version == "adeu.sbr.v0_1"
    assert claim.s_milli is not None
    assert claim.b_milli is not None
    assert claim.r_milli is not None
