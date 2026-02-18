from __future__ import annotations

from adeu_core_ir import (
    build_core_ir_from_source_text,
    canonicalize_core_ir_candidates,
    normalize_core_source_text,
    stable_core_node_id,
)


def test_normalize_core_source_text_is_whitespace_invariant() -> None:
    raw_a = "  AI   agents\n\tdelegate   work.  "
    raw_b = "AI agents delegate work."
    normalized_a = normalize_core_source_text(raw_a)
    normalized_b = normalize_core_source_text(raw_b)

    assert normalized_a.normalized_text == "AI agents delegate work."
    assert normalized_a.normalized_text == normalized_b.normalized_text
    assert normalized_a.source_text_hash == normalized_b.source_text_hash


def test_normalize_core_source_text_maps_raw_spans() -> None:
    normalized = normalize_core_source_text("  AI\tagents")
    span = normalized.to_normalized_span({"start": 2, "end": 11})
    assert span.start == 0
    assert span.end == 9
    assert normalized.normalized_text[span.start : span.end] == "AI agents"


def test_canonicalize_candidates_merges_duplicates_and_remaps_edges() -> None:
    candidates = {
        "nodes": [
            {
                "id": "e_claim_short",
                "layer": "E",
                "kind": "Claim",
                "text": "AI agents delegate work",
                "spans": [{"start": 0, "end": 6}],
            },
            {
                "id": "e_claim_long",
                "layer": "E",
                "kind": "Claim",
                "text": " ai   agents delegate work ",
                "spans": [{"start": 0, "end": 10}],
            },
            {"id": "o_concept_a", "layer": "O", "kind": "Concept", "label": "Delegation"},
            {"id": "o_concept_b", "layer": "O", "kind": "Concept", "label": " delegation "},
        ],
        "edges": [
            {"type": "about", "from": "e_claim_short", "to": "o_concept_a"},
            {"type": "about", "from": "e_claim_long", "to": "o_concept_b"},
        ],
    }

    ir = canonicalize_core_ir_candidates(
        source_text_hash="hash-a",
        source_text="AI agents delegate work",
        candidates=candidates,
    )

    assert len(ir.nodes) == 2
    assert len(ir.edges) == 1

    claim = next(node for node in ir.nodes if node.layer == "E")
    concept = next(node for node in ir.nodes if node.layer == "O")
    assert claim.spans[0].start == 0
    assert claim.spans[0].end == 10
    assert ir.edges[0].identity == ("about", claim.id, concept.id)

    claim_short_id = stable_core_node_id(
        layer="E",
        kind="Claim",
        primary_text_or_label="AI agents delegate work",
        source_text_hash="hash-a",
        spans=[{"start": 0, "end": 6}],
    )
    claim_long_id = stable_core_node_id(
        layer="E",
        kind="Claim",
        primary_text_or_label="AI agents delegate work",
        source_text_hash="hash-a",
        spans=[{"start": 0, "end": 10}],
    )
    assert claim.id == min(claim_short_id, claim_long_id)


def test_canonicalize_candidates_fails_on_unresolved_edge_refs() -> None:
    candidates = {
        "nodes": [{"id": "o_concept_1", "layer": "O", "kind": "Concept", "label": "delegation"}],
        "edges": [{"type": "about", "from": "missing_id", "to": "o_concept_1"}],
    }

    try:
        canonicalize_core_ir_candidates(source_text_hash="hash-a", candidates=candidates)
    except ValueError as exc:
        assert "unresolved candidate edge reference" in str(exc)
    else:
        raise AssertionError("expected unresolved candidate edge reference failure")


def test_build_core_ir_from_source_text_is_deterministic() -> None:
    source_a = "AI systems must provide evidence. This improves trust."
    source_b = " AI systems   must provide evidence.\nThis improves trust. "

    ir_a = build_core_ir_from_source_text(source_a)
    ir_b = build_core_ir_from_source_text(source_b)

    dump_a = ir_a.model_dump(mode="json", by_alias=True, exclude_none=True)
    dump_b = ir_b.model_dump(mode="json", by_alias=True, exclude_none=True)
    assert dump_a == dump_b
    assert ir_a.source_text_hash == ir_b.source_text_hash


def test_canonicalize_candidates_is_order_independent() -> None:
    candidates_a = {
        "nodes": [
            {"id": "o1", "layer": "O", "kind": "Concept", "label": "trust"},
            {
                "id": "e1",
                "layer": "E",
                "kind": "Claim",
                "text": "AI systems improve trust",
                "spans": [{"start": 0, "end": 24}],
            },
            {
                "id": "e2",
                "layer": "E",
                "kind": "Claim",
                "text": " AI  systems improve trust ",
                "spans": [{"start": 0, "end": 20}],
            },
        ],
        "edges": [
            {"type": "about", "from": "e1", "to": "o1"},
            {"type": "about", "from": "e2", "to": "o1"},
        ],
    }
    candidates_b = {
        "nodes": [candidates_a["nodes"][2], candidates_a["nodes"][1], candidates_a["nodes"][0]],
        "edges": [candidates_a["edges"][1], candidates_a["edges"][0]],
    }

    ir_a = canonicalize_core_ir_candidates(source_text_hash="hash-a", candidates=candidates_a)
    ir_b = canonicalize_core_ir_candidates(source_text_hash="hash-a", candidates=candidates_b)

    assert ir_a.model_dump(mode="json", by_alias=True, exclude_none=True) == ir_b.model_dump(
        mode="json",
        by_alias=True,
        exclude_none=True,
    )
