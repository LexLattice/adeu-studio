from __future__ import annotations

from adeu_core_ir import stable_core_node_id


def test_stable_core_node_id_is_deterministic() -> None:
    node_id_a = stable_core_node_id(
        layer="E",
        kind="Claim",
        primary_text_or_label="AI agents delegate work",
        source_text_hash="hash-a",
        spans=[{"start": 10, "end": 20}, {"start": 0, "end": 8}],
    )
    node_id_b = stable_core_node_id(
        layer="E",
        kind="Claim",
        primary_text_or_label="  ai   agents delegate work ",
        source_text_hash="hash-a",
        spans=[{"start": 0, "end": 8}, {"start": 10, "end": 20}],
    )
    assert node_id_a == node_id_b


def test_stable_core_node_id_changes_with_source_hash() -> None:
    node_id_a = stable_core_node_id(
        layer="O",
        kind="Concept",
        primary_text_or_label="delegation",
        source_text_hash="hash-a",
    )
    node_id_b = stable_core_node_id(
        layer="O",
        kind="Concept",
        primary_text_or_label="delegation",
        source_text_hash="hash-b",
    )
    assert node_id_a != node_id_b


def test_stable_core_node_id_is_span_segmentation_invariant() -> None:
    merged_span_id = stable_core_node_id(
        layer="E",
        kind="Claim",
        primary_text_or_label="AI delegation improves throughput",
        source_text_hash="hash-a",
        spans=[{"start": 0, "end": 10}],
    )
    overlapping_span_id = stable_core_node_id(
        layer="E",
        kind="Claim",
        primary_text_or_label="AI delegation improves throughput",
        source_text_hash="hash-a",
        spans=[{"start": 0, "end": 5}, {"start": 3, "end": 10}],
    )
    assert merged_span_id == overlapping_span_id
