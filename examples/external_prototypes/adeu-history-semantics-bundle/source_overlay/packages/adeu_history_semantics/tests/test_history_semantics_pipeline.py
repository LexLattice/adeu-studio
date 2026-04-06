from __future__ import annotations

import json
from pathlib import Path

from adeu_history_semantics import HistorySemanticBundle, compile_history_semantic_bundle

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v0"


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _load_text(name: str) -> str:
    return (FIXTURE_ROOT / name).read_text(encoding="utf-8").rstrip("\n")


def _compile_conversation_bundle() -> HistorySemanticBundle:
    return compile_history_semantic_bundle(
        source_text=_load_text("demo_conversation_history_source.txt"),
        input_kind="conversation_history",
        source_label="Demo conversation history fixture",
        corpus_wave_posture="wave_0_bootstrap_candidate",
        source_notes=[
            "bounded demo fixture",
            "non-authoritative simulated bootstrap corpus sample",
        ],
    )


def _compile_abstract_bundle() -> HistorySemanticBundle:
    return compile_history_semantic_bundle(
        source_text=_load_text("demo_abstract_like_source.txt"),
        input_kind="abstract_like",
        source_label="Demo abstract-like fixture",
        corpus_wave_posture="unassigned",
        source_notes=[
            "bounded demo fixture",
            "non-authoritative simulated abstract sample",
        ],
    )


def test_conversation_bundle_replays_the_reference_fixture_exactly() -> None:
    compiled = _compile_conversation_bundle().model_dump(mode="json", by_alias=True)
    assert compiled == _load_json("reference_history_semantic_bundle_conversation.json")


def test_abstract_bundle_replays_the_reference_fixture_exactly() -> None:
    compiled = _compile_abstract_bundle().model_dump(mode="json", by_alias=True)
    assert compiled == _load_json("reference_history_semantic_bundle_abstract.json")


def test_conversation_theme_selection_is_user_anchored_but_assistant_explication_is_retained(
) -> None:
    bundle = _compile_conversation_bundle()

    assert len(bundle.slices) == 2
    assert len(bundle.theme_anchors) == 2
    assert all(
        anchor.selection_posture == "user_message_primary"
        for anchor in bundle.theme_anchors
    )

    for packet in bundle.reconstruction_packets:
        lanes = {lane.lane_id: lane for lane in packet.lane_reconstructions}
        assert set(lanes) == {"O", "E", "D", "U"}
        assert all(lane.presence_status == "present" for lane in lanes.values())
        assert lanes["U"].dominant_role_posture == "assistant_explication"
        assert {
            lanes[lane_id].dominant_role_posture for lane_id in ("O", "E", "D")
        } == {"mixed"}
        assert lanes["U"].evidence_refs
        assert all(ref.role == "assistant" for ref in lanes["U"].evidence_refs)


def test_abstract_workspace_separates_chronology_from_inferential_order() -> None:
    bundle = _compile_abstract_bundle()

    chronology = bundle.workspace_snapshot.chronology_slice_order
    inferential = bundle.workspace_snapshot.inferential_slice_order

    assert chronology != inferential
    assert inferential[0] == bundle.slices[1].slice_id

    packets_by_slice = {packet.slice_id: packet for packet in bundle.reconstruction_packets}
    middle_packet = packets_by_slice[bundle.slices[1].slice_id]
    middle_lanes = {lane.lane_id: lane for lane in middle_packet.lane_reconstructions}
    assert middle_lanes["U"].presence_status == "weakly_present"
    assert middle_lanes["D"].presence_status == "underdetermined"
