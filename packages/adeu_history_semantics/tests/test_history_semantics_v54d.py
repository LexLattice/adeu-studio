from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path

import pytest
from adeu_history_semantics import (
    build_history_ledger,
    build_history_odeu_reconstruction_packets,
    build_history_slices,
    build_history_source_artifact,
    build_history_theme_anchors,
    build_history_workspace_snapshot,
    compute_history_workspace_frame_id,
    compute_history_workspace_question_id,
    compute_history_workspace_snapshot_id,
    preclassify_history_source,
    validate_history_workspace_snapshot,
)

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v54d"


def _question_reason(presence_status: str) -> str:
    return (
        "weak_lane"
        if presence_status == "weakly_present"
        else "underdetermined_lane"
    )


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _build_projection(
    source_name: str,
    *,
    source_label: str | None = None,
) -> dict[str, object]:
    if source_label is None:
        source_label = f"v54d {source_name}"
    source = build_history_source_artifact(
        source_text=(
            Path(__file__).parent / "fixtures" / "v54c" / source_name
        ).read_text(encoding="utf-8"),
        source_label=source_label,
        corpus_wave_posture="wave_0_bootstrap_candidate",
        source_notes=["v54d_reference_workspace_bundle"],
    )
    preclassifications = preclassify_history_source(source=source)
    ledger = build_history_ledger(preclassifications=preclassifications)
    slices = build_history_slices(ledger=ledger)
    theme_anchors = build_history_theme_anchors(ledger=ledger, slices=slices)
    packets = build_history_odeu_reconstruction_packets(
        ledger=ledger,
        slices=slices,
        theme_anchors=theme_anchors,
    )
    snapshot = build_history_workspace_snapshot(
        ledger=ledger,
        slices=slices,
        theme_anchors=theme_anchors,
        packets=packets,
    )

    return {
        "source": source,
        "preclassifications": preclassifications,
        "ledger": ledger,
        "slices": slices,
        "theme_anchors": theme_anchors,
        "packets": packets,
        "workspace_snapshot": snapshot,
    }


def _payload_snapshot_only(source_name: str) -> dict[str, object]:
    projection = _build_projection(source_name)
    return {
        "ledger": projection["ledger"].model_dump(by_alias=True),
        "slices": [
            item.model_dump(by_alias=True) for item in projection["slices"]
        ],
        "theme_anchors": [
            item.model_dump(by_alias=True) for item in projection["theme_anchors"]
        ],
        "packets": [
            item.model_dump(by_alias=True) for item in projection["packets"]
        ],
        "source": projection["source"].model_dump(by_alias=True),
        "preclassifications": [
            item.model_dump(by_alias=True) for item in projection["preclassifications"]
        ],
        "workspace_snapshot": projection["workspace_snapshot"].model_dump(by_alias=True),
    }


def _inferential_slice_order(projection: dict[str, object]) -> list[str]:
    slices = sorted(projection["slices"], key=lambda item: item.slice_index)
    packets: list = projection["packets"]
    return [
        item.slice_id
        for item in sorted(
            slices,
            key=lambda item: (
                -sum(
                    1
                    for packet in packets
                    if packet.slice_id == item.slice_id
                    for lane in packet.lane_reconstructions
                    if lane.presence_status == "present"
                ),
                item.slice_index,
            ),
        )
    ]


def test_reference_workspace_snapshot_replays_committed_fixture() -> None:
    expected = _load_json("reference_conversation_history_lf_workspace_snapshot.json")
    actual = _payload_snapshot_only("reference_conversation_history_lf.txt")

    assert actual == expected


def test_workspace_snapshot_postures_remain_advisory() -> None:
    projection = _build_projection("reference_conversation_history_lf.txt")
    snapshot = projection["workspace_snapshot"]

    assert snapshot.source_authority_posture == "normalized_source_text_authoritative"
    assert snapshot.interpretation_authority_posture == "advisory_overlay_only"
    assert snapshot.workspace_synthesis_posture == "advisory_reconstruction_only"


def test_snapshot_slice_orders_are_chronology_plus_inferential() -> None:
    projection = _build_projection("reference_conversation_history_lf.txt")
    snapshot = projection["workspace_snapshot"]

    expected_chronology = [
        item.slice_id
        for item in sorted(projection["slices"], key=lambda item: item.slice_index)
    ]
    expected_inferential = _inferential_slice_order(projection)

    assert snapshot.chronology_slice_order == expected_chronology
    assert snapshot.inferential_slice_order == expected_inferential


def test_workspace_frame_and_question_ids_are_semantically_canonical() -> None:
    projection = _build_projection("assistant_local_explicit_history_lf.txt")
    snapshot = projection["workspace_snapshot"]

    assert snapshot.semantic_hash == compute_history_workspace_snapshot_id(
        source_id=projection["ledger"].source_id,
        ledger_id=projection["ledger"].ledger_id,
        chronology_slice_order=snapshot.chronology_slice_order,
        inferential_slice_order=snapshot.inferential_slice_order,
        theme_frames=snapshot.theme_frames,
        source_authority_posture=snapshot.source_authority_posture,
        interpretation_authority_posture=snapshot.interpretation_authority_posture,
        workspace_synthesis_posture=snapshot.workspace_synthesis_posture,
        semantic_identity_mode=snapshot.semantic_identity_mode,
    )
    for frame in snapshot.theme_frames:
        assert frame.frame_id == compute_history_workspace_frame_id(
            theme_anchor_id=frame.theme_anchor_id,
            theme_display_label=frame.theme_display_label,
            slice_ids=frame.slice_ids,
            packet_ids=frame.packet_ids,
            chronology_start_order_index=frame.chronology_start_order_index,
            chronology_end_order_index=frame.chronology_end_order_index,
            underdeveloped_lane_ids=frame.underdeveloped_lane_ids,
            provenance_entry_ids=frame.provenance_entry_ids,
            open_questions=frame.open_questions,
        )
        for question in frame.open_questions:
            assert question.question_id == compute_history_workspace_question_id(
                lane_id=question.lane_id,
                reason_kind=question.reason_kind,
                question_text=question.question_text,
            )


def test_weak_and_underdetermined_lanes_emit_workspace_questions() -> None:
    projection = _build_projection("weak_underdetermined_history_lf.txt")
    packets_by_anchor = defaultdict(list)
    for packet in projection["packets"]:
        packets_by_anchor[packet.theme_anchor_id].append(packet)

    for frame in projection["workspace_snapshot"].theme_frames:
        anchor_packets = packets_by_anchor[frame.theme_anchor_id]
        question_by_lane = {
            (item.lane_id, item.reason_kind): item for item in frame.open_questions
        }

        for packet in anchor_packets:
            for lane in packet.lane_reconstructions:
                if lane.presence_status == "present":
                    assert (
                        lane.lane_id,
                        _question_reason(lane.presence_status),
                    ) not in question_by_lane
                    continue
                reason = _question_reason(lane.presence_status)
                assert (lane.lane_id, reason) in question_by_lane
                question = question_by_lane[(lane.lane_id, reason)]
                assert lane.lane_id == question.lane_id
                assert reason == question.reason_kind


def test_validation_rejects_unknown_anchor_covering() -> None:
    projection = _build_projection("reference_conversation_history_lf.txt")
    snapshot = projection["workspace_snapshot"]
    mutated_frame = snapshot.theme_frames[0].model_copy(
        update={
            "theme_anchor_id": "history_theme_anchor:unknown00000000",
        }
    )
    mutated_frame = mutated_frame.model_copy(
        update={
            "frame_id": compute_history_workspace_frame_id(
                theme_anchor_id=mutated_frame.theme_anchor_id,
                theme_display_label=mutated_frame.theme_display_label,
                slice_ids=mutated_frame.slice_ids,
                packet_ids=mutated_frame.packet_ids,
                chronology_start_order_index=mutated_frame.chronology_start_order_index,
                chronology_end_order_index=mutated_frame.chronology_end_order_index,
                underdeveloped_lane_ids=mutated_frame.underdeveloped_lane_ids,
                provenance_entry_ids=mutated_frame.provenance_entry_ids,
                open_questions=mutated_frame.open_questions,
            )
        }
    )

    with pytest.raises(
        ValueError,
        match="theme frame theme_anchor_id must reference a released anchor",
    ):
        validate_history_workspace_snapshot(
            ledger=projection["ledger"],
            slices=projection["slices"],
            theme_anchors=projection["theme_anchors"],
            packets=projection["packets"],
            snapshot=snapshot.model_copy(update={"theme_frames": [mutated_frame]}),
        )


def test_validation_rejects_missing_packet_coverage() -> None:
    projection = _build_projection("weak_underdetermined_history_lf.txt")
    snapshot = projection["workspace_snapshot"]
    frame = snapshot.theme_frames[0]
    mutated_frame = frame.model_copy(
        update={"packet_ids": frame.packet_ids[:-1] if len(frame.packet_ids) > 1 else []}
    )

    with pytest.raises(
        ValueError,
        match="theme frame packet_ids must match the released packets for that anchor",
    ):
        validate_history_workspace_snapshot(
            ledger=projection["ledger"],
            slices=projection["slices"],
            theme_anchors=projection["theme_anchors"],
            packets=projection["packets"],
            snapshot=snapshot.model_copy(update={"theme_frames": [mutated_frame]}),
        )


def test_validation_rejects_duplicate_theme_frame_per_anchor() -> None:
    projection = _build_projection("reference_conversation_history_lf.txt")
    snapshot = projection["workspace_snapshot"]
    frame = snapshot.theme_frames[0]

    with pytest.raises(
        ValueError,
        match="snapshot theme_frames must map to each released theme anchor exactly once",
    ):
        validate_history_workspace_snapshot(
            ledger=projection["ledger"],
            slices=projection["slices"],
            theme_anchors=projection["theme_anchors"],
            packets=projection["packets"],
            snapshot=snapshot.model_copy(update={"theme_frames": [frame, frame]}),
        )
