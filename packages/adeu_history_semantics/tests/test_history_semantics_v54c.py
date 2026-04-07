from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest
from adeu_history_semantics import (
    HistoryODEULaneReconstruction,
    HistoryODEUReconstructionPacket,
    build_history_ledger,
    build_history_odeu_reconstruction_packets,
    build_history_slices,
    build_history_source_artifact,
    build_history_theme_anchors,
    compute_history_odeu_packet_id,
    compute_history_odeu_packet_semantic_hash,
    preclassify_history_source,
    validate_history_odeu_reconstruction_packets,
)
from pydantic import ValidationError

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v54c"


def _load_text(name: str) -> str:
    return (FIXTURE_ROOT / name).read_bytes().decode("utf-8")


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _build_projection_from_text(source_text: str, *, source_label: str) -> dict[str, object]:
    source = build_history_source_artifact(
        source_text=source_text,
        source_label=source_label,
        corpus_wave_posture="wave_0_bootstrap_candidate",
        source_notes=["v54c_fixture"],
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
    return {
        "source": source,
        "ledger": ledger,
        "slices": slices,
        "theme_anchors": theme_anchors,
        "packets": packets,
    }


def _build_projection(source_name: str) -> dict[str, object]:
    return _build_projection_from_text(_load_text(source_name), source_label=source_name)


def _projection_payload(projection: dict[str, object]) -> dict[str, object]:
    return {
        "slices": [item.model_dump(by_alias=True) for item in projection["slices"]],
        "theme_anchors": [item.model_dump(by_alias=True) for item in projection["theme_anchors"]],
        "packets": [item.model_dump(by_alias=True) for item in projection["packets"]],
    }


def _recompute_packet_identity(payload: dict[str, object]) -> dict[str, object]:
    lane_models = [
        HistoryODEULaneReconstruction.model_validate(item)
        for item in payload["lane_reconstructions"]
    ]
    semantic_hash = compute_history_odeu_packet_semantic_hash(
        source_id=payload["source_id"],
        slice_id=payload["slice_id"],
        theme_anchor_id=payload["theme_anchor_id"],
        lane_reconstructions=lane_models,
        semantic_identity_mode=payload.get(
            "semantic_identity_mode",
            "v54c_history_packet_hash_law",
        ),
    )
    payload["semantic_hash"] = semantic_hash
    payload["packet_id"] = compute_history_odeu_packet_id(semantic_hash=semantic_hash)
    return payload


@pytest.mark.parametrize(
    ("source_name", "fixture_name"),
    [
        ("reference_conversation_history_lf.txt", "reference_history_reconstruction.json"),
        (
            "assistant_local_explicit_history_lf.txt",
            "assistant_local_explicit_reconstruction.json",
        ),
        (
            "weak_underdetermined_history_lf.txt",
            "weak_underdetermined_reconstruction.json",
        ),
    ],
)
def test_v54c_projection_matches_committed_fixtures(
    source_name: str,
    fixture_name: str,
) -> None:
    projection = _build_projection(source_name)
    assert _projection_payload(projection) == _load_json(fixture_name)


def test_reference_fixture_proves_dialogical_mixed_role_replay() -> None:
    projection = _build_projection("reference_conversation_history_lf.txt")
    packets = projection["packets"]

    mixed_lanes = [
        lane
        for packet in packets
        for lane in packet.lane_reconstructions
        if lane.explicitation_status == "dialogically_explicitated"
        and lane.dominant_role_posture == "mixed"
    ]
    assert mixed_lanes
    assert any(
        lane.lane_id == "U"
        and lane.dominant_role_posture == "assistant_explication"
        and lane.presence_status == "weakly_present"
        for packet in packets
        for lane in packet.lane_reconstructions
    )


def test_assistant_only_fixture_proves_locally_explicit_replay() -> None:
    projection = _build_projection("assistant_local_explicit_history_lf.txt")
    packet = projection["packets"][0]

    assert all(
        lane.explicitation_status == "locally_explicit" for lane in packet.lane_reconstructions
    )
    assert all(
        lane.dominant_role_posture == "source_primary" for lane in packet.lane_reconstructions
    )


def test_weak_fixture_proves_weak_and_underdetermined_lanes() -> None:
    projection = _build_projection("weak_underdetermined_history_lf.txt")
    packet = projection["packets"][0]
    lanes = {lane.lane_id: lane for lane in packet.lane_reconstructions}

    assert lanes["O"].presence_status == "weakly_present"
    assert lanes["E"].presence_status == "weakly_present"
    assert lanes["D"].presence_status == "underdetermined"
    assert lanes["U"].presence_status == "underdetermined"
    assert lanes["D"].reconstruction_text is None
    assert lanes["U"].reconstruction_text is None
    assert not lanes["D"].evidence_refs
    assert not lanes["U"].evidence_refs


def test_absent_lane_synthesized_text_is_rejected() -> None:
    payload = copy.deepcopy(_load_json("weak_underdetermined_reconstruction.json")["packets"][0])
    payload["lane_reconstructions"][2]["reconstruction_text"] = "Synthesized absent lane text."

    with pytest.raises(ValidationError, match="absent lanes must omit reconstruction_text"):
        HistoryODEUReconstructionPacket.model_validate(payload)


def test_evidence_ref_grounding_must_match_released_ledger_text() -> None:
    projection = _build_projection("reference_conversation_history_lf.txt")
    payload = copy.deepcopy(projection["packets"][0].model_dump(by_alias=True))
    payload["lane_reconstructions"][0]["evidence_refs"][0]["excerpt"] = "Synthetic paraphrase."
    packet = HistoryODEUReconstructionPacket.model_validate(_recompute_packet_identity(payload))

    with pytest.raises(
        ValueError,
        match="evidence_ref excerpt must be present in the released ledger entry text",
    ):
        validate_history_odeu_reconstruction_packets(
            ledger=projection["ledger"],
            slices=projection["slices"],
            theme_anchors=projection["theme_anchors"],
            packets=[packet, *projection["packets"][1:]],
        )


def test_explicit_lane_evidence_refs_preserve_original_entry_substrings() -> None:
    projection = _build_projection_from_text(
        "\n".join(
            [
                "Assistant: o - Ontological lane keeps packet history bounded.",
                "e: Evidence lane keeps source provenance explicit.",
                "D - Deontic lane must preserve exact excerpts.",
                "u - Utility lane helps later bounded work.",
            ]
        ),
        source_label="explicit_lane_original_excerpt_history_lf.txt",
    )
    packet = projection["packets"][0]
    entry_text = projection["ledger"].entries[0].entry_text
    lanes = {lane.lane_id: lane for lane in packet.lane_reconstructions}

    assert (
        lanes["O"].evidence_refs[0].excerpt
        == "o - Ontological lane keeps packet history bounded."
    )
    assert (
        lanes["E"].evidence_refs[0].excerpt
        == "e: Evidence lane keeps source provenance explicit."
    )
    assert lanes["D"].evidence_refs[0].excerpt == "D - Deontic lane must preserve exact excerpts."
    assert lanes["U"].evidence_refs[0].excerpt == "u - Utility lane helps later bounded work."
    assert all(lane.evidence_refs[0].excerpt in entry_text for lane in lanes.values())


def test_missing_or_duplicate_lane_sets_are_rejected() -> None:
    missing_lane_payload = copy.deepcopy(
        _load_json("reference_history_reconstruction.json")["packets"][0]
    )
    missing_lane_payload["lane_reconstructions"] = missing_lane_payload["lane_reconstructions"][:3]

    with pytest.raises(
        ValidationError,
        match="lane_reconstructions must contain exactly one O/E/D/U lane",
    ):
        HistoryODEUReconstructionPacket.model_validate(missing_lane_payload)

    duplicate_lane_payload = copy.deepcopy(
        _load_json("reference_history_reconstruction.json")["packets"][0]
    )
    duplicate_lane_payload["lane_reconstructions"] = [
        duplicate_lane_payload["lane_reconstructions"][0],
        duplicate_lane_payload["lane_reconstructions"][0],
        duplicate_lane_payload["lane_reconstructions"][2],
        duplicate_lane_payload["lane_reconstructions"][3],
    ]

    with pytest.raises(
        ValidationError,
        match="lane_reconstructions must contain exactly one O/E/D/U lane",
    ):
        HistoryODEUReconstructionPacket.model_validate(duplicate_lane_payload)


def test_noncanonical_packet_identity_replay_is_rejected() -> None:
    payload = copy.deepcopy(_load_json("reference_history_reconstruction.json")["packets"][0])
    payload["packet_id"] = "history_packet:deadbeefdeadbeef"

    with pytest.raises(
        ValidationError,
        match="packet_id must match canonical packet identity",
    ):
        HistoryODEUReconstructionPacket.model_validate(payload)

    payload = copy.deepcopy(_load_json("reference_history_reconstruction.json")["packets"][0])
    payload["semantic_hash"] = "0" * 64

    with pytest.raises(
        ValidationError,
        match="semantic_hash must match canonical packet identity basis",
    ):
        HistoryODEUReconstructionPacket.model_validate(payload)


def test_reintegrated_summary_is_rejected_in_v54c() -> None:
    payload = copy.deepcopy(_load_json("reference_history_reconstruction.json")["packets"][0])
    payload["reintegrated_summary"] = "forbidden in v54c"

    with pytest.raises(ValidationError, match="Extra inputs are not permitted"):
        HistoryODEUReconstructionPacket.model_validate(payload)


def test_workspace_field_widening_is_rejected_in_v54c() -> None:
    payload = copy.deepcopy(_load_json("reference_history_reconstruction.json")["packets"][0])
    payload["workspace_snapshot"] = {"schema": "adeu_history_workspace_snapshot@1"}

    with pytest.raises(ValidationError, match="Extra inputs are not permitted"):
        HistoryODEUReconstructionPacket.model_validate(payload)
