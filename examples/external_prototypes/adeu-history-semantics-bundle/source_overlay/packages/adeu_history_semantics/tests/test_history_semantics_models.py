from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest
from adeu_history_semantics import HistorySemanticBundle
from pydantic import ValidationError

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v0"


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def test_reference_bundles_validate() -> None:
    conversation_bundle = HistorySemanticBundle.model_validate(
        _load_json("reference_history_semantic_bundle_conversation.json")
    )
    abstract_bundle = HistorySemanticBundle.model_validate(
        _load_json("reference_history_semantic_bundle_abstract.json")
    )

    assert conversation_bundle.source.corpus_wave_posture == "wave_0_bootstrap_candidate"
    assert abstract_bundle.source.input_kind == "abstract_like"
    assert abstract_bundle.workspace_snapshot.semantic_identity_mode == (
        "adeu_history_semantics_v0_hash_law"
    )


def test_projection_only_source_mutation_preserves_bundle_identity() -> None:
    payload = copy.deepcopy(_load_json("reference_history_semantic_bundle_conversation.json"))
    assert isinstance(payload, dict)

    payload["source"]["source_label"] = "Renamed demo conversation history fixture"
    payload["source"]["source_notes"] = [
        "additional projection-only note",
        *payload["source"]["source_notes"],
    ]

    mutated = HistorySemanticBundle.model_validate(payload)
    reference = HistorySemanticBundle.model_validate(
        _load_json("reference_history_semantic_bundle_conversation.json")
    )

    assert mutated.source.source_id == reference.source.source_id
    assert mutated.bundle_id == reference.bundle_id
    assert mutated.workspace_snapshot.workspace_snapshot_id == (
        reference.workspace_snapshot.workspace_snapshot_id
    )


def test_source_text_identity_mutation_fails_closed() -> None:
    payload = copy.deepcopy(_load_json("reference_history_semantic_bundle_conversation.json"))
    assert isinstance(payload, dict)

    payload["source"]["source_text"] = "mutated source text that no longer matches the hash"

    with pytest.raises(ValidationError):
        HistorySemanticBundle.model_validate(payload)


def test_absent_lane_with_evidence_refs_is_rejected() -> None:
    payload = copy.deepcopy(_load_json("reference_history_semantic_bundle_abstract.json"))
    assert isinstance(payload, dict)

    absent_lane = payload["reconstruction_packets"][1]["lane_reconstructions"][2]
    absent_lane["evidence_refs"] = [
        {
            "schema": "adeu_history_evidence_ref@1",
            "entry_id": payload["ledger"]["entries"][2]["entry_id"],
            "role": payload["ledger"]["entries"][2]["preclassification"]["role"],
            "excerpt": "Synthetic illicit evidence ref.",
        }
    ]

    with pytest.raises(ValidationError):
        HistorySemanticBundle.model_validate(payload)


def test_provenance_refs_remain_grounded_in_ledger_entries() -> None:
    bundle = HistorySemanticBundle.model_validate(
        _load_json("reference_history_semantic_bundle_conversation.json")
    )
    entry_lookup = {entry.entry_id: entry for entry in bundle.ledger.entries}

    for packet in bundle.reconstruction_packets:
        for lane in packet.lane_reconstructions:
            for evidence_ref in lane.evidence_refs:
                entry_text = entry_lookup[evidence_ref.entry_id].entry_text
                assert evidence_ref.excerpt.rstrip(".") in entry_text

    for frame in bundle.workspace_snapshot.theme_frames:
        assert set(frame.provenance_entry_ids)
        assert set(frame.provenance_entry_ids) <= set(entry_lookup)
