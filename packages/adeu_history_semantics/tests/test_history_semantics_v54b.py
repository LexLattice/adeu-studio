from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_history_semantics import (
    HistorySourceArtifact,
    build_history_ledger,
    build_history_slices,
    build_history_source_artifact,
    build_history_theme_anchors,
    compute_history_slice_id,
    preclassify_history_source,
)

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v54b"


def _load_text(name: str) -> str:
    return (FIXTURE_ROOT / name).read_bytes().decode("utf-8")


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _build_source(
    *,
    source_text: str,
    source_label: str = "v54b fixture",
) -> HistorySourceArtifact:
    return build_history_source_artifact(
        source_text=source_text,
        source_label=source_label,
        corpus_wave_posture="wave_0_bootstrap_candidate",
        source_notes=[
            "v54b_fixture",
        ],
    )


def _build_projection(source_text: str) -> dict[str, object]:
    source = _build_source(source_text=source_text)
    preclassifications = preclassify_history_source(source=source)
    ledger = build_history_ledger(preclassifications=preclassifications)
    slices = build_history_slices(ledger=ledger)
    theme_anchors = build_history_theme_anchors(ledger=ledger, slices=slices)
    return {
        "source": source,
        "preclassifications": preclassifications,
        "ledger": ledger,
        "slices": slices,
        "theme_anchors": theme_anchors,
    }


def test_reference_projection_matches_committed_fixture() -> None:
    projection = _build_projection(_load_text("reference_conversation_history_lf.txt"))

    expected_payload = _load_json("reference_history_projection.json")
    actual_payload = {
        "ledger": projection["ledger"].model_dump(by_alias=True),
        "slices": [item.model_dump(by_alias=True) for item in projection["slices"]],
        "theme_anchors": [
            item.model_dump(by_alias=True) for item in projection["theme_anchors"]
        ],
    }

    assert actual_payload == expected_payload


def test_consecutive_same_speaker_chronology_does_not_merge_entries() -> None:
    projection = _build_projection(_load_text("consecutive_same_speaker_history_lf.txt"))

    preclassifications = projection["preclassifications"]
    ledger = projection["ledger"]
    slices = projection["slices"]
    theme_anchors = projection["theme_anchors"]

    assert len(preclassifications) == 4
    assert len(ledger.entries) == 4
    assert [entry.preclassification_id for entry in ledger.entries] == [
        item.preclassification_id for item in preclassifications
    ]
    assert [len(item.entry_ids) for item in slices] == [2, 2]
    assert [item.theme_key for item in slices] == [
        "alpha::planning::roadmap::status::ledger",
        "alpha::planning::roadmap::status::ledger",
    ]
    assert len(theme_anchors) == 1
    assert theme_anchors[0].slice_ids == [item.slice_id for item in slices]
    assert theme_anchors[0].supporting_terms == [
        "alpha",
        "planning",
        "roadmap",
        "status",
        "ledger",
        "update",
        "confirmed",
        "locked",
    ]


def test_quoted_or_fenced_multiline_content_stays_inside_one_entry() -> None:
    projection = _build_projection(_load_text("quoted_multiline_history_lf.txt"))

    preclassifications = projection["preclassifications"]
    ledger = projection["ledger"]
    slices = projection["slices"]

    assert len(preclassifications) == 2
    assert preclassifications[0].source_line_start == 1
    assert preclassifications[0].source_line_end == 5
    assert preclassifications[0].structural_markers == [
        "multi_line_message",
        "quoted_line_present",
        "code_fence_present",
    ]
    assert "> Assistant: keep role parsing bounded." in ledger.entries[0].entry_text
    assert "```text" in ledger.entries[0].entry_text
    assert slices[0].entry_ids == [ledger.entries[0].entry_id]
    assert "contains_quoted_line_present" in slices[0].boundary_tags
    assert "contains_code_fence_present" in slices[0].boundary_tags


def test_degenerate_input_with_no_lawful_theme_terms_fails_closed() -> None:
    source = _build_source(source_text=_load_text("reject_no_lawful_theme_terms.txt"))
    preclassifications = preclassify_history_source(source=source)
    ledger = build_history_ledger(preclassifications=preclassifications)

    with pytest.raises(ValueError, match="theme_terms must contain at least one lawful term"):
        build_history_slices(ledger=ledger)


def test_out_of_domain_shorthand_rejection_still_holds() -> None:
    with pytest.raises(ValueError, match="unsupported or malformed role header placement"):
        _build_source(source_text=_load_text("reject_shorthand_aliases.txt"))


def test_theme_anchor_aggregation_rejects_overlapping_entry_ids() -> None:
    projection = _build_projection(_load_text("consecutive_same_speaker_history_lf.txt"))
    ledger = projection["ledger"]
    slices = projection["slices"]

    overlapping_slice = slices[0].model_copy(
        update={
            "slice_id": compute_history_slice_id(
                source_id=ledger.source_id,
                slice_index=1,
                entry_ids=slices[0].entry_ids,
            ),
            "slice_index": 1,
            "chronology_start_order_index": 1,
            "chronology_end_order_index": 1,
        }
    )

    with pytest.raises(ValueError, match="anchor_entry_ids must not contain duplicates"):
        build_history_theme_anchors(
            ledger=ledger,
            slices=[slices[0], overlapping_slice],
        )
