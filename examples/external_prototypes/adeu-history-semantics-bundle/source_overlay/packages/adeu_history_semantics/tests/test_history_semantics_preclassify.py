from __future__ import annotations

from pathlib import Path

from adeu_history_semantics import build_history_ledger, build_history_source_artifact

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v0"


def _load_text(name: str) -> str:
    return (FIXTURE_ROOT / name).read_text(encoding="utf-8").rstrip("\n")


def test_conversation_preclassification_is_deterministic_and_turn_grouped() -> None:
    source = build_history_source_artifact(
        source_text=_load_text("demo_conversation_history_source.txt"),
        input_kind="conversation_history",
        source_label="conversation preclassification test",
    )

    first = build_history_ledger(source=source)
    second = build_history_ledger(source=source)

    assert first == second
    assert [entry.preclassification.role for entry in first.entries] == [
        "user",
        "assistant",
        "user",
        "assistant",
    ]
    assert [entry.preclassification.local_group_id for entry in first.entries] == [
        "turn:0000",
        "turn:0000",
        "turn:0001",
        "turn:0001",
    ]
    assert [
        entry.preclassification.suggested_slice_boundary_before for entry in first.entries
    ] == [False, False, True, False]

    assistant_entry = first.entries[1]
    assert assistant_entry.preclassification.origin_type == "assistant_reply"
    assert assistant_entry.preclassification.timestamp_text == "2026-02-02 10:02"
    assert assistant_entry.preclassification.source_declaration_hints == [
        "timestamp_header_detected"
    ]
    assert assistant_entry.preclassification.structural_markers == [
        "imperative_signal_present",
        "odeu_marker_present",
        "role_header_detected",
    ]
    assert assistant_entry.source_line_start == 2
    assert assistant_entry.source_line_end == 5
    assert assistant_entry.preclassification.text_shape_signals.line_count == 4
    assert assistant_entry.preclassification.text_shape_signals.word_count == 60


def test_external_paste_like_is_kept_as_a_preclassification_signal() -> None:
    pasted_history = """[2026-02-03 11:00] User: Here is pasted material:
> quoted claim
https://example.com/source
Second line of copied text.
[2026-02-03 11:05] Assistant: Thanks."""

    source = build_history_source_artifact(
        source_text=pasted_history,
        input_kind="conversation_history",
        source_label="external paste signal test",
    )
    ledger = build_history_ledger(source=source)

    user_entry = ledger.entries[0]
    assert user_entry.preclassification.role == "user"
    assert user_entry.preclassification.origin_type == "external_paste_like"
    assert user_entry.preclassification.source_declaration_hints == [
        "quote_marker_present",
        "timestamp_header_detected",
        "url_present",
    ]
    assert user_entry.preclassification.text_shape_signals.line_count == 4


def test_abstract_like_inputs_become_paragraph_entries() -> None:
    source = build_history_source_artifact(
        source_text=_load_text("demo_abstract_like_source.txt"),
        input_kind="abstract_like",
        source_label="abstract preclassification test",
    )
    ledger = build_history_ledger(source=source)

    assert [entry.unit_kind for entry in ledger.entries] == [
        "abstract_paragraph",
        "abstract_paragraph",
        "abstract_paragraph",
    ]
    assert [entry.preclassification.role for entry in ledger.entries] == [
        "unknown",
        "unknown",
        "unknown",
    ]
    assert [entry.preclassification.origin_type for entry in ledger.entries] == [
        "abstract_paragraph",
        "abstract_paragraph",
        "abstract_paragraph",
    ]
    assert [entry.preclassification.local_group_id for entry in ledger.entries] == [
        "abstract:0000",
        "abstract:0001",
        "abstract:0002",
    ]
    assert ledger.entries[0].preclassification.source_declaration_hints == [
        "abstract_header_present"
    ]
    assert ledger.entries[1].preclassification.structural_markers == [
        "odeu_marker_present"
    ]
