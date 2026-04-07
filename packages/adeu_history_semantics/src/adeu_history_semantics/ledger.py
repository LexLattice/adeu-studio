from __future__ import annotations

import re
from collections.abc import Iterable
from typing import TypedDict

from .models import (
    ROLE_VOCABULARY,
    HistoryLedger,
    HistoryLedgerEntry,
    HistoryPreclassification,
    HistorySlice,
    HistoryThemeAnchor,
    compute_history_entry_text_hash,
    compute_history_ledger_entry_id,
    compute_history_ledger_id,
    compute_history_slice_id,
    compute_history_theme_anchor_id,
    compute_history_theme_key,
    compute_history_theme_label,
)

_THEME_TOKEN_SPLIT_RE = re.compile(r"[^a-z0-9]+")
_BOUNDARY_TAG_MARKER_MAP = (
    ("multi_line_message", "contains_multi_line_message"),
    ("blank_line_present", "contains_blank_line_present"),
    ("bullet_line_present", "contains_bullet_line_present"),
    ("quoted_line_present", "contains_quoted_line_present"),
    ("code_fence_present", "contains_code_fence_present"),
    ("question_mark_present", "contains_question_mark_present"),
)


class _ThemeAnchorAggregate(TypedDict):
    slice_ids: list[str]
    anchor_entry_ids: list[str]
    supporting_terms: list[str]
    display_label: str


def build_history_ledger(
    *,
    preclassifications: list[HistoryPreclassification],
) -> HistoryLedger:
    if not preclassifications:
        raise ValueError("preclassifications must be non-empty")
    source_ids = {item.source_id for item in preclassifications}
    if len(source_ids) != 1:
        raise ValueError("preclassifications must share one source_id")

    ordered_preclassifications = sorted(preclassifications, key=lambda item: item.order_index)
    order_indexes = [item.order_index for item in ordered_preclassifications]
    if len(set(order_indexes)) != len(order_indexes):
        raise ValueError("preclassifications must have unique order_index values")
    if order_indexes != list(range(len(ordered_preclassifications))):
        raise ValueError(
            "preclassifications must cover a contiguous order_index range starting at 0"
        )

    preclassification_ids = [item.preclassification_id for item in ordered_preclassifications]
    if len(set(preclassification_ids)) != len(preclassification_ids):
        raise ValueError("preclassifications must have unique preclassification_id values")

    source_id = ordered_preclassifications[0].source_id
    entries = [
        HistoryLedgerEntry(
            entry_id=compute_history_ledger_entry_id(
                source_id=source_id,
                preclassification_id=item.preclassification_id,
            ),
            source_id=source_id,
            preclassification_id=item.preclassification_id,
            order_index=item.order_index,
            entry_text=item.message_text,
            entry_text_hash=compute_history_entry_text_hash(item.message_text),
            role=item.role,
            origin_type=item.origin_type,
            source_line_start=item.source_line_start,
            source_line_end=item.source_line_end,
            structural_markers=item.structural_markers,
        )
        for item in ordered_preclassifications
    ]
    return HistoryLedger(
        ledger_id=compute_history_ledger_id(
            source_id=source_id,
            entry_ids=[entry.entry_id for entry in entries],
        ),
        source_id=source_id,
        entries=entries,
        entry_count=len(entries),
    )


def build_history_slices(*, ledger: HistoryLedger) -> list[HistorySlice]:
    if not ledger.entries:
        raise ValueError("ledger entries must be non-empty")

    slices: list[HistorySlice] = []
    run_start = 0
    entries = ledger.entries
    for index in range(1, len(entries) + 1):
        if index < len(entries) and entries[index].role == entries[run_start].role:
            continue
        run_entries = entries[run_start:index]
        theme_terms = _derive_theme_terms(entry.entry_text for entry in run_entries)
        if not theme_terms:
            raise ValueError("theme_terms must contain at least one lawful term")
        slice_index = len(slices)
        slices.append(
            HistorySlice(
                slice_id=compute_history_slice_id(
                    source_id=ledger.source_id,
                    slice_index=slice_index,
                    entry_ids=[entry.entry_id for entry in run_entries],
                ),
                source_id=ledger.source_id,
                slice_index=slice_index,
                entry_ids=[entry.entry_id for entry in run_entries],
                chronology_start_order_index=run_entries[0].order_index,
                chronology_end_order_index=run_entries[-1].order_index,
                boundary_tags=_derive_boundary_tags(
                    entries=run_entries,
                    total_entry_count=len(entries),
                ),
                theme_terms=theme_terms,
                theme_label=compute_history_theme_label(theme_terms=theme_terms),
                theme_key=compute_history_theme_key(theme_terms=theme_terms),
            )
        )
        run_start = index

    if not slices:
        raise ValueError("slices must be non-empty")
    return slices


def build_history_theme_anchors(
    *,
    ledger: HistoryLedger,
    slices: list[HistorySlice],
) -> list[HistoryThemeAnchor]:
    if not slices:
        raise ValueError("slices must be non-empty")

    ordered_slices = sorted(slices, key=lambda item: item.slice_index)
    if [item.slice_index for item in ordered_slices] != list(range(len(ordered_slices))):
        raise ValueError("slices must cover a contiguous slice_index range starting at 0")
    if any(item.source_id != ledger.source_id for item in ordered_slices):
        raise ValueError("slices must share the ledger source_id")

    grouped: dict[str, _ThemeAnchorAggregate] = {}
    for current_slice in ordered_slices:
        aggregate = grouped.setdefault(
            current_slice.theme_key,
            {
                "slice_ids": [],
                "anchor_entry_ids": [],
                "supporting_terms": [],
                "display_label": current_slice.theme_label,
            },
        )
        aggregate["slice_ids"] = _extend_unique_or_raise(
            aggregate["slice_ids"],
            [current_slice.slice_id],
            field_name="slice_ids",
        )
        aggregate["anchor_entry_ids"] = _extend_unique_or_raise(
            aggregate["anchor_entry_ids"],
            current_slice.entry_ids,
            field_name="anchor_entry_ids",
        )
        aggregate["supporting_terms"] = _ordered_unique(
            [*aggregate["supporting_terms"], *current_slice.theme_terms]
        )

    anchors = [
        HistoryThemeAnchor(
            theme_anchor_id=compute_history_theme_anchor_id(
                source_id=ledger.source_id,
                theme_key=theme_key,
                slice_ids=aggregate["slice_ids"],
            ),
            source_id=ledger.source_id,
            theme_key=theme_key,
            display_label=aggregate["display_label"],
            slice_ids=aggregate["slice_ids"],
            anchor_entry_ids=aggregate["anchor_entry_ids"],
            supporting_terms=aggregate["supporting_terms"],
        )
        for theme_key, aggregate in grouped.items()
    ]
    if not anchors:
        raise ValueError("theme anchors must be non-empty")
    return anchors


def _derive_boundary_tags(
    *,
    entries: list[HistoryLedgerEntry],
    total_entry_count: int,
) -> list[str]:
    boundary_tags: list[str] = []
    if entries[0].order_index == 0:
        boundary_tags.append("conversation_start")
    if entries[-1].order_index == total_entry_count - 1:
        boundary_tags.append("conversation_end")
    structural_markers = {
        marker
        for entry in entries
        for marker in entry.structural_markers
    }
    for structural_marker, boundary_tag in _BOUNDARY_TAG_MARKER_MAP:
        if structural_marker in structural_markers:
            boundary_tags.append(boundary_tag)
    return boundary_tags


def _derive_theme_terms(entry_texts: Iterable[str]) -> list[str]:
    seen: set[str] = set()
    ordered: list[str] = []
    for entry_text in entry_texts:
        for token in _THEME_TOKEN_SPLIT_RE.split(entry_text.lower()):
            if not token or token.isdigit() or len(token) < 4 or token in ROLE_VOCABULARY:
                continue
            if token in seen:
                continue
            seen.add(token)
            ordered.append(token)
    return ordered


def _ordered_unique(values: list[str]) -> list[str]:
    seen: set[str] = set()
    ordered: list[str] = []
    for value in values:
        if value in seen:
            continue
        seen.add(value)
        ordered.append(value)
    return ordered


def _extend_unique_or_raise(
    existing_values: list[str],
    new_values: Iterable[str],
    *,
    field_name: str,
) -> list[str]:
    seen = set(existing_values)
    ordered = list(existing_values)
    for value in new_values:
        if value in seen:
            raise ValueError(f"{field_name} must not contain duplicates during aggregation")
        seen.add(value)
        ordered.append(value)
    return ordered


__all__ = [
    "build_history_ledger",
    "build_history_slices",
    "build_history_theme_anchors",
]
