from __future__ import annotations

from collections.abc import Sequence

from adeu_ir import SourceSpan, stable_id


def _normalize_primary_text(value: str) -> str:
    return " ".join(value.split()).strip().lower()


def _canonical_span_pairs(
    spans: Sequence[SourceSpan | dict[str, int]] | None,
) -> list[tuple[int, int]]:
    if not spans:
        return []
    pairs: set[tuple[int, int]] = set()
    for raw_span in spans:
        span = raw_span if isinstance(raw_span, SourceSpan) else SourceSpan.model_validate(raw_span)
        pairs.add((span.start, span.end))
    ordered_pairs = sorted(pairs)
    merged_pairs: list[tuple[int, int]] = []
    for start, end in ordered_pairs:
        if not merged_pairs:
            merged_pairs.append((start, end))
            continue
        prev_start, prev_end = merged_pairs[-1]
        if start <= prev_end:
            merged_pairs[-1] = (prev_start, max(prev_end, end))
            continue
        merged_pairs.append((start, end))
    return merged_pairs


def stable_core_node_id(
    *,
    layer: str,
    kind: str,
    primary_text_or_label: str,
    source_text_hash: str,
    spans: Sequence[SourceSpan | dict[str, int]] | None = None,
    prefix: str = "core",
) -> str:
    canonical_text = _normalize_primary_text(primary_text_or_label)
    canonical_spans = _canonical_span_pairs(spans)
    span_part = ",".join(f"{start}:{end}" for start, end in canonical_spans) or "-"
    return stable_id(
        layer,
        kind,
        canonical_text,
        span_part,
        source_text_hash,
        prefix=prefix,
    )
