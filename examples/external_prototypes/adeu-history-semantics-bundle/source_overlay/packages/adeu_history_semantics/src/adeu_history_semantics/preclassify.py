from __future__ import annotations

import re
from dataclasses import dataclass

from .models import (
    HistoryLedger,
    HistoryLedgerEntry,
    HistoryPreclassification,
    HistorySourceArtifact,
    HistoryTextShapeSignals,
    compute_history_entry_id,
    compute_history_entry_text_hash,
    compute_history_ledger_id,
    compute_history_source_id,
    compute_source_text_hash,
)

_HEADER_RE = re.compile(
    r"^\s*(?:\[(?P<timestamp>[^\]]+)\]\s*)?(?P<role>User|Assistant|System)\s*:\s*(?P<body>.*)$",
    re.IGNORECASE,
)
_BULLET_RE = re.compile(r"^\s*(?:[-*•]|\d+[.)])\s+")
_QUOTE_RE = re.compile(r"^\s*>")
_URL_RE = re.compile(r"https?://|www\.")
_CITATION_RE = re.compile(r"\[[0-9,\s]+\]|\([A-Z][A-Za-z]+,\s*\d{4}\)")
_EXTERNAL_SOURCE_RE = re.compile(
    r"\b(according to|source:|quoted from|from the paper|from the article)\b",
    re.IGNORECASE,
)
_ABSTRACT_HEADER_RE = re.compile(r"^\s*abstract\b", re.IGNORECASE)
_ODEU_MARKER_RE = re.compile(r"(?m)^\s*[OEDU]\s*[:\-]|\bodeu\b", re.IGNORECASE)
_DEFINITION_RE = re.compile(
    r"\b(is a|is an|is the|means|defined as|treat(?:s|ed)? as)\b",
    re.IGNORECASE,
)
_IMPERATIVE_RE = re.compile(
    r"\b(must|should|need to|keep|preserve|prefer|ensure)\b",
    re.IGNORECASE,
)
_NEGATION_RE = re.compile(r"\b(do not|must not|forbidden|not allowed|never)\b", re.IGNORECASE)
_SENTENCE_RE = re.compile(r"(?<=[.!?])\s+")


@dataclass(frozen=True)
class _RawBlock:
    unit_kind: str
    role: str
    timestamp_text: str | None
    text: str
    start_line: int
    end_line: int
    order_index: int
    local_group_id: str
    suggested_slice_boundary_before: bool
    role_header_detected: bool


def build_history_source_artifact(
    *,
    source_text: str,
    input_kind: str,
    source_label: str | None = None,
    corpus_wave_posture: str = "unassigned",
    source_notes: list[str] | None = None,
) -> HistorySourceArtifact:
    normalized_text = _normalize_source_text(source_text)
    resolved_label = source_label or (
        "Conversation history source"
        if input_kind == "conversation_history"
        else "Abstract-like source"
    )
    text_hash = compute_source_text_hash(normalized_text)
    return HistorySourceArtifact(
        source_id=compute_history_source_id(input_kind=input_kind, source_text_hash=text_hash),
        input_kind=input_kind,
        source_label=resolved_label,
        source_text=normalized_text,
        source_text_hash=text_hash,
        corpus_wave_posture=corpus_wave_posture,
        source_notes=source_notes or [],
    )


def build_history_ledger(*, source: HistorySourceArtifact) -> HistoryLedger:
    if source.input_kind == "conversation_history":
        blocks = _parse_conversation_blocks(source.source_text)
    else:
        blocks = _parse_abstract_blocks(source.source_text)

    entries: list[HistoryLedgerEntry] = []
    for block in blocks:
        shape_signals = _build_shape_signals(block.text)
        hints = _detect_source_hints(
            block.text,
            timestamp_present=block.timestamp_text is not None,
            input_kind=source.input_kind,
        )
        markers = _detect_structural_markers(
            block.text,
            role_header_detected=block.role_header_detected,
        )
        preclassification = HistoryPreclassification(
            role=block.role,
            origin_type=_classify_origin_type(
                role=block.role,
                unit_kind=block.unit_kind,
                text=block.text,
                shape_signals=shape_signals,
                source_declaration_hints=hints,
            ),
            source_declaration_hints=hints,
            timestamp_text=block.timestamp_text,
            structural_markers=markers,
            text_shape_signals=shape_signals,
            local_group_id=block.local_group_id,
            suggested_slice_boundary_before=block.suggested_slice_boundary_before,
            order_index=block.order_index,
        )
        entry_hash = compute_history_entry_text_hash(block.text)
        entry = HistoryLedgerEntry(
            entry_id=compute_history_entry_id(
                source_id=source.source_id,
                unit_kind=block.unit_kind,
                order_index=block.order_index,
                entry_text_hash=entry_hash,
            ),
            source_id=source.source_id,
            unit_kind=block.unit_kind,
            entry_text=block.text,
            entry_text_hash=entry_hash,
            source_line_start=block.start_line,
            source_line_end=block.end_line,
            preclassification=preclassification,
        )
        entries.append(entry)

    ledger_id = compute_history_ledger_id(
        source_id=source.source_id,
        entry_ids=[entry.entry_id for entry in entries],
    )
    return HistoryLedger(
        ledger_id=ledger_id,
        source_id=source.source_id,
        input_kind=source.input_kind,
        entries=entries,
        entry_count=len(entries),
    )


def _normalize_source_text(source_text: str) -> str:
    return source_text.replace("\r\n", "\n").replace("\r", "\n")


def _normalize_entry_text(text: str) -> str:
    normalized = text.replace("\r\n", "\n").replace("\r", "\n")
    lines = [line.rstrip() for line in normalized.split("\n")]
    return "\n".join(lines).strip()


def _normalize_role(role_text: str) -> str:
    lowered = role_text.casefold()
    if lowered in {"user", "u"}:
        return "user"
    if lowered in {"assistant", "a"}:
        return "assistant"
    if lowered in {"system", "s"}:
        return "system"
    return "unknown"


def _parse_conversation_blocks(text: str) -> list[_RawBlock]:
    lines = text.split("\n")
    has_headers = any(_HEADER_RE.match(line) is not None for line in lines)
    if not has_headers:
        return _parse_unclassified_conversation_blocks(text)

    temp_blocks: list[tuple[str, str | None, str, int, int, bool]] = []
    current_role = "unknown"
    current_timestamp: str | None = None
    current_lines: list[str] = []
    current_start_line: int | None = None
    current_header_detected = False
    preamble_lines: list[tuple[int, str]] = []

    def flush_preamble() -> None:
        nonlocal preamble_lines
        if not preamble_lines:
            return
        text_block = _normalize_entry_text("\n".join(line for _, line in preamble_lines))
        if text_block:
            temp_blocks.append(
                (
                    "unknown",
                    None,
                    text_block,
                    preamble_lines[0][0],
                    preamble_lines[-1][0],
                    False,
                )
            )
        preamble_lines = []

    def flush_current(end_line: int) -> None:
        nonlocal current_start_line, current_lines, current_role, current_timestamp
        if current_start_line is None:
            return
        text_block = _normalize_entry_text("\n".join(current_lines))
        if text_block:
            temp_blocks.append(
                (
                    current_role,
                    current_timestamp,
                    text_block,
                    current_start_line,
                    end_line,
                    current_header_detected,
                )
            )
        current_role = "unknown"
        current_timestamp = None
        current_lines = []
        current_start_line = None

    for line_number, line in enumerate(lines, start=1):
        header = _HEADER_RE.match(line)
        if header is not None:
            flush_preamble()
            flush_current(line_number - 1)
            current_role = _normalize_role(header.group("role"))
            current_timestamp = header.group("timestamp")
            current_lines = [header.group("body") or ""]
            current_start_line = line_number
            current_header_detected = True
            continue
        if current_start_line is None:
            preamble_lines.append((line_number, line))
        else:
            current_lines.append(line)

    flush_preamble()
    flush_current(len(lines))

    user_present = any(role == "user" for role, _, _, _, _, _ in temp_blocks)
    blocks: list[_RawBlock] = []
    turn_index = -1
    for order_index, (
        role,
        timestamp,
        block_text,
        start_line,
        end_line,
        header_detected,
    ) in enumerate(temp_blocks):
        if user_present:
            boundary_before = False
            if role == "user":
                turn_index += 1
                boundary_before = turn_index > 0
            elif turn_index < 0:
                turn_index = 0
            local_group_id = f"turn:{turn_index:04d}"
        else:
            local_group_id = f"conversation:{order_index:04d}"
            boundary_before = order_index > 0
        blocks.append(
            _RawBlock(
                unit_kind="message" if header_detected else "conversation_block",
                role=role,
                timestamp_text=timestamp,
                text=block_text,
                start_line=start_line,
                end_line=end_line,
                order_index=order_index,
                local_group_id=local_group_id,
                suggested_slice_boundary_before=boundary_before,
                role_header_detected=header_detected,
            )
        )
    return blocks


def _parse_unclassified_conversation_blocks(text: str) -> list[_RawBlock]:
    lines = text.split("\n")
    paragraphs = _split_nonempty_line_groups(lines)
    blocks: list[_RawBlock] = []
    for order_index, (start_line, end_line, paragraph_lines) in enumerate(paragraphs):
        paragraph_text = _normalize_entry_text("\n".join(paragraph_lines))
        if not paragraph_text:
            continue
        blocks.append(
            _RawBlock(
                unit_kind="conversation_block",
                role="unknown",
                timestamp_text=None,
                text=paragraph_text,
                start_line=start_line,
                end_line=end_line,
                order_index=order_index,
                local_group_id=f"conversation:{order_index:04d}",
                suggested_slice_boundary_before=order_index > 0,
                role_header_detected=False,
            )
        )
    return blocks


def _parse_abstract_blocks(text: str) -> list[_RawBlock]:
    lines = text.split("\n")
    paragraphs = _split_nonempty_line_groups(lines)
    blocks: list[_RawBlock] = []
    for order_index, (start_line, end_line, paragraph_lines) in enumerate(paragraphs):
        paragraph_text = _normalize_entry_text("\n".join(paragraph_lines))
        if not paragraph_text:
            continue
        blocks.append(
            _RawBlock(
                unit_kind="abstract_paragraph",
                role="unknown",
                timestamp_text=None,
                text=paragraph_text,
                start_line=start_line,
                end_line=end_line,
                order_index=order_index,
                local_group_id=f"abstract:{order_index:04d}",
                suggested_slice_boundary_before=order_index > 0,
                role_header_detected=False,
            )
        )
    return blocks


def _split_nonempty_line_groups(lines: list[str]) -> list[tuple[int, int, list[str]]]:
    groups: list[tuple[int, int, list[str]]] = []
    current_start: int | None = None
    current_lines: list[str] = []
    for line_number, line in enumerate(lines, start=1):
        if line.strip():
            if current_start is None:
                current_start = line_number
            current_lines.append(line)
            continue
        if current_start is not None and current_lines:
            groups.append((current_start, line_number - 1, current_lines))
            current_start = None
            current_lines = []
    if current_start is not None and current_lines:
        groups.append((current_start, len(lines), current_lines))
    if not groups and lines:
        groups.append((1, len(lines), lines))
    return groups


def _build_shape_signals(text: str) -> HistoryTextShapeSignals:
    lines = text.split("\n") if text else []
    bullets = sum(1 for line in lines if _BULLET_RE.match(line) is not None)
    quoted = sum(1 for line in lines if _QUOTE_RE.match(line) is not None)
    code_fence_count = text.count("```")
    words = re.findall(r"\b[\w'-]+\b", text)
    sentences = [chunk for chunk in _SENTENCE_RE.split(text) if chunk.strip()]
    if not sentences and text.strip():
        sentences = [text.strip()]
    return HistoryTextShapeSignals(
        char_count=len(text),
        word_count=len(words),
        sentence_count=len(sentences),
        line_count=len(lines) if lines else 1,
        question_count=text.count("?"),
        bullet_line_count=bullets,
        quoted_line_count=quoted,
        code_fence_count=code_fence_count,
    )


def _detect_source_hints(
    text: str,
    *,
    timestamp_present: bool,
    input_kind: str,
) -> list[str]:
    hints: list[str] = []
    if timestamp_present:
        hints.append("timestamp_header_detected")
    if "```" in text:
        hints.append("code_fence_present")
    if any(_QUOTE_RE.match(line) is not None for line in text.split("\n")) or '"' in text:
        hints.append("quote_marker_present")
    if _URL_RE.search(text) is not None:
        hints.append("url_present")
    if _CITATION_RE.search(text) is not None:
        hints.append("citation_marker_present")
    if _EXTERNAL_SOURCE_RE.search(text) is not None:
        hints.append("external_source_phrase_present")
    if input_kind == "abstract_like" or _ABSTRACT_HEADER_RE.match(text) is not None:
        hints.append("abstract_header_present")
    return hints


def _detect_structural_markers(text: str, *, role_header_detected: bool) -> list[str]:
    markers: list[str] = []
    if role_header_detected:
        markers.append("role_header_detected")
    if "?" in text:
        markers.append("question_mark_present")
    if _IMPERATIVE_RE.search(text) is not None:
        markers.append("imperative_signal_present")
    if sum(1 for line in text.split("\n") if _BULLET_RE.match(line) is not None) >= 1:
        markers.append("list_like_lines_present")
    if _ODEU_MARKER_RE.search(text) is not None:
        markers.append("odeu_marker_present")
    if _DEFINITION_RE.search(text) is not None:
        markers.append("definition_pattern_present")
    if _NEGATION_RE.search(text) is not None:
        markers.append("negation_guard_present")
    return markers


def _classify_origin_type(
    *,
    role: str,
    unit_kind: str,
    text: str,
    shape_signals: HistoryTextShapeSignals,
    source_declaration_hints: list[str],
) -> str:
    if unit_kind == "abstract_paragraph":
        return "abstract_paragraph"
    if role == "assistant":
        return "assistant_reply"
    if role == "system":
        return "system_instruction"
    if role == "user":
        looks_pasted = (
            shape_signals.char_count >= 500
            or shape_signals.line_count >= 5
            or "quote_marker_present" in source_declaration_hints
            or "code_fence_present" in source_declaration_hints
            or "url_present" in source_declaration_hints
        )
        return "external_paste_like" if looks_pasted else "user_native"
    if "quote_marker_present" in source_declaration_hints or shape_signals.line_count >= 5:
        return "external_paste_like"
    return "unclassified_block"


__all__ = [
    "build_history_ledger",
    "build_history_source_artifact",
]
