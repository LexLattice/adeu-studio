from __future__ import annotations

import re
from dataclasses import dataclass
from datetime import datetime

from .models import (
    SOURCE_AUTHORITY_POSTURE,
    HistoryPreclassification,
    HistorySourceArtifact,
    HistoryTextShapeSignals,
    compute_history_preclassification_id,
    compute_history_source_id,
    compute_source_text_hash,
)

_HEADER_RE = re.compile(
    r"^(?:\[(?P<timestamp>\d{4}-\d{2}-\d{2} \d{2}:\d{2})\] )?"
    r"(?P<role>User|Assistant|System):(?: (?P<body>.*))?$"
)
_HEADER_LIKE_RE = re.compile(
    r"^(?:\[[^\]]+\] )?(?:User|Assistant|System|U|A|S)\s*:",
    re.IGNORECASE,
)
_TIMESTAMP_TOKEN_RE = re.compile(r"\[\d{4}-\d{2}-\d{2} \d{2}:\d{2}\]")
_WORD_RE = re.compile(r"\b[\w'-]+\b")
_BULLET_RE = re.compile(r"^\s*(?:[-*•]|\d+[.)])\s+")
_QUOTE_RE = re.compile(r"^\s*>")


@dataclass(frozen=True)
class _ParsedMessage:
    order_index: int
    role: str
    timestamp_text: str | None
    message_text: str
    source_line_start: int
    source_line_end: int


def normalize_source_text(source_text: str) -> str:
    return source_text.replace("\r\n", "\n").replace("\r", "\n")


def build_history_source_artifact(
    *,
    source_text: str,
    input_kind: str = "conversation_history",
    source_label: str,
    corpus_wave_posture: str = "unassigned",
    source_authority_posture: str = SOURCE_AUTHORITY_POSTURE,
    source_notes: list[str] | None = None,
) -> HistorySourceArtifact:
    normalized_source_text = normalize_source_text(source_text)
    if input_kind == "conversation_history":
        _parse_conversation_history(normalized_source_text)
    source_text_hash = compute_source_text_hash(normalized_source_text)
    return HistorySourceArtifact(
        source_id=compute_history_source_id(
            input_kind=input_kind,
            source_text_hash=source_text_hash,
        ),
        input_kind=input_kind,
        source_label=source_label,
        source_text=normalized_source_text,
        source_text_hash=source_text_hash,
        corpus_wave_posture=corpus_wave_posture,
        source_authority_posture=source_authority_posture,
        source_notes=source_notes or [],
    )


def preclassify_history_source(*, source: HistorySourceArtifact) -> list[HistoryPreclassification]:
    parsed_messages = _parse_conversation_history(source.source_text)
    return [
        HistoryPreclassification(
            preclassification_id=compute_history_preclassification_id(
                source_id=source.source_id,
                order_index=parsed.order_index,
            ),
            source_id=source.source_id,
            order_index=parsed.order_index,
            message_text=parsed.message_text,
            source_line_start=parsed.source_line_start,
            source_line_end=parsed.source_line_end,
            role=_normalize_role(parsed.role),
            origin_type=_origin_type_for_role(parsed.role),
            source_declaration_hints=_source_declaration_hints(
                timestamp_text=parsed.timestamp_text,
            ),
            timestamp_text=parsed.timestamp_text,
            structural_markers=_structural_markers(parsed.message_text),
            text_shape_signals=_build_text_shape_signals(parsed.message_text),
        )
        for parsed in parsed_messages
    ]


def _parse_conversation_history(source_text: str) -> list[_ParsedMessage]:
    lines = source_text.splitlines()
    parsed_messages: list[_ParsedMessage] = []
    current_role: str | None = None
    current_timestamp: str | None = None
    current_start_line: int | None = None
    current_lines: list[str] = []

    def flush_current(end_line: int) -> None:
        nonlocal current_role, current_timestamp, current_start_line, current_lines
        if current_role is None or current_start_line is None:
            return
        message_text = "\n".join(current_lines)
        if not message_text.strip():
            raise ValueError(
                "conversation_history message starting at line "
                f"{current_start_line} must be non-empty"
            )
        parsed_messages.append(
            _ParsedMessage(
                order_index=len(parsed_messages),
                role=current_role,
                timestamp_text=current_timestamp,
                message_text=message_text,
                source_line_start=current_start_line,
                source_line_end=end_line,
            )
        )
        current_role = None
        current_timestamp = None
        current_start_line = None
        current_lines = []

    for line_number, line in enumerate(lines, start=1):
        header = _HEADER_RE.fullmatch(line)
        if header is not None:
            flush_current(line_number - 1)
            body = header.group("body") or ""
            _assert_no_disallowed_timestamp_material(
                body,
                line_number=line_number,
                context="header body",
            )
            timestamp_text = header.group("timestamp")
            if timestamp_text is not None:
                _validate_timestamp_prefix(timestamp_text, line_number=line_number)
            current_role = header.group("role")
            current_timestamp = timestamp_text
            current_start_line = line_number
            current_lines = [body]
            continue

        if current_role is None:
            raise ValueError(
                "conversation_history must start with an exact full role "
                f"header at line {line_number}"
            )
        _assert_continuation_line_is_in_domain(line, line_number=line_number)
        current_lines.append(line)

    flush_current(len(lines))
    if not parsed_messages:
        raise ValueError("conversation_history source must contain at least one message")
    return parsed_messages


def _assert_continuation_line_is_in_domain(line: str, *, line_number: int) -> None:
    _assert_no_disallowed_timestamp_material(
        line,
        line_number=line_number,
        context="continuation line",
    )
    if _HEADER_LIKE_RE.match(line) is not None:
        raise ValueError(
            f"unsupported or malformed role header placement at line {line_number}"
        )


def _assert_no_disallowed_timestamp_material(
    text: str,
    *,
    line_number: int,
    context: str,
) -> None:
    if _TIMESTAMP_TOKEN_RE.search(text) is not None or text.startswith("["):
        raise ValueError(f"unsupported timestamp placement in {context} at line {line_number}")


def _validate_timestamp_prefix(timestamp_text: str, *, line_number: int) -> None:
    try:
        parsed = datetime.strptime(timestamp_text, "%Y-%m-%d %H:%M")
    except ValueError as exc:
        raise ValueError(
            f"unsupported timestamp placement in header at line {line_number}"
        ) from exc
    if parsed.strftime("%Y-%m-%d %H:%M") != timestamp_text:
        raise ValueError(f"unsupported timestamp placement in header at line {line_number}")


def _normalize_role(role: str) -> str:
    return {
        "User": "user",
        "Assistant": "assistant",
        "System": "system",
    }[role]


def _origin_type_for_role(role: str) -> str:
    return {
        "User": "user_native",
        "Assistant": "assistant_reply",
        "System": "system_instruction",
    }[role]


def _source_declaration_hints(*, timestamp_text: str | None) -> list[str]:
    return [
        "full_role_header_present",
        "timestamp_prefix_present" if timestamp_text is not None else "timestamp_prefix_absent",
    ]


def _structural_markers(message_text: str) -> list[str]:
    lines = message_text.split("\n")
    markers: list[str] = [
        "single_line_message" if len(lines) == 1 else "multi_line_message",
    ]
    if any(not line.strip() for line in lines):
        markers.append("blank_line_present")
    if any(_BULLET_RE.match(line) is not None for line in lines):
        markers.append("bullet_line_present")
    if any(_QUOTE_RE.match(line) is not None for line in lines):
        markers.append("quoted_line_present")
    if "```" in message_text:
        markers.append("code_fence_present")
    if "?" in message_text:
        markers.append("question_mark_present")
    return markers


def _build_text_shape_signals(message_text: str) -> HistoryTextShapeSignals:
    lines = message_text.split("\n")
    return HistoryTextShapeSignals(
        char_count=len(message_text),
        word_count=len(_WORD_RE.findall(message_text)),
        line_count=len(lines),
        nonempty_line_count=sum(1 for line in lines if line.strip()),
        question_count=message_text.count("?"),
        bullet_line_count=sum(1 for line in lines if _BULLET_RE.match(line) is not None),
        quoted_line_count=sum(1 for line in lines if _QUOTE_RE.match(line) is not None),
        code_fence_count=message_text.count("```"),
    )


__all__ = [
    "build_history_source_artifact",
    "normalize_source_text",
    "preclassify_history_source",
]
