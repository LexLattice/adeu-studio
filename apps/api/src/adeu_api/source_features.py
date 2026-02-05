from __future__ import annotations

import re

from adeu_ir.models import SourceFeatures

_MODALS = ("may", "shall", "will", "should", "must")

# Phrase -> canonical token.
_CONNECTIVE_PATTERNS: list[tuple[re.Pattern[str], str]] = [
    (re.compile(r"\bnotwithstanding\b", re.IGNORECASE), "notwithstanding"),
    (re.compile(r"\bsubject\s+to\b", re.IGNORECASE), "subject_to"),
    (re.compile(r"\bprovided\s+that\b", re.IGNORECASE), "provided_that"),
    (re.compile(r"\bunless\b", re.IGNORECASE), "unless"),
]

_TIME_VAGUENESS_PATTERNS: list[re.Pattern[str]] = [
    re.compile(r"\breasonable\s+time\b", re.IGNORECASE),
    re.compile(r"\bpromptly\b", re.IGNORECASE),
    re.compile(r"\bas\s+soon\s+as\s+practicable\b", re.IGNORECASE),
]


def extract_source_features(text: str) -> SourceFeatures:
    detected_modals: list[str] = []
    for modal in _MODALS:
        if re.search(rf"\b{re.escape(modal)}\b", text, re.IGNORECASE):
            detected_modals.append(modal)

    detected_connectives: list[str] = []
    for pat, token in _CONNECTIVE_PATTERNS:
        if pat.search(text):
            detected_connectives.append(token)

    has_time_vagueness = any(p.search(text) for p in _TIME_VAGUENESS_PATTERNS)

    return SourceFeatures(
        modals=detected_modals,
        connectives=detected_connectives,
        has_time_vagueness=has_time_vagueness,
    )
