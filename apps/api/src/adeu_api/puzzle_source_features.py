from __future__ import annotations

import re
from typing import Any

_NEGATION_PATTERNS = [
    re.compile(r"\bnot\b", re.IGNORECASE),
    re.compile(r"\bfalse\b", re.IGNORECASE),
    re.compile(r"\bliar\b", re.IGNORECASE),
    re.compile(r"\blying\b", re.IGNORECASE),
    re.compile(r"\bknave\b", re.IGNORECASE),
]

_EXACTLY_ONE_PATTERNS = [
    re.compile(r"\bexactly\s+one\b", re.IGNORECASE),
    re.compile(r"\bonly\s+one\b", re.IGNORECASE),
]

_SELF_REFERENCE_PATTERNS = [
    re.compile(r"\bi\s+am\b", re.IGNORECASE),
    re.compile(r"\bthis\s+statement\b", re.IGNORECASE),
    re.compile(r"\bmy\s+statement\b", re.IGNORECASE),
]

_SPEAKER_TOKEN = re.compile(r"\b([A-HJ-Z])\b")


def extract_puzzle_source_features(text: str) -> dict[str, Any]:
    speaker_tokens = {match.group(1).upper() for match in _SPEAKER_TOKEN.finditer(text)}
    return {
        "mentions_knight": bool(re.search(r"\bknight\b", text, re.IGNORECASE)),
        "mentions_knave": bool(re.search(r"\bknave\b", text, re.IGNORECASE)),
        "has_negation": any(pattern.search(text) for pattern in _NEGATION_PATTERNS),
        "has_exactly_one": any(pattern.search(text) for pattern in _EXACTLY_ONE_PATTERNS),
        "count_speakers_guess": len(speaker_tokens),
        "has_self_reference": any(pattern.search(text) for pattern in _SELF_REFERENCE_PATTERNS),
    }
