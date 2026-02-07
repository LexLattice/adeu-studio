from __future__ import annotations

import re
from typing import Any

_TOKEN_PATTERNS: dict[str, re.Pattern[str]] = {
    "has_implication": re.compile(r"\b(if|implies|therefore|entails)\b", re.IGNORECASE),
    "has_incompatibility": re.compile(
        r"\b(incompatible|cannot both|contradicts?|exclusive)\b", re.IGNORECASE
    ),
    "has_presupposition": re.compile(r"\b(presupposes?|assumes?)\b", re.IGNORECASE),
    "has_ambiguity_cue": re.compile(r"\b(could mean|ambiguous|either|or)\b", re.IGNORECASE),
    "has_negation": re.compile(r"\b(not|no|never|cannot|can't)\b", re.IGNORECASE),
}


def extract_concept_source_features(text: str) -> dict[str, Any]:
    lowered = text.lower()
    tokens = {token for token in re.findall(r"[a-z][a-z0-9_]*", lowered)}
    features = {name: bool(pattern.search(text)) for name, pattern in _TOKEN_PATTERNS.items()}
    features["token_count"] = len(tokens)
    features["line_count"] = max(1, text.count("\n") + 1)
    return features
