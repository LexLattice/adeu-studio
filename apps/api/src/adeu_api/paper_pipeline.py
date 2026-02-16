from __future__ import annotations

import re
from typing import Any

_ABSTRACT_HEADING_RE = re.compile(r"(?im)^\s*abstract\s*[:\-]?\s*$")
_INTRO_HEADING_RE = re.compile(r"(?im)^\s*(?:1[\.\)]?\s*)?introduction\b")


def derive_cleaned_source_text(raw_source_text: str) -> str:
    """Return deterministic cleaned source text for extraction fallback flow."""
    if not raw_source_text.strip():
        return raw_source_text
    abstract_match = _ABSTRACT_HEADING_RE.search(raw_source_text)
    if abstract_match is None:
        return raw_source_text
    start = abstract_match.start()
    tail = raw_source_text[start:]
    intro_match = _INTRO_HEADING_RE.search(tail)
    if intro_match is None:
        return tail.strip()
    return tail[: intro_match.start()].strip()


def _flow_word_count(flow: dict[str, Any]) -> int:
    extract = flow.get("extract")
    if isinstance(extract, dict):
        result = extract.get("result")
        if isinstance(result, dict):
            value = result.get("word_count")
            if isinstance(value, int):
                return value
    return 0


def _flow_candidate_hash(flow: dict[str, Any]) -> str:
    extract = flow.get("extract")
    if isinstance(extract, dict):
        result = extract.get("result")
        if isinstance(result, dict):
            value = result.get("candidate_hash")
            if isinstance(value, str):
                return value
    return ""


def _flow_passes(flow: dict[str, Any]) -> bool:
    check = flow.get("check")
    if isinstance(check, dict):
        result = check.get("result")
        if isinstance(result, dict):
            value = result.get("passes")
            if isinstance(value, bool):
                return value
    value = flow.get("constraint_passes")
    return bool(value) if isinstance(value, bool) else False


def _flow_label(flow: dict[str, Any]) -> str:
    label = flow.get("label")
    return label if isinstance(label, str) else ""


def _flow_failures(flow: dict[str, Any]) -> list[str]:
    check = flow.get("check")
    if not isinstance(check, dict):
        return ["missing_check"]
    result = check.get("result")
    if not isinstance(result, dict):
        return ["missing_check_result"]
    checks = result.get("checks")
    if not isinstance(checks, dict):
        return ["missing_checks"]
    failures: list[str] = []
    for key in sorted(checks):
        value = checks.get(key)
        if value is False:
            failures.append(str(key))
    return failures


def select_best_flow(flows: list[dict[str, Any]]) -> tuple[dict[str, Any], list[str]]:
    if not flows:
        raise ValueError("at least one flow is required")

    ranked = sorted(
        flows,
        key=lambda flow: (
            1 if _flow_passes(flow) else 0,
            _flow_word_count(flow),
            _flow_candidate_hash(flow),
            _flow_label(flow),
        ),
    )
    selected = ranked[-1]
    selected_label = _flow_label(selected) or "unknown"
    selected_passes = _flow_passes(selected)
    reasons: list[str] = []
    if selected_passes:
        reasons.append(f"{selected_label}:all_pass")
    else:
        reasons.append(f"{selected_label}:best_available")

    for flow in sorted(flows, key=_flow_label):
        if flow is selected:
            continue
        label = _flow_label(flow) or "unknown"
        failures = _flow_failures(flow)
        if failures:
            reasons.append(f"{label}:fail[{','.join(failures)}]")
        else:
            reasons.append(f"{label}:lower_rank")
    return selected, reasons
