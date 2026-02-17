from __future__ import annotations

import re
from itertools import combinations
from typing import Any

_ABSTRACT_HEADING_RE = re.compile(r"(?im)^\s*abstract\s*[:\-]?\s*$")
_INTRO_HEADING_RE = re.compile(r"(?im)^\s*(?:1[\.\)]?\s*)?introduction\b")
_CHECK_FAIL_CODE_MAP = {
    "min_words": "MIN_WORDS",
    "max_words": "MAX_WORDS",
}


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
    extract_result = _flow_extract_result(flow)
    value = extract_result.get("word_count")
    if isinstance(value, int):
        return value
    check_result = _flow_check_result(flow)
    value = check_result.get("word_count")
    if isinstance(value, int):
        return value
    return 0


def _flow_extract_result(flow: dict[str, Any]) -> dict[str, Any]:
    extract = flow.get("extract")
    if isinstance(extract, dict):
        result = extract.get("result")
        if isinstance(result, dict):
            return result
    return {}


def _flow_check_result(flow: dict[str, Any]) -> dict[str, Any]:
    check = flow.get("check")
    if isinstance(check, dict):
        result = check.get("result")
        if isinstance(result, dict):
            return result
    return {}


def _flow_candidate_hash(flow: dict[str, Any]) -> str:
    extract_result = _flow_extract_result(flow)
    value = extract_result.get("candidate_hash")
    if isinstance(value, str):
        return value
    return ""


def _flow_passes(flow: dict[str, Any]) -> bool:
    structural_passes = flow.get("structural_passes")
    if isinstance(structural_passes, bool):
        return structural_passes
    check_result = _flow_check_result(flow)
    value = check_result.get("passes")
    if isinstance(value, bool):
        return value
    value = flow.get("constraint_passes")
    return bool(value) if isinstance(value, bool) else False


def _flow_label(flow: dict[str, Any]) -> str:
    label = flow.get("label")
    return label if isinstance(label, str) else ""


def _flow_failures(flow: dict[str, Any]) -> list[str]:
    fail_codes = flow.get("fail_codes")
    if isinstance(fail_codes, list) and all(isinstance(code, str) for code in fail_codes):
        return [code.lower() for code in fail_codes]

    result = _flow_check_result(flow)
    if not result:
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


def _flow_artifact_id(flow: dict[str, Any]) -> str:
    emit = flow.get("emit")
    if isinstance(emit, dict):
        result = emit.get("result")
        if isinstance(result, dict):
            value = result.get("artifact_id")
            if isinstance(value, str):
                return value
    return ""


def _flow_abstract_text(flow: dict[str, Any]) -> str:
    extract_result = _flow_extract_result(flow)
    value = extract_result.get("abstract_text")
    return value if isinstance(value, str) else ""


def _shared_prefix_ratio(a: str, b: str) -> float:
    if not a or not b:
        return 0.0
    max_prefix = min(len(a), len(b))
    shared = 0
    while shared < max_prefix and a[shared] == b[shared]:
        shared += 1
    return shared / max_prefix


def build_flow_gate_diagnostics(
    *,
    extract_result: dict[str, Any],
    check_result: dict[str, Any],
    min_sentences: int = 2,
) -> dict[str, Any]:
    checks_raw = check_result.get("checks")
    checks = dict(sorted(checks_raw.items())) if isinstance(checks_raw, dict) else {}
    sentence_count = extract_result.get("sentence_count")
    sentence_count_int = sentence_count if isinstance(sentence_count, int) else 0
    candidate_date_like = bool(extract_result.get("candidate_date_like"))
    min_sentence_pass = sentence_count_int >= min_sentences

    fail_codes: list[str] = []
    for key in sorted(checks):
        if checks.get(key) is False:
            fail_codes.append(_CHECK_FAIL_CODE_MAP.get(key, str(key).upper()))
    if not min_sentence_pass:
        fail_codes.append("MIN_SENTENCES")
    if candidate_date_like:
        fail_codes.append("DATE_HEURISTIC")

    return {
        "gate_results": {
            "checks": checks,
            "passes": bool(check_result.get("passes")),
            "word_count": check_result.get("word_count"),
            "sentence_count": sentence_count_int,
            "candidate_date_like": candidate_date_like,
            "min_sentences_required": min_sentences,
            "min_sentences": min_sentence_pass,
        },
        "fail_codes": fail_codes,
        "structural_passes": len(fail_codes) == 0,
    }


def classify_flow_divergence(flows: list[dict[str, Any]]) -> tuple[bool, str]:
    artifact_ids = sorted(
        {
            artifact_id
            for artifact_id in (_flow_artifact_id(flow) for flow in flows)
            if artifact_id
        }
    )
    if len(artifact_ids) <= 1:
        return False, "none"
    if len(flows) < 2:
        return True, "major"

    pair_classes: list[str] = []
    for left, right in combinations(flows, 2):
        left_text = _flow_abstract_text(left)
        right_text = _flow_abstract_text(right)
        left_words = _flow_word_count(left)
        right_words = _flow_word_count(right)
        word_diff = abs(left_words - right_words)
        prefix_ratio = _shared_prefix_ratio(left_text, right_text)
        if left_text == right_text:
            pair_classes.append("minor")
        elif word_diff <= 10 and prefix_ratio >= 0.8:
            pair_classes.append("minor")
        else:
            pair_classes.append("major")
    if pair_classes and all(kind == "minor" for kind in pair_classes):
        return True, "minor"
    return True, "major"


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
