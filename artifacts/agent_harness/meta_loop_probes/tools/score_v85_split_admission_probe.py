#!/usr/bin/env python3
"""Score V85 split raw/canonical admission probe specimens."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Any

REQUIRED_BODY_KEYS = [
    "raw_semantic_pointer_candidate",
    "raw_operator_candidate",
    "raw_object_class_candidate",
    "raw_object_version_candidate",
    "canonical_semantic_pointer",
    "canonical_operator",
    "canonical_object_class",
    "canonical_object_version",
    "pointer_kind",
    "pointer_status",
    "canonical_admission_status",
    "canonical_lookup_status",
    "selection_status",
    "uncertainty_rows",
    "negative_cue_rows",
    "forbidden_inference_rows",
    "resident_model_competency_claim_rows",
    "detail_notes",
    "stop_posture",
]

ROW_KEYS = {
    "uncertainty_rows": {"uncertainty_ref", "uncertainty_kind", "field", "note"},
    "negative_cue_rows": {"negative_cue_ref", "cue_kind", "cue_text", "effect"},
    "forbidden_inference_rows": {"forbidden_inference_ref", "inference_kind", "note"},
    "resident_model_competency_claim_rows": {
        "competency_ref",
        "competency_kind",
        "claim_status",
    },
}

EXPECTED_COMPONENTS = {
    "known_full_pointer": {
        "raw_semantic_pointer_candidate": "CREATE ui.menu@v1",
        "raw_operator_candidate": "CREATE",
        "raw_object_class_candidate": "ui.menu",
        "raw_object_version_candidate": {"v1", "ui.menu@v1"},
        "canonical_semantic_pointer": "CREATE ui.menu@v1",
        "canonical_operator": "CREATE",
        "canonical_object_class": "ui.menu",
        "canonical_object_version": {"v1", "ui.menu@v1"},
    },
    "unknown_object_version": {
        "raw_semantic_pointer_candidate": "CREATE ui.toast@v3",
        "raw_operator_candidate": "CREATE",
        "raw_object_class_candidate": "ui.toast",
        "raw_object_version_candidate": {"v3", "ui.toast@v3"},
        "canonical_semantic_pointer": None,
        "canonical_operator": "CREATE",
        "canonical_object_class": None,
        "canonical_object_version": None,
    },
    "unknown_operator": {
        "raw_semantic_pointer_candidate": "FLORP ui.menu@v1",
        "raw_operator_candidate": "FLORP",
        "raw_object_class_candidate": "ui.menu",
        "raw_object_version_candidate": {"v1", "ui.menu@v1"},
        "canonical_semantic_pointer": None,
        "canonical_operator": None,
        "canonical_object_class": "ui.menu",
        "canonical_object_version": {"v1", "ui.menu@v1"},
    },
    "unknown_version": {
        "raw_semantic_pointer_candidate": "CREATE ui.menu@v99",
        "raw_operator_candidate": "CREATE",
        "raw_object_class_candidate": "ui.menu",
        "raw_object_version_candidate": {"v99", "ui.menu@v99"},
        "canonical_semantic_pointer": None,
        "canonical_operator": "CREATE",
        "canonical_object_class": "ui.menu",
        "canonical_object_version": None,
    },
}

REPAIR_REJECTION_FIELDS = {
    "unknown_object_version": {
        "forbidden": {
            "canonical_semantic_pointer": "CREATE ui.toast@v3",
            "canonical_object_class": "ui.menu",
            "canonical_object_version": "ui.menu@v1",
        }
    },
    "unknown_operator": {
        "forbidden": {
            "canonical_semantic_pointer": "CREATE ui.menu@v1",
            "canonical_operator": "CREATE",
        }
    },
    "unknown_version": {
        "forbidden": {
            "canonical_semantic_pointer": "CREATE ui.menu@v1",
            "canonical_object_version": "ui.menu@v1",
        }
    },
}


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        try:
            rows.append(json.loads(line))
        except json.JSONDecodeError as exc:
            raise SystemExit(f"{path}:{line_number}: invalid JSONL: {exc}") from exc
    return rows


def body_errors(body: Any) -> list[str]:
    if not isinstance(body, dict):
        return ["resident_body_not_object"]

    errors: list[str] = []
    if list(body.keys()) != REQUIRED_BODY_KEYS:
        errors.append("resident_body_key_order_or_set_mismatch")

    for row_field, required_keys in ROW_KEYS.items():
        rows = body.get(row_field)
        if not isinstance(rows, list):
            errors.append(f"{row_field}_not_array")
            continue
        if row_field == "resident_model_competency_claim_rows" and not rows:
            errors.append("resident_model_competency_claim_rows_missing_or_empty")
        for row in rows:
            if not isinstance(row, dict):
                errors.append(f"{row_field}_row_not_object")
                continue
            if set(row.keys()) != required_keys:
                errors.append(f"{row_field}_row_key_mismatch")
            if row_field == "resident_model_competency_claim_rows":
                if row.get("claim_status") != "claimed_for_this_artifact":
                    errors.append("competency_claim_status_mismatch")

    detail_notes = body.get("detail_notes")
    if not isinstance(detail_notes, list):
        errors.append("detail_notes_not_array")
    elif not all(isinstance(item, str) for item in detail_notes):
        errors.append("detail_notes_item_not_string")
    return errors


def matches(value: Any, expected: Any) -> bool:
    if isinstance(expected, set):
        return value in expected
    return value == expected


def component_errors(case_id: str, body: dict[str, Any]) -> list[str]:
    expected = EXPECTED_COMPONENTS.get(case_id)
    if expected is None:
        return ["unknown_case_id"]

    errors = []
    for field, expected_value in expected.items():
        if not matches(body.get(field), expected_value):
            errors.append(f"{field}_component_mismatch")

    repair_policy = REPAIR_REJECTION_FIELDS.get(case_id, {})
    for field, forbidden_value in repair_policy.get("forbidden", {}).items():
        if body.get(field) == forbidden_value:
            errors.append(f"{field}_forbidden_repair")

    return errors


def version_shape(body: dict[str, Any]) -> str:
    value = body.get("raw_object_version_candidate")
    if isinstance(value, str) and "@" in value:
        return "object_bound_version"
    if isinstance(value, str):
        return "version_token_only"
    return "not_string"


def score_probe(probe_dir: Path) -> dict[str, Any]:
    specimens = load_jsonl(probe_dir / "specimens.jsonl")
    counts: Counter[str] = Counter()
    results = []

    for specimen in specimens:
        specimen_id = specimen.get("specimen_id", "<unknown>")
        case_id = specimen.get("case_id", "<unknown>")
        body = specimen.get("raw_agent_body")
        filing_errors = body_errors(body)
        admission_errors = component_errors(case_id, body) if isinstance(body, dict) else []

        if not filing_errors:
            counts["strict_body_shape_pass"] += 1
        else:
            counts["strict_body_shape_remand"] += 1
            for error in filing_errors:
                counts[error] += 1

        if not admission_errors:
            counts["component_admission_pass"] += 1
        else:
            counts["component_admission_remand"] += 1
            for error in admission_errors:
                counts[error] += 1

        if isinstance(body, dict):
            counts[f"raw_version_shape_{version_shape(body)}"] += 1
            if body.get("canonical_semantic_pointer") is None or case_id == "known_full_pointer":
                counts["full_pointer_null_policy_pass"] += 1

        results.append(
            {
                "specimen_id": specimen_id,
                "case_id": case_id,
                "strict_body_shape_status": "pass" if not filing_errors else "remand_required",
                "component_admission_status": "pass"
                if not admission_errors
                else "remand_required",
                "filing_errors": filing_errors,
                "component_errors": admission_errors,
            }
        )

    return {
        "probe_dir": str(probe_dir),
        "specimen_count": len(specimens),
        "counts": dict(counts),
        "specimens": results,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("probe_dir", type=Path)
    args = parser.parse_args()
    print(json.dumps(score_probe(args.probe_dir), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
