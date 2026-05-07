#!/usr/bin/env python3
"""Score V85 closed-option branch-selection probe specimens."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Any


REQUIRED_KEYS = [
    "raw_semantic_pointer_candidate",
    "raw_operator_candidate",
    "raw_object_class_candidate",
    "raw_object_version_token_candidate",
    "raw_object_version_ref_candidate",
    "operator_admission_branch",
    "object_admission_branch",
    "version_ref_admission_branch",
    "full_pointer_admission_branch",
    "branch_selection_status",
    "contradiction_check_rows",
    "negative_cue_rows",
    "forbidden_inference_rows",
    "resident_model_competency_claim_rows",
    "detail_notes",
    "stop_posture",
]

ROW_KEYS = {
    "contradiction_check_rows": {
        "contradiction_check_ref",
        "checked_field",
        "selected_branch",
        "prose_alignment",
        "note",
    },
    "negative_cue_rows": {"negative_cue_ref", "cue_kind", "cue_text", "effect"},
    "forbidden_inference_rows": {"forbidden_inference_ref", "inference_kind", "note"},
    "resident_model_competency_claim_rows": {
        "competency_ref",
        "competency_kind",
        "claim_status",
    },
}

EXPECTED = {
    "raw_semantic_pointer_candidate": "FLORP ui.menu@v1",
    "raw_operator_candidate": "FLORP",
    "raw_object_class_candidate": "ui.menu",
    "raw_object_version_token_candidate": "v1",
    "raw_object_version_ref_candidate": "ui.menu@v1",
    "operator_admission_branch": "OP_B",
    "object_admission_branch": "OBJ_A",
    "version_ref_admission_branch": "VER_A",
    "full_pointer_admission_branch": "PTR_C",
    "branch_selection_status": "branch_selection_complete",
    "stop_posture": "stop_after_branch_selection",
}

RAW_FIELDS = [
    "raw_semantic_pointer_candidate",
    "raw_operator_candidate",
    "raw_object_class_candidate",
    "raw_object_version_token_candidate",
    "raw_object_version_ref_candidate",
]

BRANCH_FIELDS = [
    "operator_admission_branch",
    "object_admission_branch",
    "version_ref_admission_branch",
    "full_pointer_admission_branch",
]

STATUS_FIELDS = [
    "branch_selection_status",
    "stop_posture",
]


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


def validate_shape(body: Any) -> list[str]:
    if not isinstance(body, dict):
        return ["body_not_object"]

    errors: list[str] = []
    if list(body.keys()) != REQUIRED_KEYS:
        errors.append("body_key_order_or_set_mismatch")

    for row_field, required_keys in ROW_KEYS.items():
        rows = body.get(row_field)
        if not isinstance(rows, list):
            errors.append(f"{row_field}_not_array")
            continue
        if not rows:
            errors.append(f"{row_field}_missing_or_empty")
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


def validate_expected_fields(body: Any, fields: list[str], suffix: str) -> list[str]:
    if not isinstance(body, dict):
        return ["body_not_object"]

    errors = []
    for field in fields:
        expected = EXPECTED[field]
        if body.get(field) != expected:
            errors.append(f"{field}_{suffix}")
    return errors


def contradiction_errors(body: Any) -> list[str]:
    if not isinstance(body, dict):
        return []

    errors = []
    text_parts: list[str] = []
    for field in ("negative_cue_rows", "forbidden_inference_rows", "detail_notes", "contradiction_check_rows"):
        value = body.get(field)
        if isinstance(value, list):
            text_parts.extend(json.dumps(item, sort_keys=True) for item in value)
    joined = " ".join(text_parts).lower()

    if "florp" in joined and "create" in joined and body.get("operator_admission_branch") == "OP_A":
        errors.append("field_prose_contradiction_nearest_operator_repair")
    if "do not repair" in joined and body.get("operator_admission_branch") == "OP_A":
        errors.append("field_prose_contradiction_do_not_repair")
    return errors


def score_probe(probe_dir: Path) -> dict[str, Any]:
    specimens = load_jsonl(probe_dir / "specimens.jsonl")
    counts: Counter[str] = Counter()
    results = []

    for specimen in specimens:
        specimen_id = specimen.get("specimen_id", "<unknown>")
        body = specimen.get("raw_agent_body")
        shape_errors = validate_shape(body)
        raw_parse_errors = validate_expected_fields(body, RAW_FIELDS, "raw_parse_mismatch")
        branch_errors = validate_expected_fields(body, BRANCH_FIELDS, "branch_mismatch")
        status_errors = validate_expected_fields(body, STATUS_FIELDS, "status_mismatch")
        consistency_errors = contradiction_errors(body)
        all_errors = shape_errors + raw_parse_errors + branch_errors + status_errors + consistency_errors

        counts["shape_pass" if not shape_errors else "shape_remand"] += 1
        counts["raw_parse_pass" if not raw_parse_errors else "raw_parse_remand"] += 1
        counts["branch_pass" if not branch_errors else "branch_remand"] += 1
        counts["status_pass" if not status_errors else "status_remand"] += 1
        counts["consistency_pass" if not consistency_errors else "consistency_remand"] += 1
        counts["overall_pass" if not all_errors else "overall_remand"] += 1
        for error in all_errors:
            counts[error] += 1

        results.append(
            {
                "specimen_id": specimen_id,
                "shape_status": "pass" if not shape_errors else "remand_required",
                "raw_parse_status": "pass" if not raw_parse_errors else "remand_required",
                "branch_status": "pass" if not branch_errors else "remand_required",
                "status_status": "pass" if not status_errors else "remand_required",
                "consistency_status": "pass" if not consistency_errors else "remand_required",
                "overall_status": "pass" if not all_errors else "remand_required",
                "shape_errors": shape_errors,
                "raw_parse_errors": raw_parse_errors,
                "branch_errors": branch_errors,
                "status_errors": status_errors,
                "consistency_errors": consistency_errors,
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
