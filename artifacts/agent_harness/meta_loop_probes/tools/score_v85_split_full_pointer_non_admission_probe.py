#!/usr/bin/env python3
"""Score V85 split full-pointer non-admission probe specimens."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Any


REQUIRED_KEYS = [
    "case_id",
    "operator_admission_branch",
    "object_admission_branch",
    "version_ref_admission_branch",
    "operator_object_compatibility_branch",
    "task_phase_admissibility_branch",
    "full_pointer_admission_branch",
    "full_pointer_non_admission_reason_branch",
    "repair_status_branch",
    "component_preservation_branch",
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
        "checked_branch",
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
    "delete_menu_operator_gap": {
        "operator_admission_branch": "O2",
        "object_admission_branch": "C4",
        "version_ref_admission_branch": "V6",
        "operator_object_compatibility_branch": "P5",
        "task_phase_admissibility_branch": "T7",
        "full_pointer_admission_branch": "F3",
        "full_pointer_non_admission_reason_branch": "R2",
        "repair_status_branch": "E4",
        "component_preservation_branch": "K6",
    },
    "project_menu_pair_gap": {
        "operator_admission_branch": "O5",
        "object_admission_branch": "C9",
        "version_ref_admission_branch": "V3",
        "operator_object_compatibility_branch": "P1",
        "task_phase_admissibility_branch": "T6",
        "full_pointer_admission_branch": "F6",
        "full_pointer_non_admission_reason_branch": "R6",
        "repair_status_branch": "E1",
        "component_preservation_branch": "K2",
    },
    "create_menu_version_gap": {
        "operator_admission_branch": "O8",
        "object_admission_branch": "C7",
        "version_ref_admission_branch": "V9",
        "operator_object_compatibility_branch": "P2",
        "task_phase_admissibility_branch": "T5",
        "full_pointer_admission_branch": "F4",
        "full_pointer_non_admission_reason_branch": "R7",
        "repair_status_branch": "E6",
        "component_preservation_branch": "K4",
    },
    "create_menu_full": {
        "operator_admission_branch": "O6",
        "object_admission_branch": "C5",
        "version_ref_admission_branch": "V1",
        "operator_object_compatibility_branch": "P6",
        "task_phase_admissibility_branch": "T3",
        "full_pointer_admission_branch": "F2",
        "full_pointer_non_admission_reason_branch": "R1",
        "repair_status_branch": "E3",
        "component_preservation_branch": "K8",
    },
}

NOT_ADMITTED_BRANCHES = {
    "delete_menu_operator_gap": "F3",
    "project_menu_pair_gap": "F6",
    "create_menu_version_gap": "F4",
}

COMPONENTS_PRESERVED = {
    "delete_menu_operator_gap": "K6",
    "project_menu_pair_gap": "K2",
    "create_menu_version_gap": "K4",
    "create_menu_full": "K8",
}

NO_REPAIR = {
    "delete_menu_operator_gap": "E4",
    "project_menu_pair_gap": "E1",
    "create_menu_version_gap": "E6",
    "create_menu_full": "E3",
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


def validate_shape(body: Any) -> list[str]:
    if not isinstance(body, dict):
        return ["body_not_object"]

    errors: list[str] = []
    if list(body.keys()) != REQUIRED_KEYS:
        errors.append("body_key_order_or_set_mismatch")
    if body.get("branch_selection_status") != "branch_selection_complete":
        errors.append("branch_selection_status_mismatch")
    if body.get("stop_posture") != "stop_after_branch_selection":
        errors.append("stop_posture_mismatch")

    for row_field, required_keys in ROW_KEYS.items():
        rows = body.get(row_field)
        if not isinstance(rows, list):
            errors.append(f"{row_field}_not_array")
            continue
        if row_field in {
            "contradiction_check_rows",
            "resident_model_competency_claim_rows",
        } and not rows:
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


def validate_branches(case_id: str, body: Any) -> list[str]:
    if not isinstance(body, dict):
        return ["body_not_object"]
    expected = EXPECTED.get(case_id)
    if expected is None:
        return ["unknown_case_id"]

    errors: list[str] = []
    if body.get("case_id") != case_id:
        errors.append("case_id_mismatch")
    for field, expected_branch in expected.items():
        if body.get(field) != expected_branch:
            errors.append(f"{field}_mismatch")
    return errors


def validate_policy(case_id: str, body: Any) -> list[str]:
    if not isinstance(body, dict):
        return []

    errors: list[str] = []
    if case_id in NOT_ADMITTED_BRANCHES:
        if body.get("full_pointer_admission_branch") != NOT_ADMITTED_BRANCHES[case_id]:
            errors.append("full_pointer_non_admission_missed")
        if body.get("full_pointer_non_admission_reason_branch") == "R1":
            errors.append("non_admission_reason_marked_not_applicable")

    if body.get("component_preservation_branch") != COMPONENTS_PRESERVED.get(case_id):
        errors.append("component_preservation_failure")
    if body.get("repair_status_branch") != NO_REPAIR.get(case_id):
        errors.append("repair_status_failure")

    text = json.dumps(body, sort_keys=True).lower()
    if case_id != "create_menu_full":
        if "repair" not in text:
            errors.append("repair_rejection_not_visible")
        if "null" not in text and "preserv" not in text:
            errors.append("component_preservation_not_visible")

    return errors


def score_probe(probe_dir: Path) -> dict[str, Any]:
    specimens = load_jsonl(probe_dir / "specimens.jsonl")
    counts: Counter[str] = Counter()
    results = []

    for specimen in specimens:
        specimen_id = specimen.get("specimen_id", "<unknown>")
        case_id = specimen.get("case_id", "<unknown>")
        body = specimen.get("raw_agent_body")
        shape_errors = validate_shape(body)
        branch_errors = validate_branches(case_id, body)
        policy_errors = validate_policy(case_id, body)
        all_errors = shape_errors + branch_errors + policy_errors

        counts["shape_pass" if not shape_errors else "shape_remand"] += 1
        counts["branch_pass" if not branch_errors else "branch_remand"] += 1
        counts["policy_pass" if not policy_errors else "policy_remand"] += 1
        counts["overall_pass" if not all_errors else "overall_remand"] += 1
        if not policy_errors and isinstance(body, dict):
            counts["component_preservation_pass"] += 1
            counts["repair_status_pass"] += 1
            if case_id in NOT_ADMITTED_BRANCHES:
                counts["full_pointer_non_admission_pass"] += 1
        for error in all_errors:
            counts[error] += 1

        results.append(
            {
                "specimen_id": specimen_id,
                "case_id": case_id,
                "shape_status": "pass" if not shape_errors else "remand_required",
                "branch_status": "pass" if not branch_errors else "remand_required",
                "policy_status": "pass" if not policy_errors else "remand_required",
                "overall_status": "pass" if not all_errors else "remand_required",
                "shape_errors": shape_errors,
                "branch_errors": branch_errors,
                "policy_errors": policy_errors,
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
