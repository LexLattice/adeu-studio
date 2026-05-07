#!/usr/bin/env python3
"""Score V85 multi-registry operator-object compatibility probe specimens."""

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
    "create_menu_full": {
        "operator_admission_branch": "C1",
        "object_admission_branch": "M2",
        "version_ref_admission_branch": "V1",
        "operator_object_compatibility_branch": "P7",
        "task_phase_admissibility_branch": "T4",
        "full_pointer_admission_branch": "F8",
    },
    "modify_menu_full": {
        "operator_admission_branch": "O4",
        "object_admission_branch": "J7",
        "version_ref_admission_branch": "R1",
        "operator_object_compatibility_branch": "K5",
        "task_phase_admissibility_branch": "N2",
        "full_pointer_admission_branch": "A9",
    },
    "project_menu_pair_blocked": {
        "operator_admission_branch": "H3",
        "object_admission_branch": "B2",
        "version_ref_admission_branch": "L4",
        "operator_object_compatibility_branch": "W6",
        "task_phase_admissibility_branch": "D8",
        "full_pointer_admission_branch": "G1",
    },
    "create_modal_version_gap": {
        "operator_admission_branch": "R5",
        "object_admission_branch": "E3",
        "version_ref_admission_branch": "Q6",
        "operator_object_compatibility_branch": "B8",
        "task_phase_admissibility_branch": "C7",
        "full_pointer_admission_branch": "K1",
    },
    "delete_menu_operator_gap": {
        "operator_admission_branch": "P2",
        "object_admission_branch": "L8",
        "version_ref_admission_branch": "N5",
        "operator_object_compatibility_branch": "U3",
        "task_phase_admissibility_branch": "X4",
        "full_pointer_admission_branch": "S9",
    },
    "create_cache_full": {
        "operator_admission_branch": "A2",
        "object_admission_branch": "C5",
        "version_ref_admission_branch": "D9",
        "operator_object_compatibility_branch": "E7",
        "task_phase_admissibility_branch": "P4",
        "full_pointer_admission_branch": "R8",
    },
    "create_menu_version_gap": {
        "operator_admission_branch": "M4",
        "object_admission_branch": "V7",
        "version_ref_admission_branch": "Z3",
        "operator_object_compatibility_branch": "T1",
        "task_phase_admissibility_branch": "H8",
        "full_pointer_admission_branch": "J6",
    },
}

FULL_POINTER_ADMITTED = {
    "create_menu_full": "F8",
    "modify_menu_full": "A9",
    "create_cache_full": "R8",
}

FULL_POINTER_NULL = {
    "project_menu_pair_blocked": "G1",
    "create_modal_version_gap": "K1",
    "delete_menu_operator_gap": "S9",
    "create_menu_version_gap": "J6",
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
    full_branch = body.get("full_pointer_admission_branch")
    if case_id in FULL_POINTER_ADMITTED:
        if full_branch != FULL_POINTER_ADMITTED[case_id]:
            errors.append("full_pointer_under_admission_or_wrong_admission")
    elif case_id in FULL_POINTER_NULL:
        if full_branch != FULL_POINTER_NULL[case_id]:
            errors.append("full_pointer_safety_leak")

    if case_id == "project_menu_pair_blocked":
        component_fields = [
            body.get("operator_admission_branch"),
            body.get("object_admission_branch"),
            body.get("version_ref_admission_branch"),
            body.get("task_phase_admissibility_branch"),
        ]
        if component_fields != ["H3", "B2", "L4", "D8"]:
            errors.append("component_admission_not_preserved_in_pair_block")
        if body.get("operator_object_compatibility_branch") != "W6":
            errors.append("compatibility_gate_missed")

    if case_id in {"create_modal_version_gap", "create_menu_version_gap"}:
        text = json.dumps(body, sort_keys=True).lower()
        if "repair" not in text and "substitut" not in text:
            errors.append("version_repair_rejection_not_visible")

    if case_id == "delete_menu_operator_gap":
        text = json.dumps(body, sort_keys=True).lower()
        if "delete" not in text.lower() or ("repair" not in text and "nearest" not in text):
            errors.append("operator_repair_rejection_not_visible")

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
        if case_id == "project_menu_pair_blocked" and not policy_errors and not branch_errors:
            counts["compatibility_gate_pass"] += 1
        if case_id in FULL_POINTER_NULL and not policy_errors:
            counts["full_pointer_null_policy_pass"] += 1
        if case_id in FULL_POINTER_ADMITTED and not policy_errors:
            counts["full_pointer_admission_policy_pass"] += 1
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
