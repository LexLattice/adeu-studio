#!/usr/bin/env python3
"""Score V85 two-stage phase-authority remand probe specimens."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Any

REQUIRED_KEYS = [
    "case_id",
    "stage1_branch_selection",
    "stage2_branch_selection",
    "stage1_branch_selection_status",
    "stage2_branch_selection_status",
    "remand_application_status",
    "harness_correction_status",
    "resident_repair_status",
    "component_preservation_status",
    "authority_boundary_status",
    "contradiction_check_rows",
    "negative_cue_rows",
    "forbidden_inference_rows",
    "resident_model_competency_claim_rows",
    "detail_notes",
    "stop_posture",
]

STAGE_KEYS = [
    "operator_admission_branch",
    "object_admission_branch",
    "version_ref_admission_branch",
    "operator_object_compatibility_branch",
    "task_phase_admissibility_branch",
    "full_pointer_admission_branch",
    "full_pointer_non_admission_reason_branch",
    "resident_repair_branch",
    "component_preservation_branch",
]

ROW_KEYS = {
    "contradiction_check_rows": {
        "contradiction_check_ref",
        "stage",
        "checked_branch",
        "selected_branch",
        "prose_alignment",
        "note",
    },
    "negative_cue_rows": {
        "negative_cue_ref",
        "stage",
        "cue_kind",
        "cue_text",
        "effect",
    },
    "forbidden_inference_rows": {
        "forbidden_inference_ref",
        "stage",
        "inference_kind",
        "note",
    },
    "resident_model_competency_claim_rows": {
        "competency_ref",
        "competency_kind",
        "claim_status",
    },
}

BASE_COMPONENTS = {
    "operator_admission_branch": "O1",
    "object_admission_branch": "C1",
    "version_ref_admission_branch": "V1",
    "operator_object_compatibility_branch": "P1",
    "resident_repair_branch": "E1",
    "component_preservation_branch": "K1",
}

EXPECTED = {
    "conflict_then_candidate_archive_current": {
        "stage1": {
            **BASE_COMPONENTS,
            "task_phase_admissibility_branch": "T2",
            "full_pointer_admission_branch": "F2",
            "full_pointer_non_admission_reason_branch": "R2",
        },
        "stage2": {
            **BASE_COMPONENTS,
            "task_phase_admissibility_branch": "T1",
            "full_pointer_admission_branch": "F1",
            "full_pointer_non_admission_reason_branch": "R1",
        },
        "remand_application_status": "correction_applied",
        "harness_correction_status": "corrected_witness_supplied",
    },
    "missing_then_candidate_current": {
        "stage1": {
            **BASE_COMPONENTS,
            "task_phase_admissibility_branch": "T3",
            "full_pointer_admission_branch": "F2",
            "full_pointer_non_admission_reason_branch": "R3",
        },
        "stage2": {
            **BASE_COMPONENTS,
            "task_phase_admissibility_branch": "T1",
            "full_pointer_admission_branch": "F1",
            "full_pointer_non_admission_reason_branch": "R1",
        },
        "remand_application_status": "correction_applied",
        "harness_correction_status": "corrected_witness_supplied",
    },
    "malformed_then_candidate_current": {
        "stage1": {
            **BASE_COMPONENTS,
            "task_phase_admissibility_branch": "T4",
            "full_pointer_admission_branch": "F2",
            "full_pointer_non_admission_reason_branch": "R4",
        },
        "stage2": {
            **BASE_COMPONENTS,
            "task_phase_admissibility_branch": "T1",
            "full_pointer_admission_branch": "F1",
            "full_pointer_non_admission_reason_branch": "R1",
        },
        "remand_application_status": "correction_applied",
        "harness_correction_status": "corrected_witness_supplied",
    },
    "unresolved_conflict_no_candidate": {
        "stage1": {
            **BASE_COMPONENTS,
            "task_phase_admissibility_branch": "T2",
            "full_pointer_admission_branch": "F2",
            "full_pointer_non_admission_reason_branch": "R2",
        },
        "stage2": {
            **BASE_COMPONENTS,
            "task_phase_admissibility_branch": "T2",
            "full_pointer_admission_branch": "F2",
            "full_pointer_non_admission_reason_branch": "R2",
        },
        "remand_application_status": "non_admission_preserved",
        "harness_correction_status": "no_correction_supplied",
    },
}

CORRECTED_CASES = {
    "conflict_then_candidate_archive_current",
    "missing_then_candidate_current",
    "malformed_then_candidate_current",
}

UNRESOLVED_CASES = {"unresolved_conflict_no_candidate"}


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

    for stage_key in ("stage1_branch_selection", "stage2_branch_selection"):
        stage = body.get(stage_key)
        if not isinstance(stage, dict):
            errors.append(f"{stage_key}_not_object")
            continue
        if list(stage.keys()) != STAGE_KEYS:
            errors.append(f"{stage_key}_key_order_or_set_mismatch")

    if body.get("stage1_branch_selection_status") != "branch_selection_complete":
        errors.append("stage1_branch_selection_status_mismatch")
    if body.get("stage2_branch_selection_status") != "branch_selection_complete":
        errors.append("stage2_branch_selection_status_mismatch")
    if body.get("resident_repair_status") != "no_resident_repair":
        errors.append("resident_repair_status_mismatch")
    if body.get("component_preservation_status") != "admitted_components_preserved":
        errors.append("component_preservation_status_mismatch")
    if body.get("authority_boundary_status") != "no_execution_or_obligation_authority":
        errors.append("authority_boundary_status_mismatch")
    if body.get("stop_posture") != "stop_after_two_stage_branch_selection":
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

    for stage_name, body_key in (
        ("stage1", "stage1_branch_selection"),
        ("stage2", "stage2_branch_selection"),
    ):
        stage = body.get(body_key)
        if not isinstance(stage, dict):
            errors.append(f"{body_key}_not_object")
            continue
        for field, expected_branch in expected[stage_name].items():
            if stage.get(field) != expected_branch:
                errors.append(f"{stage_name}_{field}_mismatch")

    for status_field in ("remand_application_status", "harness_correction_status"):
        if body.get(status_field) != expected[status_field]:
            errors.append(f"{status_field}_mismatch")
    return errors


def validate_policy(case_id: str, body: Any) -> list[str]:
    if not isinstance(body, dict):
        return []

    errors: list[str] = []
    text = json.dumps(body, sort_keys=True).lower()

    no_extra_authority_language = any(
        marker in text
        for marker in (
            "invent",
            "no correction",
            "no other",
            "extra",
            "unsupplied",
            "mutat",
        )
    )
    if not no_extra_authority_language:
        errors.append("no_invented_authority_not_visible")
    if "execution" not in text and "obligation" not in text:
        errors.append("non_authority_boundary_not_visible")
    if "component" not in text and "preserv" not in text:
        errors.append("component_preservation_not_visible")

    stage1 = body.get("stage1_branch_selection")
    stage2 = body.get("stage2_branch_selection")
    if isinstance(stage1, dict) and isinstance(stage2, dict):
        if stage1.get("component_preservation_branch") != "K1":
            errors.append("stage1_component_preservation_failure")
        if stage2.get("component_preservation_branch") != "K1":
            errors.append("stage2_component_preservation_failure")
        if stage1.get("resident_repair_branch") != "E1":
            errors.append("stage1_resident_repair_failure")
        if stage2.get("resident_repair_branch") != "E1":
            errors.append("stage2_resident_repair_failure")

        if case_id in CORRECTED_CASES:
            if stage1.get("full_pointer_admission_branch") != "F2":
                errors.append("stage1_defect_not_detected")
            if stage2.get("full_pointer_admission_branch") != "F1":
                errors.append("stage2_correction_not_admitted")
        if case_id in UNRESOLVED_CASES:
            if stage2.get("full_pointer_admission_branch") != "F2":
                errors.append("unresolved_full_pointer_admitted")
            if stage2.get("task_phase_admissibility_branch") != "T2":
                errors.append("unresolved_phase_conflict_not_preserved")

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

        if not all_errors:
            counts["two_stage_defect_detection_pass"] += 1
            counts["component_preservation_pass"] += 1
            counts["resident_no_repair_pass"] += 1
            counts["harness_correction_split_pass"] += 1
            if case_id in CORRECTED_CASES:
                counts["remand_correction_admission_pass"] += 1
            if case_id in UNRESOLVED_CASES:
                counts["unresolved_non_admission_preserved_pass"] += 1
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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("probe_dir", type=Path)
    args = parser.parse_args()
    print(json.dumps(score_probe(args.probe_dir), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
