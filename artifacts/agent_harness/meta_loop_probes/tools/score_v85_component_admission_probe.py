#!/usr/bin/env python3
"""Score V85 local component-admission probe specimens."""

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
    "raw_object_version_token_candidate",
    "raw_object_version_ref_candidate",
    "canonical_semantic_pointer",
    "canonical_operator",
    "canonical_object_class",
    "canonical_object_version_ref",
    "pointer_kind",
    "component_admission_status",
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

EXPECTED_CASE_FIELDS = {
    "known_full_pointer": {
        "raw_semantic_pointer_candidate": "CREATE ui.menu@v1",
        "raw_operator_candidate": "CREATE",
        "raw_object_class_candidate": "ui.menu",
        "raw_object_version_token_candidate": "v1",
        "raw_object_version_ref_candidate": "ui.menu@v1",
        "canonical_semantic_pointer": "CREATE ui.menu@v1",
        "canonical_operator": "CREATE",
        "canonical_object_class": "ui.menu",
        "canonical_object_version_ref": "ui.menu@v1",
        "pointer_kind": "explicit_pointer_candidate",
        "component_admission_status": "full_admission",
        "canonical_lookup_status": "full_registry_match",
        "selection_status": "candidate_only",
        "stop_posture": "stop_after_component_admission_filing",
    },
    "unknown_object_version": {
        "raw_semantic_pointer_candidate": "CREATE ui.toast@v3",
        "raw_operator_candidate": "CREATE",
        "raw_object_class_candidate": "ui.toast",
        "raw_object_version_token_candidate": "v3",
        "raw_object_version_ref_candidate": "ui.toast@v3",
        "canonical_semantic_pointer": None,
        "canonical_operator": "CREATE",
        "canonical_object_class": None,
        "canonical_object_version_ref": None,
        "pointer_kind": "explicit_pointer_candidate",
        "component_admission_status": "operator_only_admission",
        "canonical_lookup_status": "object_class_version_registry_gap",
        "selection_status": "candidate_only",
        "stop_posture": "stop_after_component_admission_filing",
    },
    "unknown_operator": {
        "raw_semantic_pointer_candidate": "FLORP ui.menu@v1",
        "raw_operator_candidate": "FLORP",
        "raw_object_class_candidate": "ui.menu",
        "raw_object_version_token_candidate": "v1",
        "raw_object_version_ref_candidate": "ui.menu@v1",
        "canonical_semantic_pointer": None,
        "canonical_operator": None,
        "canonical_object_class": "ui.menu",
        "canonical_object_version_ref": "ui.menu@v1",
        "pointer_kind": "explicit_pointer_candidate",
        "component_admission_status": "object_version_only_admission",
        "canonical_lookup_status": "operator_registry_gap",
        "selection_status": "candidate_only",
        "stop_posture": "stop_after_component_admission_filing",
    },
    "unknown_version": {
        "raw_semantic_pointer_candidate": "CREATE ui.menu@v99",
        "raw_operator_candidate": "CREATE",
        "raw_object_class_candidate": "ui.menu",
        "raw_object_version_token_candidate": "v99",
        "raw_object_version_ref_candidate": "ui.menu@v99",
        "canonical_semantic_pointer": None,
        "canonical_operator": "CREATE",
        "canonical_object_class": "ui.menu",
        "canonical_object_version_ref": None,
        "pointer_kind": "explicit_pointer_candidate",
        "component_admission_status": "operator_object_only_admission",
        "canonical_lookup_status": "object_version_registry_gap",
        "selection_status": "candidate_only",
        "stop_posture": "stop_after_component_admission_filing",
    },
}

CANDIDATE_COMPONENT_FIELDS = [
    "raw_semantic_pointer_candidate",
    "raw_operator_candidate",
    "raw_object_class_candidate",
    "raw_object_version_token_candidate",
    "raw_object_version_ref_candidate",
    "canonical_semantic_pointer",
    "canonical_operator",
    "canonical_object_class",
    "canonical_object_version_ref",
]

ROUTING_STATUS_FIELDS = [
    "pointer_kind",
    "component_admission_status",
    "canonical_lookup_status",
    "selection_status",
    "stop_posture",
]

CLOSED_STATUS_FIELDS = {
    "pointer_kind": {"explicit_pointer_candidate"},
    "component_admission_status": {
        "full_admission",
        "operator_only_admission",
        "object_version_only_admission",
        "operator_object_only_admission",
    },
    "canonical_lookup_status": {
        "full_registry_match",
        "object_class_version_registry_gap",
        "operator_registry_gap",
        "object_version_registry_gap",
    },
    "selection_status": {"candidate_only"},
    "stop_posture": {"stop_after_component_admission_filing"},
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

    for field, allowed in CLOSED_STATUS_FIELDS.items():
        if body.get(field) not in allowed:
            errors.append(f"{field}_closed_value_mismatch")

    return errors


def validate_components(case_id: str, body: Any) -> list[str]:
    if not isinstance(body, dict):
        return ["resident_body_not_object"]

    expected = EXPECTED_CASE_FIELDS.get(case_id)
    if expected is None:
        return ["unknown_case_id"]

    errors: list[str] = []
    for field, expected_value in expected.items():
        if body.get(field) != expected_value:
            errors.append(f"{field}_component_mismatch")
    return errors


def validate_expected_fields(
    case_id: str,
    body: Any,
    fields: list[str],
    suffix: str,
) -> list[str]:
    if not isinstance(body, dict):
        return ["resident_body_not_object"]

    expected = EXPECTED_CASE_FIELDS.get(case_id)
    if expected is None:
        return ["unknown_case_id"]

    errors: list[str] = []
    for field in fields:
        if body.get(field) != expected[field]:
            errors.append(f"{field}_{suffix}")
    return errors


def classify_failure(errors: list[str]) -> list[str]:
    labels: list[str] = []
    if "canonical_operator_component_mismatch" in errors:
        labels.append("operator_overblocked_or_repaired")
    if "canonical_object_class_component_mismatch" in errors:
        labels.append("object_class_overblocked_or_repaired")
    if "canonical_object_version_ref_component_mismatch" in errors:
        labels.append("object_version_overblocked_or_repaired")
    if "canonical_semantic_pointer_component_mismatch" in errors:
        labels.append("full_pointer_admission_mismatch")
    if any(error.endswith("_closed_value_mismatch") for error in errors):
        labels.append("closed_status_mismatch")
    return labels


def score_probe(probe_dir: Path) -> dict[str, Any]:
    specimens = load_jsonl(probe_dir / "specimens.jsonl")
    counts: Counter[str] = Counter()
    results = []

    for specimen in specimens:
        specimen_id = specimen.get("specimen_id", "<unknown>")
        case_id = specimen.get("case_id", "<unknown>")
        body = specimen.get("raw_agent_body")

        shape_errors = validate_shape(body)
        component_errors = validate_components(case_id, body)
        component_value_errors = validate_expected_fields(
            case_id,
            body,
            CANDIDATE_COMPONENT_FIELDS,
            "component_mismatch",
        )
        routing_status_errors = validate_expected_fields(
            case_id,
            body,
            ROUTING_STATUS_FIELDS,
            "status_mismatch",
        )
        all_errors = shape_errors + component_errors

        counts["strict_body_shape_pass" if not shape_errors else "strict_body_shape_remand"] += 1
        counts[
            "component_admission_pass"
            if not component_errors
            else "component_admission_remand"
        ] += 1
        counts[
            "component_value_pass"
            if not component_value_errors
            else "component_value_remand"
        ] += 1
        counts[
            "routing_status_pass"
            if not routing_status_errors
            else "routing_status_remand"
        ] += 1
        counts["overall_pass" if not all_errors else "overall_remand"] += 1

        if isinstance(body, dict):
            if body.get("canonical_semantic_pointer") is None or case_id == "known_full_pointer":
                counts["full_pointer_policy_pass"] += 1
            if body.get("raw_object_version_token_candidate") in {"v1", "v3", "v99"}:
                counts["version_token_shape_pass"] += 1
            if isinstance(body.get("raw_object_version_ref_candidate"), str) and "@" in body.get(
                "raw_object_version_ref_candidate"
            ):
                counts["version_ref_shape_pass"] += 1

        for error in all_errors:
            counts[error] += 1
        for label in classify_failure(all_errors):
            counts[label] += 1

        results.append(
            {
                "specimen_id": specimen_id,
                "case_id": case_id,
                "strict_body_shape_status": "pass" if not shape_errors else "remand_required",
                "component_admission_status": "pass"
                if not component_errors
                else "remand_required",
                "component_value_status": "pass"
                if not component_value_errors
                else "remand_required",
                "routing_status": "pass" if not routing_status_errors else "remand_required",
                "overall_status": "pass" if not all_errors else "remand_required",
                "shape_errors": shape_errors,
                "component_errors": component_errors,
                "component_value_errors": component_value_errors,
                "routing_status_errors": routing_status_errors,
                "failure_labels": classify_failure(all_errors),
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
