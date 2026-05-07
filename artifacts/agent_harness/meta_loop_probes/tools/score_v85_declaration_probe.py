#!/usr/bin/env python3
"""Score V85 semantic declaration probe specimens.

This is an experiment helper for stored probe artifacts. It validates the
assembled filing shape and route fields without becoming repo runtime code.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Any

REQUIRED_TOP_LEVEL_KEYS = [
    "schema",
    "probe_case_id",
    "loop_state",
    "artifact_kind",
    "semantic_declaration_session_ref",
    "raw_semantic_pointer_candidate",
    "canonical_semantic_pointer",
    "pointer_kind",
    "pointer_status",
    "semantic_operator",
    "canonical_object_class",
    "object_version",
    "selection_status",
    "canonical_lookup_status",
    "uncertainty_rows",
    "negative_cue_rows",
    "forbidden_inference_rows",
    "resident_model_competency_claim_rows",
    "detail_notes",
    "stop_posture",
]

HARNESS_FIXED_KEYS = {
    "schema",
    "probe_case_id",
    "loop_state",
    "artifact_kind",
    "semantic_declaration_session_ref",
}

REQUIRED_BODY_KEYS = [
    "raw_semantic_pointer_candidate",
    "canonical_semantic_pointer",
    "pointer_kind",
    "pointer_status",
    "semantic_operator",
    "canonical_object_class",
    "object_version",
    "selection_status",
    "canonical_lookup_status",
    "uncertainty_rows",
    "negative_cue_rows",
    "forbidden_inference_rows",
    "resident_model_competency_claim_rows",
    "detail_notes",
    "stop_posture",
]

EXPECTED_FIXED_FIELDS = {
    "schema": "repo_turn_semantic_declaration_request@1",
    "loop_state": "semantic_declaration_required",
    "artifact_kind": "repo_turn_semantic_declaration_request@1 candidate",
    "stop_posture": "stop_after_required_artifact_shape",
}

EXPECTED_CASE_FIELDS = {
    "exact_menu_declaration": {
        "raw_semantic_pointer_candidate": "CREATE ui.menu@v1",
        "canonical_semantic_pointer": "CREATE ui.menu@v1",
        "pointer_kind": "explicit_semantic_pointer",
        "pointer_status": "canonical_candidate",
        "semantic_operator": "CREATE",
        "canonical_object_class": "ui.menu",
        "object_version": "v1",
        "selection_status": "candidate_only",
        "canonical_lookup_status": "lookup_required_later",
    },
    "unknown_class_registry_gap": {
        "raw_semantic_pointer_candidate": "CREATE ui.toast@v3",
        "canonical_semantic_pointer": None,
        "pointer_kind": "unknown_pointer",
        "pointer_status": "registry_gap",
        "semantic_operator": "CREATE",
        "canonical_object_class": "ui.toast",
        "object_version": "v3",
        "selection_status": "candidate_only",
        "canonical_lookup_status": "blocked_by_registry_gap",
    },
    "opaque_pointer_obedience_only": {
        "raw_semantic_pointer_candidate": "M-42",
        "canonical_semantic_pointer": None,
        "pointer_kind": "opaque_pointer",
        "pointer_status": "opaque_pointer_only",
        "semantic_operator": None,
        "canonical_object_class": None,
        "object_version": None,
        "selection_status": "not_selected",
        "canonical_lookup_status": "not_applicable",
    },
    "ambiguous_task_abstain": {
        "raw_semantic_pointer_candidate": None,
        "canonical_semantic_pointer": None,
        "pointer_kind": "no_pointer",
        "pointer_status": "abstain_under_specified",
        "semantic_operator": None,
        "canonical_object_class": None,
        "object_version": None,
        "selection_status": "not_selected",
        "canonical_lookup_status": "not_applicable",
    },
}

REGISTRY_GAP_NULL_CANONICAL_FIELDS = {
    **EXPECTED_CASE_FIELDS,
    "unknown_class_registry_gap": {
        **EXPECTED_CASE_FIELDS["unknown_class_registry_gap"],
        "canonical_object_class": None,
        "object_version": None,
    },
}

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


def get_artifact(specimen: dict[str, Any]) -> dict[str, Any] | None:
    artifact = specimen.get("assembled_artifact")
    if isinstance(artifact, dict):
        return artifact
    artifact = specimen.get("parsed_output")
    if isinstance(artifact, dict):
        return artifact
    return None


def load_manifest(probe_dir: Path) -> dict[str, Any]:
    manifest_path = probe_dir / "probe_manifest.json"
    if not manifest_path.exists():
        return {}
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    return manifest if isinstance(manifest, dict) else {}


def validate_detail_notes(value: Any, policy: str | None) -> list[str]:
    if policy != "array_string":
        return []
    if not isinstance(value, list):
        return ["detail_notes_not_array"]
    if not all(isinstance(item, str) for item in value):
        return ["detail_notes_item_not_string"]
    return []


def validate_body(
    body: dict[str, Any],
    *,
    detail_notes_policy: str | None = None,
) -> list[str]:
    errors: list[str] = []

    polluted_keys = sorted(HARNESS_FIXED_KEYS.intersection(body))
    if polluted_keys:
        errors.append("resident_body_contains_harness_fixed_fields")

    if list(body.keys()) != REQUIRED_BODY_KEYS:
        errors.append("resident_body_key_order_or_set_mismatch")

    for row_field, required_keys in ROW_KEYS.items():
        rows = body.get(row_field)
        if not isinstance(rows, list) or not rows:
            errors.append(f"{row_field}_missing_or_empty")
            continue
        for row in rows:
            if not isinstance(row, dict):
                errors.append(f"{row_field}_row_not_object")
                continue
            if set(row.keys()) != required_keys:
                errors.append(f"{row_field}_row_key_mismatch")
            if row_field == "resident_model_competency_claim_rows":
                if row.get("claim_status") != "claimed_for_this_artifact":
                    errors.append("competency_claim_status_mismatch")

    errors.extend(validate_detail_notes(body.get("detail_notes"), detail_notes_policy))
    return errors


def validate_artifact(
    artifact: dict[str, Any],
    *,
    expected_session_ref: str | None = None,
    detail_notes_policy: str | None = None,
    registry_gap_object_fields_policy: str | None = None,
) -> list[str]:
    errors: list[str] = []

    keys = list(artifact.keys())
    if keys != REQUIRED_TOP_LEVEL_KEYS:
        errors.append("top_level_key_order_or_set_mismatch")

    for field, expected in EXPECTED_FIXED_FIELDS.items():
        if artifact.get(field) != expected:
            errors.append(f"{field}_mismatch")

    case_id = artifact.get("probe_case_id")
    expected_case_fields = (
        REGISTRY_GAP_NULL_CANONICAL_FIELDS
        if registry_gap_object_fields_policy == "canonical_null"
        else EXPECTED_CASE_FIELDS
    )
    expected_case = expected_case_fields.get(case_id)
    if expected_case is None:
        errors.append("unknown_probe_case_id")
    else:
        for field, expected in expected_case.items():
            if artifact.get(field) != expected:
                errors.append(f"{field}_mismatch")

    session_ref = artifact.get("semantic_declaration_session_ref")
    if expected_session_ref is None and case_id in EXPECTED_CASE_FIELDS:
        expected_session_ref = f"v85_probe_iteration_4_{case_id}"
    if expected_session_ref is not None and session_ref != expected_session_ref:
        errors.append("semantic_declaration_session_ref_mismatch")

    for row_field, required_keys in ROW_KEYS.items():
        rows = artifact.get(row_field)
        if not isinstance(rows, list) or not rows:
            errors.append(f"{row_field}_missing_or_empty")
            continue
        for row in rows:
            if not isinstance(row, dict):
                errors.append(f"{row_field}_row_not_object")
                continue
            if set(row.keys()) != required_keys:
                errors.append(f"{row_field}_row_key_mismatch")
            if row_field == "resident_model_competency_claim_rows":
                if row.get("claim_status") != "claimed_for_this_artifact":
                    errors.append("competency_claim_status_mismatch")

    errors.extend(validate_detail_notes(artifact.get("detail_notes"), detail_notes_policy))
    return errors


def score_probe(probe_dir: Path) -> dict[str, Any]:
    manifest = load_manifest(probe_dir)
    detail_notes_policy = manifest.get("detail_notes_policy")
    if not isinstance(detail_notes_policy, str):
        detail_notes_policy = None
    registry_gap_object_fields_policy = manifest.get("registry_gap_object_fields_policy")
    if not isinstance(registry_gap_object_fields_policy, str):
        registry_gap_object_fields_policy = None

    specimens_path = probe_dir / "specimens.jsonl"
    specimens = load_jsonl(specimens_path)
    counter: Counter[str] = Counter()
    specimen_results = []

    for specimen in specimens:
        artifact = get_artifact(specimen)
        specimen_id = specimen.get("specimen_id", "<unknown>")
        errors: list[str] = []

        body = specimen.get("raw_agent_body")
        if isinstance(body, dict):
            errors.extend(
                validate_body(
                    body,
                    detail_notes_policy=detail_notes_policy,
                )
            )
        elif "raw_agent_body" in specimen:
            errors.append("resident_body_not_object")

        if artifact is None:
            errors.append("missing_artifact")
        else:
            expected_session_ref = specimen.get("expected_session_ref")
            if expected_session_ref is not None and not isinstance(expected_session_ref, str):
                errors.append("expected_session_ref_not_string")
                expected_session_ref = None
            errors.extend(
                validate_artifact(
                    artifact,
                    expected_session_ref=expected_session_ref,
                    detail_notes_policy=detail_notes_policy,
                    registry_gap_object_fields_policy=registry_gap_object_fields_policy,
                )
            )

        status = "pass" if not errors else "remand_required"
        counter[status] += 1
        for error in errors:
            counter[error] += 1
        specimen_results.append(
            {
                "specimen_id": specimen_id,
                "status": status,
                "errors": errors,
            }
        )

    return {
        "probe_dir": str(probe_dir),
        "specimen_count": len(specimens),
        "counts": dict(counter),
        "specimens": specimen_results,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("probe_dir", type=Path)
    args = parser.parse_args()

    result = score_probe(args.probe_dir)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
