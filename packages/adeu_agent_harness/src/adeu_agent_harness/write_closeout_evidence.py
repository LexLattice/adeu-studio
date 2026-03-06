from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from urm_runtime.hashing import canonical_json, sha256_canonical_json

from ._v46_verifier_common import (
    AHK4603_ARTIFACT_INVALID,
    AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
    AHK4608_CONTRACT_REGISTRY_INVALID,
    AHK4610_EVIDENCE_BUNDLE_HASH_SUBJECT_DRIFT,
    AHK4611_EVIDENCE_SLOT_OR_SCHEMA_VIOLATION,
    AHK4612_EVIDENCE_EMISSION_AUTHORITY_VIOLATION,
    AHK4613_VERIFIER_PROVENANCE_INVALID,
    AHK4615_VERIFICATION_FAILURE_WITHOUT_REJECTION_DIAGNOSTIC,
    DEFAULT_DIAGNOSTIC_REGISTRY_PATH,
    DEFAULT_REJECTIONS_ROOT,
    POLICY_SOURCE_ENUM_V46,
    TaskpackVerifierError,
    VerifierIssue,
    coerce_artifact_path,
    emit_rejection_diagnostic,
    fail,
    is_sha256,
    load_diagnostic_registry,
    load_json_object,
    normalize_relative_path,
    project_repo_root,
    require_deterministic_env_v46,
    require_schema,
    write_json,
)
from .compile import TaskpackCompileError, verify_taskpack_bundle
from .verify_taskpack_run import VERIFICATION_RESULT_SCHEMA

EVIDENCE_SLOTS_SCHEMA = "taskpack/evidence_slots@1"

EVIDENCE_BUNDLE_SCHEMA = "taskpack_closeout_evidence_bundle@1"
VERIFIER_PROVENANCE_SCHEMA = "taskpack_verifier_provenance@1"
EVIDENCE_WRITER_RESULT_SCHEMA = "taskpack_evidence_writer_result@1"

DEFAULT_EVIDENCE_ROOT = "artifacts/agent_harness/v46/evidence"

RUNTIME_OBSERVABILITY_SCHEMA = "runtime_observability_comparison@1"
METRIC_KEY_CONTINUITY_SCHEMA = "metric_key_continuity_assertion@1"
HANDOFF_COMPLETION_EVIDENCE_SCHEMA = "v34a_handoff_completion_evidence@1"
MATRIX_PARITY_EVIDENCE_SCHEMA = "v34b_matrix_parity_evidence@1"
ADAPTER_MATRIX_SCHEMA = "adapter_matrix@1"
ADAPTER_MATRIX_PARITY_REPORT_SCHEMA = "adapter_matrix_parity_report@1"

EVIDENCE_SCHEMA_ALLOWLIST = (
    RUNTIME_OBSERVABILITY_SCHEMA,
    METRIC_KEY_CONTINUITY_SCHEMA,
    HANDOFF_COMPLETION_EVIDENCE_SCHEMA,
    MATRIX_PARITY_EVIDENCE_SCHEMA,
)

EVIDENCE_SCHEMA_TO_SLOT_ID = {
    RUNTIME_OBSERVABILITY_SCHEMA: "runtime_observability_comparison",
    METRIC_KEY_CONTINUITY_SCHEMA: "metric_key_continuity_assertion",
    HANDOFF_COMPLETION_EVIDENCE_SCHEMA: "v34a_handoff_completion_evidence",
    MATRIX_PARITY_EVIDENCE_SCHEMA: "v34b_matrix_parity_evidence",
}

_HANDOFF_COMPLETION_SHARED_BINDING_VALIDATOR = (
    "packages/adeu_agent_harness.verify_taskpack_signature."
    "validate_signature_verification_result_for_downstream"
)

_HANDOFF_COMPLETION_REQUIRED_BINDING_FIELDS = [
    "taskpack_manifest_hash",
    "taskpack_bundle_hash",
    "signature_envelope_hash",
    "trust_anchor_registry_hash",
    "verification_reference_time_utc",
    "preflight_invocation_binding_hash",
    "signer_key_id",
    "algorithm",
    "verified",
]

_HANDOFF_COMPLETION_REQUIRED_KEYS = {
    "schema",
    "contract_source",
    "preflight_entrypoint",
    "runner_entrypoint",
    "verifier_entrypoint",
    "evidence_writer_entrypoint",
    "packaging_entrypoints",
    "shared_binding_validator_used",
    "binding_fields_verified",
    "verified_required",
    "signature_result_consumed_by_runner",
    "signature_result_consumed_by_verifier",
    "signature_result_consumed_by_packaging",
    "current_taskpack_snapshot_binding_enforced",
    "detached_user_supplied_handoff_forbidden",
    "historical_v47_to_v48_continuity_guard_repaired",
    "verification_passed",
    "metric_key_cardinality",
    "metric_key_exact_set_equal_v48",
    "notes",
}

_MATRIX_PARITY_REQUIRED_KEYS = {
    "schema",
    "contract_source",
    "matrix_registry_path",
    "matrix_report_path",
    "matrix_report_hash",
    "lane_id_tuple",
    "enabled_row_policy",
    "lane_count_authority",
    "lane_count",
    "deployment_modes_covered",
    "adapter_ids_covered",
    "runtime_ids_covered",
    "singleton_runtime_id_enforced",
    "runtime_id_source_policy",
    "runtime_id_host_inference_forbidden",
    "declared_registry_only",
    "lexicographic_lane_order_enforced",
    "canonical_subtree_exact_match_required",
    "canonical_subtree_source_policy",
    "policy_equivalence_exact_match_required",
    "policy_equivalence_subject_keys_verified",
    "policy_equivalence_value_shapes_verified",
    "report_covers_all_declared_lanes",
    "verification_passed",
    "metric_key_cardinality",
    "metric_key_exact_set_equal_v49",
    "notes",
}
_BASE_REQUIRED_EVIDENCE_SLOT_IDS = sorted(
    (
        EVIDENCE_SCHEMA_TO_SLOT_ID[RUNTIME_OBSERVABILITY_SCHEMA],
        EVIDENCE_SCHEMA_TO_SLOT_ID[METRIC_KEY_CONTINUITY_SCHEMA],
        EVIDENCE_SCHEMA_TO_SLOT_ID[HANDOFF_COMPLETION_EVIDENCE_SCHEMA],
    )
)
_V50_REQUIRED_EVIDENCE_SLOT_IDS = sorted(EVIDENCE_SCHEMA_TO_SLOT_ID.values())
_MATRIX_REQUIRED_LANE_ID_LIST = [
    "deployment_mode",
    "adapter_id",
    "runtime_id",
]
_MATRIX_ENABLED_ROW_POLICY = "registry_is_enabled_only_disabled_rows_forbidden_non_v50"
_MATRIX_LANE_COUNT_AUTHORITY = "all_registry_rows_only_because_disabled_rows_are_forbidden"
_MATRIX_RUNTIME_ID_SOURCE_POLICY = "contract_derived_only_no_host_environment_inference"
_MATRIX_CANONICAL_SUBTREE_SOURCE_POLICY = (
    "existing_frozen_packaging_and_verifier_canonical_artifact_subject_family_only"
)
_MATRIX_POLICY_EQUIVALENCE_SUBJECT_KEYS = [
    "allowlist_violations",
    "forbidden_effects_detected",
    "issue_code_set",
    "required_evidence_slots_filled",
]
_MATRIX_POLICY_EQUIVALENCE_VALUE_SHAPES = {
    "issue_code_set": "lexicographically_sorted_unique_string_list_canonical_form",
    "required_evidence_slots_filled": "boolean",
    "allowlist_violations": "lexicographically_sorted_unique_normalized_posix_path_list",
    "forbidden_effects_detected": "boolean",
}
_MATRIX_DEPLOYMENT_MODES = ["adeu_integrated", "standalone"]
_MATRIX_RUNTIME_IDS = ["local_python_cli"]

_REQUIRED_VERIFIED_RESULT_KEYS = {
    "schema",
    "contract_schema",
    "taskpack_manifest_hash",
    "candidate_change_plan_hash",
    "runner_provenance_hash",
    "verification_result",
    "exit_status",
    "verified_result_hash",
    "verified_artifacts",
}

_EXPECTED_VERIFICATION_CROSS_CHECKS = [
    "taskpack_manifest_hash_match",
    "candidate_change_plan_hash_match",
    "policy_validation_result_consistency",
    "exit_status_consistency",
]


@dataclass(frozen=True)
class EvidenceWriterResult:
    evidence_bundle_path: Path
    evidence_bundle_hash: str
    verifier_provenance_path: Path
    verifier_provenance_hash: str
    rejection_diagnostic_path: Path | None


def _load_verified_result(path: Path) -> dict[str, Any]:
    payload = load_json_object(path)
    require_schema(payload, expected_schema=VERIFICATION_RESULT_SCHEMA, path=path)
    if set(payload.keys()) != _REQUIRED_VERIFIED_RESULT_KEYS:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="verified result keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
            artifact_path=str(path),
            policy_source="runner_provenance",
        )
    if payload.get("contract_schema") != "v33c_verifier_contract@1":
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="verified result contract_schema mismatch",
            details={"path": str(path), "contract_schema": payload.get("contract_schema")},
            artifact_path=str(path),
            policy_source="runner_provenance",
        )

    for field in (
        "taskpack_manifest_hash",
        "candidate_change_plan_hash",
        "runner_provenance_hash",
        "verified_result_hash",
    ):
        value = payload.get(field)
        if not isinstance(value, str) or not is_sha256(value):
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="verified result hash field is missing or invalid",
                details={"path": str(path), "field": field},
                artifact_path=str(path),
                policy_source="runner_provenance",
            )

    verification_result = payload.get("verification_result")
    if not isinstance(verification_result, dict):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="verified result verification_result must be an object",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="runner_provenance",
        )
    if set(verification_result.keys()) != {"passed", "issues", "cross_checks"}:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="verified result verification_result keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(verification_result.keys())},
            artifact_path=str(path),
            policy_source="runner_provenance",
        )
    if verification_result.get("passed") is not True:
        raise fail(
            code=AHK4612_EVIDENCE_EMISSION_AUTHORITY_VIOLATION,
            message="evidence emission requires verification_result.passed=true",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="runner_provenance",
        )
    if verification_result.get("issues") != []:
        raise fail(
            code=AHK4612_EVIDENCE_EMISSION_AUTHORITY_VIOLATION,
            message="evidence emission requires empty verification_result.issues",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="runner_provenance",
        )
    cross_checks = verification_result.get("cross_checks")
    if not isinstance(cross_checks, list) or cross_checks != _EXPECTED_VERIFICATION_CROSS_CHECKS:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="verified result cross_checks list mismatch",
            details={"path": str(path), "cross_checks": cross_checks},
            artifact_path=str(path),
            policy_source="runner_provenance",
        )

    expected_hash_subject = {
        "taskpack_manifest_hash": payload["taskpack_manifest_hash"],
        "candidate_change_plan_hash": payload["candidate_change_plan_hash"],
        "runner_provenance_hash": payload["runner_provenance_hash"],
        "verification_result": verification_result,
        "exit_status": payload.get("exit_status"),
    }
    recomputed_hash = sha256_canonical_json(expected_hash_subject)
    if recomputed_hash != payload["verified_result_hash"]:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="verified result hash recomputation mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="runner_provenance",
        )
    return payload


def _load_evidence_slots(path: Path) -> tuple[dict[str, Any], list[str]]:
    payload = load_json_object(path)
    require_schema(payload, expected_schema=EVIDENCE_SLOTS_SCHEMA, path=path)
    if set(payload.keys()) != {"schema", "profile_id", "required_count", "slots"}:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="EVIDENCE_SLOTS payload keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
            artifact_path=str(path),
            policy_source="evidence_slots",
        )
    slots = payload.get("slots")
    if not isinstance(slots, list) or not slots:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="EVIDENCE_SLOTS slots must be a non-empty array",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="evidence_slots",
        )

    normalized_slots: list[dict[str, Any]] = []
    for index, slot in enumerate(slots):
        if not isinstance(slot, dict):
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="EVIDENCE_SLOTS slot entry must be an object",
                details={"path": str(path), "index": index},
                artifact_path=str(path),
                policy_source="evidence_slots",
            )
        if set(slot.keys()) != {"slot_id", "description", "required"}:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="EVIDENCE_SLOTS slot keys must match frozen grammar",
                details={"path": str(path), "index": index, "keys": sorted(slot.keys())},
                artifact_path=str(path),
                policy_source="evidence_slots",
            )
        slot_id = slot.get("slot_id")
        if not isinstance(slot_id, str) or not slot_id:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="EVIDENCE_SLOTS slot_id must be a non-empty string",
                details={"path": str(path), "index": index},
                artifact_path=str(path),
                policy_source="evidence_slots",
            )
        if not isinstance(slot.get("required"), bool):
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="EVIDENCE_SLOTS slot required must be boolean",
                details={"path": str(path), "index": index},
                artifact_path=str(path),
                policy_source="evidence_slots",
            )
        normalized_slots.append(slot)

    slot_ids = [slot["slot_id"] for slot in normalized_slots]
    if len(set(slot_ids)) != len(slot_ids):
        raise fail(
            code=AHK4608_CONTRACT_REGISTRY_INVALID,
            message="EVIDENCE_SLOTS slot_id entries must be unique",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="evidence_slots",
        )

    required_slot_ids = sorted(
        slot["slot_id"] for slot in normalized_slots if slot["required"] is True
    )
    if required_slot_ids not in (
        _BASE_REQUIRED_EVIDENCE_SLOT_IDS,
        _V50_REQUIRED_EVIDENCE_SLOT_IDS,
    ):
        raise fail(
            code=AHK4611_EVIDENCE_SLOT_OR_SCHEMA_VIOLATION,
            message="required evidence slots do not match an allowed frozen closeout slot set",
            details={
                "path": str(path),
                "required_slot_ids": required_slot_ids,
                "allowed_required_slot_sets": [
                    _BASE_REQUIRED_EVIDENCE_SLOT_IDS,
                    _V50_REQUIRED_EVIDENCE_SLOT_IDS,
                ],
            },
            artifact_path=str(path),
            policy_source="evidence_slots",
        )

    required_count = payload.get("required_count")
    if required_count != len(required_slot_ids):
        raise fail(
            code=AHK4611_EVIDENCE_SLOT_OR_SCHEMA_VIOLATION,
            message="required_count does not match required slot cardinality",
            details={
                "path": str(path),
                "required_count": required_count,
                "expected_required_count": len(required_slot_ids),
            },
            artifact_path=str(path),
            policy_source="evidence_slots",
        )

    return payload, required_slot_ids


def _validate_evidence_schema_allowlist() -> None:
    if set(EVIDENCE_SCHEMA_ALLOWLIST) != set(EVIDENCE_SCHEMA_TO_SLOT_ID):
        raise fail(
            code=AHK4611_EVIDENCE_SLOT_OR_SCHEMA_VIOLATION,
            message="evidence schema allowlist drift detected",
            details={
                "evidence_schema_allowlist": sorted(EVIDENCE_SCHEMA_ALLOWLIST),
                "evidence_schema_to_slot_id": sorted(EVIDENCE_SCHEMA_TO_SLOT_ID),
            },
            artifact_path="EVIDENCE_SLOTS.json",
            policy_source="evidence_slots",
        )


def _load_block(path: Path, *, expected_schema: str) -> dict[str, Any]:
    payload = load_json_object(path)
    require_schema(payload, expected_schema=expected_schema, path=path)
    canonicalized = json.loads(canonical_json(payload))
    if not isinstance(canonicalized, dict):
        raise fail(
            code=AHK4610_EVIDENCE_BUNDLE_HASH_SUBJECT_DRIFT,
            message="canonicalized evidence block must be an object",
            details={"path": str(path), "schema": expected_schema},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    return canonicalized


def _load_handoff_completion_evidence(path: Path) -> dict[str, Any]:
    payload = _load_block(path, expected_schema=HANDOFF_COMPLETION_EVIDENCE_SCHEMA)
    if set(payload.keys()) != _HANDOFF_COMPLETION_REQUIRED_KEYS:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="handoff completion evidence keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    for field in (
        "contract_source",
        "preflight_entrypoint",
        "runner_entrypoint",
        "verifier_entrypoint",
        "evidence_writer_entrypoint",
        "shared_binding_validator_used",
        "notes",
    ):
        value = payload.get(field)
        if not isinstance(value, str) or not value:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="handoff completion evidence string field must be non-empty",
                details={"path": str(path), "field": field},
                artifact_path=str(path),
                policy_source="stop_gate_metrics",
            )

    if (
        payload["shared_binding_validator_used"]
        != _HANDOFF_COMPLETION_SHARED_BINDING_VALIDATOR
    ):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="handoff completion evidence validator binding mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    packaging_entrypoints = payload.get("packaging_entrypoints")
    if (
        not isinstance(packaging_entrypoints, list)
        or not packaging_entrypoints
        or any(not isinstance(value, str) or not value for value in packaging_entrypoints)
        or len(set(packaging_entrypoints)) != len(packaging_entrypoints)
    ):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message=(
                "handoff completion evidence packaging_entrypoints must be "
                "unique non-empty strings"
            ),
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    binding_fields_verified = payload.get("binding_fields_verified")
    if binding_fields_verified != _HANDOFF_COMPLETION_REQUIRED_BINDING_FIELDS:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="handoff completion evidence binding_fields_verified mismatch",
            details={"path": str(path), "binding_fields_verified": binding_fields_verified},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    for field in (
        "verified_required",
        "signature_result_consumed_by_runner",
        "signature_result_consumed_by_verifier",
        "signature_result_consumed_by_packaging",
        "current_taskpack_snapshot_binding_enforced",
        "detached_user_supplied_handoff_forbidden",
        "historical_v47_to_v48_continuity_guard_repaired",
        "verification_passed",
        "metric_key_exact_set_equal_v48",
    ):
        if payload.get(field) is not True:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="handoff completion evidence boolean field must be true",
                details={"path": str(path), "field": field, "value": payload.get(field)},
                artifact_path=str(path),
                policy_source="stop_gate_metrics",
            )

    if payload.get("metric_key_cardinality") != 80:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="handoff completion evidence metric_key_cardinality must equal 80",
            details={
                "path": str(path),
                "metric_key_cardinality": payload.get("metric_key_cardinality"),
            },
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    return payload


def _load_matrix_parity_evidence(root: Path, path: Path) -> dict[str, Any]:
    payload = _load_block(path, expected_schema=MATRIX_PARITY_EVIDENCE_SCHEMA)
    if set(payload.keys()) != _MATRIX_PARITY_REQUIRED_KEYS:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="matrix parity evidence keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    for field in (
        "contract_source",
        "matrix_registry_path",
        "matrix_report_path",
        "runtime_id_source_policy",
        "canonical_subtree_source_policy",
        "notes",
    ):
        value = payload.get(field)
        if not isinstance(value, str) or not value:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="matrix parity evidence string field must be non-empty",
                details={"path": str(path), "field": field},
                artifact_path=str(path),
                policy_source="stop_gate_metrics",
            )

    if payload.get("matrix_report_hash") is None or not is_sha256(payload["matrix_report_hash"]):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="matrix parity evidence matrix_report_hash must be a sha256 string",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    if payload.get("lane_id_tuple") != _MATRIX_REQUIRED_LANE_ID_LIST:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="matrix parity evidence lane_id_tuple mismatch",
            details={"path": str(path), "lane_id_tuple": payload.get("lane_id_tuple")},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if payload.get("enabled_row_policy") != _MATRIX_ENABLED_ROW_POLICY:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="matrix parity evidence enabled_row_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if payload.get("lane_count_authority") != _MATRIX_LANE_COUNT_AUTHORITY:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="matrix parity evidence lane_count_authority mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if payload.get("runtime_id_source_policy") != _MATRIX_RUNTIME_ID_SOURCE_POLICY:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="matrix parity evidence runtime_id_source_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        payload.get("canonical_subtree_source_policy")
        != _MATRIX_CANONICAL_SUBTREE_SOURCE_POLICY
    ):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="matrix parity evidence canonical_subtree_source_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        payload.get("policy_equivalence_subject_keys_verified")
        != _MATRIX_POLICY_EQUIVALENCE_SUBJECT_KEYS
    ):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="matrix parity evidence policy_equivalence_subject_keys_verified mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        payload.get("policy_equivalence_value_shapes_verified")
        != _MATRIX_POLICY_EQUIVALENCE_VALUE_SHAPES
    ):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="matrix parity evidence policy_equivalence_value_shapes_verified mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    if payload.get("deployment_modes_covered") != _MATRIX_DEPLOYMENT_MODES:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="matrix parity evidence deployment_modes_covered mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if payload.get("runtime_ids_covered") != _MATRIX_RUNTIME_IDS:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="matrix parity evidence runtime_ids_covered mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    adapter_ids_covered = payload.get("adapter_ids_covered")
    if (
        not isinstance(adapter_ids_covered, list)
        or not adapter_ids_covered
        or any(not isinstance(value, str) or not value for value in adapter_ids_covered)
        or adapter_ids_covered != sorted(set(adapter_ids_covered))
    ):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="matrix parity evidence adapter_ids_covered must be sorted unique strings",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    for field in (
        "singleton_runtime_id_enforced",
        "runtime_id_host_inference_forbidden",
        "declared_registry_only",
        "lexicographic_lane_order_enforced",
        "canonical_subtree_exact_match_required",
        "policy_equivalence_exact_match_required",
        "report_covers_all_declared_lanes",
        "verification_passed",
        "metric_key_exact_set_equal_v49",
    ):
        if payload.get(field) is not True:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="matrix parity evidence boolean field must be true",
                details={"path": str(path), "field": field, "value": payload.get(field)},
                artifact_path=str(path),
                policy_source="stop_gate_metrics",
            )

    lane_count = payload.get("lane_count")
    if not isinstance(lane_count, int) or lane_count <= 0:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="matrix parity evidence lane_count must be a positive integer",
            details={"path": str(path), "lane_count": lane_count},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if payload.get("metric_key_cardinality") != 80:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="matrix parity evidence metric_key_cardinality must equal 80",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    matrix_registry_path = coerce_artifact_path(root, payload["matrix_registry_path"])
    matrix_report_path = coerce_artifact_path(root, payload["matrix_report_path"])
    matrix_registry_payload = load_json_object(matrix_registry_path)
    require_schema(
        matrix_registry_payload,
        expected_schema=ADAPTER_MATRIX_SCHEMA,
        path=matrix_registry_path,
    )
    matrix_report_payload = load_json_object(matrix_report_path)
    require_schema(
        matrix_report_payload,
        expected_schema=ADAPTER_MATRIX_PARITY_REPORT_SCHEMA,
        path=matrix_report_path,
    )

    if matrix_report_payload.get("report_hash") != payload["matrix_report_hash"]:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="matrix parity evidence report hash does not match matrix report payload",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if matrix_report_payload.get("matrix_registry_path") != payload["matrix_registry_path"]:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="matrix parity evidence registry path does not match matrix report payload",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        matrix_report_payload.get("matrix_registry_hash")
        != matrix_registry_payload.get("matrix_registry_hash")
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="matrix report matrix_registry_hash does not match matrix registry payload",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    lane_rows = matrix_report_payload.get("lane_rows")
    if not isinstance(lane_rows, list) or len(lane_rows) != lane_count:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="matrix parity evidence lane_count does not match matrix report lane rows",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if len(matrix_registry_payload.get("rows", [])) != lane_count:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="matrix parity evidence lane_count does not match matrix registry rows",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    report_adapter_ids = sorted(
        {
            row["adapter_id"]
            for row in lane_rows
            if isinstance(row, dict) and isinstance(row.get("adapter_id"), str)
        }
    )
    report_runtime_ids = sorted(
        {
            row["runtime_id"]
            for row in lane_rows
            if isinstance(row, dict) and isinstance(row.get("runtime_id"), str)
        }
    )
    report_deployment_modes = sorted(
        {
            row["deployment_mode"]
            for row in lane_rows
            if isinstance(row, dict) and isinstance(row.get("deployment_mode"), str)
        }
    )
    if report_adapter_ids != adapter_ids_covered:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="matrix parity evidence adapter_ids_covered mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if report_runtime_ids != payload["runtime_ids_covered"]:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="matrix parity evidence runtime_ids_covered mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if report_deployment_modes != payload["deployment_modes_covered"]:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="matrix parity evidence deployment_modes_covered mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    pairwise_parity = matrix_report_payload.get("pairwise_parity")
    if (
        not isinstance(pairwise_parity, list)
        or not pairwise_parity
        or any(
            not isinstance(row, dict)
            or row.get("canonical_subtree_exact_match") is not True
            or row.get("policy_equivalence_exact_match") is not True
            for row in pairwise_parity
        )
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message=(
                "matrix parity evidence requires pairwise parity rows with exact-match "
                "booleans"
            ),
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    return payload


def _emit_verifier_provenance(
    *,
    root: Path,
    evidence_root: Path,
    taskpack_manifest_hash: str,
    candidate_change_plan_hash: str,
    runner_provenance_hash: str,
    verification_result: dict[str, Any],
    evidence_bundle_hash: str,
) -> tuple[Path, str]:
    payload = {
        "schema": VERIFIER_PROVENANCE_SCHEMA,
        "taskpack_manifest_hash": taskpack_manifest_hash,
        "candidate_change_plan_hash": candidate_change_plan_hash,
        "runner_provenance_hash": runner_provenance_hash,
        "verification_result": verification_result,
        "evidence_bundle_hash": evidence_bundle_hash,
        "exit_status": "success",
    }
    hashed_subject = {
        "taskpack_manifest_hash": payload["taskpack_manifest_hash"],
        "candidate_change_plan_hash": payload["candidate_change_plan_hash"],
        "runner_provenance_hash": payload["runner_provenance_hash"],
        "verification_result": payload["verification_result"],
        "evidence_bundle_hash": payload["evidence_bundle_hash"],
        "exit_status": payload["exit_status"],
    }
    provenance_hash = sha256_canonical_json(hashed_subject)
    payload["provenance_hash"] = provenance_hash

    provenance_path = (
        evidence_root
        / "provenance"
        / f"{taskpack_manifest_hash}_{candidate_change_plan_hash}.json"
    )
    write_json(provenance_path, payload)

    loaded = load_json_object(provenance_path)
    require_schema(loaded, expected_schema=VERIFIER_PROVENANCE_SCHEMA, path=provenance_path)
    loaded_hash = loaded.get("provenance_hash")
    if not isinstance(loaded_hash, str) or not is_sha256(loaded_hash):
        raise fail(
            code=AHK4613_VERIFIER_PROVENANCE_INVALID,
            message="verifier provenance_hash is missing or invalid",
            details={"path": str(provenance_path)},
            artifact_path=str(provenance_path),
            policy_source="runner_provenance",
        )
    if loaded_hash != provenance_hash:
        raise fail(
            code=AHK4613_VERIFIER_PROVENANCE_INVALID,
            message="verifier provenance_hash drift detected",
            details={"path": str(provenance_path)},
            artifact_path=str(provenance_path),
            policy_source="runner_provenance",
        )

    return provenance_path, provenance_hash


def write_closeout_evidence(
    *,
    taskpack_dir: str | Path,
    verified_result_path: str | Path,
    runtime_observability_comparison_path: str | Path,
    metric_key_continuity_assertion_path: str | Path,
    handoff_completion_evidence_path: str | Path,
    matrix_parity_evidence_path: str | Path | None = None,
    evidence_output_root: str | Path,
    diagnostic_registry_path: str | Path,
    repo_root_path: str | Path | None = None,
) -> EvidenceWriterResult:
    require_deterministic_env_v46()
    root = project_repo_root(Path(repo_root_path) if repo_root_path is not None else None)

    manifest_hash: str | None = None
    candidate_hash: str | None = None
    registry_codes: set[str] = set()
    rejection_diagnostic_path: Path | None = None

    try:
        _validate_evidence_schema_allowlist()
        _, registry_codes = load_diagnostic_registry(
            root=root,
            registry_rel_path=normalize_relative_path(str(diagnostic_registry_path)),
        )

        taskpack_rel = normalize_relative_path(str(taskpack_dir))
        verified_result_rel = normalize_relative_path(str(verified_result_path))
        runtime_rel = normalize_relative_path(str(runtime_observability_comparison_path))
        continuity_rel = normalize_relative_path(str(metric_key_continuity_assertion_path))
        handoff_rel = normalize_relative_path(str(handoff_completion_evidence_path))
        matrix_rel = (
            None
            if matrix_parity_evidence_path is None
            else normalize_relative_path(str(matrix_parity_evidence_path))
        )
        evidence_output_rel = normalize_relative_path(str(evidence_output_root))

        taskpack_path = coerce_artifact_path(root, taskpack_rel)
        verified_result_artifact_path = coerce_artifact_path(root, verified_result_rel)
        runtime_path = coerce_artifact_path(root, runtime_rel)
        continuity_path = coerce_artifact_path(root, continuity_rel)
        handoff_path = coerce_artifact_path(root, handoff_rel)
        matrix_path = None if matrix_rel is None else coerce_artifact_path(root, matrix_rel)
        evidence_root = coerce_artifact_path(root, evidence_output_rel)

        try:
            manifest_hash = verify_taskpack_bundle(out_dir=taskpack_rel, repo_root_path=root)
        except TaskpackCompileError as exc:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="taskpack bundle verification failed",
                details={"error": str(exc), "taskpack_dir": taskpack_rel},
                artifact_path=taskpack_rel,
                policy_source="taskpack_manifest",
            ) from exc

        verified_result_payload = _load_verified_result(verified_result_artifact_path)
        candidate_hash = verified_result_payload["candidate_change_plan_hash"]
        if verified_result_payload["taskpack_manifest_hash"] != manifest_hash:
            raise fail(
                code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
                message="verified result taskpack_manifest_hash mismatch",
                details={"path": verified_result_rel},
                artifact_path=verified_result_rel,
                policy_source="taskpack_manifest",
            )

        _, required_slot_ids = _load_evidence_slots(taskpack_path / "EVIDENCE_SLOTS.json")
        matrix_slot_required = (
            EVIDENCE_SCHEMA_TO_SLOT_ID[MATRIX_PARITY_EVIDENCE_SCHEMA] in required_slot_ids
        )
        if matrix_slot_required and matrix_path is None:
            raise fail(
                code=AHK4611_EVIDENCE_SLOT_OR_SCHEMA_VIOLATION,
                message="matrix parity evidence block is required by EVIDENCE_SLOTS",
                details={"path": str(taskpack_path / 'EVIDENCE_SLOTS.json')},
                artifact_path=str(taskpack_path / "EVIDENCE_SLOTS.json"),
                policy_source="evidence_slots",
            )
        if not matrix_slot_required and matrix_path is not None:
            raise fail(
                code=AHK4611_EVIDENCE_SLOT_OR_SCHEMA_VIOLATION,
                message="matrix parity evidence block is not authorized by EVIDENCE_SLOTS",
                details={"path": str(taskpack_path / 'EVIDENCE_SLOTS.json')},
                artifact_path=str(taskpack_path / "EVIDENCE_SLOTS.json"),
                policy_source="evidence_slots",
            )

        blocks = [
            {
                "slot_id": EVIDENCE_SCHEMA_TO_SLOT_ID[RUNTIME_OBSERVABILITY_SCHEMA],
                "schema": RUNTIME_OBSERVABILITY_SCHEMA,
                "payload": _load_block(runtime_path, expected_schema=RUNTIME_OBSERVABILITY_SCHEMA),
            },
            {
                "slot_id": EVIDENCE_SCHEMA_TO_SLOT_ID[METRIC_KEY_CONTINUITY_SCHEMA],
                "schema": METRIC_KEY_CONTINUITY_SCHEMA,
                "payload": _load_block(
                    continuity_path,
                    expected_schema=METRIC_KEY_CONTINUITY_SCHEMA,
                ),
            },
            {
                "slot_id": EVIDENCE_SCHEMA_TO_SLOT_ID[HANDOFF_COMPLETION_EVIDENCE_SCHEMA],
                "schema": HANDOFF_COMPLETION_EVIDENCE_SCHEMA,
                "payload": _load_handoff_completion_evidence(handoff_path),
            },
        ]
        if matrix_slot_required:
            assert matrix_path is not None
            blocks.append(
                {
                    "slot_id": EVIDENCE_SCHEMA_TO_SLOT_ID[MATRIX_PARITY_EVIDENCE_SCHEMA],
                    "schema": MATRIX_PARITY_EVIDENCE_SCHEMA,
                    "payload": _load_matrix_parity_evidence(root, matrix_path),
                }
            )
        blocks = sorted(blocks, key=lambda row: (row["slot_id"], row["schema"]))

        emitted_schemas = tuple(block["schema"] for block in blocks)
        expected_schemas = {
            schema
            for schema, slot_id in EVIDENCE_SCHEMA_TO_SLOT_ID.items()
            if slot_id in required_slot_ids
        }
        if set(emitted_schemas) != expected_schemas:
            raise fail(
                code=AHK4611_EVIDENCE_SLOT_OR_SCHEMA_VIOLATION,
                message="emitted evidence schema set must match frozen closeout allowlist",
                details={
                    "emitted_schemas": emitted_schemas,
                    "expected_schemas": sorted(expected_schemas),
                },
                artifact_path=evidence_output_rel,
                policy_source="evidence_slots",
            )

        ordered_rejection_diagnostics_optional: list[dict[str, Any]] = []
        hash_subject = {
            "taskpack_manifest_hash": manifest_hash,
            "ordered_evidence_blocks": blocks,
            "ordered_rejection_diagnostics_optional": ordered_rejection_diagnostics_optional,
        }
        evidence_bundle_hash = sha256_canonical_json(hash_subject)

        bundle_payload = {
            "schema": EVIDENCE_BUNDLE_SCHEMA,
            "taskpack_manifest_hash": manifest_hash,
            "candidate_change_plan_hash": candidate_hash,
            "ordered_evidence_blocks": blocks,
            "ordered_rejection_diagnostics_optional": ordered_rejection_diagnostics_optional,
            "evidence_bundle_hash": evidence_bundle_hash,
        }

        bundle_path = evidence_root / f"{manifest_hash}_{candidate_hash}.json"
        write_json(bundle_path, bundle_payload)
        write_json(
            evidence_root / f"{manifest_hash}_{candidate_hash}.sha256.json",
            {
                "schema": "taskpack_closeout_evidence_bundle_hash@1",
                "taskpack_manifest_hash": manifest_hash,
                "candidate_change_plan_hash": candidate_hash,
                "evidence_bundle_hash": evidence_bundle_hash,
            },
        )

        loaded_bundle = load_json_object(bundle_path)
        require_schema(loaded_bundle, expected_schema=EVIDENCE_BUNDLE_SCHEMA, path=bundle_path)
        if loaded_bundle.get("evidence_bundle_hash") != evidence_bundle_hash:
            raise fail(
                code=AHK4610_EVIDENCE_BUNDLE_HASH_SUBJECT_DRIFT,
                message="evidence bundle hash drift detected",
                details={"path": str(bundle_path)},
                artifact_path=str(bundle_path),
                policy_source="stop_gate_metrics",
            )

        verifier_provenance_path, verifier_provenance_hash = _emit_verifier_provenance(
            root=root,
            evidence_root=evidence_root,
            taskpack_manifest_hash=manifest_hash,
            candidate_change_plan_hash=candidate_hash,
            runner_provenance_hash=verified_result_payload["runner_provenance_hash"],
            verification_result=verified_result_payload["verification_result"],
            evidence_bundle_hash=evidence_bundle_hash,
        )

        return EvidenceWriterResult(
            evidence_bundle_path=bundle_path,
            evidence_bundle_hash=evidence_bundle_hash,
            verifier_provenance_path=verifier_provenance_path,
            verifier_provenance_hash=verifier_provenance_hash,
            rejection_diagnostic_path=None,
        )

    except TaskpackVerifierError as exc:
        if not registry_codes:
            registry_codes = {
                AHK4603_ARTIFACT_INVALID,
                AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
                AHK4608_CONTRACT_REGISTRY_INVALID,
                AHK4610_EVIDENCE_BUNDLE_HASH_SUBJECT_DRIFT,
                AHK4611_EVIDENCE_SLOT_OR_SCHEMA_VIOLATION,
                AHK4612_EVIDENCE_EMISSION_AUTHORITY_VIOLATION,
                AHK4613_VERIFIER_PROVENANCE_INVALID,
                AHK4615_VERIFICATION_FAILURE_WITHOUT_REJECTION_DIAGNOSTIC,
            }

        issue = exc.issue or VerifierIssue(
            issue_code=exc.code,
            reason=exc.message,
            artifact_path=exc.details.get("path", ""),
            evidence_slot_id="evidence_writer",
            policy_source="runner_result",
        )
        if issue.policy_source not in POLICY_SOURCE_ENUM_V46:
            issue = VerifierIssue(
                issue_code=issue.issue_code,
                reason=issue.reason,
                artifact_path=issue.artifact_path,
                evidence_slot_id=issue.evidence_slot_id,
                policy_source="runner_result",
            )

        try:
            rejection_diagnostic_path = emit_rejection_diagnostic(
                root=root,
                output_root_rel=DEFAULT_REJECTIONS_ROOT,
                taskpack_manifest_hash=manifest_hash,
                candidate_change_plan_hash=candidate_hash,
                issues=[issue],
                allowed_codes=registry_codes,
            )
        except TaskpackVerifierError as rejection_exc:
            raise TaskpackVerifierError(
                code=AHK4615_VERIFICATION_FAILURE_WITHOUT_REJECTION_DIAGNOSTIC,
                message="evidence writer failure without rejection diagnostic emission",
                details={
                    "original_error": str(exc),
                    "rejection_error": str(rejection_exc),
                },
                issue=VerifierIssue(
                    issue_code=AHK4615_VERIFICATION_FAILURE_WITHOUT_REJECTION_DIAGNOSTIC,
                    reason="evidence writer failure without rejection diagnostic emission",
                    artifact_path=exc.details.get("path", ""),
                    evidence_slot_id="evidence_writer",
                    policy_source="stop_gate_metrics",
                ),
            ) from exc

        details = dict(exc.details)
        details["rejection_diagnostic_path"] = rejection_diagnostic_path.as_posix()
        raise TaskpackVerifierError(
            code=exc.code,
            message=exc.message,
            details=details,
            issue=issue,
        ) from exc


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Emit deterministic closeout evidence bundle from verified-result "
            "artifact and allowlisted closeout block payloads."
        ),
    )
    parser.add_argument(
        "--taskpack-dir",
        required=True,
        help="Repo-relative taskpack directory containing EVIDENCE_SLOTS.json authority.",
    )
    parser.add_argument(
        "--verified-result",
        required=True,
        help="Repo-relative path to taskpack_verification_result@1 artifact.",
    )
    parser.add_argument(
        "--runtime-observability-comparison",
        required=True,
        help="Repo-relative path to runtime_observability_comparison@1 payload.",
    )
    parser.add_argument(
        "--metric-key-continuity-assertion",
        required=True,
        help="Repo-relative path to metric_key_continuity_assertion@1 payload.",
    )
    parser.add_argument(
        "--handoff-completion-evidence",
        required=True,
        help="Repo-relative path to v34a_handoff_completion_evidence@1 payload.",
    )
    parser.add_argument(
        "--matrix-parity-evidence",
        default=None,
        help="Optional repo-relative path to v34b_matrix_parity_evidence@1 payload.",
    )
    parser.add_argument(
        "--evidence-output-root",
        default=DEFAULT_EVIDENCE_ROOT,
        help="Repo-relative output root for evidence bundle/provenance artifacts.",
    )
    parser.add_argument(
        "--diagnostic-registry",
        default=DEFAULT_DIAGNOSTIC_REGISTRY_PATH,
        help="Repo-relative path to authoritative v46 diagnostic registry JSON.",
    )
    parser.add_argument(
        "--repo-root",
        default=None,
        help="Optional repository root override. Defaults to deterministic repo_root(anchor=cwd).",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        result = write_closeout_evidence(
            taskpack_dir=args.taskpack_dir,
            verified_result_path=args.verified_result,
            runtime_observability_comparison_path=args.runtime_observability_comparison,
            metric_key_continuity_assertion_path=args.metric_key_continuity_assertion,
            handoff_completion_evidence_path=args.handoff_completion_evidence,
            matrix_parity_evidence_path=args.matrix_parity_evidence,
            evidence_output_root=args.evidence_output_root,
            diagnostic_registry_path=args.diagnostic_registry,
            repo_root_path=args.repo_root,
        )
    except TaskpackVerifierError as exc:
        sys.stderr.write(str(exc) + "\n")
        return 1

    payload = {
        "schema": EVIDENCE_WRITER_RESULT_SCHEMA,
        "evidence_bundle_path": result.evidence_bundle_path.as_posix(),
        "evidence_bundle_hash": result.evidence_bundle_hash,
        "verifier_provenance_path": result.verifier_provenance_path.as_posix(),
        "verifier_provenance_hash": result.verifier_provenance_hash,
        "rejection_diagnostic_path": (
            result.rejection_diagnostic_path.as_posix()
            if result.rejection_diagnostic_path is not None
            else None
        ),
    }
    sys.stdout.write(canonical_json(payload) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
