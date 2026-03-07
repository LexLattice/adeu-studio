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
from .attestation import (
    ATTESTATION_BINDING_FIELDS,
    ATTESTATION_VERIFICATION_RESULT_SCHEMA,
    LOCAL_EQUIVALENCE_BINDING_FIELDS,
    LOCAL_EQUIVALENCE_SUBJECT_FIELDS,
    LOCAL_EQUIVALENCE_SUBJECT_POLICY,
    LOCAL_VERIFIER_ENTRYPOINT,
    NORMALIZED_CLAIM_FIELDS,
    PROVIDER_ATTESTATION_INPUT_SCHEMA,
    PROVIDER_ID,
    PROVIDER_ID_COMPARISON_POLICY,
    REMOTE_ENCLAVE_ATTESTATION_SCHEMA,
    SHARED_ATTESTATION_VALIDATOR,
    SHARED_ATTESTATION_VALIDATOR_IDENTIFIER,
    SHARED_ATTESTATION_VALIDATOR_IDENTIFIER_POLICY,
)
from .attestation import (
    RUNNER_PROVENANCE_HASH_POLICY as ATTESTATION_RUNNER_PROVENANCE_HASH_POLICY,
)
from .attestation import (
    VERIFICATION_PASSED_POLICY as ATTESTATION_VERIFICATION_PASSED_POLICY,
)
from .compile import TaskpackCompileError, verify_taskpack_bundle
from .policy_recompute import (
    ALLOWED_ISSUE_CODES,
    COMPARISON_SUBJECT_FIELDS,
    ISSUE_TUPLE_FIELDS,
    ISSUE_TUPLE_ORDER_POLICY,
    ISSUES_REPRESENTATION_POLICY,
    POLICY_RECOMPUTE_RESULT_SCHEMA,
    SHARED_RECOMPUTE_ENGINE,
)
from .retry_context import (
    CONTROL_MARKER_NEUTRALIZATION,
    DETERMINISTIC_ISSUE_ORDER_POLICY,
    ESCAPING_POLICY,
    MAX_EXCERPT_CHARS_PER_ISSUE,
    MAX_EXCERPT_LINES_PER_ISSUE,
    MAX_ISSUE_COUNT,
    MAX_REASON_CHARS,
    MAX_TOTAL_OUTPUT_CHARS,
    MISSING_EXCERPT_SOURCE_POLICY,
    OVERFLOW_POLICY,
    RETRY_CONTEXT_FEEDER_RESULT_SCHEMA,
    RETRY_CONTEXT_SANITIZATION_PROFILE_SCHEMA,
    SHARED_FEEDER_ENGINE,
    SHARED_FEEDER_ENGINE_IDENTIFIER,
    WHITESPACE_POLICY,
)
from .retry_context import (
    POLICY_SOURCE_POLICY as RETRY_CONTEXT_POLICY_SOURCE_POLICY,
)
from .retry_context import (
    TARGET_PATH_NORMALIZATION_POLICY as RETRY_CONTEXT_TARGET_PATH_NORMALIZATION_POLICY,
)
from .retry_context import (
    VERIFICATION_PASSED_POLICY as RETRY_CONTEXT_VERIFICATION_PASSED_POLICY,
)
from .verify_taskpack_run import (
    RUNNER_PROVENANCE_SCHEMA as TASKPACK_RUNNER_PROVENANCE_SCHEMA,
)
from .verify_taskpack_run import (
    VERIFICATION_RESULT_SCHEMA,
)

EVIDENCE_SLOTS_SCHEMA = "taskpack/evidence_slots@1"

EVIDENCE_BUNDLE_SCHEMA = "taskpack_closeout_evidence_bundle@1"
VERIFIER_PROVENANCE_SCHEMA = "taskpack_verifier_provenance@1"
EVIDENCE_WRITER_RESULT_SCHEMA = "taskpack_evidence_writer_result@1"

DEFAULT_EVIDENCE_ROOT = "artifacts/agent_harness/v46/evidence"

RUNTIME_OBSERVABILITY_SCHEMA = "runtime_observability_comparison@1"
METRIC_KEY_CONTINUITY_SCHEMA = "metric_key_continuity_assertion@1"
HANDOFF_COMPLETION_EVIDENCE_SCHEMA = "v34a_handoff_completion_evidence@1"
MATRIX_PARITY_EVIDENCE_SCHEMA = "v34b_matrix_parity_evidence@1"
POLICY_RECOMPUTE_EVIDENCE_SCHEMA = "v34c_policy_recompute_evidence@1"
RETRY_CONTEXT_EVIDENCE_SCHEMA = "v34d_retry_context_evidence@1"
ATTESTATION_EVIDENCE_SCHEMA = "v34e_attestation_evidence@1"
ADAPTER_MATRIX_SCHEMA = "adapter_matrix@1"
ADAPTER_MATRIX_PARITY_REPORT_SCHEMA = "adapter_matrix_parity_report@1"

EVIDENCE_SCHEMA_ALLOWLIST = (
    RUNTIME_OBSERVABILITY_SCHEMA,
    METRIC_KEY_CONTINUITY_SCHEMA,
    HANDOFF_COMPLETION_EVIDENCE_SCHEMA,
    MATRIX_PARITY_EVIDENCE_SCHEMA,
    POLICY_RECOMPUTE_EVIDENCE_SCHEMA,
    RETRY_CONTEXT_EVIDENCE_SCHEMA,
    ATTESTATION_EVIDENCE_SCHEMA,
)

EVIDENCE_SCHEMA_TO_SLOT_ID = {
    RUNTIME_OBSERVABILITY_SCHEMA: "runtime_observability_comparison",
    METRIC_KEY_CONTINUITY_SCHEMA: "metric_key_continuity_assertion",
    HANDOFF_COMPLETION_EVIDENCE_SCHEMA: "v34a_handoff_completion_evidence",
    MATRIX_PARITY_EVIDENCE_SCHEMA: "v34b_matrix_parity_evidence",
    POLICY_RECOMPUTE_EVIDENCE_SCHEMA: "v34c_policy_recompute_evidence",
    RETRY_CONTEXT_EVIDENCE_SCHEMA: "v34d_retry_context_evidence",
    ATTESTATION_EVIDENCE_SCHEMA: "v34e_attestation_evidence",
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
_POLICY_RECOMPUTE_EVIDENCE_REQUIRED_KEYS = {
    "schema",
    "contract_source",
    "recompute_entrypoint",
    "shared_recompute_engine_used",
    "verifier_entrypoint",
    "policy_recompute_result_path",
    "policy_recompute_result_hash",
    "comparison_subject_fields",
    "exit_status_subject_policy",
    "issue_tuple_fields",
    "issue_tuple_order_policy",
    "issues_representation_policy",
    "duplicate_issue_tuples_forbidden",
    "allowed_issue_codes",
    "allowed_issue_codes_closed_exact",
    "candidate_change_plan_binding_policy",
    "runner_policy_failure_input_materialization_required",
    "runner_reason_line_range_non_authoritative",
    "mismatch_fail_closed",
    "exact_match_requires_empty_deltas",
    "policy_recompute_result_emitted",
    "typed_diff_summary_emitted",
    "success_class_verification_result_forbidden_on_mismatch",
    "verification_passed",
    "metric_key_cardinality",
    "metric_key_exact_set_equal_v50",
    "notes",
}
_RETRY_CONTEXT_EVIDENCE_REQUIRED_KEYS = {
    "schema",
    "contract_source",
    "feeder_entrypoint",
    "shared_feeder_engine_used",
    "shared_feeder_engine_identifier",
    "retry_context_feeder_result_path",
    "retry_context_feeder_result_hash",
    "sanitization_profile_path",
    "sanitization_profile_hash",
    "source_rejection_diagnostic_schema",
    "policy_source_closed_inherited_surface",
    "runner_result_semantic_input_forbidden",
    "advisory_only_non_authoritative",
    "automatic_retry_dispatch_forbidden",
    "downstream_diagnostic_aggregation_forbidden",
    "policy_success_explicit_request_without_diagnostic_fails_closed",
    "raw_repo_file_content_forbidden",
    "duplicate_issue_tuples_forbidden",
    "excerpt_bounds_enforced",
    "overflow_policy",
    "missing_excerpt_source_policy",
    "total_output_bound_enforced",
    "control_marker_neutralization_enforced",
    "deterministic_issue_order_enforced",
    "verification_passed",
    "verification_passed_policy",
    "success_path_absence_without_request_allowed",
    "metric_key_cardinality",
    "metric_key_exact_set_equal_v51",
    "notes",
}
_ATTESTATION_EVIDENCE_REQUIRED_KEYS = {
    "schema",
    "contract_source",
    "attestation_entrypoint",
    "shared_attestation_validator_used",
    "shared_attestation_validator_identifier",
    "shared_attestation_validator_identifier_policy",
    "local_verifier_entrypoint",
    "remote_enclave_attestation_path",
    "remote_enclave_attestation_hash",
    "attested_verified_result_path",
    "attested_verified_result_hash",
    "local_verified_result_path",
    "local_verified_result_hash",
    "attestation_verification_result_path",
    "attestation_verification_result_hash",
    "provider_id",
    "provider_id_closed_singleton_enforced",
    "provider_id_comparison_policy",
    "attestation_trust_anchor_registry_reused",
    "runner_provenance_hash_policy",
    "attestation_verified_required",
    "input_mode_artifact_ingestion_only",
    "attested_verified_result_schema_validated",
    "current_local_verification_recomputed",
    "current_local_verification_materialization_failure_fails_closed",
    "local_equivalence_required",
    "local_equivalence_subject_fields_verified",
    "local_equivalence_binding_fields_verified",
    "local_equivalence_subject_policy",
    "local_equivalence_verified",
    "opaque_provider_evidence_hash_audit_only",
    "normalized_claim_conflicts_forbidden",
    "remote_transport_or_job_dispatch_forbidden",
    "deployment_mode_expansion_forbidden",
    "verification_passed",
    "verification_passed_policy",
    "metric_key_cardinality",
    "metric_key_exact_set_equal_v52",
    "notes",
}
_BASE_REQUIRED_EVIDENCE_SLOT_IDS = sorted(
    (
        EVIDENCE_SCHEMA_TO_SLOT_ID[RUNTIME_OBSERVABILITY_SCHEMA],
        EVIDENCE_SCHEMA_TO_SLOT_ID[METRIC_KEY_CONTINUITY_SCHEMA],
        EVIDENCE_SCHEMA_TO_SLOT_ID[HANDOFF_COMPLETION_EVIDENCE_SCHEMA],
    )
)
_V50_REQUIRED_EVIDENCE_SLOT_IDS = sorted(
    (
        *_BASE_REQUIRED_EVIDENCE_SLOT_IDS,
        EVIDENCE_SCHEMA_TO_SLOT_ID[MATRIX_PARITY_EVIDENCE_SCHEMA],
    )
)
_V51_REQUIRED_EVIDENCE_SLOT_IDS = sorted(
    (
        *_V50_REQUIRED_EVIDENCE_SLOT_IDS,
        EVIDENCE_SCHEMA_TO_SLOT_ID[POLICY_RECOMPUTE_EVIDENCE_SCHEMA],
    )
)
_V52_REQUIRED_EVIDENCE_SLOT_IDS = sorted(
    (
        *_V51_REQUIRED_EVIDENCE_SLOT_IDS,
        EVIDENCE_SCHEMA_TO_SLOT_ID[RETRY_CONTEXT_EVIDENCE_SCHEMA],
    )
)
_V53_REQUIRED_EVIDENCE_SLOT_IDS = sorted(
    (
        *_V52_REQUIRED_EVIDENCE_SLOT_IDS,
        EVIDENCE_SCHEMA_TO_SLOT_ID[ATTESTATION_EVIDENCE_SCHEMA],
    )
)
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
_POLICY_RECOMPUTE_EXIT_STATUS_SUBJECT_POLICY = (
    "runner_policy_verdict_status_under_frozen_validator_scope_not_verifier_process_exit_code"
)
_POLICY_RECOMPUTE_CANDIDATE_CHANGE_PLAN_BINDING_POLICY = (
    "recompute_binds_to_runner_recorded_canonical_candidate_change_plan_hash_"
    "runner_result_dry_run_supplies_execution_mode_only"
)
_RETRY_CONTEXT_SOURCE_REJECTION_DIAGNOSTIC_SCHEMA = "candidate_change_plan_rejection_diagnostic@1"

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
_REMOTE_ATTESTATION_REQUIRED_KEYS = {
    "schema",
    "shared_attestation_validator",
    "shared_attestation_validator_identifier",
    "source_provider_schema",
    "input_mode_artifact_ingestion_only",
    "provider_id_comparison_policy",
    "provider_id_closed_singleton_enforced",
    "opaque_provider_evidence_hash_audit_only",
    "normalized_claim_conflicts_forbidden",
    "normalized_claim_fields",
    "normalized_claims",
    "attestation_verified",
    "attestation_hash",
}
_ATTESTATION_VERIFICATION_RESULT_REQUIRED_KEYS = {
    "schema",
    "contract_schema",
    "shared_attestation_validator",
    "shared_attestation_validator_identifier",
    "local_verifier_entrypoint",
    "remote_enclave_attestation_path",
    "remote_enclave_attestation_hash",
    "attested_verified_result_path",
    "attested_verified_result_hash",
    "local_verified_result_path",
    "local_verified_result_hash",
    "taskpack_manifest_hash",
    "candidate_change_plan_hash",
    "runner_provenance_hash",
    "trust_anchor_registry_hash",
    "verification_reference_time_utc",
    "provider_id",
    "provider_id_closed_singleton_enforced",
    "provider_id_comparison_policy",
    "attestation_trust_anchor_registry_reused",
    "attestation_key_id",
    "algorithm",
    "runner_provenance_hash_policy",
    "attestation_binding_fields_verified",
    "attestation_verified",
    "input_mode_artifact_ingestion_only",
    "attested_verified_result_schema_validated",
    "current_local_verification_recomputed",
    "current_local_verification_materialization_failure_fails_closed",
    "local_equivalence_required",
    "local_equivalence_subject_fields_verified",
    "local_equivalence_binding_fields_verified",
    "local_equivalence_subject_policy",
    "local_equivalence_verified",
    "opaque_provider_evidence_hash_audit_only",
    "normalized_claim_conflicts_forbidden",
    "remote_transport_or_job_dispatch_forbidden",
    "deployment_mode_expansion_forbidden",
    "verification_passed",
    "verification_passed_policy",
    "result_hash",
}


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
        _V51_REQUIRED_EVIDENCE_SLOT_IDS,
        _V52_REQUIRED_EVIDENCE_SLOT_IDS,
        _V53_REQUIRED_EVIDENCE_SLOT_IDS,
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
                    _V51_REQUIRED_EVIDENCE_SLOT_IDS,
                    _V52_REQUIRED_EVIDENCE_SLOT_IDS,
                    _V53_REQUIRED_EVIDENCE_SLOT_IDS,
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


def _recompute_self_hash(payload: dict[str, Any], *, hash_field: str) -> str:
    hash_subject = dict(payload)
    hash_subject.pop(hash_field, None)
    return sha256_canonical_json(hash_subject)


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


def _load_policy_recompute_evidence(
    root: Path,
    path: Path,
    *,
    verified_result_payload: dict[str, Any],
) -> dict[str, Any]:
    payload = _load_block(path, expected_schema=POLICY_RECOMPUTE_EVIDENCE_SCHEMA)
    if set(payload.keys()) != _POLICY_RECOMPUTE_EVIDENCE_REQUIRED_KEYS:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="policy recompute evidence keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    for field in (
        "contract_source",
        "recompute_entrypoint",
        "shared_recompute_engine_used",
        "verifier_entrypoint",
        "policy_recompute_result_path",
        "exit_status_subject_policy",
        "issue_tuple_order_policy",
        "issues_representation_policy",
        "candidate_change_plan_binding_policy",
        "notes",
    ):
        value = payload.get(field)
        if not isinstance(value, str) or not value:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="policy recompute evidence string field must be non-empty",
                details={"path": str(path), "field": field},
                artifact_path=str(path),
                policy_source="stop_gate_metrics",
            )

    if payload.get("shared_recompute_engine_used") != SHARED_RECOMPUTE_ENGINE:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="policy recompute evidence shared_recompute_engine_used mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if payload.get("comparison_subject_fields") != list(COMPARISON_SUBJECT_FIELDS):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="policy recompute evidence comparison_subject_fields mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if payload.get("exit_status_subject_policy") != _POLICY_RECOMPUTE_EXIT_STATUS_SUBJECT_POLICY:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="policy recompute evidence exit_status_subject_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if payload.get("issue_tuple_fields") != list(ISSUE_TUPLE_FIELDS):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="policy recompute evidence issue_tuple_fields mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if payload.get("issue_tuple_order_policy") != ISSUE_TUPLE_ORDER_POLICY:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="policy recompute evidence issue_tuple_order_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if payload.get("issues_representation_policy") != ISSUES_REPRESENTATION_POLICY:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="policy recompute evidence issues_representation_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if payload.get("allowed_issue_codes") != list(ALLOWED_ISSUE_CODES):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="policy recompute evidence allowed_issue_codes mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        payload.get("candidate_change_plan_binding_policy")
        != _POLICY_RECOMPUTE_CANDIDATE_CHANGE_PLAN_BINDING_POLICY
    ):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="policy recompute evidence candidate_change_plan_binding_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    if (
        payload.get("policy_recompute_result_hash") is None
        or not is_sha256(payload["policy_recompute_result_hash"])
    ):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message=(
                "policy recompute evidence policy_recompute_result_hash must be a "
                "sha256 string"
            ),
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    for field in (
        "duplicate_issue_tuples_forbidden",
        "allowed_issue_codes_closed_exact",
        "runner_policy_failure_input_materialization_required",
        "runner_reason_line_range_non_authoritative",
        "mismatch_fail_closed",
        "exact_match_requires_empty_deltas",
        "policy_recompute_result_emitted",
        "typed_diff_summary_emitted",
        "success_class_verification_result_forbidden_on_mismatch",
        "verification_passed",
        "metric_key_exact_set_equal_v50",
    ):
        if payload.get(field) is not True:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="policy recompute evidence boolean field must be true",
                details={"path": str(path), "field": field, "value": payload.get(field)},
                artifact_path=str(path),
                policy_source="stop_gate_metrics",
            )

    if payload.get("metric_key_cardinality") != 80:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="policy recompute evidence metric_key_cardinality must equal 80",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    policy_recompute_result_path = coerce_artifact_path(
        root,
        payload["policy_recompute_result_path"],
    )
    policy_recompute_result_payload = load_json_object(policy_recompute_result_path)
    require_schema(
        policy_recompute_result_payload,
        expected_schema=POLICY_RECOMPUTE_RESULT_SCHEMA,
        path=policy_recompute_result_path,
    )
    if (
        policy_recompute_result_payload.get("result_hash")
        != payload["policy_recompute_result_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="policy recompute evidence result hash does not match policy recompute payload",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        policy_recompute_result_payload.get("shared_recompute_engine")
        != payload["shared_recompute_engine_used"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message=(
                "policy recompute evidence shared engine does not match policy "
                "recompute payload"
            ),
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        policy_recompute_result_payload.get("taskpack_manifest_hash")
        != verified_result_payload["taskpack_manifest_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="policy recompute evidence taskpack_manifest_hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        policy_recompute_result_payload.get("candidate_change_plan_hash")
        != verified_result_payload["candidate_change_plan_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="policy recompute evidence candidate_change_plan_hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        policy_recompute_result_payload.get("runner_provenance_hash")
        != verified_result_payload["runner_provenance_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="policy recompute evidence runner_provenance_hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    typed_diff_summary = policy_recompute_result_payload.get("typed_diff_summary")
    if (
        not isinstance(typed_diff_summary, dict)
        or typed_diff_summary.get("exact_match") is not True
        or typed_diff_summary.get("mismatch_fields") != []
        or typed_diff_summary.get("runner_only_issues") != []
        or typed_diff_summary.get("recompute_only_issues") != []
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="policy recompute evidence requires exact-match policy recompute payload",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    return payload


def _retry_context_issue_identity_rows(
    items: list[Any],
    *,
    path: Path,
) -> list[tuple[str, str, int, str]]:
    identity_rows: list[tuple[str, str, int, str]] = []
    for index, item in enumerate(items):
        if not isinstance(item, dict):
            raise fail(
                code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
                message="retry context result item must be an object",
                details={"path": str(path), "index": index},
                artifact_path=str(path),
                policy_source="stop_gate_metrics",
            )
        issue_reference = item.get("issue_reference")
        if not isinstance(issue_reference, dict):
            raise fail(
                code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
                message="retry context result item issue_reference must be an object",
                details={"path": str(path), "index": index},
                artifact_path=str(path),
                policy_source="stop_gate_metrics",
            )
        issue_code = issue_reference.get("issue_code")
        target_path = issue_reference.get("target_path")
        hunk_index = issue_reference.get("hunk_index")
        policy_source = issue_reference.get("policy_source")
        if (
            not isinstance(issue_code, str)
            or not isinstance(target_path, str)
            or not isinstance(hunk_index, int)
            or not isinstance(policy_source, str)
        ):
            raise fail(
                code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
                message="retry context result item issue_reference fields are malformed",
                details={"path": str(path), "index": index},
                artifact_path=str(path),
                policy_source="stop_gate_metrics",
            )
        identity_rows.append((issue_code, target_path, hunk_index, policy_source))
    return identity_rows


def _load_retry_context_evidence(
    root: Path,
    path: Path,
    *,
    verified_result_payload: dict[str, Any],
) -> dict[str, Any]:
    payload = _load_block(path, expected_schema=RETRY_CONTEXT_EVIDENCE_SCHEMA)
    if set(payload.keys()) != _RETRY_CONTEXT_EVIDENCE_REQUIRED_KEYS:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="retry context evidence keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    for field in (
        "contract_source",
        "feeder_entrypoint",
        "shared_feeder_engine_used",
        "shared_feeder_engine_identifier",
        "retry_context_feeder_result_path",
        "sanitization_profile_path",
        "source_rejection_diagnostic_schema",
        "overflow_policy",
        "missing_excerpt_source_policy",
        "verification_passed_policy",
        "notes",
    ):
        value = payload.get(field)
        if not isinstance(value, str) or not value:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="retry context evidence string field must be non-empty",
                details={"path": str(path), "field": field},
                artifact_path=str(path),
                policy_source="stop_gate_metrics",
            )

    if payload.get("shared_feeder_engine_used") != SHARED_FEEDER_ENGINE:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="retry context evidence shared_feeder_engine_used mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if payload.get("shared_feeder_engine_identifier") != SHARED_FEEDER_ENGINE_IDENTIFIER:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="retry context evidence shared_feeder_engine_identifier mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        payload.get("source_rejection_diagnostic_schema")
        != _RETRY_CONTEXT_SOURCE_REJECTION_DIAGNOSTIC_SCHEMA
    ):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="retry context evidence source_rejection_diagnostic_schema mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if payload.get("overflow_policy") != OVERFLOW_POLICY:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="retry context evidence overflow_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if payload.get("missing_excerpt_source_policy") != MISSING_EXCERPT_SOURCE_POLICY:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="retry context evidence missing_excerpt_source_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        payload.get("verification_passed_policy")
        != RETRY_CONTEXT_VERIFICATION_PASSED_POLICY
    ):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="retry context evidence verification_passed_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    for field in (
        "policy_source_closed_inherited_surface",
        "runner_result_semantic_input_forbidden",
        "advisory_only_non_authoritative",
        "automatic_retry_dispatch_forbidden",
        "downstream_diagnostic_aggregation_forbidden",
        "policy_success_explicit_request_without_diagnostic_fails_closed",
        "raw_repo_file_content_forbidden",
        "duplicate_issue_tuples_forbidden",
        "excerpt_bounds_enforced",
        "total_output_bound_enforced",
        "control_marker_neutralization_enforced",
        "deterministic_issue_order_enforced",
        "verification_passed",
        "success_path_absence_without_request_allowed",
        "metric_key_exact_set_equal_v51",
    ):
        if payload.get(field) is not True:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="retry context evidence boolean field must be true",
                details={"path": str(path), "field": field, "value": payload.get(field)},
                artifact_path=str(path),
                policy_source="stop_gate_metrics",
            )

    for field in ("retry_context_feeder_result_hash", "sanitization_profile_hash"):
        if payload.get(field) is None or not is_sha256(payload[field]):
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="retry context evidence hash field must be a sha256 string",
                details={"path": str(path), "field": field},
                artifact_path=str(path),
                policy_source="stop_gate_metrics",
            )

    if payload.get("metric_key_cardinality") != 80:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="retry context evidence metric_key_cardinality must equal 80",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    retry_context_result_path = coerce_artifact_path(
        root,
        payload["retry_context_feeder_result_path"],
    )
    retry_context_result_payload = load_json_object(retry_context_result_path)
    require_schema(
        retry_context_result_payload,
        expected_schema=RETRY_CONTEXT_FEEDER_RESULT_SCHEMA,
        path=retry_context_result_path,
    )
    if (
        retry_context_result_payload.get("result_hash")
        != payload["retry_context_feeder_result_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context evidence result hash does not match feeder result payload",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        retry_context_result_payload.get("shared_feeder_engine")
        != payload["shared_feeder_engine_used"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context evidence shared engine does not match feeder result payload",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        retry_context_result_payload.get("shared_feeder_engine_identifier")
        != payload["shared_feeder_engine_identifier"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context evidence shared engine identifier mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        retry_context_result_payload.get("taskpack_manifest_hash")
        != verified_result_payload["taskpack_manifest_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context evidence taskpack_manifest_hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        retry_context_result_payload.get("source_rejection_diagnostic_schema")
        != payload["source_rejection_diagnostic_schema"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context evidence source schema mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if retry_context_result_payload.get("advisory_only_non_authoritative") is not True:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context result advisory-only posture mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if retry_context_result_payload.get("automatic_retry_dispatch_forbidden") is not True:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context result automatic retry dispatch posture mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if retry_context_result_payload.get("downstream_diagnostic_aggregation_forbidden") is not True:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context result downstream aggregation posture mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if retry_context_result_payload.get("raw_repo_file_content_forbidden") is not True:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context result raw repo file content posture mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        retry_context_result_payload.get("target_path_normalization_policy")
        != RETRY_CONTEXT_TARGET_PATH_NORMALIZATION_POLICY
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context result target_path_normalization_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        retry_context_result_payload.get("policy_source_policy")
        != RETRY_CONTEXT_POLICY_SOURCE_POLICY
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context result policy_source_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        retry_context_result_payload.get("deterministic_issue_order_policy")
        != DETERMINISTIC_ISSUE_ORDER_POLICY
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context result deterministic_issue_order_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if retry_context_result_payload.get("overflow_policy") != payload["overflow_policy"]:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context result overflow_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        retry_context_result_payload.get("missing_excerpt_source_policy")
        != payload["missing_excerpt_source_policy"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context result missing_excerpt_source_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        retry_context_result_payload.get("policy_success_absence_without_request_allowed")
        is not True
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context result success-path absence policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        retry_context_result_payload.get("sanitization_profile_path")
        != payload["sanitization_profile_path"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context result sanitization_profile_path mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        retry_context_result_payload.get("sanitization_profile_hash")
        != payload["sanitization_profile_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context result sanitization_profile_hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    items = retry_context_result_payload.get("items")
    if not isinstance(items, list):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context result items must be a list",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    identity_rows = _retry_context_issue_identity_rows(items, path=retry_context_result_path)
    ordered_items = sorted(
        identity_rows,
    )
    if identity_rows != ordered_items:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context result issues must remain in deterministic order",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if len(set(identity_rows)) != len(identity_rows):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context result duplicate issue tuples are forbidden",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    sanitization_profile_path = coerce_artifact_path(
        root,
        payload["sanitization_profile_path"],
    )
    sanitization_profile_payload = load_json_object(sanitization_profile_path)
    require_schema(
        sanitization_profile_payload,
        expected_schema=RETRY_CONTEXT_SANITIZATION_PROFILE_SCHEMA,
        path=sanitization_profile_path,
    )
    if (
        sanitization_profile_payload.get("profile_hash")
        != payload["sanitization_profile_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context evidence sanitization profile hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        sanitization_profile_payload.get("shared_feeder_engine")
        != payload["shared_feeder_engine_used"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context evidence sanitization profile shared engine mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        sanitization_profile_payload.get("shared_feeder_engine_identifier")
        != payload["shared_feeder_engine_identifier"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context evidence sanitization profile shared engine identifier mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if sanitization_profile_payload.get("advisory_only_non_authoritative") is not True:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context sanitization profile advisory-only posture mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if sanitization_profile_payload.get("automatic_retry_dispatch_forbidden") is not True:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context sanitization profile automatic retry dispatch posture mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if sanitization_profile_payload.get("downstream_diagnostic_aggregation_forbidden") is not True:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context sanitization profile downstream aggregation posture mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if sanitization_profile_payload.get("raw_repo_file_content_forbidden") is not True:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context sanitization profile raw repo file content posture mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        sanitization_profile_payload.get("target_path_normalization_policy")
        != RETRY_CONTEXT_TARGET_PATH_NORMALIZATION_POLICY
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context sanitization profile target_path_normalization_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        sanitization_profile_payload.get("policy_source_policy")
        != RETRY_CONTEXT_POLICY_SOURCE_POLICY
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context sanitization profile policy_source_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if sanitization_profile_payload.get("overflow_policy") != payload["overflow_policy"]:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context sanitization profile overflow_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        sanitization_profile_payload.get("missing_excerpt_source_policy")
        != payload["missing_excerpt_source_policy"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context sanitization profile missing_excerpt_source_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        sanitization_profile_payload.get("control_marker_neutralization")
        != CONTROL_MARKER_NEUTRALIZATION
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context sanitization profile control marker policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if sanitization_profile_payload.get("escaping_policy") != ESCAPING_POLICY:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context sanitization profile escaping_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if sanitization_profile_payload.get("whitespace_policy") != WHITESPACE_POLICY:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context sanitization profile whitespace_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if sanitization_profile_payload.get("max_issue_count") != MAX_ISSUE_COUNT:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context sanitization profile max_issue_count mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if sanitization_profile_payload.get("max_reason_chars") != MAX_REASON_CHARS:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context sanitization profile max_reason_chars mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        sanitization_profile_payload.get("max_excerpt_lines_per_issue")
        != MAX_EXCERPT_LINES_PER_ISSUE
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context sanitization profile max_excerpt_lines_per_issue mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        sanitization_profile_payload.get("max_excerpt_chars_per_issue")
        != MAX_EXCERPT_CHARS_PER_ISSUE
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context sanitization profile max_excerpt_chars_per_issue mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if sanitization_profile_payload.get("max_total_output_chars") != MAX_TOTAL_OUTPUT_CHARS:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context sanitization profile max_total_output_chars mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if retry_context_result_payload.get("total_output_chars_used", 0) > MAX_TOTAL_OUTPUT_CHARS:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="retry context result exceeds max_total_output_chars",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    return payload


def _load_attestation_evidence(
    root: Path,
    path: Path,
    *,
    verified_result_payload: dict[str, Any],
) -> dict[str, Any]:
    payload = _load_block(path, expected_schema=ATTESTATION_EVIDENCE_SCHEMA)
    if set(payload.keys()) != _ATTESTATION_EVIDENCE_REQUIRED_KEYS:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="attestation evidence keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    for field in (
        "contract_source",
        "attestation_entrypoint",
        "shared_attestation_validator_used",
        "shared_attestation_validator_identifier",
        "shared_attestation_validator_identifier_policy",
        "local_verifier_entrypoint",
        "remote_enclave_attestation_path",
        "attested_verified_result_path",
        "local_verified_result_path",
        "attestation_verification_result_path",
        "provider_id",
        "provider_id_comparison_policy",
        "runner_provenance_hash_policy",
        "local_equivalence_subject_policy",
        "verification_passed_policy",
        "notes",
    ):
        value = payload.get(field)
        if not isinstance(value, str) or not value:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="attestation evidence string field must be non-empty",
                details={"path": str(path), "field": field},
                artifact_path=str(path),
                policy_source="stop_gate_metrics",
            )

    if payload.get("shared_attestation_validator_used") != SHARED_ATTESTATION_VALIDATOR:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="attestation evidence shared_attestation_validator_used mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        payload.get("shared_attestation_validator_identifier")
        != SHARED_ATTESTATION_VALIDATOR_IDENTIFIER
    ):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="attestation evidence shared_attestation_validator_identifier mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        payload.get("shared_attestation_validator_identifier_policy")
        != SHARED_ATTESTATION_VALIDATOR_IDENTIFIER_POLICY
    ):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="attestation evidence shared_attestation_validator_identifier_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if payload.get("local_verifier_entrypoint") != LOCAL_VERIFIER_ENTRYPOINT:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="attestation evidence local_verifier_entrypoint mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if payload.get("provider_id") != PROVIDER_ID:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="attestation evidence provider_id mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        payload.get("provider_id_comparison_policy")
        != PROVIDER_ID_COMPARISON_POLICY
    ):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="attestation evidence provider_id_comparison_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        payload.get("runner_provenance_hash_policy")
        != ATTESTATION_RUNNER_PROVENANCE_HASH_POLICY
    ):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="attestation evidence runner_provenance_hash_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        payload.get("verification_passed_policy")
        != ATTESTATION_VERIFICATION_PASSED_POLICY
    ):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="attestation evidence verification_passed_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    if payload.get("local_equivalence_subject_policy") != LOCAL_EQUIVALENCE_SUBJECT_POLICY:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="attestation evidence local_equivalence_subject_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    for field in (
        "provider_id_closed_singleton_enforced",
        "attestation_trust_anchor_registry_reused",
        "attestation_verified_required",
        "input_mode_artifact_ingestion_only",
        "attested_verified_result_schema_validated",
        "current_local_verification_recomputed",
        "current_local_verification_materialization_failure_fails_closed",
        "local_equivalence_required",
        "local_equivalence_verified",
        "opaque_provider_evidence_hash_audit_only",
        "normalized_claim_conflicts_forbidden",
        "remote_transport_or_job_dispatch_forbidden",
        "deployment_mode_expansion_forbidden",
        "verification_passed",
        "metric_key_exact_set_equal_v52",
    ):
        if payload.get(field) is not True:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="attestation evidence boolean field must be true",
                details={"path": str(path), "field": field, "value": payload.get(field)},
                artifact_path=str(path),
                policy_source="stop_gate_metrics",
            )

    if payload.get("metric_key_cardinality") != 80:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="attestation evidence metric_key_cardinality must equal 80",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    for field in (
        "remote_enclave_attestation_hash",
        "attested_verified_result_hash",
        "local_verified_result_hash",
        "attestation_verification_result_hash",
    ):
        if payload.get(field) is None or not is_sha256(payload[field]):
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="attestation evidence hash field must be a sha256 string",
                details={"path": str(path), "field": field},
                artifact_path=str(path),
                policy_source="stop_gate_metrics",
            )

    if payload.get("local_equivalence_subject_fields_verified") != list(
        LOCAL_EQUIVALENCE_SUBJECT_FIELDS
    ):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="attestation evidence local_equivalence_subject_fields_verified mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if payload.get("local_equivalence_binding_fields_verified") != list(
        LOCAL_EQUIVALENCE_BINDING_FIELDS
    ):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="attestation evidence local_equivalence_binding_fields_verified mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    remote_attestation_path = coerce_artifact_path(
        root, payload["remote_enclave_attestation_path"]
    )
    remote_attestation_payload = _load_block(
        remote_attestation_path, expected_schema=REMOTE_ENCLAVE_ATTESTATION_SCHEMA
    )
    if set(remote_attestation_payload.keys()) != _REMOTE_ATTESTATION_REQUIRED_KEYS:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation keys must match frozen grammar",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        remote_attestation_payload.get("attestation_hash")
        != payload["remote_enclave_attestation_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation evidence remote attestation hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if _recompute_self_hash(remote_attestation_payload, hash_field="attestation_hash") != payload[
        "remote_enclave_attestation_hash"
    ]:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation self-hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        remote_attestation_payload.get("shared_attestation_validator")
        != SHARED_ATTESTATION_VALIDATOR
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation shared validator mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        remote_attestation_payload.get("shared_attestation_validator_identifier")
        != SHARED_ATTESTATION_VALIDATOR_IDENTIFIER
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation validator identifier mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        remote_attestation_payload.get("source_provider_schema")
        != PROVIDER_ATTESTATION_INPUT_SCHEMA
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation source_provider_schema mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if remote_attestation_payload.get("input_mode_artifact_ingestion_only") is not True:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation input mode posture mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        remote_attestation_payload.get("provider_id_comparison_policy")
        != PROVIDER_ID_COMPARISON_POLICY
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation provider_id_comparison_policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if remote_attestation_payload.get("provider_id_closed_singleton_enforced") is not True:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation singleton provider posture mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if remote_attestation_payload.get("opaque_provider_evidence_hash_audit_only") is not True:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation opaque provider evidence policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if remote_attestation_payload.get("normalized_claim_conflicts_forbidden") is not True:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation normalized claim conflict policy mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if remote_attestation_payload.get("attestation_verified") is not True:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation attestation_verified mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if remote_attestation_payload.get("normalized_claim_fields") != list(NORMALIZED_CLAIM_FIELDS):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation normalized_claim_fields mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    normalized_claims = remote_attestation_payload.get("normalized_claims")
    if not isinstance(normalized_claims, dict):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation normalized_claims must be an object",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if normalized_claims.get("provider_id") != payload["provider_id"]:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation provider_id mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        normalized_claims.get("taskpack_manifest_hash")
        != verified_result_payload["taskpack_manifest_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation taskpack_manifest_hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        normalized_claims.get("candidate_change_plan_hash")
        != verified_result_payload["candidate_change_plan_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation candidate_change_plan_hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    attested_verified_result_path = coerce_artifact_path(
        root, payload["attested_verified_result_path"]
    )
    attested_verified_result_payload = _load_verified_result(attested_verified_result_path)
    if (
        attested_verified_result_payload["verified_result_hash"]
        != payload["attested_verified_result_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation evidence attested_verified_result_hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    local_verified_result_path = coerce_artifact_path(root, payload["local_verified_result_path"])
    local_verified_result_payload = _load_verified_result(local_verified_result_path)
    if (
        local_verified_result_payload["verified_result_hash"]
        != payload["local_verified_result_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation evidence local_verified_result_hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        local_verified_result_payload["verified_result_hash"]
        != verified_result_payload["verified_result_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message=(
                "attestation evidence local verified result must match closeout "
                "verified result"
            ),
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        attested_verified_result_payload["verified_result_hash"]
        != local_verified_result_payload["verified_result_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message=(
                "attested verified result must exactly match current local "
                "verified result"
            ),
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    local_runner_provenance_rel = local_verified_result_payload["verified_artifacts"].get(
        "runner_provenance_path"
    )
    if not isinstance(local_runner_provenance_rel, str) or not local_runner_provenance_rel:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="local verified result runner_provenance_path is missing or invalid",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    local_runner_provenance_path = coerce_artifact_path(root, local_runner_provenance_rel)
    local_runner_provenance_payload = load_json_object(local_runner_provenance_path)
    require_schema(
        local_runner_provenance_payload,
        expected_schema=TASKPACK_RUNNER_PROVENANCE_SCHEMA,
        path=local_runner_provenance_path,
    )
    full_runner_provenance_hash = sha256_canonical_json(local_runner_provenance_payload)
    if normalized_claims.get("runner_provenance_hash") != full_runner_provenance_hash:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation runner_provenance_hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )

    attestation_verification_result_path = coerce_artifact_path(
        root, payload["attestation_verification_result_path"]
    )
    attestation_verification_result_payload = _load_block(
        attestation_verification_result_path,
        expected_schema=ATTESTATION_VERIFICATION_RESULT_SCHEMA,
    )
    if (
        set(attestation_verification_result_payload.keys())
        != _ATTESTATION_VERIFICATION_RESULT_REQUIRED_KEYS
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation verification result keys must match frozen grammar",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        attestation_verification_result_payload.get("result_hash")
        != payload["attestation_verification_result_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation evidence verification result hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if _recompute_self_hash(
        attestation_verification_result_payload, hash_field="result_hash"
    ) != payload["attestation_verification_result_hash"]:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation verification result self-hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        attestation_verification_result_payload.get("shared_attestation_validator")
        != payload["shared_attestation_validator_used"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation verification result shared validator mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        attestation_verification_result_payload.get("shared_attestation_validator_identifier")
        != payload["shared_attestation_validator_identifier"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation verification result validator identifier mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        attestation_verification_result_payload.get("local_verifier_entrypoint")
        != payload["local_verifier_entrypoint"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation verification result local verifier entrypoint mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        attestation_verification_result_payload.get("remote_enclave_attestation_path")
        != payload["remote_enclave_attestation_path"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation verification result attestation path mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    for field in (
        "remote_enclave_attestation_hash",
        "attested_verified_result_path",
        "attested_verified_result_hash",
        "local_verified_result_path",
        "local_verified_result_hash",
        "provider_id",
        "provider_id_comparison_policy",
        "runner_provenance_hash_policy",
        "local_equivalence_subject_policy",
        "verification_passed_policy",
    ):
        if attestation_verification_result_payload.get(field) != payload[field]:
            raise fail(
                code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
                message="attestation verification result field mismatch",
                details={"path": str(path), "field": field},
                artifact_path=str(path),
                policy_source="stop_gate_metrics",
            )
    if (
        attestation_verification_result_payload.get("runner_provenance_hash")
        != full_runner_provenance_hash
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation verification result runner_provenance_hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        attestation_verification_result_payload.get("taskpack_manifest_hash")
        != verified_result_payload["taskpack_manifest_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation verification result taskpack_manifest_hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        attestation_verification_result_payload.get("candidate_change_plan_hash")
        != verified_result_payload["candidate_change_plan_hash"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation verification result candidate_change_plan_hash mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        attestation_verification_result_payload.get("attestation_binding_fields_verified")
        != list(ATTESTATION_BINDING_FIELDS)
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation verification result attestation_binding_fields_verified mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        attestation_verification_result_payload.get("local_equivalence_subject_fields_verified")
        != payload["local_equivalence_subject_fields_verified"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation verification result subject fields mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    if (
        attestation_verification_result_payload.get("local_equivalence_binding_fields_verified")
        != payload["local_equivalence_binding_fields_verified"]
    ):
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation verification result binding fields mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="stop_gate_metrics",
        )
    for field in (
        "provider_id_closed_singleton_enforced",
        "attestation_trust_anchor_registry_reused",
        "attestation_verified",
        "input_mode_artifact_ingestion_only",
        "attested_verified_result_schema_validated",
        "current_local_verification_recomputed",
        "current_local_verification_materialization_failure_fails_closed",
        "local_equivalence_required",
        "local_equivalence_verified",
        "opaque_provider_evidence_hash_audit_only",
        "normalized_claim_conflicts_forbidden",
        "remote_transport_or_job_dispatch_forbidden",
        "deployment_mode_expansion_forbidden",
        "verification_passed",
    ):
        if attestation_verification_result_payload.get(field) is not True:
            raise fail(
                code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
                message="attestation verification result boolean field must be true",
                details={"path": str(path), "field": field},
                artifact_path=str(path),
                policy_source="stop_gate_metrics",
            )

    if normalized_claims.get("verified_result_hash") != payload["attested_verified_result_hash"]:
        raise fail(
            code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
            message="remote enclave attestation verified_result_hash mismatch",
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
    policy_recompute_evidence_path: str | Path | None = None,
    retry_context_evidence_path: str | Path | None = None,
    attestation_evidence_path: str | Path | None = None,
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
        policy_recompute_rel = (
            None
            if policy_recompute_evidence_path is None
            else normalize_relative_path(str(policy_recompute_evidence_path))
        )
        retry_context_rel = (
            None
            if retry_context_evidence_path is None
            else normalize_relative_path(str(retry_context_evidence_path))
        )
        attestation_rel = (
            None
            if attestation_evidence_path is None
            else normalize_relative_path(str(attestation_evidence_path))
        )
        evidence_output_rel = normalize_relative_path(str(evidence_output_root))

        taskpack_path = coerce_artifact_path(root, taskpack_rel)
        verified_result_artifact_path = coerce_artifact_path(root, verified_result_rel)
        runtime_path = coerce_artifact_path(root, runtime_rel)
        continuity_path = coerce_artifact_path(root, continuity_rel)
        handoff_path = coerce_artifact_path(root, handoff_rel)
        matrix_path = None if matrix_rel is None else coerce_artifact_path(root, matrix_rel)
        policy_recompute_path = (
            None
            if policy_recompute_rel is None
            else coerce_artifact_path(root, policy_recompute_rel)
        )
        retry_context_path = (
            None
            if retry_context_rel is None
            else coerce_artifact_path(root, retry_context_rel)
        )
        attestation_path = (
            None
            if attestation_rel is None
            else coerce_artifact_path(root, attestation_rel)
        )
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
        policy_recompute_slot_required = (
            EVIDENCE_SCHEMA_TO_SLOT_ID[POLICY_RECOMPUTE_EVIDENCE_SCHEMA] in required_slot_ids
        )
        retry_context_slot_required = (
            EVIDENCE_SCHEMA_TO_SLOT_ID[RETRY_CONTEXT_EVIDENCE_SCHEMA] in required_slot_ids
        )
        attestation_slot_required = (
            EVIDENCE_SCHEMA_TO_SLOT_ID[ATTESTATION_EVIDENCE_SCHEMA] in required_slot_ids
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
        if policy_recompute_slot_required and policy_recompute_path is None:
            raise fail(
                code=AHK4611_EVIDENCE_SLOT_OR_SCHEMA_VIOLATION,
                message="policy recompute evidence block is required by EVIDENCE_SLOTS",
                details={"path": str(taskpack_path / 'EVIDENCE_SLOTS.json')},
                artifact_path=str(taskpack_path / "EVIDENCE_SLOTS.json"),
                policy_source="evidence_slots",
            )
        if not policy_recompute_slot_required and policy_recompute_path is not None:
            raise fail(
                code=AHK4611_EVIDENCE_SLOT_OR_SCHEMA_VIOLATION,
                message="policy recompute evidence block is not authorized by EVIDENCE_SLOTS",
                details={"path": str(taskpack_path / 'EVIDENCE_SLOTS.json')},
                artifact_path=str(taskpack_path / "EVIDENCE_SLOTS.json"),
                policy_source="evidence_slots",
            )
        if retry_context_slot_required and retry_context_path is None:
            raise fail(
                code=AHK4611_EVIDENCE_SLOT_OR_SCHEMA_VIOLATION,
                message="retry context evidence block is required by EVIDENCE_SLOTS",
                details={"path": str(taskpack_path / 'EVIDENCE_SLOTS.json')},
                artifact_path=str(taskpack_path / "EVIDENCE_SLOTS.json"),
                policy_source="evidence_slots",
            )
        if not retry_context_slot_required and retry_context_path is not None:
            raise fail(
                code=AHK4611_EVIDENCE_SLOT_OR_SCHEMA_VIOLATION,
                message="retry context evidence block is not authorized by EVIDENCE_SLOTS",
                details={"path": str(taskpack_path / 'EVIDENCE_SLOTS.json')},
                artifact_path=str(taskpack_path / "EVIDENCE_SLOTS.json"),
                policy_source="evidence_slots",
            )
        if attestation_slot_required and attestation_path is None:
            raise fail(
                code=AHK4611_EVIDENCE_SLOT_OR_SCHEMA_VIOLATION,
                message="attestation evidence block is required by EVIDENCE_SLOTS",
                details={"path": str(taskpack_path / 'EVIDENCE_SLOTS.json')},
                artifact_path=str(taskpack_path / "EVIDENCE_SLOTS.json"),
                policy_source="evidence_slots",
            )
        if not attestation_slot_required and attestation_path is not None:
            raise fail(
                code=AHK4611_EVIDENCE_SLOT_OR_SCHEMA_VIOLATION,
                message="attestation evidence block is not authorized by EVIDENCE_SLOTS",
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
        if policy_recompute_slot_required:
            assert policy_recompute_path is not None
            blocks.append(
                {
                    "slot_id": EVIDENCE_SCHEMA_TO_SLOT_ID[POLICY_RECOMPUTE_EVIDENCE_SCHEMA],
                    "schema": POLICY_RECOMPUTE_EVIDENCE_SCHEMA,
                    "payload": _load_policy_recompute_evidence(
                        root,
                        policy_recompute_path,
                        verified_result_payload=verified_result_payload,
                    ),
                }
            )
        if retry_context_slot_required:
            assert retry_context_path is not None
            blocks.append(
                {
                    "slot_id": EVIDENCE_SCHEMA_TO_SLOT_ID[RETRY_CONTEXT_EVIDENCE_SCHEMA],
                    "schema": RETRY_CONTEXT_EVIDENCE_SCHEMA,
                    "payload": _load_retry_context_evidence(
                        root,
                        retry_context_path,
                        verified_result_payload=verified_result_payload,
                    ),
                }
            )
        if attestation_slot_required:
            assert attestation_path is not None
            blocks.append(
                {
                    "slot_id": EVIDENCE_SCHEMA_TO_SLOT_ID[ATTESTATION_EVIDENCE_SCHEMA],
                    "schema": ATTESTATION_EVIDENCE_SCHEMA,
                    "payload": _load_attestation_evidence(
                        root,
                        attestation_path,
                        verified_result_payload=verified_result_payload,
                    ),
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
        "--policy-recompute-evidence",
        default=None,
        help="Optional repo-relative path to v34c_policy_recompute_evidence@1 payload.",
    )
    parser.add_argument(
        "--retry-context-evidence",
        default=None,
        help="Optional repo-relative path to v34d_retry_context_evidence@1 payload.",
    )
    parser.add_argument(
        "--attestation-evidence",
        default=None,
        help="Optional repo-relative path to v34e_attestation_evidence@1 payload.",
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
            policy_recompute_evidence_path=args.policy_recompute_evidence,
            retry_context_evidence_path=args.retry_context_evidence,
            attestation_evidence_path=args.attestation_evidence,
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
