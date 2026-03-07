from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from adeu_ir.repo import repo_root
from urm_runtime.hashing import canonical_json, sha256_canonical_json

from ._v46_verifier_common import DEFAULT_DIAGNOSTIC_REGISTRY_PATH
from ._v48_signing_common import parse_reference_time_utc
from .compile import TaskpackCompileError
from .verify_taskpack_run import (
    RUNNER_PROVENANCE_SCHEMA,
    TaskpackVerifierError,
    _load_runner_provenance,
    verify_taskpack_run,
)
from .verify_taskpack_signature import (
    TaskpackSigningError,
    TrustAnchorKeyRecord,
    _load_trust_anchor_registry,
    load_validated_downstream_signature_handoff,
)

REMOTE_ENCLAVE_ATTESTATION_SCHEMA = "remote_enclave_attestation@1"
ATTESTATION_VERIFICATION_RESULT_SCHEMA = "attestation_verification_result@1"
ATTESTATION_OUTPUT_SCHEMA = "taskpack_attestation_validator_result@1"
ATTESTATION_ERROR_SCHEMA = "taskpack_attestation_error@1"
ATTESTED_VERIFICATION_RESULT_SCHEMA = "taskpack_verification_result@1"
PROVIDER_ATTESTATION_INPUT_SCHEMA = "deterministic_test_enclave_attestation_input@1"
ATTESTATION_CONTRACT_SCHEMA = "v34e_attested_verifier_contract@1"
DEFAULT_ATTESTATION_OUTPUT_ROOT = "artifacts/agent_harness/v53/attestation"
DEFAULT_LOCAL_VERIFICATION_OUTPUT_ROOT = "artifacts/agent_harness/v53/local_verification"
DEFAULT_LOCAL_POLICY_RECOMPUTE_OUTPUT_ROOT = "artifacts/agent_harness/v53/local_recompute"
LOCAL_VERIFIER_ENTRYPOINT = "python -m adeu_agent_harness.verify_taskpack_run"
SHARED_ATTESTATION_VALIDATOR = (
    "adeu_agent_harness.attestation.validate_attested_verification"
)
SHARED_ATTESTATION_VALIDATOR_IDENTIFIER = (
    "v34e_attestation_validator@1:"
    "adeu_agent_harness.attestation.validate_attested_verification"
)
SHARED_ATTESTATION_VALIDATOR_IDENTIFIER_POLICY = (
    "frozen_module_function_path_or_registry_key_no_free_text"
)
PROVIDER_ID = "deterministic_test_enclave"
PROVIDER_ID_COMPARISON_POLICY = (
    "exact_case_sensitive_equality_against_deterministic_test_enclave"
)
RUNNER_PROVENANCE_HASH_POLICY = (
    "sha256_over_full_taskpack_runner_provenance_at_1_canonical_json_artifact"
)
OPAQUE_PROVIDER_EVIDENCE_HASH_POLICY = (
    "audit_only_binding_to_raw_provider_blob_not_part_of_exact_local_equivalence_subject"
)
LOCAL_EQUIVALENCE_SUBJECT_POLICY = (
    "exact_match_subject_is_verified_result_hash_only_binding_fields_separately_guard_"
    "input_identity_and_current_local_result_must_be_materialized_in_current_v53_flow_from_"
    "same_authoritative_inputs"
)
VERIFICATION_PASSED_POLICY = (
    "true_means_attestation_normalization_validation_local_equivalence_guards_and_closeout_"
    "validation_passed_not_policy_validation_packaging_validation_or_remote_job_success"
)
NORMALIZED_CLAIM_FIELDS = (
    "provider_id",
    "attestation_key_id",
    "algorithm",
    "verification_reference_time_utc",
    "taskpack_manifest_hash",
    "candidate_change_plan_hash",
    "runner_provenance_hash",
    "verified_result_hash",
    "opaque_provider_evidence_hash",
)
ATTESTATION_BINDING_FIELDS = (
    "taskpack_manifest_hash",
    "candidate_change_plan_hash",
    "runner_provenance_hash",
    "verified_result_hash",
    "trust_anchor_registry_hash",
    "verification_reference_time_utc",
    "attestation_key_id",
    "algorithm",
    "provider_id",
    "attestation_verified",
)
LOCAL_EQUIVALENCE_BINDING_FIELDS = (
    "taskpack_manifest_hash",
    "candidate_change_plan_hash",
    "runner_provenance_hash",
    "verified_result_hash",
)
LOCAL_EQUIVALENCE_SUBJECT_FIELDS = ("verified_result_hash",)
_VERIFIED_RESULT_REQUIRED_KEYS = {
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
_PROVIDER_ATTESTATION_REQUIRED_KEYS = {
    "schema",
    "provider_id",
    "attestation_key_id",
    "algorithm",
    "verification_reference_time_utc",
    "taskpack_manifest_hash",
    "candidate_change_plan_hash",
    "runner_provenance_hash",
    "verified_result_hash",
    "attestation_verified",
    "opaque_provider_evidence",
}
_SHA256_PATTERN = re.compile(r"[0-9a-f]{64}")

AHK5301_INPUT_INVALID = "AHK5301"
AHK5302_SCHEMA_MISMATCH = "AHK5302"
AHK5303_ATTESTATION_INVALID = "AHK5303"
AHK5304_CROSS_ARTIFACT_HASH_MISMATCH = "AHK5304"
AHK5305_PROVIDER_POLICY_VIOLATION = "AHK5305"
AHK5306_TRUST_ANCHOR_POLICY_VIOLATION = "AHK5306"
AHK5307_ATTESTED_VERIFICATION_RESULT_INVALID = "AHK5307"
AHK5308_LOCAL_EQUIVALENCE_MISMATCH = "AHK5308"
AHK5309_LOCAL_VERIFICATION_MATERIALIZATION_FAILED = "AHK5309"
AHK5310_RESULT_INVALID = "AHK5310"


@dataclass(frozen=True)
class AttestationArtifacts:
    remote_enclave_attestation_path: Path
    remote_enclave_attestation_hash: str
    attestation_verification_result_path: Path
    attestation_verification_result_hash: str
    attested_verified_result_path: Path
    attested_verified_result_hash: str
    local_verified_result_path: Path
    local_verified_result_hash: str


class TaskpackAttestationError(RuntimeError):
    def __init__(self, *, code: str, message: str, details: dict[str, Any] | None = None) -> None:
        self.code = code
        self.message = message
        self.details = details or {}
        payload = {
            "schema": ATTESTATION_ERROR_SCHEMA,
            "code": code,
            "message": message,
            "details": self.details,
        }
        super().__init__(canonical_json(payload))


def _fail(
    *, code: str, message: str, details: dict[str, Any] | None = None
) -> TaskpackAttestationError:
    return TaskpackAttestationError(code=code, message=message, details=details)


def _normalize_relative_path(raw_path: str) -> str:
    path_text = raw_path.strip().replace("\\", "/")
    if not path_text or path_text.startswith("/"):
        raise _fail(
            code=AHK5301_INPUT_INVALID,
            message="path must be repo-relative posix",
            details={"path": raw_path},
        )
    raw_segments = path_text.split("/")
    if any(segment == ".." for segment in raw_segments):
        raise _fail(
            code=AHK5301_INPUT_INVALID,
            message="path must not escape repository root",
            details={"path": raw_path},
        )
    segments = [segment for segment in raw_segments if segment and segment != "."]
    if not segments:
        raise _fail(
            code=AHK5301_INPUT_INVALID,
            message="path resolves to repository root",
            details={"path": raw_path},
        )
    return "/".join(segments)


def _safe_join(root: Path, rel_path: str) -> Path:
    normalized = _normalize_relative_path(rel_path)
    path = (root / normalized).resolve()
    root_resolved = root.resolve()
    try:
        path.relative_to(root_resolved)
    except ValueError as exc:
        raise _fail(
            code=AHK5301_INPUT_INVALID,
            message="resolved path escapes repository root",
            details={"path": rel_path},
        ) from exc
    return path


def _resolve_repo_path(root: Path, raw_path: str | Path) -> Path:
    candidate = Path(raw_path)
    if candidate.is_absolute():
        resolved = candidate.resolve()
        root_resolved = root.resolve()
        try:
            resolved.relative_to(root_resolved)
        except ValueError as exc:
            raise _fail(
                code=AHK5301_INPUT_INVALID,
                message="absolute path escapes repository root",
                details={"path": str(raw_path)},
            ) from exc
        return resolved
    return _safe_join(root, str(raw_path))


def _load_json_object(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise _fail(
            code=AHK5301_INPUT_INVALID,
            message="required json path does not exist",
            details={"path": str(path)},
        ) from exc
    except OSError as exc:
        raise _fail(
            code=AHK5301_INPUT_INVALID,
            message="required json path cannot be read",
            details={"path": str(path), "error": str(exc)},
        ) from exc
    except json.JSONDecodeError as exc:
        raise _fail(
            code=AHK5301_INPUT_INVALID,
            message="json payload is invalid",
            details={"path": str(path), "error": str(exc)},
        ) from exc
    if not isinstance(payload, dict):
        raise _fail(
            code=AHK5301_INPUT_INVALID,
            message="json payload must decode to an object",
            details={"path": str(path)},
        )
    return payload


def _require_schema(payload: dict[str, Any], *, expected_schema: str, path: Path) -> None:
    if payload.get("schema") != expected_schema:
        raise _fail(
            code=AHK5302_SCHEMA_MISMATCH,
            message="schema mismatch",
            details={
                "path": str(path),
                "expected_schema": expected_schema,
                "observed_schema": payload.get("schema"),
            },
        )


def _require_string(
    value: Any,
    *,
    field: str,
    path: Path,
    code: str = AHK5301_INPUT_INVALID,
) -> str:
    if not isinstance(value, str) or not value:
        raise _fail(
            code=code,
            message="required string field is missing or invalid",
            details={"path": str(path), "field": field},
        )
    return value


def _require_bool(
    value: Any,
    *,
    field: str,
    path: Path,
    code: str = AHK5301_INPUT_INVALID,
) -> bool:
    if not isinstance(value, bool):
        raise _fail(
            code=code,
            message="required boolean field is missing or invalid",
            details={"path": str(path), "field": field},
        )
    return value


def _require_sha256(value: Any, *, field: str, path: Path, code: str) -> str:
    if not isinstance(value, str) or _SHA256_PATTERN.fullmatch(value) is None:
        raise _fail(
            code=code,
            message="required sha256 field is missing or invalid",
            details={"path": str(path), "field": field},
        )
    return value


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(canonical_json(payload) + "\n", encoding="utf-8")


def _load_provider_attestation_input(path: Path) -> tuple[dict[str, Any], str]:
    payload = _load_json_object(path)
    _require_schema(payload, expected_schema=PROVIDER_ATTESTATION_INPUT_SCHEMA, path=path)
    if set(payload.keys()) != _PROVIDER_ATTESTATION_REQUIRED_KEYS:
        raise _fail(
            code=AHK5303_ATTESTATION_INVALID,
            message="provider attestation input keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
        )
    _require_string(
        payload.get("provider_id"),
        field="provider_id",
        path=path,
        code=AHK5305_PROVIDER_POLICY_VIOLATION,
    )
    _require_string(
        payload.get("attestation_key_id"),
        field="attestation_key_id",
        path=path,
        code=AHK5303_ATTESTATION_INVALID,
    )
    _require_string(
        payload.get("algorithm"),
        field="algorithm",
        path=path,
        code=AHK5303_ATTESTATION_INVALID,
    )
    _require_string(
        payload.get("verification_reference_time_utc"),
        field="verification_reference_time_utc",
        path=path,
        code=AHK5303_ATTESTATION_INVALID,
    )
    for field in (
        "taskpack_manifest_hash",
        "candidate_change_plan_hash",
        "runner_provenance_hash",
        "verified_result_hash",
    ):
        _require_sha256(
            payload.get(field),
            field=field,
            path=path,
            code=AHK5303_ATTESTATION_INVALID,
        )
    if _require_bool(
        payload.get("attestation_verified"),
        field="attestation_verified",
        path=path,
        code=AHK5303_ATTESTATION_INVALID,
    ) is not True:
        raise _fail(
            code=AHK5303_ATTESTATION_INVALID,
            message="attestation_verified must be present and equal true",
            details={"path": str(path)},
        )
    _require_string(
        payload.get("opaque_provider_evidence"),
        field="opaque_provider_evidence",
        path=path,
        code=AHK5303_ATTESTATION_INVALID,
    )
    opaque_provider_evidence = payload["opaque_provider_evidence"].encode("utf-8")
    return payload, hashlib.sha256(opaque_provider_evidence).hexdigest()


def _load_verified_result(path: Path) -> dict[str, Any]:
    payload = _load_json_object(path)
    _require_schema(payload, expected_schema=ATTESTED_VERIFICATION_RESULT_SCHEMA, path=path)
    if set(payload.keys()) != _VERIFIED_RESULT_REQUIRED_KEYS:
        raise _fail(
            code=AHK5307_ATTESTED_VERIFICATION_RESULT_INVALID,
            message="verified result keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
        )
    if payload.get("contract_schema") != "v33c_verifier_contract@1":
        raise _fail(
            code=AHK5307_ATTESTED_VERIFICATION_RESULT_INVALID,
            message="verified result contract_schema mismatch",
            details={"path": str(path), "contract_schema": payload.get("contract_schema")},
        )
    for field in (
        "taskpack_manifest_hash",
        "candidate_change_plan_hash",
        "runner_provenance_hash",
        "verified_result_hash",
    ):
        _require_sha256(
            payload.get(field),
            field=field,
            path=path,
            code=AHK5307_ATTESTED_VERIFICATION_RESULT_INVALID,
        )
    verification_result = payload.get("verification_result")
    if not isinstance(verification_result, dict):
        raise _fail(
            code=AHK5307_ATTESTED_VERIFICATION_RESULT_INVALID,
            message="verified result verification_result must be an object",
            details={"path": str(path)},
        )
    if set(verification_result.keys()) != {"passed", "issues", "cross_checks"}:
        raise _fail(
            code=AHK5307_ATTESTED_VERIFICATION_RESULT_INVALID,
            message="verified result verification_result keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(verification_result.keys())},
        )
    if verification_result.get("passed") is not True:
        raise _fail(
            code=AHK5307_ATTESTED_VERIFICATION_RESULT_INVALID,
            message="attested verified result requires verification_result.passed=true",
            details={"path": str(path)},
        )
    if verification_result.get("issues") != []:
        raise _fail(
            code=AHK5307_ATTESTED_VERIFICATION_RESULT_INVALID,
            message="attested verified result requires empty verification_result.issues",
            details={"path": str(path)},
        )
    cross_checks = verification_result.get("cross_checks")
    if not isinstance(cross_checks, list) or cross_checks != _EXPECTED_VERIFICATION_CROSS_CHECKS:
        raise _fail(
            code=AHK5307_ATTESTED_VERIFICATION_RESULT_INVALID,
            message="verified result cross_checks list mismatch",
            details={"path": str(path), "cross_checks": cross_checks},
        )
    exit_status = payload.get("exit_status")
    if not isinstance(exit_status, str) or not exit_status:
        raise _fail(
            code=AHK5307_ATTESTED_VERIFICATION_RESULT_INVALID,
            message="verified result exit_status must be a non-empty string",
            details={"path": str(path)},
        )
    verified_artifacts = payload.get("verified_artifacts")
    if not isinstance(verified_artifacts, dict):
        raise _fail(
            code=AHK5307_ATTESTED_VERIFICATION_RESULT_INVALID,
            message="verified result verified_artifacts must be an object",
            details={"path": str(path)},
        )
    expected_hash_subject = {
        "taskpack_manifest_hash": payload["taskpack_manifest_hash"],
        "candidate_change_plan_hash": payload["candidate_change_plan_hash"],
        "runner_provenance_hash": payload["runner_provenance_hash"],
        "verification_result": verification_result,
        "exit_status": exit_status,
    }
    recomputed_hash = sha256_canonical_json(expected_hash_subject)
    if recomputed_hash != payload["verified_result_hash"]:
        raise _fail(
            code=AHK5307_ATTESTED_VERIFICATION_RESULT_INVALID,
            message="verified result hash recomputation mismatch",
            details={"path": str(path)},
        )
    return payload


def _load_runner_provenance_full_hash(path: Path) -> tuple[dict[str, Any], str]:
    try:
        payload = _load_runner_provenance(path)
    except TaskpackVerifierError as exc:
        raise _fail(
            code=AHK5301_INPUT_INVALID,
            message="runner provenance artifact is invalid",
            details={"path": str(path), "verifier_error": str(exc)},
        ) from exc
    if payload.get("schema") != RUNNER_PROVENANCE_SCHEMA:
        raise _fail(
            code=AHK5302_SCHEMA_MISMATCH,
            message="runner provenance schema mismatch",
            details={"path": str(path), "observed_schema": payload.get("schema")},
        )
    return payload, sha256_canonical_json(payload)


def _require_provider_policy(provider_input: dict[str, Any], *, path: Path) -> None:
    if provider_input["provider_id"] != PROVIDER_ID:
        raise _fail(
            code=AHK5305_PROVIDER_POLICY_VIOLATION,
            message="provider_id is outside closed singleton test-provider surface",
            details={
                "path": str(path),
                "provider_id": provider_input["provider_id"],
                "provider_id_comparison_policy": PROVIDER_ID_COMPARISON_POLICY,
            },
        )


def _validate_attestation_key(
    *,
    registry_records: dict[str, TrustAnchorKeyRecord],
    provider_input: dict[str, Any],
    verification_reference_time_utc: str,
    path: Path,
) -> None:
    key_id = provider_input["attestation_key_id"]
    algorithm = provider_input["algorithm"]
    key_record = registry_records.get(key_id)
    if key_record is None:
        raise _fail(
            code=AHK5306_TRUST_ANCHOR_POLICY_VIOLATION,
            message="attestation key_id is not present in reused trust-anchor registry",
            details={"path": str(path), "attestation_key_id": key_id},
        )
    if key_record.algorithm != algorithm:
        raise _fail(
            code=AHK5306_TRUST_ANCHOR_POLICY_VIOLATION,
            message="attestation algorithm must match reused trust-anchor registry",
            details={
                "path": str(path),
                "attestation_key_id": key_id,
                "algorithm": algorithm,
                "registry_algorithm": key_record.algorithm,
            },
        )
    if key_record.revoked:
        raise _fail(
            code=AHK5306_TRUST_ANCHOR_POLICY_VIOLATION,
            message="attestation key is revoked in reused trust-anchor registry",
            details={"path": str(path), "attestation_key_id": key_id},
        )
    reference_text = provider_input["verification_reference_time_utc"]
    if reference_text != verification_reference_time_utc:
        raise _fail(
            code=AHK5304_CROSS_ARTIFACT_HASH_MISMATCH,
            message=(
                "attestation verification_reference_time_utc must match explicit "
                "validator input"
            ),
            details={
                "path": str(path),
                "attestation_verification_reference_time_utc": reference_text,
                "validator_verification_reference_time_utc": verification_reference_time_utc,
            },
        )
    reference_time = parse_reference_time_utc(
        verification_reference_time_utc,
        artifact_path=str(path),
    )
    if key_record.expires_at_utc <= reference_time:
        raise _fail(
            code=AHK5306_TRUST_ANCHOR_POLICY_VIOLATION,
            message="attestation key is expired for explicit verification reference time",
            details={
                "path": str(path),
                "attestation_key_id": key_id,
                "expires_at_utc": key_record.expires_at_utc.strftime("%Y-%m-%dT%H:%M:%SZ"),
                "verification_reference_time_utc": verification_reference_time_utc,
            },
        )


def _validate_normalized_claims(
    *,
    provider_input: dict[str, Any],
    opaque_provider_evidence_hash: str,
    manifest_hash: str,
    candidate_change_plan_hash: str,
    runner_provenance_hash: str,
    attested_verified_result_hash: str,
    attestation_path: Path,
) -> dict[str, Any]:
    normalized_claims = {
        "provider_id": provider_input["provider_id"],
        "attestation_key_id": provider_input["attestation_key_id"],
        "algorithm": provider_input["algorithm"],
        "verification_reference_time_utc": provider_input["verification_reference_time_utc"],
        "taskpack_manifest_hash": provider_input["taskpack_manifest_hash"],
        "candidate_change_plan_hash": provider_input["candidate_change_plan_hash"],
        "runner_provenance_hash": provider_input["runner_provenance_hash"],
        "verified_result_hash": provider_input["verified_result_hash"],
        "opaque_provider_evidence_hash": opaque_provider_evidence_hash,
    }
    expected_claims = {
        "provider_id": PROVIDER_ID,
        "attestation_key_id": provider_input["attestation_key_id"],
        "algorithm": provider_input["algorithm"],
        "verification_reference_time_utc": provider_input["verification_reference_time_utc"],
        "taskpack_manifest_hash": manifest_hash,
        "candidate_change_plan_hash": candidate_change_plan_hash,
        "runner_provenance_hash": runner_provenance_hash,
        "verified_result_hash": attested_verified_result_hash,
        "opaque_provider_evidence_hash": opaque_provider_evidence_hash,
    }
    if normalized_claims != expected_claims:
        raise _fail(
            code=AHK5304_CROSS_ARTIFACT_HASH_MISMATCH,
            message=(
                "duplicate or conflicting normalized claims after provider-neutral "
                "normalization are forbidden"
            ),
            details={
                "path": str(attestation_path),
                "normalized_claims": normalized_claims,
                "expected_claims": expected_claims,
            },
        )
    return normalized_claims


def validate_attested_verification(
    *,
    taskpack_dir: str | Path,
    candidate_change_plan_path: str | Path,
    runner_result_path: str | Path,
    runner_provenance_path: str | Path,
    attested_verified_result_path: str | Path,
    provider_attestation_input_path: str | Path,
    signature_verification_result_path: str | Path,
    signature_envelope_path: str | Path,
    trust_anchor_registry_path: str | Path,
    verification_reference_time_utc: str,
    attestation_output_root: str = DEFAULT_ATTESTATION_OUTPUT_ROOT,
    local_verification_output_root: str = DEFAULT_LOCAL_VERIFICATION_OUTPUT_ROOT,
    local_policy_recompute_output_root: str = DEFAULT_LOCAL_POLICY_RECOMPUTE_OUTPUT_ROOT,
    diagnostic_registry_path: str | Path = DEFAULT_DIAGNOSTIC_REGISTRY_PATH,
    repo_root_path: str | Path | None = None,
) -> AttestationArtifacts:
    root = repo_root(anchor=repo_root_path)
    taskpack_dir_path = _resolve_repo_path(root, taskpack_dir)
    candidate_path = _resolve_repo_path(root, candidate_change_plan_path)
    runner_result_artifact_path = _resolve_repo_path(root, runner_result_path)
    runner_provenance_artifact_path = _resolve_repo_path(root, runner_provenance_path)
    attested_verified_result_artifact_path = _resolve_repo_path(root, attested_verified_result_path)
    provider_attestation_artifact_path = _resolve_repo_path(root, provider_attestation_input_path)
    attestation_output_root_rel = _normalize_relative_path(attestation_output_root)
    attestation_output_root_path = _safe_join(root, attestation_output_root_rel)

    try:
        handoff = load_validated_downstream_signature_handoff(
            taskpack_dir=taskpack_dir_path.relative_to(root).as_posix(),
            signature_verification_result_path=str(signature_verification_result_path),
            signature_envelope_path=str(signature_envelope_path),
            trust_anchor_registry_path=str(trust_anchor_registry_path),
            verification_reference_time_utc=verification_reference_time_utc,
            repo_root_path=root,
        )
    except (TaskpackCompileError, TaskpackSigningError) as exc:
        raise _fail(
            code=AHK5306_TRUST_ANCHOR_POLICY_VIOLATION,
            message="attestation validation requires valid reused v34a trust-anchor handoff",
            details={"error": str(exc)},
        ) from exc

    provider_input, opaque_provider_evidence_hash = _load_provider_attestation_input(
        provider_attestation_artifact_path
    )
    _require_provider_policy(provider_input, path=provider_attestation_artifact_path)
    registry_records = _load_trust_anchor_registry(handoff.trust_anchor_registry_path)
    _validate_attestation_key(
        registry_records=registry_records,
        provider_input=provider_input,
        verification_reference_time_utc=handoff.verification_reference_time_utc,
        path=provider_attestation_artifact_path,
    )

    runner_provenance_payload, full_runner_provenance_hash = _load_runner_provenance_full_hash(
        runner_provenance_artifact_path
    )
    attested_verified_payload = _load_verified_result(attested_verified_result_artifact_path)
    manifest_hash = handoff.taskpack_snapshot.manifest_hash
    candidate_hash = attested_verified_payload["candidate_change_plan_hash"]

    if provider_input["taskpack_manifest_hash"] != manifest_hash:
        raise _fail(
            code=AHK5304_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation taskpack_manifest_hash must match canonical manifest hash",
            details={
                "path": str(provider_attestation_artifact_path),
                "attestation_taskpack_manifest_hash": provider_input["taskpack_manifest_hash"],
                "canonical_taskpack_manifest_hash": manifest_hash,
            },
        )
    if provider_input["candidate_change_plan_hash"] != candidate_hash:
        raise _fail(
            code=AHK5304_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation candidate_change_plan_hash must match attested verified result",
            details={
                "path": str(provider_attestation_artifact_path),
                "attestation_candidate_change_plan_hash": provider_input[
                    "candidate_change_plan_hash"
                ],
                "attested_candidate_change_plan_hash": candidate_hash,
            },
        )
    if provider_input["runner_provenance_hash"] != full_runner_provenance_hash:
        raise _fail(
            code=AHK5304_CROSS_ARTIFACT_HASH_MISMATCH,
            message=(
                "attestation runner_provenance_hash must match full canonical runner "
                "provenance artifact hash"
            ),
            details={
                "path": str(provider_attestation_artifact_path),
                "attestation_runner_provenance_hash": provider_input["runner_provenance_hash"],
                "canonical_runner_provenance_hash": full_runner_provenance_hash,
                "runner_provenance_hash_policy": RUNNER_PROVENANCE_HASH_POLICY,
            },
        )
    if provider_input["verified_result_hash"] != attested_verified_payload["verified_result_hash"]:
        raise _fail(
            code=AHK5304_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attestation verified_result_hash must match attested verified result hash",
            details={
                "path": str(provider_attestation_artifact_path),
                "attestation_verified_result_hash": provider_input["verified_result_hash"],
                "attested_verified_result_hash": attested_verified_payload["verified_result_hash"],
            },
        )
    if attested_verified_payload["taskpack_manifest_hash"] != manifest_hash:
        raise _fail(
            code=AHK5304_CROSS_ARTIFACT_HASH_MISMATCH,
            message="attested verified result taskpack_manifest_hash mismatch",
            details={"path": str(attested_verified_result_artifact_path)},
        )
    if runner_provenance_payload["candidate_change_plan_hash"] != candidate_hash:
        raise _fail(
            code=AHK5304_CROSS_ARTIFACT_HASH_MISMATCH,
            message="runner provenance candidate_change_plan_hash mismatch",
            details={"path": str(runner_provenance_artifact_path)},
        )
    if runner_provenance_payload["taskpack_manifest_hash"] != manifest_hash:
        raise _fail(
            code=AHK5304_CROSS_ARTIFACT_HASH_MISMATCH,
            message="runner provenance taskpack_manifest_hash mismatch",
            details={"path": str(runner_provenance_artifact_path)},
        )

    normalized_claims = _validate_normalized_claims(
        provider_input=provider_input,
        opaque_provider_evidence_hash=opaque_provider_evidence_hash,
        manifest_hash=manifest_hash,
        candidate_change_plan_hash=candidate_hash,
        runner_provenance_hash=full_runner_provenance_hash,
        attested_verified_result_hash=attested_verified_payload["verified_result_hash"],
        attestation_path=provider_attestation_artifact_path,
    )

    attestation_dir = attestation_output_root_path / "remote_enclave_attestation"
    attestation_path = attestation_dir / f"{manifest_hash}_{candidate_hash}.json"
    remote_attestation_payload = {
        "schema": REMOTE_ENCLAVE_ATTESTATION_SCHEMA,
        "shared_attestation_validator": SHARED_ATTESTATION_VALIDATOR,
        "shared_attestation_validator_identifier": SHARED_ATTESTATION_VALIDATOR_IDENTIFIER,
        "source_provider_schema": PROVIDER_ATTESTATION_INPUT_SCHEMA,
        "input_mode_artifact_ingestion_only": True,
        "provider_id_comparison_policy": PROVIDER_ID_COMPARISON_POLICY,
        "provider_id_closed_singleton_enforced": True,
        "opaque_provider_evidence_hash_audit_only": True,
        "normalized_claim_conflicts_forbidden": True,
        "normalized_claim_fields": list(NORMALIZED_CLAIM_FIELDS),
        "normalized_claims": normalized_claims,
        "attestation_verified": True,
    }
    remote_attestation_payload["attestation_hash"] = sha256_canonical_json(
        remote_attestation_payload
    )
    _write_json(attestation_path, remote_attestation_payload)

    loaded_remote_attestation = _load_json_object(attestation_path)
    _require_schema(
        loaded_remote_attestation,
        expected_schema=REMOTE_ENCLAVE_ATTESTATION_SCHEMA,
        path=attestation_path,
    )
    if (
        loaded_remote_attestation.get("attestation_hash")
        != remote_attestation_payload["attestation_hash"]
    ):
        raise _fail(
            code=AHK5310_RESULT_INVALID,
            message="remote enclave attestation hash drift detected",
            details={"path": str(attestation_path)},
        )

    try:
        local_verifier_result = verify_taskpack_run(
            taskpack_dir=taskpack_dir_path.relative_to(root).as_posix(),
            candidate_change_plan_path=candidate_path.relative_to(root).as_posix(),
            runner_result_path=runner_result_artifact_path.relative_to(root).as_posix(),
            runner_provenance_path=runner_provenance_artifact_path.relative_to(root).as_posix(),
            policy_rejection_diagnostics_path=None,
            signature_verification_result_path=str(signature_verification_result_path),
            signature_envelope_path=str(signature_envelope_path),
            trust_anchor_registry_path=str(trust_anchor_registry_path),
            verification_reference_time_utc=handoff.verification_reference_time_utc,
            verification_output_root=local_verification_output_root,
            policy_recompute_output_root=local_policy_recompute_output_root,
            diagnostic_registry_path=diagnostic_registry_path,
            repo_root_path=root,
        )
    except TaskpackVerifierError as exc:
        raise _fail(
            code=AHK5309_LOCAL_VERIFICATION_MATERIALIZATION_FAILED,
            message="current local verifier result could not be materialized in current v53 flow",
            details={"verifier_error": str(exc)},
        ) from exc

    local_verified_result_payload = _load_verified_result(
        local_verifier_result.verification_result_path
    )
    local_verified_result_hash = local_verified_result_payload["verified_result_hash"]
    attested_verified_result_hash = attested_verified_payload["verified_result_hash"]

    if local_verified_result_payload["taskpack_manifest_hash"] != manifest_hash:
        raise _fail(
            code=AHK5304_CROSS_ARTIFACT_HASH_MISMATCH,
            message="current local verifier result taskpack_manifest_hash mismatch",
            details={"path": str(local_verifier_result.verification_result_path)},
        )
    if local_verified_result_payload["candidate_change_plan_hash"] != candidate_hash:
        raise _fail(
            code=AHK5304_CROSS_ARTIFACT_HASH_MISMATCH,
            message="current local verifier result candidate_change_plan_hash mismatch",
            details={"path": str(local_verifier_result.verification_result_path)},
        )
    if local_verified_result_hash != attested_verified_result_hash:
        raise _fail(
            code=AHK5308_LOCAL_EQUIVALENCE_MISMATCH,
            message=(
                "attested verified result hash must exactly match current local "
                "verified result hash"
            ),
            details={
                "attested_verified_result_path": str(attested_verified_result_artifact_path),
                "attested_verified_result_hash": attested_verified_result_hash,
                "local_verified_result_path": str(local_verifier_result.verification_result_path),
                "local_verified_result_hash": local_verified_result_hash,
                "local_equivalence_subject_policy": LOCAL_EQUIVALENCE_SUBJECT_POLICY,
            },
        )

    verification_dir = attestation_output_root_path / "verification"
    attestation_verification_result_path = (
        verification_dir / f"{manifest_hash}_{candidate_hash}.json"
    )
    attestation_verification_payload = {
        "schema": ATTESTATION_VERIFICATION_RESULT_SCHEMA,
        "contract_schema": ATTESTATION_CONTRACT_SCHEMA,
        "shared_attestation_validator": SHARED_ATTESTATION_VALIDATOR,
        "shared_attestation_validator_identifier": SHARED_ATTESTATION_VALIDATOR_IDENTIFIER,
        "local_verifier_entrypoint": LOCAL_VERIFIER_ENTRYPOINT,
        "remote_enclave_attestation_path": attestation_path.relative_to(root).as_posix(),
        "remote_enclave_attestation_hash": remote_attestation_payload["attestation_hash"],
        "attested_verified_result_path": (
            attested_verified_result_artifact_path.relative_to(root).as_posix()
        ),
        "attested_verified_result_hash": attested_verified_result_hash,
        "local_verified_result_path": (
            local_verifier_result.verification_result_path.relative_to(root).as_posix()
        ),
        "local_verified_result_hash": local_verified_result_hash,
        "taskpack_manifest_hash": manifest_hash,
        "candidate_change_plan_hash": candidate_hash,
        "runner_provenance_hash": full_runner_provenance_hash,
        "trust_anchor_registry_hash": handoff.trust_anchor_registry_hash,
        "verification_reference_time_utc": handoff.verification_reference_time_utc,
        "provider_id": provider_input["provider_id"],
        "provider_id_closed_singleton_enforced": True,
        "provider_id_comparison_policy": PROVIDER_ID_COMPARISON_POLICY,
        "attestation_trust_anchor_registry_reused": True,
        "attestation_key_id": provider_input["attestation_key_id"],
        "algorithm": provider_input["algorithm"],
        "runner_provenance_hash_policy": RUNNER_PROVENANCE_HASH_POLICY,
        "attestation_binding_fields_verified": list(ATTESTATION_BINDING_FIELDS),
        "attestation_verified": True,
        "input_mode_artifact_ingestion_only": True,
        "attested_verified_result_schema_validated": True,
        "current_local_verification_recomputed": True,
        "current_local_verification_materialization_failure_fails_closed": True,
        "local_equivalence_required": True,
        "local_equivalence_subject_fields_verified": list(LOCAL_EQUIVALENCE_SUBJECT_FIELDS),
        "local_equivalence_binding_fields_verified": list(LOCAL_EQUIVALENCE_BINDING_FIELDS),
        "local_equivalence_subject_policy": LOCAL_EQUIVALENCE_SUBJECT_POLICY,
        "local_equivalence_verified": True,
        "opaque_provider_evidence_hash_audit_only": True,
        "normalized_claim_conflicts_forbidden": True,
        "remote_transport_or_job_dispatch_forbidden": True,
        "deployment_mode_expansion_forbidden": True,
        "verification_passed": True,
        "verification_passed_policy": VERIFICATION_PASSED_POLICY,
    }
    attestation_verification_payload["result_hash"] = sha256_canonical_json(
        attestation_verification_payload
    )
    _write_json(attestation_verification_result_path, attestation_verification_payload)

    loaded_verification_result = _load_json_object(attestation_verification_result_path)
    _require_schema(
        loaded_verification_result,
        expected_schema=ATTESTATION_VERIFICATION_RESULT_SCHEMA,
        path=attestation_verification_result_path,
    )
    if (
        loaded_verification_result.get("result_hash")
        != attestation_verification_payload["result_hash"]
    ):
        raise _fail(
            code=AHK5310_RESULT_INVALID,
            message="attestation verification result hash drift detected",
            details={"path": str(attestation_verification_result_path)},
        )

    return AttestationArtifacts(
        remote_enclave_attestation_path=attestation_path,
        remote_enclave_attestation_hash=remote_attestation_payload["attestation_hash"],
        attestation_verification_result_path=attestation_verification_result_path,
        attestation_verification_result_hash=attestation_verification_payload["result_hash"],
        attested_verified_result_path=attested_verified_result_artifact_path,
        attested_verified_result_hash=attested_verified_result_hash,
        local_verified_result_path=local_verifier_result.verification_result_path,
        local_verified_result_hash=local_verified_result_hash,
    )


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Validate deterministic v53 provider-neutral attestation inputs against current "
            "local verifier equivalence."
        ),
    )
    parser.add_argument("--taskpack-dir", required=True, help="Repo-relative taskpack directory.")
    parser.add_argument(
        "--candidate-change-plan",
        required=True,
        help="Repo-relative path to candidate_change_plan@1 JSON artifact.",
    )
    parser.add_argument(
        "--runner-result",
        required=True,
        help="Repo-relative path to taskpack_runner_result@1 JSON artifact.",
    )
    parser.add_argument(
        "--runner-provenance",
        required=True,
        help="Repo-relative path to taskpack_runner_provenance@1 JSON artifact.",
    )
    parser.add_argument(
        "--attested-verified-result",
        required=True,
        help="Repo-relative path to externally supplied taskpack_verification_result@1 artifact.",
    )
    parser.add_argument(
        "--provider-attestation-input",
        required=True,
        help="Repo-relative path to deterministic_test_enclave_attestation_input@1 artifact.",
    )
    parser.add_argument(
        "--signature-verification-result",
        required=True,
        help="Repo-relative path to signature_verification_result@1 JSON artifact.",
    )
    parser.add_argument(
        "--signature-envelope",
        required=True,
        help="Repo-relative path to taskpack_signature_envelope@1 JSON artifact.",
    )
    parser.add_argument(
        "--trust-anchor-registry",
        required=True,
        help="Repo-relative path to taskpack_trust_anchor_registry@1 JSON artifact.",
    )
    parser.add_argument(
        "--verification-reference-time-utc",
        required=True,
        help="Explicit RFC3339 UTC Z reference time used for reused trust-anchor checks.",
    )
    parser.add_argument(
        "--attestation-output-root",
        default=DEFAULT_ATTESTATION_OUTPUT_ROOT,
        help="Repo-relative output root for remote_enclave_attestation@1 artifacts.",
    )
    parser.add_argument(
        "--local-verification-output-root",
        default=DEFAULT_LOCAL_VERIFICATION_OUTPUT_ROOT,
        help=(
            "Repo-relative output root for current local "
            "taskpack_verification_result@1 artifacts."
        ),
    )
    parser.add_argument(
        "--local-policy-recompute-output-root",
        default=DEFAULT_LOCAL_POLICY_RECOMPUTE_OUTPUT_ROOT,
        help="Repo-relative output root for current-flow policy_recompute_result@1 artifacts.",
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
        result = validate_attested_verification(
            taskpack_dir=args.taskpack_dir,
            candidate_change_plan_path=args.candidate_change_plan,
            runner_result_path=args.runner_result,
            runner_provenance_path=args.runner_provenance,
            attested_verified_result_path=args.attested_verified_result,
            provider_attestation_input_path=args.provider_attestation_input,
            signature_verification_result_path=args.signature_verification_result,
            signature_envelope_path=args.signature_envelope,
            trust_anchor_registry_path=args.trust_anchor_registry,
            verification_reference_time_utc=args.verification_reference_time_utc,
            attestation_output_root=args.attestation_output_root,
            local_verification_output_root=args.local_verification_output_root,
            local_policy_recompute_output_root=args.local_policy_recompute_output_root,
            diagnostic_registry_path=args.diagnostic_registry,
            repo_root_path=args.repo_root,
        )
    except TaskpackAttestationError as exc:
        sys.stderr.write(str(exc) + "\n")
        return 1

    payload = {
        "schema": ATTESTATION_OUTPUT_SCHEMA,
        "remote_enclave_attestation_path": result.remote_enclave_attestation_path.as_posix(),
        "remote_enclave_attestation_hash": result.remote_enclave_attestation_hash,
        "attestation_verification_result_path": (
            result.attestation_verification_result_path.as_posix()
        ),
        "attestation_verification_result_hash": result.attestation_verification_result_hash,
        "attested_verified_result_path": result.attested_verified_result_path.as_posix(),
        "attested_verified_result_hash": result.attested_verified_result_hash,
        "local_verified_result_path": result.local_verified_result_path.as_posix(),
        "local_verified_result_hash": result.local_verified_result_hash,
    }
    sys.stdout.write(canonical_json(payload) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
