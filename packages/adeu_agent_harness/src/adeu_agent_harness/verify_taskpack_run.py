from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from urm_runtime.hashing import canonical_json, sha256_canonical_json

from ._v46_verifier_common import (
    AHK4600_PATH_POLICY_VIOLATION,
    AHK4602_SCHEMA_MISMATCH,
    AHK4603_ARTIFACT_INVALID,
    AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
    AHK4605_POLICY_VALIDATION_CONSISTENCY_MISMATCH,
    AHK4606_RUNNER_REJECTION_DIAGNOSTIC_INVALID,
    AHK4607_VERIFICATION_RESULT_INVALID,
    AHK4608_CONTRACT_REGISTRY_INVALID,
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
from .compile import TaskpackCompileError
from .policy_recompute import (
    DEFAULT_POLICY_RECOMPUTE_OUTPUT_ROOT,
    POLICY_RECOMPUTE_RESULT_SCHEMA,
    TaskpackPolicyRecomputeError,
    emit_policy_recompute_result,
    project_runner_policy_outcome,
    recompute_policy_validation,
)
from .run_taskpack import (
    CANDIDATE_CHANGE_PLAN_SCHEMA,
    REJECTION_DIAGNOSTIC_SCHEMA,
    RUNNER_PROVENANCE_SCHEMA,
    RUNNER_RESULT_SCHEMA,
    TaskpackRunnerError,
    _load_allowlist_payload_from_bytes,
    _load_candidate_change_plan,
    _load_commands_payload_from_bytes,
    _load_forbidden_payload_from_bytes,
)
from .verify_taskpack_signature import (
    TaskpackSigningError,
    load_validated_downstream_signature_handoff,
)

VERIFICATION_RESULT_SCHEMA = "taskpack_verification_result@1"
VERIFIER_RESULT_SCHEMA = "taskpack_verifier_result@1"
VERIFIER_CONTRACT_SCHEMA = "v33c_verifier_contract@1"

DEFAULT_VERIFICATION_ROOT = "artifacts/agent_harness/v46/verification"

_REQUIRED_RUNNER_RESULT_KEYS = {
    "schema",
    "dry_run",
    "candidate_change_plan_hash",
    "dry_run_preview_path",
    "provenance_path",
    "provenance_hash",
    "rejection_diagnostic_path",
}

_REQUIRED_PROVENANCE_KEYS = {
    "schema",
    "taskpack_manifest_hash",
    "adapter_id",
    "candidate_change_plan_hash",
    "policy_validation_result",
    "exit_status",
    "provenance_hash",
}

_REQUIRED_POLICY_RESULT_KEYS = {"passed", "issues"}

_REQUIRED_RUNNER_REJECTION_KEYS = {
    "schema",
    "taskpack_manifest_hash",
    "candidate_change_plan_hash",
    "issues",
}


@dataclass(frozen=True)
class TaskpackVerifierResult:
    verification_result_path: Path
    verified_result_hash: str
    policy_recompute_result_path: Path
    policy_recompute_result_hash: str
    rejection_diagnostic_path: Path | None


def _load_runner_result(path: Path) -> dict[str, Any]:
    payload = load_json_object(path)
    require_schema(payload, expected_schema=RUNNER_RESULT_SCHEMA, path=path)
    if set(payload.keys()) != _REQUIRED_RUNNER_RESULT_KEYS:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="runner result keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
            artifact_path=str(path),
            policy_source="runner_result",
        )
    if not isinstance(payload.get("dry_run"), bool):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="runner result dry_run must be boolean",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="runner_result",
        )
    candidate_hash = payload.get("candidate_change_plan_hash")
    provenance_hash = payload.get("provenance_hash")
    provenance_path = payload.get("provenance_path")
    dry_run_preview_path = payload.get("dry_run_preview_path")
    if not isinstance(candidate_hash, str) or not is_sha256(candidate_hash):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="runner result candidate_change_plan_hash is missing or invalid",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="runner_result",
        )
    if not isinstance(provenance_hash, str) or not is_sha256(provenance_hash):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="runner result provenance_hash is missing or invalid",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="runner_result",
        )
    if not isinstance(provenance_path, str) or not provenance_path:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="runner result provenance_path is missing or invalid",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="runner_result",
        )
    if dry_run_preview_path is not None and not isinstance(dry_run_preview_path, str):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="runner result dry_run_preview_path must be string or null",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="runner_result",
        )
    rejection_path = payload.get("rejection_diagnostic_path")
    if rejection_path is not None and not isinstance(rejection_path, str):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="runner result rejection_diagnostic_path must be string or null",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="runner_result",
        )
    return payload


def _load_runner_provenance(path: Path) -> dict[str, Any]:
    payload = load_json_object(path)
    require_schema(payload, expected_schema=RUNNER_PROVENANCE_SCHEMA, path=path)
    if set(payload.keys()) != _REQUIRED_PROVENANCE_KEYS:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="runner provenance keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
            artifact_path=str(path),
            policy_source="runner_provenance",
        )
    for key in (
        "taskpack_manifest_hash",
        "adapter_id",
        "candidate_change_plan_hash",
        "exit_status",
        "provenance_hash",
    ):
        value = payload.get(key)
        if not isinstance(value, str) or not value:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="runner provenance required string field is missing or invalid",
                details={"path": str(path), "field": key},
                artifact_path=str(path),
                policy_source="runner_provenance",
            )
    if not is_sha256(payload["taskpack_manifest_hash"]):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="runner provenance taskpack_manifest_hash is not sha256",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="runner_provenance",
        )
    if not is_sha256(payload["candidate_change_plan_hash"]):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="runner provenance candidate_change_plan_hash is not sha256",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="runner_provenance",
        )
    if not is_sha256(payload["provenance_hash"]):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="runner provenance provenance_hash is not sha256",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="runner_provenance",
        )

    policy_validation_result = payload.get("policy_validation_result")
    if not isinstance(policy_validation_result, dict):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="runner provenance policy_validation_result must be an object",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="runner_provenance",
        )
    if set(policy_validation_result.keys()) != _REQUIRED_POLICY_RESULT_KEYS:
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="policy_validation_result keys must match frozen grammar",
            details={
                "path": str(path),
                "keys": sorted(policy_validation_result.keys()),
            },
            artifact_path=str(path),
            policy_source="runner_provenance",
        )

    passed = policy_validation_result.get("passed")
    issues = policy_validation_result.get("issues")
    if not isinstance(passed, bool) or not isinstance(issues, list):
        raise fail(
            code=AHK4603_ARTIFACT_INVALID,
            message="policy_validation_result passed/issues fields are invalid",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="runner_provenance",
        )

    for index, issue in enumerate(issues):
        if not isinstance(issue, dict):
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="policy_validation_result issue entry must be an object",
                details={"path": str(path), "index": index},
                artifact_path=str(path),
                policy_source="runner_provenance",
            )
        if set(issue.keys()) != {"issue_code", "target_path", "hunk_index"}:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="policy_validation_result issue keys must match frozen grammar",
                details={"path": str(path), "index": index, "keys": sorted(issue.keys())},
                artifact_path=str(path),
                policy_source="runner_provenance",
            )
        if not isinstance(issue.get("issue_code"), str):
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="policy_validation_result issue_code must be string",
                details={"path": str(path), "index": index},
                artifact_path=str(path),
                policy_source="runner_provenance",
            )
        if not isinstance(issue.get("target_path"), str):
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="policy_validation_result target_path must be string",
                details={"path": str(path), "index": index},
                artifact_path=str(path),
                policy_source="runner_provenance",
            )
        if not isinstance(issue.get("hunk_index"), int):
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="policy_validation_result hunk_index must be integer",
                details={"path": str(path), "index": index},
                artifact_path=str(path),
                policy_source="runner_provenance",
            )
    return payload


def _recompute_runner_provenance_hash(provenance_payload: dict[str, Any]) -> str:
    hashed_subject = {
        "taskpack_manifest_hash": provenance_payload["taskpack_manifest_hash"],
        "adapter_id": provenance_payload["adapter_id"],
        "candidate_change_plan_hash": provenance_payload["candidate_change_plan_hash"],
        "policy_validation_result": provenance_payload["policy_validation_result"],
        "exit_status": provenance_payload["exit_status"],
    }
    return sha256_canonical_json(hashed_subject)


def _load_verifier_signature_handoff(
    *,
    taskpack_dir: str | Path,
    signature_verification_result_path: str | Path,
    signature_envelope_path: str | Path,
    trust_anchor_registry_path: str | Path,
    verification_reference_time_utc: str,
    repo_root_path: str | Path | None,
):
    try:
        return load_validated_downstream_signature_handoff(
            taskpack_dir=taskpack_dir,
            signature_verification_result_path=signature_verification_result_path,
            signature_envelope_path=signature_envelope_path,
            trust_anchor_registry_path=trust_anchor_registry_path,
            verification_reference_time_utc=verification_reference_time_utc,
            repo_root_path=repo_root_path,
        )
    except (TaskpackCompileError, TaskpackSigningError) as exc:
        failure_code = (
            AHK4604_CROSS_ARTIFACT_HASH_MISMATCH
            if exc.code in {"AHK0019", "AHK0020", "AHK4804"}
            else AHK4603_ARTIFACT_INVALID
        )
        raise fail(
            code=failure_code,
            message="verifier signing handoff validation failed",
            details={
                "signing_error_code": exc.code,
                "signing_error": exc.message,
                "signing_details": exc.details,
            },
            artifact_path=str(signature_verification_result_path),
            policy_source="taskpack_manifest",
        ) from exc


def _load_runner_rejection_diagnostic(path: Path) -> dict[str, Any]:
    payload = load_json_object(path)
    require_schema(payload, expected_schema=REJECTION_DIAGNOSTIC_SCHEMA, path=path)
    if set(payload.keys()) != _REQUIRED_RUNNER_REJECTION_KEYS:
        raise fail(
            code=AHK4606_RUNNER_REJECTION_DIAGNOSTIC_INVALID,
            message="runner rejection diagnostic keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
            artifact_path=str(path),
            policy_source="runner_result",
        )

    issues = payload.get("issues")
    if not isinstance(issues, list) or not issues:
        raise fail(
            code=AHK4606_RUNNER_REJECTION_DIAGNOSTIC_INVALID,
            message="runner rejection diagnostic issues must be a non-empty array",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="runner_result",
        )

    normalized_issues: list[dict[str, Any]] = []
    for index, issue in enumerate(issues):
        if not isinstance(issue, dict):
            raise fail(
                code=AHK4606_RUNNER_REJECTION_DIAGNOSTIC_INVALID,
                message="runner rejection diagnostic issue entry must be an object",
                details={"path": str(path), "index": index},
                artifact_path=str(path),
                policy_source="runner_result",
            )
        expected_keys = {
            "issue_code",
            "reason",
            "target_path",
            "hunk_index",
            "line_range",
            "policy_source",
        }
        if set(issue.keys()) != expected_keys:
            raise fail(
                code=AHK4606_RUNNER_REJECTION_DIAGNOSTIC_INVALID,
                message="runner rejection diagnostic issue keys must match frozen grammar",
                details={"path": str(path), "index": index, "keys": sorted(issue.keys())},
                artifact_path=str(path),
                policy_source="runner_result",
            )
        if not isinstance(issue.get("issue_code"), str):
            raise fail(
                code=AHK4606_RUNNER_REJECTION_DIAGNOSTIC_INVALID,
                message="runner rejection diagnostic issue_code must be string",
                details={"path": str(path), "index": index},
                artifact_path=str(path),
                policy_source="runner_result",
            )
        if not isinstance(issue.get("target_path"), str):
            raise fail(
                code=AHK4606_RUNNER_REJECTION_DIAGNOSTIC_INVALID,
                message="runner rejection diagnostic target_path must be string",
                details={"path": str(path), "index": index},
                artifact_path=str(path),
                policy_source="runner_result",
            )
        if not isinstance(issue.get("hunk_index"), int):
            raise fail(
                code=AHK4606_RUNNER_REJECTION_DIAGNOSTIC_INVALID,
                message="runner rejection diagnostic hunk_index must be integer",
                details={"path": str(path), "index": index},
                artifact_path=str(path),
                policy_source="runner_result",
            )
        normalized_issues.append(issue)

    if normalized_issues != sorted(
        normalized_issues,
        key=lambda row: (row["issue_code"], row["target_path"], row["hunk_index"]),
    ):
        raise fail(
            code=AHK4606_RUNNER_REJECTION_DIAGNOSTIC_INVALID,
            message="runner rejection diagnostic issue ordering drift detected",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="runner_result",
        )

    for field in ("taskpack_manifest_hash", "candidate_change_plan_hash"):
        value = payload.get(field)
        if not isinstance(value, str) or not is_sha256(value):
            raise fail(
                code=AHK4606_RUNNER_REJECTION_DIAGNOSTIC_INVALID,
                message="runner rejection diagnostic hash field is missing or invalid",
                details={"path": str(path), "field": field},
                artifact_path=str(path),
                policy_source="runner_result",
            )
    return payload


def _verification_hash_subject(
    *,
    taskpack_manifest_hash: str,
    candidate_change_plan_hash: str,
    runner_provenance_hash: str,
) -> dict[str, Any]:
    return {
        "taskpack_manifest_hash": taskpack_manifest_hash,
        "candidate_change_plan_hash": candidate_change_plan_hash,
        "runner_provenance_hash": runner_provenance_hash,
        "verification_result": {
            "passed": True,
            "issues": [],
            "cross_checks": [
                "taskpack_manifest_hash_match",
                "candidate_change_plan_hash_match",
                "policy_validation_result_consistency",
                "exit_status_consistency",
            ],
        },
        "exit_status": "success",
    }


def _emit_policy_recompute_result_for_verification(
    *,
    taskpack_path: Path,
    taskpack_component_bytes: dict[str, bytes],
    candidate_plan: Any,
    runner_result_payload: dict[str, Any],
    runner_provenance_payload: dict[str, Any],
    taskpack_manifest_hash: str,
    candidate_change_plan_hash: str,
    runner_provenance_hash: str,
    output_dir: Path,
) -> tuple[Path, str]:
    allowlist_paths = _load_allowlist_payload_from_bytes(
        path=taskpack_path / "ALLOWLIST.json",
        payload_bytes=taskpack_component_bytes["ALLOWLIST.json"],
    )
    forbidden_paths, _forbidden_effects, forbidden_operation_kinds = (
        _load_forbidden_payload_from_bytes(
            path=taskpack_path / "FORBIDDEN.json",
            payload_bytes=taskpack_component_bytes["FORBIDDEN.json"],
        )
    )
    _deterministic_env, commands_by_run = _load_commands_payload_from_bytes(
        path=taskpack_path / "COMMANDS.json",
        payload_bytes=taskpack_component_bytes["COMMANDS.json"],
    )
    runner_outcome = project_runner_policy_outcome(runner_provenance_payload)
    recompute_outcome = recompute_policy_validation(
        plan=candidate_plan,
        allowlist_paths=allowlist_paths,
        forbidden_paths=forbidden_paths,
        forbidden_operation_kinds=forbidden_operation_kinds,
        allowed_command_runs=commands_by_run.keys(),
        dry_run=runner_result_payload["dry_run"],
    )
    artifact = emit_policy_recompute_result(
        output_dir=output_dir,
        taskpack_manifest_hash=taskpack_manifest_hash,
        candidate_change_plan_hash=candidate_change_plan_hash,
        runner_provenance_hash=runner_provenance_hash,
        dry_run=runner_result_payload["dry_run"],
        runner_outcome=runner_outcome,
        recompute_outcome=recompute_outcome,
    )
    loaded = load_json_object(artifact.result_path)
    require_schema(
        loaded,
        expected_schema=POLICY_RECOMPUTE_RESULT_SCHEMA,
        path=artifact.result_path,
    )
    loaded_hash = loaded.get("result_hash")
    if not isinstance(loaded_hash, str) or not is_sha256(loaded_hash):
        raise fail(
            code=AHK4607_VERIFICATION_RESULT_INVALID,
            message="policy recompute result hash is missing or invalid",
            details={"path": str(artifact.result_path)},
            artifact_path=str(artifact.result_path),
            policy_source="runner_provenance",
        )
    if loaded_hash != artifact.result_hash:
        raise fail(
            code=AHK4607_VERIFICATION_RESULT_INVALID,
            message="policy recompute result hash drift detected",
            details={"path": str(artifact.result_path)},
            artifact_path=str(artifact.result_path),
            policy_source="runner_provenance",
        )
    return artifact.result_path, artifact.result_hash


def verify_taskpack_run(
    *,
    taskpack_dir: str | Path,
    candidate_change_plan_path: str | Path,
    runner_result_path: str | Path,
    runner_provenance_path: str | Path,
    policy_rejection_diagnostics_path: str | Path | None,
    signature_verification_result_path: str | Path,
    signature_envelope_path: str | Path,
    trust_anchor_registry_path: str | Path,
    verification_reference_time_utc: str,
    verification_output_root: str | Path,
    policy_recompute_output_root: str | Path = DEFAULT_POLICY_RECOMPUTE_OUTPUT_ROOT,
    diagnostic_registry_path: str | Path,
    repo_root_path: str | Path | None = None,
) -> TaskpackVerifierResult:
    require_deterministic_env_v46()
    root = project_repo_root(Path(repo_root_path) if repo_root_path is not None else None)

    manifest_hash: str | None = None
    candidate_hash: str | None = None
    registry_codes: set[str] = set()
    rejection_diagnostic_path: Path | None = None

    try:
        _, registry_codes = load_diagnostic_registry(
            root=root,
            registry_rel_path=normalize_relative_path(str(diagnostic_registry_path)),
        )

        taskpack_rel = normalize_relative_path(str(taskpack_dir))
        candidate_rel = normalize_relative_path(str(candidate_change_plan_path))
        runner_result_rel = normalize_relative_path(str(runner_result_path))
        runner_provenance_rel = normalize_relative_path(str(runner_provenance_path))
        verification_output_rel = normalize_relative_path(str(verification_output_root))
        policy_recompute_output_rel = normalize_relative_path(str(policy_recompute_output_root))

        handoff = _load_verifier_signature_handoff(
            taskpack_dir=taskpack_rel,
            signature_verification_result_path=signature_verification_result_path,
            signature_envelope_path=signature_envelope_path,
            trust_anchor_registry_path=trust_anchor_registry_path,
            verification_reference_time_utc=verification_reference_time_utc,
            repo_root_path=root,
        )
        candidate_path = coerce_artifact_path(root, candidate_rel)
        runner_result_artifact_path = coerce_artifact_path(root, runner_result_rel)
        runner_provenance_artifact_path = coerce_artifact_path(root, runner_provenance_rel)
        manifest_hash = handoff.taskpack_snapshot.manifest_hash

        try:
            candidate_plan = _load_candidate_change_plan(candidate_path)
        except TaskpackRunnerError as exc:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="candidate_change_plan artifact is invalid",
                details={"error": str(exc), "path": candidate_rel},
                artifact_path=candidate_rel,
                policy_source="candidate_change_plan",
            ) from exc
        if candidate_plan.schema != CANDIDATE_CHANGE_PLAN_SCHEMA:
            raise fail(
                code=AHK4602_SCHEMA_MISMATCH,
                message="candidate change plan schema mismatch",
                details={
                    "path": candidate_rel,
                    "expected_schema": CANDIDATE_CHANGE_PLAN_SCHEMA,
                    "observed_schema": candidate_plan.schema,
                },
                artifact_path=candidate_rel,
                policy_source="candidate_change_plan",
            )
        candidate_hash = candidate_plan.candidate_change_plan_hash

        runner_result_payload = _load_runner_result(runner_result_artifact_path)
        runner_provenance_payload = _load_runner_provenance(runner_provenance_artifact_path)

        resolved_runner_result_provenance_path = coerce_artifact_path(
            root,
            str(runner_result_payload["provenance_path"]),
        )
        if resolved_runner_result_provenance_path != runner_provenance_artifact_path:
            raise fail(
                code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
                message=(
                    "runner result provenance_path does not match verifier input "
                    "provenance path"
                ),
                details={
                    "runner_result_provenance_path": str(resolved_runner_result_provenance_path),
                    "input_provenance_path": str(runner_provenance_artifact_path),
                },
                artifact_path=runner_result_rel,
                policy_source="runner_result",
            )

        recomputed_provenance_hash = _recompute_runner_provenance_hash(runner_provenance_payload)
        if recomputed_provenance_hash != runner_provenance_payload["provenance_hash"]:
            raise fail(
                code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
                message="runner provenance hash recomputation mismatch",
                details={"path": runner_provenance_rel},
                artifact_path=runner_provenance_rel,
                policy_source="runner_provenance",
            )
        if runner_result_payload["provenance_hash"] != recomputed_provenance_hash:
            raise fail(
                code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
                message="runner result provenance_hash does not match recomputed provenance hash",
                details={"path": runner_result_rel},
                artifact_path=runner_result_rel,
                policy_source="runner_result",
            )

        if runner_result_payload["candidate_change_plan_hash"] != candidate_hash:
            raise fail(
                code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
                message=(
                    "runner result candidate_change_plan_hash does not match "
                    "canonical recomputation"
                ),
                details={"path": runner_result_rel},
                artifact_path=runner_result_rel,
                policy_source="candidate_change_plan",
            )
        if runner_provenance_payload["candidate_change_plan_hash"] != candidate_hash:
            raise fail(
                code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
                message=(
                    "runner provenance candidate_change_plan_hash does not match "
                    "canonical recomputation"
                ),
                details={"path": runner_provenance_rel},
                artifact_path=runner_provenance_rel,
                policy_source="candidate_change_plan",
            )
        if runner_provenance_payload["taskpack_manifest_hash"] != manifest_hash:
            raise fail(
                code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
                message=(
                    "runner provenance taskpack_manifest_hash does not match "
                    "manifest recomputation"
                ),
                details={"path": runner_provenance_rel},
                artifact_path=runner_provenance_rel,
                policy_source="taskpack_manifest",
            )

        policy_validation_result = runner_provenance_payload["policy_validation_result"]
        passed = policy_validation_result["passed"]
        issues = policy_validation_result["issues"]
        exit_status = runner_provenance_payload["exit_status"]
        runner_rejection_path_value = runner_result_payload["rejection_diagnostic_path"]

        if passed:
            if issues:
                raise fail(
                    code=AHK4605_POLICY_VALIDATION_CONSISTENCY_MISMATCH,
                    message="policy_validation_result passed=true requires empty issues array",
                    details={"path": runner_provenance_rel},
                    artifact_path=runner_provenance_rel,
                    policy_source="runner_provenance",
                )
            if exit_status != "success":
                raise fail(
                    code=AHK4605_POLICY_VALIDATION_CONSISTENCY_MISMATCH,
                    message="policy_validation_result passed=true requires exit_status=success",
                    details={"path": runner_provenance_rel, "exit_status": exit_status},
                    artifact_path=runner_provenance_rel,
                    policy_source="runner_provenance",
                )
            if runner_rejection_path_value is not None:
                raise fail(
                    code=AHK4605_POLICY_VALIDATION_CONSISTENCY_MISMATCH,
                    message=(
                        "runner result rejection_diagnostic_path must be null "
                        "when policy passed"
                    ),
                    details={"path": runner_result_rel},
                    artifact_path=runner_result_rel,
                    policy_source="runner_result",
                )
            if policy_rejection_diagnostics_path is not None:
                raise fail(
                    code=AHK4605_POLICY_VALIDATION_CONSISTENCY_MISMATCH,
                    message="policy_rejection_diagnostics input is forbidden when policy passed",
                    details={"path": str(policy_rejection_diagnostics_path)},
                    artifact_path=runner_result_rel,
                    policy_source="runner_result",
                )
        else:
            if not issues:
                raise fail(
                    code=AHK4605_POLICY_VALIDATION_CONSISTENCY_MISMATCH,
                    message="policy_validation_result passed=false requires non-empty issues array",
                    details={"path": runner_provenance_rel},
                    artifact_path=runner_provenance_rel,
                    policy_source="runner_provenance",
                )
            if exit_status != "policy_validation_failed":
                raise fail(
                    code=AHK4605_POLICY_VALIDATION_CONSISTENCY_MISMATCH,
                    message=(
                        "policy_validation_result passed=false requires "
                        "exit_status=policy_validation_failed"
                    ),
                    details={"path": runner_provenance_rel, "exit_status": exit_status},
                    artifact_path=runner_provenance_rel,
                    policy_source="runner_provenance",
                )

            if policy_rejection_diagnostics_path is not None:
                rejection_artifact_path = coerce_artifact_path(
                    root,
                    str(policy_rejection_diagnostics_path),
                )
            elif isinstance(runner_rejection_path_value, str) and runner_rejection_path_value:
                rejection_artifact_path = coerce_artifact_path(root, runner_rejection_path_value)
            else:
                raise fail(
                    code=AHK4606_RUNNER_REJECTION_DIAGNOSTIC_INVALID,
                    message="policy failure requires policy rejection diagnostics artifact",
                    details={"path": runner_result_rel},
                    artifact_path=runner_result_rel,
                    policy_source="runner_result",
                )
            if isinstance(runner_rejection_path_value, str) and runner_rejection_path_value:
                resolved_runner_rejection_path = coerce_artifact_path(
                    root, runner_rejection_path_value
                )
                if resolved_runner_rejection_path != rejection_artifact_path:
                    raise fail(
                        code=AHK4605_POLICY_VALIDATION_CONSISTENCY_MISMATCH,
                        message=(
                            "policy rejection diagnostics input path does not match "
                            "runner result rejection_diagnostic_path"
                        ),
                        details={
                            "runner_result_rejection_diagnostic_path": str(
                                resolved_runner_rejection_path
                            ),
                            "input_policy_rejection_diagnostics_path": str(
                                rejection_artifact_path
                            ),
                        },
                        artifact_path=runner_result_rel,
                        policy_source="runner_result",
                    )

            runner_rejection_payload = _load_runner_rejection_diagnostic(rejection_artifact_path)
            if runner_rejection_payload["taskpack_manifest_hash"] != manifest_hash:
                raise fail(
                    code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
                    message="runner rejection diagnostic taskpack_manifest_hash mismatch",
                    details={"path": str(rejection_artifact_path)},
                    artifact_path=str(rejection_artifact_path),
                    policy_source="runner_result",
                )
            if runner_rejection_payload["candidate_change_plan_hash"] != candidate_hash:
                raise fail(
                    code=AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
                    message="runner rejection diagnostic candidate_change_plan_hash mismatch",
                    details={"path": str(rejection_artifact_path)},
                    artifact_path=str(rejection_artifact_path),
                    policy_source="runner_result",
                )

        try:
            (
                policy_recompute_result_path,
                policy_recompute_result_hash,
            ) = _emit_policy_recompute_result_for_verification(
                taskpack_path=handoff.taskpack_snapshot.out_dir,
                taskpack_component_bytes=handoff.taskpack_snapshot.component_bytes_by_path,
                candidate_plan=candidate_plan,
                runner_result_payload=runner_result_payload,
                runner_provenance_payload=runner_provenance_payload,
                taskpack_manifest_hash=manifest_hash,
                candidate_change_plan_hash=candidate_hash,
                runner_provenance_hash=recomputed_provenance_hash,
                output_dir=coerce_artifact_path(root, policy_recompute_output_rel),
            )
        except TaskpackPolicyRecomputeError as exc:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="policy recompute baseline generation failed",
                details={
                    "policy_recompute_error_code": exc.code,
                    "policy_recompute_error": exc.message,
                    "policy_recompute_details": exc.details,
                },
                artifact_path=policy_recompute_output_rel,
                policy_source="runner_provenance",
            ) from exc
        except TaskpackRunnerError as exc:
            raise fail(
                code=AHK4603_ARTIFACT_INVALID,
                message="policy recompute baseline generation failed",
                details={
                    "runner_error_code": exc.code,
                    "runner_error": exc.message,
                    "runner_error_details": exc.details,
                },
                artifact_path=policy_recompute_output_rel,
                policy_source="runner_provenance",
            ) from exc

        hash_subject = _verification_hash_subject(
            taskpack_manifest_hash=manifest_hash,
            candidate_change_plan_hash=candidate_hash,
            runner_provenance_hash=recomputed_provenance_hash,
        )
        verified_result_hash = sha256_canonical_json(hash_subject)

        verified_result_payload: dict[str, Any] = {
            "schema": VERIFICATION_RESULT_SCHEMA,
            "contract_schema": VERIFIER_CONTRACT_SCHEMA,
            "taskpack_manifest_hash": manifest_hash,
            "candidate_change_plan_hash": candidate_hash,
            "runner_provenance_hash": recomputed_provenance_hash,
            "verification_result": hash_subject["verification_result"],
            "exit_status": hash_subject["exit_status"],
            "verified_result_hash": verified_result_hash,
            "verified_artifacts": {
                "taskpack_dir": taskpack_rel,
                "candidate_change_plan_path": candidate_rel,
                "runner_result_path": runner_result_rel,
                "runner_provenance_path": runner_provenance_rel,
            },
        }

        verification_dir = coerce_artifact_path(root, verification_output_rel)
        verification_result_path = verification_dir / f"{manifest_hash}_{candidate_hash}.json"
        write_json(verification_result_path, verified_result_payload)

        loaded = load_json_object(verification_result_path)
        require_schema(
            loaded,
            expected_schema=VERIFICATION_RESULT_SCHEMA,
            path=verification_result_path,
        )
        loaded_hash = loaded.get("verified_result_hash")
        if not isinstance(loaded_hash, str) or not is_sha256(loaded_hash):
            raise fail(
                code=AHK4607_VERIFICATION_RESULT_INVALID,
                message="verified_result_hash is missing or invalid",
                details={"path": str(verification_result_path)},
                artifact_path=str(verification_result_path),
                policy_source="runner_provenance",
            )
        if loaded_hash != verified_result_hash:
            raise fail(
                code=AHK4607_VERIFICATION_RESULT_INVALID,
                message="verification result hash drift detected",
                details={"path": str(verification_result_path)},
                artifact_path=str(verification_result_path),
                policy_source="runner_provenance",
            )

        return TaskpackVerifierResult(
            verification_result_path=verification_result_path,
            verified_result_hash=verified_result_hash,
            policy_recompute_result_path=policy_recompute_result_path,
            policy_recompute_result_hash=policy_recompute_result_hash,
            rejection_diagnostic_path=None,
        )

    except TaskpackVerifierError as exc:
        if not registry_codes:
            # If registry load itself failed, fallback to frozen local codes.
            registry_codes = {
                AHK4600_PATH_POLICY_VIOLATION,
                AHK4602_SCHEMA_MISMATCH,
                AHK4603_ARTIFACT_INVALID,
                AHK4604_CROSS_ARTIFACT_HASH_MISMATCH,
                AHK4605_POLICY_VALIDATION_CONSISTENCY_MISMATCH,
                AHK4606_RUNNER_REJECTION_DIAGNOSTIC_INVALID,
                AHK4607_VERIFICATION_RESULT_INVALID,
                AHK4608_CONTRACT_REGISTRY_INVALID,
                AHK4615_VERIFICATION_FAILURE_WITHOUT_REJECTION_DIAGNOSTIC,
            }
        issue = exc.issue or VerifierIssue(
            issue_code=exc.code,
            reason=exc.message,
            artifact_path=exc.details.get("path", ""),
            evidence_slot_id="verification",
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
                message="verification failure without rejection diagnostic emission",
                details={
                    "original_error": str(exc),
                    "rejection_error": str(rejection_exc),
                },
                issue=VerifierIssue(
                    issue_code=AHK4615_VERIFICATION_FAILURE_WITHOUT_REJECTION_DIAGNOSTIC,
                    reason="verification failure without rejection diagnostic emission",
                    artifact_path=exc.details.get("path", ""),
                    evidence_slot_id="verification",
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
            "Verify deterministic v45 runner artifacts under v46 auditor-only "
            "consistency rules before evidence emission."
        ),
    )
    parser.add_argument(
        "--taskpack-dir",
        required=True,
        help="Repo-relative taskpack directory containing manifest/components.",
    )
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
        "--policy-rejection-diagnostics",
        default=None,
        help="Optional repo-relative path to candidate_change_plan_rejection_diagnostic@1 JSON.",
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
        help="Explicit RFC3339 UTC Z reference time used for v48/v49 signing lifecycle checks.",
    )
    parser.add_argument(
        "--verification-output-root",
        default=DEFAULT_VERIFICATION_ROOT,
        help="Repo-relative output root for taskpack_verification_result@1 artifact.",
    )
    parser.add_argument(
        "--policy-recompute-output-root",
        default=DEFAULT_POLICY_RECOMPUTE_OUTPUT_ROOT,
        help="Repo-relative output root for policy_recompute_result@1 artifact.",
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
        result = verify_taskpack_run(
            taskpack_dir=args.taskpack_dir,
            candidate_change_plan_path=args.candidate_change_plan,
            runner_result_path=args.runner_result,
            runner_provenance_path=args.runner_provenance,
            policy_rejection_diagnostics_path=args.policy_rejection_diagnostics,
            signature_verification_result_path=args.signature_verification_result,
            signature_envelope_path=args.signature_envelope,
            trust_anchor_registry_path=args.trust_anchor_registry,
            verification_reference_time_utc=args.verification_reference_time_utc,
            verification_output_root=args.verification_output_root,
            policy_recompute_output_root=args.policy_recompute_output_root,
            diagnostic_registry_path=args.diagnostic_registry,
            repo_root_path=args.repo_root,
        )
    except TaskpackVerifierError as exc:
        sys.stderr.write(str(exc) + "\n")
        return 1

    payload = {
        "schema": VERIFIER_RESULT_SCHEMA,
        "verification_result_path": result.verification_result_path.as_posix(),
        "verified_result_hash": result.verified_result_hash,
        "policy_recompute_result_path": result.policy_recompute_result_path.as_posix(),
        "policy_recompute_result_hash": result.policy_recompute_result_hash,
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
