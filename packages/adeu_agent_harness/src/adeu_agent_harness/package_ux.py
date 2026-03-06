from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from urm_runtime.hashing import canonical_json, sha256_canonical_json

from ._v47_packaging_common import (
    AHK4703_ARTIFACT_INVALID,
    AHK4704_CROSS_ARTIFACT_HASH_MISMATCH,
    AHK4705_DEPLOYMENT_MODE_POLICY_VIOLATION,
    AHK4706_MODE_CONTRACT_IDENTITY_MISMATCH,
    AHK4707_PACKAGING_MANIFEST_INVALID,
    AHK4708_CONTRACT_REGISTRY_INVALID,
    AHK4709_PACKAGING_REJECTION_DIAGNOSTIC_INVALID,
    AHK4710_PACKAGING_PROVENANCE_INVALID,
    AHK4711_SUBPROCESS_MODE_POLICY_VIOLATION,
    AHK4712_CANONICAL_SUBJECT_PATH_NORMALIZATION_DRIFT,
    AHK4713_PACKAGING_FAILURE_WITHOUT_REJECTION_DIAGNOSTIC,
    DEFAULT_DIAGNOSTIC_REGISTRY_PATH,
    DEFAULT_REJECTIONS_ROOT,
    POLICY_SOURCE_ENUM_V47,
    PackagingIssue,
    TaskpackPackagingError,
    coerce_artifact_path,
    emit_rejection_diagnostic,
    fail,
    is_sha256,
    load_diagnostic_registry,
    load_json_object,
    normalize_relative_path,
    project_repo_root,
    require_deterministic_env_v47,
    require_schema,
    write_json,
)
from .compile import TaskpackCompileError
from .verify_taskpack_run import VERIFICATION_RESULT_SCHEMA
from .verify_taskpack_signature import (
    TaskpackSigningError,
    load_validated_downstream_signature_handoff,
)
from .write_closeout_evidence import (
    EVIDENCE_BUNDLE_SCHEMA,
    METRIC_KEY_CONTINUITY_SCHEMA,
    RUNTIME_OBSERVABILITY_SCHEMA,
    VERIFIER_PROVENANCE_SCHEMA,
)

PACKAGING_MANIFEST_SCHEMA = "taskpack_ux_packaging_manifest@1"
PACKAGING_PROVENANCE_SCHEMA = "taskpack_packaging_provenance@1"
PACKAGING_RESULT_SCHEMA = "taskpack_packaging_result@1"

DEFAULT_PACKAGING_ROOT = "artifacts/agent_harness/v47/packaging"

DEPLOYMENT_MODE_INTEGRATED = "adeu_integrated"
DEPLOYMENT_MODE_STANDALONE = "standalone"
DEPLOYMENT_MODES = (DEPLOYMENT_MODE_INTEGRATED, DEPLOYMENT_MODE_STANDALONE)

_SUBPROCESS_DELEGATION_ENV_OVERRIDE = "ADEU_DEPLOYMENT_MODE_OVERRIDE"

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

_REQUIRED_EVIDENCE_BUNDLE_KEYS = {
    "schema",
    "taskpack_manifest_hash",
    "candidate_change_plan_hash",
    "ordered_evidence_blocks",
    "ordered_rejection_diagnostics_optional",
    "evidence_bundle_hash",
}

_REQUIRED_VERIFIER_PROVENANCE_KEYS = {
    "schema",
    "taskpack_manifest_hash",
    "candidate_change_plan_hash",
    "runner_provenance_hash",
    "verification_result",
    "evidence_bundle_hash",
    "exit_status",
    "provenance_hash",
}

_POLICY_EQUIVALENCE_SUBJECT_KEYS = {
    "issue_code_set",
    "required_evidence_slots_filled",
    "allowlist_violations",
    "forbidden_effects_detected",
}

_ALLOWLIST_VIOLATION_ISSUE_CODES = frozenset(
    {
        "allowlist_violation",
    }
)

_FORBIDDEN_EFFECT_ISSUE_CODES = frozenset(
    {
        "forbidden_path_violation",
        "forbidden_operation_kind",
        "model_suggested_command_execution_detected",
        "dry_run_subprocess_execution_detected",
    }
)

_TASKPACK_CANONICAL_COMPONENTS = (
    "TASKPACK.md",
    "ACCEPTANCE.json",
    "ALLOWLIST.json",
    "FORBIDDEN.json",
    "COMMANDS.json",
    "EVIDENCE_SLOTS.json",
    "taskpack_manifest.json",
)


@dataclass(frozen=True)
class TaskpackPackagingResult:
    packaging_manifest_path: Path
    packaging_bundle_hash: str
    packaging_provenance_path: Path
    packaging_provenance_hash: str
    rejection_diagnostic_path: Path | None
    deployment_mode: str


def _read_canonical_json(path: Path) -> dict[str, Any]:
    payload = load_json_object(path)
    return payload


def _read_canonical_json_bytes(*, payload_bytes: bytes, source_path: Path) -> dict[str, Any]:
    try:
        parsed = json.loads(payload_bytes.decode("utf-8"))
    except UnicodeDecodeError as exc:
        raise fail(
            code=AHK4703_ARTIFACT_INVALID,
            message="json artifact is not valid utf-8",
            details={"path": str(source_path), "error": str(exc)},
            artifact_path=str(source_path),
            policy_source="taskpack_manifest",
        ) from exc
    except json.JSONDecodeError as exc:
        raise fail(
            code=AHK4703_ARTIFACT_INVALID,
            message="json artifact is invalid",
            details={"path": str(source_path), "error": str(exc)},
            artifact_path=str(source_path),
            policy_source="taskpack_manifest",
        ) from exc
    if not isinstance(parsed, dict):
        raise fail(
            code=AHK4703_ARTIFACT_INVALID,
            message="json artifact must decode to an object",
            details={"path": str(source_path)},
            artifact_path=str(source_path),
            policy_source="taskpack_manifest",
        )
    return parsed


def _normalize_repo_relative_path_for_hash(*, root: Path, absolute_path: Path) -> str:
    root_resolved = root.resolve()
    resolved = absolute_path.resolve()
    try:
        rel = resolved.relative_to(root_resolved).as_posix()
    except ValueError as exc:
        raise fail(
            code=AHK4712_CANONICAL_SUBJECT_PATH_NORMALIZATION_DRIFT,
            message="emitted path is outside repository root",
            details={"path": str(absolute_path)},
            artifact_path=str(absolute_path),
            policy_source="packaging_manifest",
        ) from exc
    normalized = normalize_relative_path(rel)
    if "\\" in normalized:
        raise fail(
            code=AHK4712_CANONICAL_SUBJECT_PATH_NORMALIZATION_DRIFT,
            message="normalized emitted path still contains os-native separator",
            details={"path": normalized},
            artifact_path=normalized,
            policy_source="packaging_manifest",
        )
    return normalized


def _write_canonical_json_file(
    *,
    path: Path,
    payload: dict[str, Any],
) -> None:
    write_json(path, payload)


def _normalize_issue_artifact_path_for_diagnostic(*, root: Path, artifact_path: str) -> str:
    candidate_text = artifact_path.strip()
    if not candidate_text:
        return "packaging"

    candidate_path = Path(candidate_text)
    if not candidate_path.is_absolute():
        return candidate_text

    root_resolved = root.resolve()
    resolved = candidate_path.resolve()
    try:
        return resolved.relative_to(root_resolved).as_posix()
    except ValueError:
        return "packaging"


def _copy_taskpack_component(
    *,
    mode_root: Path,
    component_name: str,
    component_bytes: bytes,
) -> Path:
    destination_path = mode_root / "canonical" / component_name
    destination_path.parent.mkdir(parents=True, exist_ok=True)

    if destination_path.suffix.lower() == ".json":
        payload = _read_canonical_json_bytes(
            payload_bytes=component_bytes,
            source_path=destination_path,
        )
        _write_canonical_json_file(path=destination_path, payload=payload)
    else:
        destination_path.write_bytes(component_bytes)
    return destination_path


def _emit_canonical_artifact_file(
    *,
    source_path: Path,
    destination_path: Path,
    expected_schema: str,
) -> Path:
    payload = _read_canonical_json(source_path)
    require_schema(payload, expected_schema=expected_schema, path=source_path)
    _write_canonical_json_file(path=destination_path, payload=payload)
    return destination_path


def _load_packaging_signature_handoff(
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
            AHK4704_CROSS_ARTIFACT_HASH_MISMATCH
            if exc.code in {"AHK0019", "AHK0020", "AHK4804"}
            else AHK4703_ARTIFACT_INVALID
        )
        raise fail(
            code=failure_code,
            message="packaging signing handoff validation failed",
            details={
                "signing_error_code": exc.code,
                "signing_error": exc.message,
                "signing_details": exc.details,
            },
            artifact_path=str(signature_verification_result_path),
            policy_source="taskpack_manifest",
        ) from exc


def _load_verified_result(path: Path) -> dict[str, Any]:
    payload = load_json_object(path)
    require_schema(payload, expected_schema=VERIFICATION_RESULT_SCHEMA, path=path)
    if set(payload.keys()) != _REQUIRED_VERIFIED_RESULT_KEYS:
        raise fail(
            code=AHK4703_ARTIFACT_INVALID,
            message="verified result keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
            artifact_path=str(path),
            policy_source="verified_result",
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
                code=AHK4703_ARTIFACT_INVALID,
                message="verified result hash field is missing or invalid",
                details={"path": str(path), "field": field},
                artifact_path=str(path),
                policy_source="verified_result",
            )

    verification_result = payload.get("verification_result")
    if not isinstance(verification_result, dict):
        raise fail(
            code=AHK4703_ARTIFACT_INVALID,
            message="verification_result must be an object",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="verified_result",
        )
    if set(verification_result.keys()) != {"passed", "issues", "cross_checks"}:
        raise fail(
            code=AHK4703_ARTIFACT_INVALID,
            message="verification_result keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(verification_result.keys())},
            artifact_path=str(path),
            policy_source="verified_result",
        )
    if verification_result.get("passed") is not True or verification_result.get("issues") != []:
        raise fail(
            code=AHK4706_MODE_CONTRACT_IDENTITY_MISMATCH,
            message=(
                "packaging requires verified_result verification_result "
                "passed=true and issues=[]"
            ),
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="verified_result",
        )

    hash_subject = {
        "taskpack_manifest_hash": payload["taskpack_manifest_hash"],
        "candidate_change_plan_hash": payload["candidate_change_plan_hash"],
        "runner_provenance_hash": payload["runner_provenance_hash"],
        "verification_result": verification_result,
        "exit_status": payload.get("exit_status"),
    }
    recomputed_hash = sha256_canonical_json(hash_subject)
    if recomputed_hash != payload["verified_result_hash"]:
        raise fail(
            code=AHK4704_CROSS_ARTIFACT_HASH_MISMATCH,
            message="verified result hash recomputation mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="verified_result",
        )
    return payload


def _load_evidence_bundle(path: Path) -> dict[str, Any]:
    payload = load_json_object(path)
    require_schema(payload, expected_schema=EVIDENCE_BUNDLE_SCHEMA, path=path)
    if set(payload.keys()) != _REQUIRED_EVIDENCE_BUNDLE_KEYS:
        raise fail(
            code=AHK4703_ARTIFACT_INVALID,
            message="evidence bundle keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
            artifact_path=str(path),
            policy_source="evidence_bundle",
        )

    manifest_hash = payload.get("taskpack_manifest_hash")
    candidate_hash = payload.get("candidate_change_plan_hash")
    evidence_bundle_hash = payload.get("evidence_bundle_hash")
    if not isinstance(manifest_hash, str) or not is_sha256(manifest_hash):
        raise fail(
            code=AHK4703_ARTIFACT_INVALID,
            message="evidence bundle taskpack_manifest_hash is missing or invalid",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="evidence_bundle",
        )
    if not isinstance(candidate_hash, str) or not is_sha256(candidate_hash):
        raise fail(
            code=AHK4703_ARTIFACT_INVALID,
            message="evidence bundle candidate_change_plan_hash is missing or invalid",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="evidence_bundle",
        )
    if not isinstance(evidence_bundle_hash, str) or not is_sha256(evidence_bundle_hash):
        raise fail(
            code=AHK4703_ARTIFACT_INVALID,
            message="evidence bundle evidence_bundle_hash is missing or invalid",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="evidence_bundle",
        )

    hash_subject = {
        "taskpack_manifest_hash": manifest_hash,
        "ordered_evidence_blocks": payload["ordered_evidence_blocks"],
        "ordered_rejection_diagnostics_optional": payload["ordered_rejection_diagnostics_optional"],
    }
    recomputed_hash = sha256_canonical_json(hash_subject)
    if recomputed_hash != evidence_bundle_hash:
        raise fail(
            code=AHK4704_CROSS_ARTIFACT_HASH_MISMATCH,
            message="evidence bundle hash recomputation mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="evidence_bundle",
        )
    return payload


def _load_verifier_provenance(path: Path) -> dict[str, Any]:
    payload = load_json_object(path)
    require_schema(payload, expected_schema=VERIFIER_PROVENANCE_SCHEMA, path=path)
    if set(payload.keys()) != _REQUIRED_VERIFIER_PROVENANCE_KEYS:
        raise fail(
            code=AHK4703_ARTIFACT_INVALID,
            message="verifier provenance keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
            artifact_path=str(path),
            policy_source="verifier_provenance",
        )

    for key in (
        "taskpack_manifest_hash",
        "candidate_change_plan_hash",
        "runner_provenance_hash",
        "evidence_bundle_hash",
        "exit_status",
        "provenance_hash",
    ):
        value = payload.get(key)
        if not isinstance(value, str) or not value:
            raise fail(
                code=AHK4703_ARTIFACT_INVALID,
                message="verifier provenance required field is missing or invalid",
                details={"path": str(path), "field": key},
                artifact_path=str(path),
                policy_source="verifier_provenance",
            )

    for key in (
        "taskpack_manifest_hash",
        "candidate_change_plan_hash",
        "runner_provenance_hash",
        "evidence_bundle_hash",
        "provenance_hash",
    ):
        if not is_sha256(payload[key]):
            raise fail(
                code=AHK4703_ARTIFACT_INVALID,
                message="verifier provenance hash field must be sha256",
                details={"path": str(path), "field": key},
                artifact_path=str(path),
                policy_source="verifier_provenance",
            )

    hash_subject = {
        "taskpack_manifest_hash": payload["taskpack_manifest_hash"],
        "candidate_change_plan_hash": payload["candidate_change_plan_hash"],
        "runner_provenance_hash": payload["runner_provenance_hash"],
        "verification_result": payload["verification_result"],
        "evidence_bundle_hash": payload["evidence_bundle_hash"],
        "exit_status": payload["exit_status"],
    }
    recomputed_hash = sha256_canonical_json(hash_subject)
    if recomputed_hash != payload["provenance_hash"]:
        raise fail(
            code=AHK4710_PACKAGING_PROVENANCE_INVALID,
            message="verifier provenance hash recomputation mismatch",
            details={"path": str(path)},
            artifact_path=str(path),
            policy_source="verifier_provenance",
        )

    return payload


def _load_runtime_observability(path: Path) -> dict[str, Any]:
    payload = load_json_object(path)
    require_schema(payload, expected_schema=RUNTIME_OBSERVABILITY_SCHEMA, path=path)
    return payload


def _load_metric_key_continuity(path: Path) -> dict[str, Any]:
    payload = load_json_object(path)
    require_schema(payload, expected_schema=METRIC_KEY_CONTINUITY_SCHEMA, path=path)
    return payload


def _extract_policy_equivalence(
    *,
    evidence_slots_payload: dict[str, Any],
    evidence_slots_artifact_path: Path,
    verified_result_payload: dict[str, Any],
    evidence_bundle_payload: dict[str, Any],
) -> dict[str, Any]:
    required_slot_ids = {
        slot["slot_id"]
        for slot in evidence_slots_payload.get("slots", [])
        if (
            isinstance(slot, dict)
            and slot.get("required") is True
            and isinstance(slot.get("slot_id"), str)
        )
    }

    observed_slot_ids = {
        block.get("slot_id")
        for block in evidence_bundle_payload.get("ordered_evidence_blocks", [])
        if isinstance(block, dict)
    }
    required_evidence_slots_filled = required_slot_ids.issubset(observed_slot_ids)

    issue_code_set: set[str] = set()
    for diag in evidence_bundle_payload.get("ordered_rejection_diagnostics_optional", []):
        if not isinstance(diag, dict):
            continue
        for issue in diag.get("issues", []):
            if isinstance(issue, dict) and isinstance(issue.get("issue_code"), str):
                issue_code_set.add(issue["issue_code"])

    runner_policy_issue_codes: set[str] = set()
    allowlist_violations: set[str] = set()
    verification_result = verified_result_payload.get("verification_result")
    if isinstance(verification_result, dict):
        for issue in verification_result.get("issues", []):
            if not isinstance(issue, dict):
                continue
            issue_code = issue.get("issue_code")
            if isinstance(issue_code, str):
                runner_policy_issue_codes.add(issue_code)
            target = issue.get("target_path")
            if (
                isinstance(issue_code, str)
                and issue_code in _ALLOWLIST_VIOLATION_ISSUE_CODES
                and isinstance(target, str)
                and target
            ):
                normalized = normalize_relative_path(target)
                allowlist_violations.add(normalized)

    forbidden_effects_detected = not _FORBIDDEN_EFFECT_ISSUE_CODES.isdisjoint(
        issue_code_set.union(runner_policy_issue_codes)
    )

    parity_subject = {
        "issue_code_set": sorted(issue_code_set),
        "required_evidence_slots_filled": required_evidence_slots_filled,
        "allowlist_violations": sorted(allowlist_violations),
        "forbidden_effects_detected": forbidden_effects_detected,
    }

    if set(parity_subject.keys()) != _POLICY_EQUIVALENCE_SUBJECT_KEYS:
        raise fail(
            code=AHK4706_MODE_CONTRACT_IDENTITY_MISMATCH,
            message="policy-equivalence subject keys must match frozen grammar",
            details={"keys": sorted(parity_subject.keys())},
            artifact_path=str(evidence_slots_artifact_path),
            policy_source="packaging_manifest",
        )
    return parity_subject


def _emit_mode_bundle_file(*, mode_root: Path, deployment_mode: str) -> Path:
    bundle_path = mode_root / "bundle" / "launcher.txt"
    bundle_path.parent.mkdir(parents=True, exist_ok=True)
    bundle_path.write_text(
        f"schema=taskpack_ux_mode_bundle@1\ndeployment_mode={deployment_mode}\n",
        encoding="utf-8",
    )
    return bundle_path


def _hash_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _emit_packaging_manifest(
    *,
    mode_root: Path,
    deployment_mode: str,
    authority_artifact_hashes: dict[str, str],
    emitted_files_records: list[dict[str, str]],
) -> tuple[Path, str]:
    packaging_bundle_hash = sha256_canonical_json(emitted_files_records)
    manifest_payload = {
        "schema": PACKAGING_MANIFEST_SCHEMA,
        "deployment_mode": deployment_mode,
        "authority_artifact_hashes": authority_artifact_hashes,
        "emitted_files": emitted_files_records,
        "packaging_bundle_hash": packaging_bundle_hash,
    }
    manifest_path = mode_root / "taskpack_ux_packaging_manifest.json"
    write_json(manifest_path, manifest_payload)

    loaded_manifest = load_json_object(manifest_path)
    require_schema(loaded_manifest, expected_schema=PACKAGING_MANIFEST_SCHEMA, path=manifest_path)
    if loaded_manifest.get("packaging_bundle_hash") != packaging_bundle_hash:
        raise fail(
            code=AHK4707_PACKAGING_MANIFEST_INVALID,
            message="packaging manifest bundle hash drift detected",
            details={"path": str(manifest_path)},
            artifact_path=str(manifest_path),
            policy_source="packaging_manifest",
        )

    return manifest_path, packaging_bundle_hash


def _emit_packaging_provenance(
    *,
    mode_root: Path,
    taskpack_manifest_hash: str,
    verified_result_hash: str,
    evidence_bundle_hash: str,
    deployment_mode: str,
    parity_result: dict[str, Any],
) -> tuple[Path, str]:
    hash_subject = {
        "taskpack_manifest_hash": taskpack_manifest_hash,
        "verified_result_hash": verified_result_hash,
        "evidence_bundle_hash": evidence_bundle_hash,
        "deployment_mode": deployment_mode,
        "parity_result": parity_result,
        "exit_status": "success",
    }
    provenance_hash = sha256_canonical_json(hash_subject)
    payload = {
        "schema": PACKAGING_PROVENANCE_SCHEMA,
        **hash_subject,
        "provenance_hash": provenance_hash,
    }
    provenance_path = (
        mode_root
        / "provenance"
        / f"{taskpack_manifest_hash}_{verified_result_hash}.json"
    )
    write_json(provenance_path, payload)

    loaded = load_json_object(provenance_path)
    require_schema(loaded, expected_schema=PACKAGING_PROVENANCE_SCHEMA, path=provenance_path)
    if loaded.get("provenance_hash") != provenance_hash:
        raise fail(
            code=AHK4710_PACKAGING_PROVENANCE_INVALID,
            message="packaging provenance hash drift detected",
            details={"path": str(provenance_path)},
            artifact_path=str(provenance_path),
            policy_source="packaging_manifest",
        )

    return provenance_path, provenance_hash


def package_ux_surface(
    *,
    expected_mode: str,
    deployment_mode: str,
    taskpack_dir: str | Path,
    signature_verification_result_path: str | Path,
    signature_envelope_path: str | Path,
    trust_anchor_registry_path: str | Path,
    verification_reference_time_utc: str,
    verified_result_path: str | Path,
    evidence_bundle_path: str | Path,
    verifier_provenance_path: str | Path,
    runtime_observability_comparison_path: str | Path,
    metric_key_continuity_assertion_path: str | Path,
    packaging_output_root: str | Path,
    diagnostic_registry_path: str | Path,
    dry_run: bool,
    repo_root_path: str | Path | None = None,
) -> TaskpackPackagingResult:
    require_deterministic_env_v47()
    root = project_repo_root(Path(repo_root_path) if repo_root_path is not None else None)

    manifest_hash: str | None = None
    verified_result_hash: str | None = None
    registry_codes: set[str] = set()
    rejection_diagnostic_path: Path | None = None

    try:
        if expected_mode not in DEPLOYMENT_MODES:
            raise fail(
                code=AHK4705_DEPLOYMENT_MODE_POLICY_VIOLATION,
                message="expected_mode is outside frozen deployment mode enum",
                details={"expected_mode": expected_mode},
                artifact_path=str(taskpack_dir),
                deployment_mode=deployment_mode,
                policy_source="packaging_manifest",
            )

        if deployment_mode not in DEPLOYMENT_MODES:
            raise fail(
                code=AHK4705_DEPLOYMENT_MODE_POLICY_VIOLATION,
                message="deployment_mode is outside frozen deployment mode enum",
                details={"deployment_mode": deployment_mode},
                artifact_path=str(taskpack_dir),
                deployment_mode=deployment_mode,
                policy_source="packaging_manifest",
            )
        if deployment_mode != expected_mode:
            raise fail(
                code=AHK4705_DEPLOYMENT_MODE_POLICY_VIOLATION,
                message="deployment_mode must match mode-specific entrypoint",
                details={"deployment_mode": deployment_mode, "expected_mode": expected_mode},
                artifact_path=str(taskpack_dir),
                deployment_mode=deployment_mode,
                policy_source="packaging_manifest",
            )

        if os.environ.get(_SUBPROCESS_DELEGATION_ENV_OVERRIDE) is not None:
            raise fail(
                code=AHK4711_SUBPROCESS_MODE_POLICY_VIOLATION,
                message="deployment mode env override is forbidden in v47",
                details={"env_var": _SUBPROCESS_DELEGATION_ENV_OVERRIDE},
                artifact_path="environment",
                deployment_mode=deployment_mode,
                policy_source="packaging_manifest",
            )

        _, registry_codes = load_diagnostic_registry(
            root=root,
            registry_rel_path=normalize_relative_path(str(diagnostic_registry_path)),
        )

        taskpack_rel = normalize_relative_path(str(taskpack_dir))
        verified_result_rel = normalize_relative_path(str(verified_result_path))
        evidence_bundle_rel = normalize_relative_path(str(evidence_bundle_path))
        verifier_provenance_rel = normalize_relative_path(str(verifier_provenance_path))
        runtime_rel = normalize_relative_path(str(runtime_observability_comparison_path))
        continuity_rel = normalize_relative_path(str(metric_key_continuity_assertion_path))
        packaging_output_rel = normalize_relative_path(str(packaging_output_root))

        handoff = _load_packaging_signature_handoff(
            taskpack_dir=taskpack_rel,
            signature_verification_result_path=signature_verification_result_path,
            signature_envelope_path=signature_envelope_path,
            trust_anchor_registry_path=trust_anchor_registry_path,
            verification_reference_time_utc=verification_reference_time_utc,
            repo_root_path=root,
        )
        taskpack_path = handoff.taskpack_snapshot.out_dir
        verified_result_artifact = coerce_artifact_path(root, verified_result_rel)
        evidence_bundle_artifact = coerce_artifact_path(root, evidence_bundle_rel)
        verifier_provenance_artifact = coerce_artifact_path(root, verifier_provenance_rel)
        runtime_artifact = coerce_artifact_path(root, runtime_rel)
        continuity_artifact = coerce_artifact_path(root, continuity_rel)
        packaging_root = coerce_artifact_path(root, packaging_output_rel)
        manifest_hash = handoff.taskpack_snapshot.manifest_hash

        verified_result_payload = _load_verified_result(verified_result_artifact)
        evidence_bundle_payload = _load_evidence_bundle(evidence_bundle_artifact)
        verifier_provenance_payload = _load_verifier_provenance(verifier_provenance_artifact)
        runtime_payload = _load_runtime_observability(runtime_artifact)
        continuity_payload = _load_metric_key_continuity(continuity_artifact)
        evidence_slots_payload = _read_canonical_json_bytes(
            payload_bytes=handoff.taskpack_snapshot.component_bytes_by_path["EVIDENCE_SLOTS.json"],
            source_path=taskpack_path / "EVIDENCE_SLOTS.json",
        )

        verified_result_hash = verified_result_payload["verified_result_hash"]

        if verified_result_payload["taskpack_manifest_hash"] != manifest_hash:
            raise fail(
                code=AHK4704_CROSS_ARTIFACT_HASH_MISMATCH,
                message="verified result taskpack_manifest_hash mismatch",
                details={"path": verified_result_rel},
                artifact_path=verified_result_rel,
                deployment_mode=deployment_mode,
                policy_source="verified_result",
            )
        if evidence_bundle_payload["taskpack_manifest_hash"] != manifest_hash:
            raise fail(
                code=AHK4704_CROSS_ARTIFACT_HASH_MISMATCH,
                message="evidence bundle taskpack_manifest_hash mismatch",
                details={"path": evidence_bundle_rel},
                artifact_path=evidence_bundle_rel,
                deployment_mode=deployment_mode,
                policy_source="evidence_bundle",
            )
        if verifier_provenance_payload["taskpack_manifest_hash"] != manifest_hash:
            raise fail(
                code=AHK4704_CROSS_ARTIFACT_HASH_MISMATCH,
                message="verifier provenance taskpack_manifest_hash mismatch",
                details={"path": verifier_provenance_rel},
                artifact_path=verifier_provenance_rel,
                deployment_mode=deployment_mode,
                policy_source="verifier_provenance",
            )
        if (
            verifier_provenance_payload["evidence_bundle_hash"]
            != evidence_bundle_payload["evidence_bundle_hash"]
        ):
            raise fail(
                code=AHK4704_CROSS_ARTIFACT_HASH_MISMATCH,
                message="verifier provenance evidence_bundle_hash mismatch",
                details={"path": verifier_provenance_rel},
                artifact_path=verifier_provenance_rel,
                deployment_mode=deployment_mode,
                policy_source="verifier_provenance",
            )

        mode_root = packaging_root / deployment_mode
        canonical_root = mode_root / "canonical"
        canonical_root.mkdir(parents=True, exist_ok=True)

        emitted_paths: list[Path] = []

        for component in _TASKPACK_CANONICAL_COMPONENTS:
            emitted_paths.append(
                _copy_taskpack_component(
                    mode_root=mode_root,
                    component_name=component,
                    component_bytes=(
                        handoff.taskpack_snapshot.manifest_bytes
                        if component == "taskpack_manifest.json"
                        else handoff.taskpack_snapshot.component_bytes_by_path[component]
                    ),
                )
            )

        emitted_paths.append(
            _emit_canonical_artifact_file(
                source_path=verified_result_artifact,
                destination_path=canonical_root / "taskpack_verification_result.json",
                expected_schema=VERIFICATION_RESULT_SCHEMA,
            )
        )
        emitted_paths.append(
            _emit_canonical_artifact_file(
                source_path=evidence_bundle_artifact,
                destination_path=canonical_root / "taskpack_closeout_evidence_bundle.json",
                expected_schema=EVIDENCE_BUNDLE_SCHEMA,
            )
        )
        emitted_paths.append(
            _emit_canonical_artifact_file(
                source_path=verifier_provenance_artifact,
                destination_path=canonical_root / "taskpack_verifier_provenance.json",
                expected_schema=VERIFIER_PROVENANCE_SCHEMA,
            )
        )
        emitted_paths.append(
            _emit_canonical_artifact_file(
                source_path=runtime_artifact,
                destination_path=canonical_root / "runtime_observability_comparison.json",
                expected_schema=RUNTIME_OBSERVABILITY_SCHEMA,
            )
        )
        emitted_paths.append(
            _emit_canonical_artifact_file(
                source_path=continuity_artifact,
                destination_path=canonical_root / "metric_key_continuity_assertion.json",
                expected_schema=METRIC_KEY_CONTINUITY_SCHEMA,
            )
        )

        emitted_paths.append(
            _emit_mode_bundle_file(mode_root=mode_root, deployment_mode=deployment_mode)
        )

        emitted_files_records: list[dict[str, str]] = []
        for emitted_path in emitted_paths:
            normalized_path = _normalize_repo_relative_path_for_hash(
                root=root,
                absolute_path=emitted_path,
            )
            emitted_files_records.append(
                {
                    "path": normalized_path,
                    "sha256": _hash_file(emitted_path),
                }
            )

        emitted_files_records.sort(key=lambda row: row["path"])

        authority_artifact_hashes = {
            "taskpack_manifest_hash": manifest_hash,
            "verified_result_hash": verified_result_payload["verified_result_hash"],
            "evidence_bundle_hash": evidence_bundle_payload["evidence_bundle_hash"],
            "verifier_provenance_hash": verifier_provenance_payload["provenance_hash"],
            "runtime_observability_comparison_hash": sha256_canonical_json(runtime_payload),
            "metric_key_continuity_assertion_hash": sha256_canonical_json(continuity_payload),
        }

        manifest_path, packaging_bundle_hash = _emit_packaging_manifest(
            mode_root=mode_root,
            deployment_mode=deployment_mode,
            authority_artifact_hashes=authority_artifact_hashes,
            emitted_files_records=emitted_files_records,
        )

        policy_equivalence = _extract_policy_equivalence(
            evidence_slots_payload=evidence_slots_payload,
            evidence_slots_artifact_path=taskpack_path / "EVIDENCE_SLOTS.json",
            verified_result_payload=verified_result_payload,
            evidence_bundle_payload=evidence_bundle_payload,
        )

        parity_result = {
            "schema_typed_artifact_validation_passed": True,
            "policy_equivalence": policy_equivalence,
            "dry_run": dry_run,
        }

        provenance_path, provenance_hash = _emit_packaging_provenance(
            mode_root=mode_root,
            taskpack_manifest_hash=manifest_hash,
            verified_result_hash=verified_result_payload["verified_result_hash"],
            evidence_bundle_hash=evidence_bundle_payload["evidence_bundle_hash"],
            deployment_mode=deployment_mode,
            parity_result=parity_result,
        )

        return TaskpackPackagingResult(
            packaging_manifest_path=manifest_path,
            packaging_bundle_hash=packaging_bundle_hash,
            packaging_provenance_path=provenance_path,
            packaging_provenance_hash=provenance_hash,
            rejection_diagnostic_path=None,
            deployment_mode=deployment_mode,
        )

    except TaskpackPackagingError as exc:
        if not registry_codes:
            registry_codes = {
                AHK4703_ARTIFACT_INVALID,
                AHK4704_CROSS_ARTIFACT_HASH_MISMATCH,
                AHK4705_DEPLOYMENT_MODE_POLICY_VIOLATION,
                AHK4706_MODE_CONTRACT_IDENTITY_MISMATCH,
                AHK4707_PACKAGING_MANIFEST_INVALID,
                AHK4708_CONTRACT_REGISTRY_INVALID,
                AHK4709_PACKAGING_REJECTION_DIAGNOSTIC_INVALID,
                AHK4710_PACKAGING_PROVENANCE_INVALID,
                AHK4711_SUBPROCESS_MODE_POLICY_VIOLATION,
                AHK4712_CANONICAL_SUBJECT_PATH_NORMALIZATION_DRIFT,
                AHK4713_PACKAGING_FAILURE_WITHOUT_REJECTION_DIAGNOSTIC,
            }

        issue = exc.issue or PackagingIssue(
            issue_code=exc.code,
            reason=exc.message,
            artifact_path=exc.details.get("path", "packaging"),
            deployment_mode=deployment_mode,
            policy_source="packaging_manifest",
        )
        issue = PackagingIssue(
            issue_code=issue.issue_code,
            reason=issue.reason,
            artifact_path=_normalize_issue_artifact_path_for_diagnostic(
                root=root,
                artifact_path=issue.artifact_path,
            ),
            deployment_mode=issue.deployment_mode,
            policy_source=issue.policy_source,
        )

        if issue.policy_source not in POLICY_SOURCE_ENUM_V47:
            issue = PackagingIssue(
                issue_code=issue.issue_code,
                reason=issue.reason,
                artifact_path=issue.artifact_path,
                deployment_mode=issue.deployment_mode,
                policy_source="packaging_manifest",
            )

        try:
            rejection_diagnostic_path = emit_rejection_diagnostic(
                root=root,
                output_root_rel=DEFAULT_REJECTIONS_ROOT,
                taskpack_manifest_hash=manifest_hash,
                verified_result_hash=verified_result_hash,
                issues=[issue],
                allowed_codes=registry_codes,
            )
        except TaskpackPackagingError as rejection_exc:
            raise TaskpackPackagingError(
                code=AHK4713_PACKAGING_FAILURE_WITHOUT_REJECTION_DIAGNOSTIC,
                message="packaging failure without rejection diagnostic emission",
                details={"original_error": str(exc), "rejection_error": str(rejection_exc)},
                issue=PackagingIssue(
                    issue_code=AHK4713_PACKAGING_FAILURE_WITHOUT_REJECTION_DIAGNOSTIC,
                    reason="packaging failure without rejection diagnostic emission",
                    artifact_path=exc.details.get("path", "packaging"),
                    deployment_mode=deployment_mode,
                    policy_source="stop_gate_metrics",
                ),
            ) from exc

        details = dict(exc.details)
        details["rejection_diagnostic_path"] = rejection_diagnostic_path.as_posix()
        raise TaskpackPackagingError(
            code=exc.code,
            message=exc.message,
            details=details,
            issue=issue,
        ) from exc


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Emit deterministic v47 packaging surface artifacts for the selected "
            "deployment mode from verified-result/evidence/provenance inputs."
        ),
    )
    parser.add_argument(
        "--deployment-mode",
        required=True,
        help="Deployment mode authority input. Must match mode-specific entrypoint.",
    )
    parser.add_argument(
        "--taskpack-dir",
        required=True,
        help="Repo-relative taskpack directory containing manifest/components.",
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
        "--verified-result",
        required=True,
        help="Repo-relative path to taskpack_verification_result@1 artifact.",
    )
    parser.add_argument(
        "--evidence-bundle",
        required=True,
        help="Repo-relative path to taskpack_closeout_evidence_bundle@1 artifact.",
    )
    parser.add_argument(
        "--verifier-provenance",
        required=True,
        help="Repo-relative path to taskpack_verifier_provenance@1 artifact.",
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
        "--packaging-output-root",
        default=DEFAULT_PACKAGING_ROOT,
        help="Repo-relative output root for v47 packaging artifacts.",
    )
    parser.add_argument(
        "--diagnostic-registry",
        default=DEFAULT_DIAGNOSTIC_REGISTRY_PATH,
        help="Repo-relative path to authoritative v47 diagnostic registry JSON.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Emit deterministic packaging preview artifacts only.",
    )
    parser.add_argument(
        "--repo-root",
        default=None,
        help="Optional repository root override. Defaults to deterministic repo_root(anchor=cwd).",
    )
    return parser.parse_args(argv)


def main_for_mode(*, expected_mode: str, argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        result = package_ux_surface(
            expected_mode=expected_mode,
            deployment_mode=args.deployment_mode,
            taskpack_dir=args.taskpack_dir,
            signature_verification_result_path=args.signature_verification_result,
            signature_envelope_path=args.signature_envelope,
            trust_anchor_registry_path=args.trust_anchor_registry,
            verification_reference_time_utc=args.verification_reference_time_utc,
            verified_result_path=args.verified_result,
            evidence_bundle_path=args.evidence_bundle,
            verifier_provenance_path=args.verifier_provenance,
            runtime_observability_comparison_path=args.runtime_observability_comparison,
            metric_key_continuity_assertion_path=args.metric_key_continuity_assertion,
            packaging_output_root=args.packaging_output_root,
            diagnostic_registry_path=args.diagnostic_registry,
            dry_run=bool(args.dry_run),
            repo_root_path=args.repo_root,
        )
    except TaskpackPackagingError as exc:
        sys.stderr.write(str(exc) + "\n")
        return 1

    payload = {
        "schema": PACKAGING_RESULT_SCHEMA,
        "deployment_mode": result.deployment_mode,
        "packaging_manifest_path": result.packaging_manifest_path.as_posix(),
        "packaging_bundle_hash": result.packaging_bundle_hash,
        "packaging_provenance_path": result.packaging_provenance_path.as_posix(),
        "packaging_provenance_hash": result.packaging_provenance_hash,
        "rejection_diagnostic_path": (
            result.rejection_diagnostic_path.as_posix()
            if result.rejection_diagnostic_path is not None
            else None
        ),
    }
    sys.stdout.write(canonical_json(payload) + "\n")
    return 0
