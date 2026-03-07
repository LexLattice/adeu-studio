from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from adeu_ir.repo import repo_root
from urm_runtime.hashing import canonical_json, sha256_canonical_json

from ._v47_packaging_common import (
    DEFAULT_DIAGNOSTIC_REGISTRY_PATH as PACKAGING_DEFAULT_DIAGNOSTIC_REGISTRY_PATH,
)
from .package_ux import (
    DEPLOYMENT_MODE_STANDALONE,
    PACKAGING_MANIFEST_SCHEMA,
    PACKAGING_PROVENANCE_SCHEMA,
    PACKAGING_RESULT_SCHEMA,
    TaskpackPackagingError,
    TaskpackPackagingResult,
    package_ux_surface,
)

STANDALONE_INTEGRITY_VERIFICATION_RESULT_SCHEMA = (
    "standalone_integrity_verification_result@1"
)
STANDALONE_INTEGRITY_OUTPUT_SCHEMA = "taskpack_standalone_integrity_checker_result@1"
STANDALONE_INTEGRITY_ERROR_SCHEMA = "taskpack_standalone_integrity_error@1"
STANDALONE_INTEGRITY_CONTRACT_SCHEMA = "v34f_standalone_integrity_contract@1"
DIAGNOSTIC_REGISTRY_SCHEMA = "taskpack_standalone_integrity_diagnostic_registry@1"
DEFAULT_DIAGNOSTIC_REGISTRY_PATH = (
    "packages/adeu_agent_harness/src/adeu_agent_harness/diagnostic_registry_v54.json"
)
DEFAULT_INTEGRITY_OUTPUT_ROOT = "artifacts/agent_harness/v54/standalone_integrity"
DEFAULT_PACKAGING_OUTPUT_ROOT = "artifacts/agent_harness/v54/packaging"
SHARED_INTEGRITY_CHECKER = (
    "adeu_agent_harness.standalone_integrity.verify_standalone_integrity"
)
SHARED_INTEGRITY_CHECKER_IDENTIFIER = (
    "v34f_standalone_integrity_checker@1:"
    "adeu_agent_harness.standalone_integrity.verify_standalone_integrity"
)
SHARED_INTEGRITY_CHECKER_IDENTIFIER_POLICY = (
    "frozen_module_function_path_or_registry_key_no_free_text"
)
INTEGRITY_CHECKER_ENTRYPOINT = "python -m adeu_agent_harness.standalone_integrity"
VERIFICATION_PASSED_POLICY = (
    "true_means_integrity_checker_validation_inventory_bundle_hash_guards_and_closeout_"
    "validation_passed_not_installer_success_or_deployment_mode_release"
)
_NULL_SHA256 = "0" * 64
_SHA256_PATTERN = re.compile(r"[0-9a-f]{64}")
_DIAGNOSTIC_PREFIX_PATTERN = re.compile(r"AHK54[0-9]{2}")
_REQUIRED_DETERMINISTIC_ENV = {
    "TZ": "UTC",
    "LC_ALL": "C",
    "PYTHONHASHSEED": "0",
}

AHK5401_INPUT_INVALID = "AHK5401"
AHK5402_SCHEMA_MISMATCH = "AHK5402"
AHK5403_ARTIFACT_INVALID = "AHK5403"
AHK5404_CROSS_ARTIFACT_HASH_MISMATCH = "AHK5404"
AHK5405_DEPLOYMENT_MODE_POLICY_VIOLATION = "AHK5405"
AHK5406_INTEGRITY_POLICY_VIOLATION = "AHK5406"
AHK5407_PACKAGING_MATERIALIZATION_FAILED = "AHK5407"
AHK5408_RESULT_INVALID = "AHK5408"
AHK5409_CONTRACT_REGISTRY_INVALID = "AHK5409"


@dataclass(frozen=True)
class StandaloneIntegrityArtifacts:
    standalone_packaging_result_path: Path | None
    standalone_packaging_manifest_path: Path | None
    standalone_packaging_provenance_path: Path | None
    standalone_packaging_bundle_hash: str | None
    recomputed_manifest_bundle_hash: str | None
    standalone_integrity_verification_result_path: Path
    standalone_integrity_verification_result_hash: str
    verification_passed: bool


class TaskpackStandaloneIntegrityError(RuntimeError):
    def __init__(self, *, code: str, message: str, details: dict[str, Any] | None = None) -> None:
        self.code = code
        self.message = message
        self.details = details or {}
        payload = {
            "schema": STANDALONE_INTEGRITY_ERROR_SCHEMA,
            "code": code,
            "message": message,
            "details": self.details,
        }
        super().__init__(canonical_json(payload))


def _fail(
    *, code: str, message: str, details: dict[str, Any] | None = None
) -> TaskpackStandaloneIntegrityError:
    return TaskpackStandaloneIntegrityError(code=code, message=message, details=details)


def _normalize_relative_path(raw_path: str, *, code: str = AHK5401_INPUT_INVALID) -> str:
    path_text = raw_path.strip().replace("\\", "/")
    if not path_text or path_text.startswith("/"):
        raise _fail(
            code=code,
            message="path must be repo-relative posix",
            details={"path": raw_path},
        )
    raw_segments = path_text.split("/")
    if any(segment == ".." for segment in raw_segments):
        raise _fail(
            code=code,
            message="path must not escape repository root",
            details={"path": raw_path},
        )
    segments = [segment for segment in raw_segments if segment and segment != "."]
    if not segments:
        raise _fail(
            code=code,
            message="path resolves to repository root",
            details={"path": raw_path},
        )
    return "/".join(segments)


def _safe_join(root: Path, rel_path: str, *, code: str = AHK5401_INPUT_INVALID) -> Path:
    normalized = _normalize_relative_path(rel_path, code=code)
    path = (root / normalized).resolve()
    root_resolved = root.resolve()
    try:
        path.relative_to(root_resolved)
    except ValueError as exc:
        raise _fail(
            code=code,
            message="resolved path escapes repository root",
            details={"path": rel_path},
        ) from exc
    return path


def _resolve_repo_path(
    root: Path,
    raw_path: str | Path,
    *,
    code: str = AHK5401_INPUT_INVALID,
) -> Path:
    candidate = Path(raw_path)
    if candidate.is_absolute():
        resolved = candidate.resolve()
        try:
            resolved.relative_to(root.resolve())
        except ValueError as exc:
            raise _fail(
                code=code,
                message="absolute path escapes repository root",
                details={"path": str(raw_path)},
            ) from exc
        return resolved
    return _safe_join(root, str(raw_path), code=code)


def _resolve_output_root(root: Path, raw_path: str | Path) -> Path:
    try:
        return _resolve_repo_path(root, raw_path, code=AHK5401_INPUT_INVALID)
    except TaskpackStandaloneIntegrityError:
        return _safe_join(root, DEFAULT_INTEGRITY_OUTPUT_ROOT, code=AHK5401_INPUT_INVALID)


def _as_repo_relative_posix(root: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError as exc:
        raise _fail(
            code=AHK5401_INPUT_INVALID,
            message="path escapes repository root",
            details={"path": str(path)},
        ) from exc


def _load_json_object(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise _fail(
            code=AHK5401_INPUT_INVALID,
            message="required json path does not exist",
            details={"path": str(path)},
        ) from exc
    except OSError as exc:
        raise _fail(
            code=AHK5401_INPUT_INVALID,
            message="required json path cannot be read",
            details={"path": str(path), "error": str(exc)},
        ) from exc
    except json.JSONDecodeError as exc:
        raise _fail(
            code=AHK5401_INPUT_INVALID,
            message="json payload is invalid",
            details={"path": str(path), "error": str(exc)},
        ) from exc
    if not isinstance(payload, dict):
        raise _fail(
            code=AHK5401_INPUT_INVALID,
            message="json payload must decode to an object",
            details={"path": str(path)},
        )
    return payload


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(canonical_json(payload) + "\n", encoding="utf-8")


def _require_schema(payload: dict[str, Any], *, expected_schema: str, path: Path) -> None:
    observed = payload.get("schema")
    if observed != expected_schema:
        raise _fail(
            code=AHK5402_SCHEMA_MISMATCH,
            message="schema mismatch",
            details={
                "path": str(path),
                "expected_schema": expected_schema,
                "observed_schema": observed,
            },
        )


def _require_sha256(value: Any, *, field: str, code: str = AHK5403_ARTIFACT_INVALID) -> str:
    if not isinstance(value, str) or not _SHA256_PATTERN.fullmatch(value):
        raise _fail(code=code, message=f"{field} must be a sha256 hex string")
    return value


def _require_bool(value: Any, *, field: str, code: str = AHK5403_ARTIFACT_INVALID) -> bool:
    if not isinstance(value, bool):
        raise _fail(code=code, message=f"{field} must be a boolean")
    return value


def _require_string(value: Any, *, field: str, code: str = AHK5403_ARTIFACT_INVALID) -> str:
    if not isinstance(value, str) or not value:
        raise _fail(code=code, message=f"{field} must be a non-empty string")
    return value


def _require_deterministic_env() -> None:
    observed = {key: os.environ.get(key) for key in sorted(_REQUIRED_DETERMINISTIC_ENV)}
    if observed != _REQUIRED_DETERMINISTIC_ENV:
        raise _fail(
            code=AHK5403_ARTIFACT_INVALID,
            message="deterministic environment contract drift detected",
            details={
                "required_deterministic_env": _REQUIRED_DETERMINISTIC_ENV,
                "observed_deterministic_env": observed,
            },
        )


def _load_diagnostic_registry(root: Path, registry_rel_path: str | Path) -> None:
    registry_path = _resolve_repo_path(root, registry_rel_path, code=AHK5401_INPUT_INVALID)
    payload = _load_json_object(registry_path)
    _require_schema(payload, expected_schema=DIAGNOSTIC_REGISTRY_SCHEMA, path=registry_path)
    if set(payload.keys()) != {"schema", "codes"}:
        raise _fail(
            code=AHK5409_CONTRACT_REGISTRY_INVALID,
            message="diagnostic registry keys must match frozen grammar",
            details={"path": str(registry_path), "keys": sorted(payload.keys())},
        )
    codes = payload.get("codes")
    if not isinstance(codes, list) or not codes:
        raise _fail(
            code=AHK5409_CONTRACT_REGISTRY_INVALID,
            message="diagnostic registry codes must be a non-empty array",
            details={"path": str(registry_path)},
        )
    seen: set[str] = set()
    for index, entry in enumerate(codes):
        if not isinstance(entry, dict):
            raise _fail(
                code=AHK5409_CONTRACT_REGISTRY_INVALID,
                message="diagnostic registry entry must be an object",
                details={"path": str(registry_path), "index": index},
            )
        if set(entry.keys()) != {"issue_code", "title", "description"}:
            raise _fail(
                code=AHK5409_CONTRACT_REGISTRY_INVALID,
                message="diagnostic registry entry keys must match frozen grammar",
                details={
                    "path": str(registry_path),
                    "index": index,
                    "keys": sorted(entry.keys()),
                },
            )
        issue_code = _require_string(
            entry.get("issue_code"),
            field="issue_code",
            code=AHK5409_CONTRACT_REGISTRY_INVALID,
        )
        if not _DIAGNOSTIC_PREFIX_PATTERN.fullmatch(issue_code):
            raise _fail(
                code=AHK5409_CONTRACT_REGISTRY_INVALID,
                message="diagnostic registry issue_code must use AHK54xx prefix",
                details={"path": str(registry_path), "issue_code": issue_code},
            )
        if issue_code in seen:
            raise _fail(
                code=AHK5409_CONTRACT_REGISTRY_INVALID,
                message="diagnostic registry contains duplicate issue_code",
                details={"path": str(registry_path), "issue_code": issue_code},
            )
        seen.add(issue_code)


def _default_result_payload() -> dict[str, Any]:
    return {
        "schema": STANDALONE_INTEGRITY_VERIFICATION_RESULT_SCHEMA,
        "contract_schema": STANDALONE_INTEGRITY_CONTRACT_SCHEMA,
        "shared_integrity_checker": SHARED_INTEGRITY_CHECKER,
        "shared_integrity_checker_identifier": SHARED_INTEGRITY_CHECKER_IDENTIFIER,
        "shared_integrity_checker_identifier_policy": (
            SHARED_INTEGRITY_CHECKER_IDENTIFIER_POLICY
        ),
        "integrity_checker_entrypoint": INTEGRITY_CHECKER_ENTRYPOINT,
        "standalone_packaging_result_path": None,
        "standalone_packaging_manifest_path": None,
        "standalone_packaging_provenance_path": None,
        "standalone_packaging_provenance_hash": None,
        "standalone_packaging_bundle_hash": None,
        "recomputed_manifest_bundle_hash": None,
        "deployment_mode": DEPLOYMENT_MODE_STANDALONE,
        "deployment_mode_standalone_only": True,
        "verification_result_semantic_input_forbidden": True,
        "packaging_manifest_schema_validated": False,
        "packaging_manifest_bundle_hash_subject_verified": False,
        "packaging_provenance_binding_verified": False,
        "packaging_provenance_artifact_hash_verified": False,
        "current_packaging_materialization_recomputed": False,
        "current_packaging_materialization_failure_fails_closed": True,
        "bundle_root_input_explicit": False,
        "manifest_paths_bundle_relative": False,
        "manifest_normalized_path_duplicates_forbidden": True,
        "normalized_emitted_path_duplicates_forbidden": True,
        "bundle_root_escape_forbidden": True,
        "symlinks_forbidden": True,
        "regular_files_only": True,
        "actual_emitted_file_hashes_recomputed": False,
        "emitted_file_inventory_exact_match_verified": False,
        "missing_or_extra_bundle_files_fail_closed": True,
        "integrity_result_emitted_on_failure": True,
        "integrity_result_emitted_on_input_validation_failure": True,
        "raw_repo_reads_forbidden": True,
        "auto_fetch_or_unpack_forbidden": True,
        "issues": [],
        "verification_passed": False,
        "verification_passed_policy": VERIFICATION_PASSED_POLICY,
    }


def _emit_result_artifact(
    *,
    root: Path,
    output_root_path: Path,
    manifest_hash: str | None,
    packaging_bundle_hash: str | None,
    payload: dict[str, Any],
) -> tuple[Path, str]:
    manifest_segment = (
        manifest_hash
        if isinstance(manifest_hash, str) and _SHA256_PATTERN.fullmatch(manifest_hash)
        else _NULL_SHA256
    )
    bundle_segment = (
        packaging_bundle_hash
        if isinstance(packaging_bundle_hash, str)
        and _SHA256_PATTERN.fullmatch(packaging_bundle_hash)
        else _NULL_SHA256
    )
    verification_dir = output_root_path / "verification"
    result_path = verification_dir / f"{manifest_segment}_{bundle_segment}.json"
    payload["result_hash"] = sha256_canonical_json(payload)
    _write_json(result_path, payload)
    loaded = _load_json_object(result_path)
    _require_schema(
        loaded,
        expected_schema=STANDALONE_INTEGRITY_VERIFICATION_RESULT_SCHEMA,
        path=result_path,
    )
    if loaded.get("result_hash") != payload["result_hash"]:
        raise _fail(
            code=AHK5408_RESULT_INVALID,
            message="standalone integrity verification result hash drift detected",
            details={"path": str(result_path)},
        )
    return result_path, payload["result_hash"]


def _write_packaging_result_artifact(
    *,
    root: Path,
    packaging_result: TaskpackPackagingResult,
    packaging_output_root: Path,
) -> tuple[Path, dict[str, Any]]:
    path = (
        packaging_output_root
        / f"taskpack_packaging_result_{packaging_result.deployment_mode}.json"
    )
    payload = {
        "schema": PACKAGING_RESULT_SCHEMA,
        "deployment_mode": packaging_result.deployment_mode,
        "packaging_manifest_path": _as_repo_relative_posix(
            root, packaging_result.packaging_manifest_path
        ),
        "packaging_bundle_hash": packaging_result.packaging_bundle_hash,
        "packaging_provenance_path": _as_repo_relative_posix(
            root, packaging_result.packaging_provenance_path
        ),
        "packaging_provenance_hash": packaging_result.packaging_provenance_hash,
        "rejection_diagnostic_path": (
            _as_repo_relative_posix(root, packaging_result.rejection_diagnostic_path)
            if packaging_result.rejection_diagnostic_path is not None
            else None
        ),
    }
    _write_json(path, payload)
    loaded = _load_json_object(path)
    _require_schema(loaded, expected_schema=PACKAGING_RESULT_SCHEMA, path=path)
    return path, loaded


def _validate_packaging_manifest(
    *,
    root: Path,
    bundle_root: Path,
    manifest_path: Path,
) -> tuple[dict[str, Any], list[dict[str, str]], str]:
    manifest_payload = _load_json_object(manifest_path)
    _require_schema(manifest_payload, expected_schema=PACKAGING_MANIFEST_SCHEMA, path=manifest_path)
    if set(manifest_payload.keys()) != {
        "schema",
        "deployment_mode",
        "authority_artifact_hashes",
        "emitted_files",
        "packaging_bundle_hash",
    }:
        raise _fail(
            code=AHK5403_ARTIFACT_INVALID,
            message="packaging manifest keys must match frozen grammar",
            details={"path": str(manifest_path), "keys": sorted(manifest_payload.keys())},
        )
    deployment_mode = _require_string(
        manifest_payload.get("deployment_mode"),
        field="deployment_mode",
        code=AHK5405_DEPLOYMENT_MODE_POLICY_VIOLATION,
    )
    if deployment_mode != DEPLOYMENT_MODE_STANDALONE:
        raise _fail(
            code=AHK5405_DEPLOYMENT_MODE_POLICY_VIOLATION,
            message="packaging manifest deployment_mode must equal standalone",
            details={"path": str(manifest_path), "deployment_mode": deployment_mode},
        )
    authority_artifact_hashes = manifest_payload.get("authority_artifact_hashes")
    if not isinstance(authority_artifact_hashes, dict):
        raise _fail(
            code=AHK5403_ARTIFACT_INVALID,
            message="authority_artifact_hashes must be an object",
            details={"path": str(manifest_path)},
        )
    emitted_files = manifest_payload.get("emitted_files")
    if not isinstance(emitted_files, list) or not emitted_files:
        raise _fail(
            code=AHK5403_ARTIFACT_INVALID,
            message="emitted_files must be a non-empty array",
            details={"path": str(manifest_path)},
        )

    normalized_rows: list[dict[str, str]] = []
    seen_paths: set[str] = set()
    for index, row in enumerate(emitted_files):
        if not isinstance(row, dict) or set(row.keys()) != {"path", "sha256"}:
            raise _fail(
                code=AHK5403_ARTIFACT_INVALID,
                message="manifest emitted_files rows must match frozen grammar",
                details={"path": str(manifest_path), "index": index},
            )
        raw_path = _require_string(
            row.get("path"),
            field="path",
            code=AHK5403_ARTIFACT_INVALID,
        )
        absolute_path = _resolve_repo_path(root, raw_path, code=AHK5401_INPUT_INVALID)
        try:
            normalized_path = absolute_path.relative_to(bundle_root).as_posix()
        except ValueError as exc:
            raise _fail(
                code=AHK5406_INTEGRITY_POLICY_VIOLATION,
                message="manifest path escapes declared bundle root",
                details={"path": raw_path, "bundle_root": str(bundle_root)},
            ) from exc
        normalized_path = _normalize_relative_path(
            normalized_path, code=AHK5406_INTEGRITY_POLICY_VIOLATION
        )
        if normalized_path in seen_paths:
            raise _fail(
                code=AHK5406_INTEGRITY_POLICY_VIOLATION,
                message="duplicate normalized manifest emitted path is forbidden",
                details={"path": raw_path, "normalized_path": normalized_path},
            )
        seen_paths.add(normalized_path)
        if absolute_path.is_symlink():
            raise _fail(
                code=AHK5406_INTEGRITY_POLICY_VIOLATION,
                message="symlink bundle entries are forbidden",
                details={"path": raw_path, "normalized_path": normalized_path},
            )
        if not absolute_path.is_file():
            raise _fail(
                code=AHK5406_INTEGRITY_POLICY_VIOLATION,
                message="manifest emitted entries must reference regular files",
                details={"path": raw_path, "normalized_path": normalized_path},
            )
        normalized_rows.append(
            {
                "path": normalized_path,
                "sha256": _require_sha256(
                    row.get("sha256"),
                    field="sha256",
                    code=AHK5403_ARTIFACT_INVALID,
                ),
            }
        )

    if normalized_rows != sorted(normalized_rows, key=lambda row: row["path"]):
        raise _fail(
            code=AHK5406_INTEGRITY_POLICY_VIOLATION,
            message="manifest emitted rows must be sorted lexicographically by normalized path",
            details={"path": str(manifest_path)},
        )

    declared_bundle_hash = _require_sha256(
        manifest_payload.get("packaging_bundle_hash"),
        field="packaging_bundle_hash",
        code=AHK5403_ARTIFACT_INVALID,
    )
    recomputed_bundle_hash = sha256_canonical_json(emitted_files)
    if recomputed_bundle_hash != declared_bundle_hash:
        raise _fail(
            code=AHK5404_CROSS_ARTIFACT_HASH_MISMATCH,
            message="packaging manifest bundle hash must match frozen emitted_files hash subject",
            details={"path": str(manifest_path)},
        )
    return manifest_payload, normalized_rows, recomputed_bundle_hash


def _normalize_bundle_relative_path(
    *,
    bundle_root: Path,
    artifact_path: Path,
    code: str = AHK5406_INTEGRITY_POLICY_VIOLATION,
) -> str:
    try:
        relative_path = artifact_path.relative_to(bundle_root).as_posix()
    except ValueError as exc:
        raise _fail(
            code=code,
            message="artifact path escapes declared bundle root",
            details={"path": str(artifact_path), "bundle_root": str(bundle_root)},
        ) from exc
    return _normalize_relative_path(relative_path, code=code)


def _build_actual_inventory(*, bundle_root: Path, ignored_paths: set[str]) -> list[dict[str, str]]:
    inventory: list[dict[str, str]] = []
    seen_paths: set[str] = set()
    for dirpath, dirnames, filenames in os.walk(bundle_root, topdown=True, followlinks=False):
        dir_path = Path(dirpath)
        for dirname in list(dirnames):
            child = dir_path / dirname
            if child.is_symlink():
                raise _fail(
                    code=AHK5406_INTEGRITY_POLICY_VIOLATION,
                    message="symlink bundle entries are forbidden",
                    details={"path": str(child)},
                )
        for filename in filenames:
            child = dir_path / filename
            if child.is_symlink():
                raise _fail(
                    code=AHK5406_INTEGRITY_POLICY_VIOLATION,
                    message="symlink bundle entries are forbidden",
                    details={"path": str(child)},
                )
            if not child.is_file():
                raise _fail(
                    code=AHK5406_INTEGRITY_POLICY_VIOLATION,
                    message="bundle inventory must contain regular files only",
                    details={"path": str(child)},
                )
            relative_path = _normalize_relative_path(
                child.relative_to(bundle_root).as_posix(),
                code=AHK5406_INTEGRITY_POLICY_VIOLATION,
            )
            if relative_path in ignored_paths:
                continue
            if relative_path in seen_paths:
                raise _fail(
                    code=AHK5406_INTEGRITY_POLICY_VIOLATION,
                    message="duplicate normalized emitted path is forbidden",
                    details={"path": str(child), "normalized_path": relative_path},
                )
            seen_paths.add(relative_path)
            inventory.append(
                {
                    "path": relative_path,
                    "sha256": hashlib.sha256(child.read_bytes()).hexdigest(),
                }
            )
    inventory.sort(key=lambda row: row["path"])
    return inventory


def _validate_packaging_provenance(
    *,
    manifest_payload: dict[str, Any],
    provenance_path: Path,
) -> tuple[dict[str, Any], str]:
    provenance_payload = _load_json_object(provenance_path)
    _require_schema(
        provenance_payload,
        expected_schema=PACKAGING_PROVENANCE_SCHEMA,
        path=provenance_path,
    )
    if set(provenance_payload.keys()) != {
        "schema",
        "taskpack_manifest_hash",
        "verified_result_hash",
        "evidence_bundle_hash",
        "deployment_mode",
        "parity_result",
        "exit_status",
        "provenance_hash",
    }:
        raise _fail(
            code=AHK5403_ARTIFACT_INVALID,
            message="packaging provenance keys must match frozen grammar",
            details={"path": str(provenance_path), "keys": sorted(provenance_payload.keys())},
        )
    if provenance_payload.get("deployment_mode") != DEPLOYMENT_MODE_STANDALONE:
        raise _fail(
            code=AHK5405_DEPLOYMENT_MODE_POLICY_VIOLATION,
            message="packaging provenance deployment_mode must equal standalone",
            details={"path": str(provenance_path)},
        )
    hash_subject = {
        "taskpack_manifest_hash": _require_sha256(
            provenance_payload.get("taskpack_manifest_hash"),
            field="taskpack_manifest_hash",
        ),
        "verified_result_hash": _require_sha256(
            provenance_payload.get("verified_result_hash"),
            field="verified_result_hash",
        ),
        "evidence_bundle_hash": _require_sha256(
            provenance_payload.get("evidence_bundle_hash"),
            field="evidence_bundle_hash",
        ),
        "deployment_mode": provenance_payload["deployment_mode"],
        "parity_result": provenance_payload.get("parity_result"),
        "exit_status": _require_string(
            provenance_payload.get("exit_status"),
            field="exit_status",
            code=AHK5403_ARTIFACT_INVALID,
        ),
    }
    if hash_subject["exit_status"] != "success":
        raise _fail(
            code=AHK5403_ARTIFACT_INVALID,
            message="packaging provenance exit_status must equal success",
            details={"path": str(provenance_path)},
        )
    if not isinstance(hash_subject["parity_result"], dict):
        raise _fail(
            code=AHK5403_ARTIFACT_INVALID,
            message="packaging provenance parity_result must be an object",
            details={"path": str(provenance_path)},
        )
    declared_hash = _require_sha256(
        provenance_payload.get("provenance_hash"),
        field="provenance_hash",
        code=AHK5403_ARTIFACT_INVALID,
    )
    recomputed_hash = sha256_canonical_json(hash_subject)
    if recomputed_hash != declared_hash:
        raise _fail(
            code=AHK5404_CROSS_ARTIFACT_HASH_MISMATCH,
            message="packaging provenance hash must match frozen subject",
            details={"path": str(provenance_path)},
        )
    authority_hashes = manifest_payload["authority_artifact_hashes"]
    if hash_subject["taskpack_manifest_hash"] != authority_hashes.get("taskpack_manifest_hash"):
        raise _fail(
            code=AHK5404_CROSS_ARTIFACT_HASH_MISMATCH,
            message="packaging provenance taskpack_manifest_hash mismatch",
            details={"path": str(provenance_path)},
        )
    if hash_subject["verified_result_hash"] != authority_hashes.get("verified_result_hash"):
        raise _fail(
            code=AHK5404_CROSS_ARTIFACT_HASH_MISMATCH,
            message="packaging provenance verified_result_hash mismatch",
            details={"path": str(provenance_path)},
        )
    if hash_subject["evidence_bundle_hash"] != authority_hashes.get("evidence_bundle_hash"):
        raise _fail(
            code=AHK5404_CROSS_ARTIFACT_HASH_MISMATCH,
            message="packaging provenance evidence_bundle_hash mismatch",
            details={"path": str(provenance_path)},
        )
    return provenance_payload, sha256_canonical_json(provenance_payload)


def _build_failure_issue(
    *,
    root: Path,
    code: str,
    message: str,
    details: dict[str, Any],
    bundle_root: Path | None,
) -> dict[str, str]:
    artifact_path = details.get("path")
    normalized_artifact_path = "standalone_integrity"
    if isinstance(artifact_path, str) and artifact_path:
        try:
            artifact_candidate = _resolve_repo_path(
                root, artifact_path, code=AHK5401_INPUT_INVALID
            )
            normalized_artifact_path = _as_repo_relative_posix(root, artifact_candidate)
        except TaskpackStandaloneIntegrityError:
            normalized_artifact_path = artifact_path.replace("\\", "/")
    emitted_path = details.get("normalized_path")
    if (
        not isinstance(emitted_path, str)
        and bundle_root is not None
        and isinstance(artifact_path, str)
    ):
        try:
            artifact_candidate = _resolve_repo_path(
                root, artifact_path, code=AHK5401_INPUT_INVALID
            )
            emitted_path = artifact_candidate.relative_to(bundle_root).as_posix()
        except (TaskpackStandaloneIntegrityError, ValueError):
            emitted_path = ""
    if not isinstance(emitted_path, str):
        emitted_path = ""
    return {
        "issue_code": code,
        "artifact_path": normalized_artifact_path,
        "emitted_path": emitted_path,
        "reason": message,
    }


def verify_standalone_integrity(
    *,
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
    bundle_root: str | Path,
    packaging_output_root: str | Path = DEFAULT_PACKAGING_OUTPUT_ROOT,
    integrity_output_root: str | Path = DEFAULT_INTEGRITY_OUTPUT_ROOT,
    diagnostic_registry_path: str | Path = DEFAULT_DIAGNOSTIC_REGISTRY_PATH,
    packaging_diagnostic_registry_path: str | Path = PACKAGING_DEFAULT_DIAGNOSTIC_REGISTRY_PATH,
    dry_run: bool = True,
    repo_root_path: str | Path | None = None,
) -> StandaloneIntegrityArtifacts:
    root = repo_root(anchor=repo_root_path)
    integrity_output_root_path = _resolve_output_root(root, integrity_output_root)
    payload = _default_result_payload()
    manifest_hash: str | None = None
    packaging_bundle_hash: str | None = None
    bundle_root_path: Path | None = None
    packaging_result_path: Path | None = None
    packaging_manifest_path: Path | None = None
    packaging_provenance_path: Path | None = None

    try:
        _require_deterministic_env()
        _load_diagnostic_registry(root, diagnostic_registry_path)

        bundle_root_path = _resolve_repo_path(root, bundle_root, code=AHK5401_INPUT_INVALID)
        payload["bundle_root_input_explicit"] = True

        packaging_output_root_path = _resolve_repo_path(
            root, packaging_output_root, code=AHK5401_INPUT_INVALID
        )
        expected_bundle_root = packaging_output_root_path / DEPLOYMENT_MODE_STANDALONE
        if bundle_root_path != expected_bundle_root.resolve():
            raise _fail(
                code=AHK5406_INTEGRITY_POLICY_VIOLATION,
                message="bundle_root must exactly match packaging_output_root/standalone",
                details={
                    "path": str(bundle_root_path),
                    "expected_bundle_root": str(expected_bundle_root),
                },
            )

        packaging_result = package_ux_surface(
            expected_mode=DEPLOYMENT_MODE_STANDALONE,
            deployment_mode=DEPLOYMENT_MODE_STANDALONE,
            taskpack_dir=taskpack_dir,
            signature_verification_result_path=signature_verification_result_path,
            signature_envelope_path=signature_envelope_path,
            trust_anchor_registry_path=trust_anchor_registry_path,
            verification_reference_time_utc=verification_reference_time_utc,
            verified_result_path=verified_result_path,
            evidence_bundle_path=evidence_bundle_path,
            verifier_provenance_path=verifier_provenance_path,
            runtime_observability_comparison_path=runtime_observability_comparison_path,
            metric_key_continuity_assertion_path=metric_key_continuity_assertion_path,
            packaging_output_root=packaging_output_root,
            diagnostic_registry_path=packaging_diagnostic_registry_path,
            dry_run=bool(dry_run),
            repo_root_path=root,
        )
        payload["current_packaging_materialization_recomputed"] = True

        if packaging_result.deployment_mode != DEPLOYMENT_MODE_STANDALONE:
            raise _fail(
                code=AHK5405_DEPLOYMENT_MODE_POLICY_VIOLATION,
                message="materialized packaging deployment_mode must equal standalone",
                details={"deployment_mode": packaging_result.deployment_mode},
            )

        if packaging_result.rejection_diagnostic_path is not None:
            raise _fail(
                code=AHK5406_INTEGRITY_POLICY_VIOLATION,
                message=(
                    "standalone integrity checker requires successful standalone "
                    "packaging materialization"
                ),
                details={"path": str(packaging_result.rejection_diagnostic_path)},
            )

        packaging_result_path, packaging_result_payload = _write_packaging_result_artifact(
            root=root,
            packaging_result=packaging_result,
            packaging_output_root=packaging_output_root_path,
        )
        packaging_manifest_path = packaging_result.packaging_manifest_path
        packaging_provenance_path = packaging_result.packaging_provenance_path
        payload["standalone_packaging_result_path"] = _as_repo_relative_posix(
            root, packaging_result_path
        )
        payload["standalone_packaging_manifest_path"] = _as_repo_relative_posix(
            root, packaging_manifest_path
        )
        payload["standalone_packaging_provenance_path"] = _as_repo_relative_posix(
            root, packaging_provenance_path
        )
        payload["standalone_packaging_bundle_hash"] = packaging_result.packaging_bundle_hash
        packaging_bundle_hash = packaging_result.packaging_bundle_hash

        if (
            packaging_result_payload["packaging_manifest_path"]
            != payload["standalone_packaging_manifest_path"]
        ):
            raise _fail(
                code=AHK5404_CROSS_ARTIFACT_HASH_MISMATCH,
                message="packaging result manifest path must match materialized manifest path",
                details={"path": str(packaging_result_path)},
            )
        if (
            packaging_result_payload["packaging_provenance_path"]
            != payload["standalone_packaging_provenance_path"]
        ):
            raise _fail(
                code=AHK5404_CROSS_ARTIFACT_HASH_MISMATCH,
                message="packaging result provenance path must match materialized provenance path",
                details={"path": str(packaging_result_path)},
            )
        if (
            packaging_result_payload["packaging_bundle_hash"]
            != packaging_result.packaging_bundle_hash
        ):
            raise _fail(
                code=AHK5404_CROSS_ARTIFACT_HASH_MISMATCH,
                message="packaging result bundle hash must match materialized bundle hash",
                details={"path": str(packaging_result_path)},
            )

        manifest_payload, manifest_normalized_rows, recomputed_manifest_bundle_hash = (
            _validate_packaging_manifest(
                root=root,
                bundle_root=bundle_root_path,
                manifest_path=packaging_manifest_path,
            )
        )
        payload["packaging_manifest_schema_validated"] = True
        payload["manifest_paths_bundle_relative"] = True
        payload["recomputed_manifest_bundle_hash"] = recomputed_manifest_bundle_hash
        manifest_hash = manifest_payload["authority_artifact_hashes"].get("taskpack_manifest_hash")
        if not isinstance(manifest_hash, str) or not _SHA256_PATTERN.fullmatch(manifest_hash):
            raise _fail(
                code=AHK5403_ARTIFACT_INVALID,
                message="packaging manifest taskpack_manifest_hash must be a sha256 hex string",
                details={"path": str(packaging_manifest_path)},
            )
        if packaging_result.packaging_bundle_hash != manifest_payload["packaging_bundle_hash"]:
            raise _fail(
                code=AHK5404_CROSS_ARTIFACT_HASH_MISMATCH,
                message="packaging result bundle hash must match manifest bundle hash",
                details={"path": str(packaging_result_path)},
            )
        payload["packaging_manifest_bundle_hash_subject_verified"] = True

        provenance_payload, provenance_artifact_hash = _validate_packaging_provenance(
            manifest_payload=manifest_payload,
            provenance_path=packaging_provenance_path,
        )
        if (
            packaging_result_payload["packaging_provenance_hash"]
            != provenance_payload["provenance_hash"]
        ):
            raise _fail(
                code=AHK5404_CROSS_ARTIFACT_HASH_MISMATCH,
                message="packaging result provenance hash must match provenance payload hash",
                details={"path": str(packaging_result_path)},
            )
        payload["standalone_packaging_provenance_hash"] = provenance_artifact_hash
        payload["packaging_provenance_binding_verified"] = True
        payload["packaging_provenance_artifact_hash_verified"] = True

        ignored_paths = {
            _normalize_bundle_relative_path(
                bundle_root=bundle_root_path,
                artifact_path=packaging_manifest_path,
            ),
            _normalize_bundle_relative_path(
                bundle_root=bundle_root_path,
                artifact_path=packaging_provenance_path,
            ),
        }
        actual_inventory = _build_actual_inventory(
            bundle_root=bundle_root_path,
            ignored_paths=ignored_paths,
        )
        payload["actual_emitted_file_hashes_recomputed"] = True
        if actual_inventory != manifest_normalized_rows:
            raise _fail(
                code=AHK5406_INTEGRITY_POLICY_VIOLATION,
                message="actual emitted-file inventory must exactly match normalized manifest rows",
                details={"path": str(bundle_root_path)},
            )
        payload["emitted_file_inventory_exact_match_verified"] = True

        payload["verification_passed"] = True
    except TaskpackPackagingError as exc:
        failure = _fail(
            code=AHK5407_PACKAGING_MATERIALIZATION_FAILED,
            message=(
                "current standalone packaging output could not be materialized "
                "in current v54 flow"
            ),
            details={
                "packaging_error_code": exc.code,
                "packaging_error": exc.message,
                "path": str(bundle_root),
            },
        )
        issue = _build_failure_issue(
            root=root,
            code=failure.code,
            message=failure.message,
            details=failure.details,
            bundle_root=bundle_root_path,
        )
        payload["issues"] = [issue]
        result_path, result_hash = _emit_result_artifact(
            root=root,
            output_root_path=integrity_output_root_path,
            manifest_hash=manifest_hash,
            packaging_bundle_hash=packaging_bundle_hash,
            payload=payload,
        )
        failure.details["standalone_integrity_verification_result_path"] = _as_repo_relative_posix(
            root, result_path
        )
        failure.details["standalone_integrity_verification_result_hash"] = result_hash
        raise _fail(
            code=failure.code,
            message=failure.message,
            details=failure.details,
        ) from exc
    except TaskpackStandaloneIntegrityError as exc:
        issue = _build_failure_issue(
            root=root,
            code=exc.code,
            message=exc.message,
            details=exc.details,
            bundle_root=bundle_root_path,
        )
        payload["issues"] = [issue]
        result_path, result_hash = _emit_result_artifact(
            root=root,
            output_root_path=integrity_output_root_path,
            manifest_hash=manifest_hash,
            packaging_bundle_hash=packaging_bundle_hash,
            payload=payload,
        )
        exc.details["standalone_integrity_verification_result_path"] = _as_repo_relative_posix(
            root, result_path
        )
        exc.details["standalone_integrity_verification_result_hash"] = result_hash
        raise _fail(code=exc.code, message=exc.message, details=exc.details) from exc

    result_path, result_hash = _emit_result_artifact(
        root=root,
        output_root_path=integrity_output_root_path,
        manifest_hash=manifest_hash,
        packaging_bundle_hash=packaging_bundle_hash,
        payload=payload,
    )
    return StandaloneIntegrityArtifacts(
        standalone_packaging_result_path=packaging_result_path,
        standalone_packaging_manifest_path=packaging_manifest_path,
        standalone_packaging_provenance_path=packaging_provenance_path,
        standalone_packaging_bundle_hash=packaging_bundle_hash,
        recomputed_manifest_bundle_hash=payload["recomputed_manifest_bundle_hash"],
        standalone_integrity_verification_result_path=result_path,
        standalone_integrity_verification_result_hash=result_hash,
        verification_passed=True,
    )


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Materialize current standalone packaging output and verify deterministic v54 "
            "bundle integrity against the packaging manifest and provenance."
        ),
    )
    parser.add_argument("--taskpack-dir", required=True, help="Repo-relative taskpack directory.")
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
        help="Explicit RFC3339 UTC Z reference time used for reused signing checks.",
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
        "--bundle-root",
        required=True,
        help=(
            "Explicit repo-relative standalone bundle root input. Must equal "
            "packaging_output_root/standalone."
        ),
    )
    parser.add_argument(
        "--packaging-output-root",
        default=DEFAULT_PACKAGING_OUTPUT_ROOT,
        help="Repo-relative output root for current-flow standalone packaging materialization.",
    )
    parser.add_argument(
        "--integrity-output-root",
        default=DEFAULT_INTEGRITY_OUTPUT_ROOT,
        help="Repo-relative output root for standalone_integrity_verification_result@1 artifacts.",
    )
    parser.add_argument(
        "--diagnostic-registry",
        default=DEFAULT_DIAGNOSTIC_REGISTRY_PATH,
        help="Repo-relative path to authoritative v54 diagnostic registry JSON.",
    )
    parser.add_argument(
        "--packaging-diagnostic-registry",
        default=PACKAGING_DEFAULT_DIAGNOSTIC_REGISTRY_PATH,
        help="Repo-relative path to authoritative v47 packaging diagnostic registry JSON.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Materialize deterministic standalone packaging preview artifacts only.",
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
        result = verify_standalone_integrity(
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
            bundle_root=args.bundle_root,
            packaging_output_root=args.packaging_output_root,
            integrity_output_root=args.integrity_output_root,
            diagnostic_registry_path=args.diagnostic_registry,
            packaging_diagnostic_registry_path=args.packaging_diagnostic_registry,
            dry_run=bool(args.dry_run),
            repo_root_path=args.repo_root,
        )
    except TaskpackStandaloneIntegrityError as exc:
        sys.stderr.write(str(exc) + "\n")
        return 1

    payload = {
        "schema": STANDALONE_INTEGRITY_OUTPUT_SCHEMA,
        "standalone_packaging_result_path": (
            result.standalone_packaging_result_path.as_posix()
            if result.standalone_packaging_result_path is not None
            else None
        ),
        "standalone_packaging_manifest_path": (
            result.standalone_packaging_manifest_path.as_posix()
            if result.standalone_packaging_manifest_path is not None
            else None
        ),
        "standalone_packaging_provenance_path": (
            result.standalone_packaging_provenance_path.as_posix()
            if result.standalone_packaging_provenance_path is not None
            else None
        ),
        "standalone_packaging_bundle_hash": result.standalone_packaging_bundle_hash,
        "recomputed_manifest_bundle_hash": result.recomputed_manifest_bundle_hash,
        "standalone_integrity_verification_result_path": (
            result.standalone_integrity_verification_result_path.as_posix()
        ),
        "standalone_integrity_verification_result_hash": (
            result.standalone_integrity_verification_result_hash
        ),
        "verification_passed": result.verification_passed,
    }
    sys.stdout.write(canonical_json(payload) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
