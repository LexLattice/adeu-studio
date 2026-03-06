from __future__ import annotations

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any

from adeu_ir.repo import repo_root
from urm_runtime.hashing import canonical_json, sha256_canonical_json

from .package_ux import (
    DEPLOYMENT_MODE_INTEGRATED,
    DEPLOYMENT_MODE_STANDALONE,
    PACKAGING_MANIFEST_SCHEMA,
    PACKAGING_PROVENANCE_SCHEMA,
    PACKAGING_RESULT_SCHEMA,
)
from .run_taskpack import (
    RUNNER_ADAPTER_REGISTRY_SCHEMA,
    RUNNER_PROVENANCE_SCHEMA,
    TaskpackRunnerError,
    _load_adapter_registry,
)

ADAPTER_MATRIX_SCHEMA = "adapter_matrix@1"
ADAPTER_MATRIX_EVALUATION_INPUTS_SCHEMA = "adapter_matrix_evaluation_inputs@1"
ADAPTER_MATRIX_PARITY_REPORT_SCHEMA = "adapter_matrix_parity_report@1"
ADAPTER_MATRIX_BUILD_RESULT_SCHEMA = "adapter_matrix_build_result@1"
ADAPTER_MATRIX_REPORT_RESULT_SCHEMA = "adapter_matrix_parity_report_result@1"

DEFAULT_MATRIX_REGISTRY_PATH = "artifacts/agent_harness/v50/matrix/adapter_matrix.json"
DEFAULT_MATRIX_REPORT_PATH = "artifacts/agent_harness/v50/matrix/adapter_matrix_parity_report.json"
DEFAULT_DIAGNOSTIC_REGISTRY_PATH = (
    "packages/adeu_agent_harness/src/adeu_agent_harness/diagnostic_registry_v50.json"
)

LANE_ID_TUPLE = (
    "deployment_mode",
    "adapter_id",
    "runtime_id",
)
DEPLOYMENT_MODES = (
    DEPLOYMENT_MODE_INTEGRATED,
    DEPLOYMENT_MODE_STANDALONE,
)
ENABLED_ROW_POLICY = "registry_is_enabled_only_disabled_rows_forbidden_non_v50"
TUPLE_ORDER_POLICY = "lexicographic_over_deployment_mode_adapter_id_runtime_id"
ADAPTER_ID_SOURCE_POLICY = "must_reference_declared_runner_adapter_registry_ids_only"
ADAPTER_KIND_POLICY = "candidate_plan_passthrough_only_non_v50_expansion_forbidden"
RUNTIME_ID_POLICY = "singleton_only_for_v50"
SINGLETON_RUNTIME_ID = "local_python_cli"
RUNTIME_ID_SOURCE_POLICY = "contract_derived_only_no_host_environment_inference"
RUNTIME_ID_OVERRIDE_POLICY = (
    "explicit_override_must_equal_singleton_case_sensitive_before_adapter_execution_"
    "else_fail_closed"
)
LANE_PAIRING_POLICY = (
    "for_each_declared_adapter_id_exactly_two_deployment_mode_rows_required_under_"
    "singleton_runtime_id"
)
LANE_COUNT_AUTHORITY = "all_registry_rows_only_because_disabled_rows_are_forbidden"
POLICY_EQUIVALENCE_VALUE_SHAPES = {
    "issue_code_set": "lexicographically_sorted_unique_string_list_canonical_form",
    "required_evidence_slots_filled": "boolean",
    "allowlist_violations": "lexicographically_sorted_unique_normalized_posix_path_list",
    "forbidden_effects_detected": "boolean",
}
CANONICAL_SUBTREE_SOURCE_POLICY = (
    "existing_frozen_packaging_and_verifier_canonical_artifact_subject_family_only"
)
POLICY_EQUIVALENCE_SOURCE_POLICY = (
    "typed_artifacts_and_deterministic_matrix_report_only_no_logs_repo_state_or_ad_hoc_reanalysis"
)
MATRIX_REPORT_COMPLETENESS_POLICY = "every_declared_lane_must_appear_exactly_once"
_REQUIRED_DETERMINISTIC_ENV = {
    "TZ": "UTC",
    "LC_ALL": "C",
    "PYTHONHASHSEED": "0",
}
_SHA256_PATTERN = re.compile(r"[0-9a-f]{64}")

AHK5000_PATH_POLICY_VIOLATION = "AHK5000"
AHK5001_JSON_OBJECT_REQUIRED = "AHK5001"
AHK5002_SCHEMA_MISMATCH = "AHK5002"
AHK5003_MATRIX_REGISTRY_INVALID = "AHK5003"
AHK5004_MATRIX_INPUT_INVALID = "AHK5004"
AHK5005_MATRIX_REPORT_INVALID = "AHK5005"
AHK5006_CROSS_ARTIFACT_HASH_MISMATCH = "AHK5006"
AHK5007_MATRIX_LANE_COMPLETENESS_VIOLATION = "AHK5007"
AHK5008_CONTRACT_REGISTRY_INVALID = "AHK5008"

_DIAGNOSTIC_PREFIX_PATTERN = re.compile(r"AHK50[0-9]{2}")

_ADAPTER_MATRIX_KEYS = {
    "schema",
    "lane_id_tuple",
    "declared_registry_only",
    "enabled_row_policy",
    "tuple_order_policy",
    "deployment_mode_enum",
    "adapter_id_source_policy",
    "adapter_kind_policy",
    "runtime_id_policy",
    "singleton_runtime_id",
    "runtime_id_source_policy",
    "runtime_id_override_policy",
    "lane_pairing_policy",
    "lane_count_authority",
    "source_runner_adapter_registry_path",
    "source_runner_adapter_registry_hash",
    "rows",
    "matrix_registry_hash",
}
_ADAPTER_MATRIX_ROW_KEYS = {
    "deployment_mode",
    "adapter_id",
    "runtime_id",
    "adapter_kind",
}
_EVALUATION_INPUT_KEYS = {
    "schema",
    "matrix_registry_path",
    "lane_inputs",
}
_EVALUATION_LANE_KEYS = {
    "deployment_mode",
    "adapter_id",
    "runtime_id",
    "runner_provenance_path",
    "packaging_result_path",
}
_PACKAGING_RESULT_KEYS = {
    "schema",
    "deployment_mode",
    "packaging_manifest_path",
    "packaging_bundle_hash",
    "packaging_provenance_path",
    "packaging_provenance_hash",
    "rejection_diagnostic_path",
}
_PACKAGING_MANIFEST_KEYS = {
    "schema",
    "deployment_mode",
    "authority_artifact_hashes",
    "emitted_files",
    "packaging_bundle_hash",
}
_PACKAGING_PROVENANCE_KEYS = {
    "schema",
    "taskpack_manifest_hash",
    "verified_result_hash",
    "evidence_bundle_hash",
    "deployment_mode",
    "parity_result",
    "exit_status",
    "provenance_hash",
}
_PARITY_RESULT_KEYS = {
    "schema_typed_artifact_validation_passed",
    "policy_equivalence",
    "dry_run",
}
_POLICY_EQUIVALENCE_KEYS = set(POLICY_EQUIVALENCE_VALUE_SHAPES)
_RUNNER_PROVENANCE_KEYS = {
    "schema",
    "taskpack_manifest_hash",
    "adapter_id",
    "candidate_change_plan_hash",
    "policy_validation_result",
    "exit_status",
    "provenance_hash",
}
_REPORT_KEYS = {
    "schema",
    "matrix_registry_path",
    "matrix_registry_hash",
    "lane_id_tuple",
    "enabled_row_policy",
    "declared_registry_only",
    "lexicographic_lane_order_enforced",
    "runtime_id_source_policy",
    "runtime_id_host_inference_forbidden",
    "canonical_subtree_exact_match_required",
    "canonical_subtree_source_policy",
    "policy_equivalence_exact_match_required",
    "policy_equivalence_subject_keys_verified",
    "policy_equivalence_value_shapes_verified",
    "report_covers_all_declared_lanes",
    "lane_rows",
    "pairwise_parity",
    "report_hash",
}
_REPORT_LANE_ROW_KEYS = {
    "deployment_mode",
    "adapter_id",
    "runtime_id",
    "taskpack_manifest_hash",
    "candidate_change_plan_hash",
    "runner_provenance_hash",
    "packaging_manifest_path",
    "packaging_provenance_path",
    "canonical_subtree_hash",
    "policy_equivalence_hash",
}
_REPORT_PAIR_KEYS = {
    "adapter_id",
    "runtime_id",
    "deployment_modes",
    "taskpack_manifest_hash",
    "candidate_change_plan_hash",
    "canonical_subtree_exact_match",
    "policy_equivalence_exact_match",
}


@dataclass(frozen=True, order=True)
class MatrixLane:
    deployment_mode: str
    adapter_id: str
    runtime_id: str

    def as_payload(self) -> dict[str, str]:
        return {
            "deployment_mode": self.deployment_mode,
            "adapter_id": self.adapter_id,
            "runtime_id": self.runtime_id,
        }


@dataclass(frozen=True)
class AdapterMatrixResult:
    matrix_registry_path: Path
    matrix_registry_hash: str


@dataclass(frozen=True)
class AdapterMatrixParityReportResult:
    matrix_report_path: Path
    matrix_report_hash: str


class TaskpackMatrixError(RuntimeError):
    def __init__(self, *, code: str, message: str, details: dict[str, Any] | None = None) -> None:
        self.code = code
        self.message = message
        self.details = details or {}
        payload = {
            "schema": "taskpack_matrix_error@1",
            "code": code,
            "message": message,
            "details": self.details,
        }
        super().__init__(canonical_json(payload))


def _fail(*, code: str, message: str, details: dict[str, Any] | None = None) -> TaskpackMatrixError:
    return TaskpackMatrixError(code=code, message=message, details=details)


def _require_deterministic_env() -> None:
    observed = {
        key: os.environ.get(key)
        for key in _REQUIRED_DETERMINISTIC_ENV
        if os.environ.get(key) != _REQUIRED_DETERMINISTIC_ENV[key]
    }
    if observed:
        raise _fail(
            code=AHK5005_MATRIX_REPORT_INVALID,
            message="deterministic environment drift detected",
            details={
                "required_deterministic_env": _REQUIRED_DETERMINISTIC_ENV,
                "observed_drift": observed,
            },
        )


def _normalize_relative_path(raw_path: str) -> str:
    path_text = raw_path.strip().replace("\\", "/")
    if not path_text:
        raise _fail(
            code=AHK5000_PATH_POLICY_VIOLATION,
            message="path must not be empty",
            details={"path": raw_path},
        )
    if path_text.startswith("/"):
        raise _fail(
            code=AHK5000_PATH_POLICY_VIOLATION,
            message="absolute paths are forbidden",
            details={"path": raw_path},
        )
    if re.match(r"^[A-Za-z]:[\\/]", path_text):
        raise _fail(
            code=AHK5000_PATH_POLICY_VIOLATION,
            message="windows absolute paths are forbidden",
            details={"path": raw_path},
        )

    segments: list[str] = []
    for segment in path_text.split("/"):
        if segment in ("", "."):
            continue
        if segment == "..":
            if not segments:
                raise _fail(
                    code=AHK5000_PATH_POLICY_VIOLATION,
                    message="path escapes repository root",
                    details={"path": raw_path},
                )
            segments.pop()
            continue
        segments.append(segment)

    if not segments:
        raise _fail(
            code=AHK5000_PATH_POLICY_VIOLATION,
            message="path resolves to repository root",
            details={"path": raw_path},
        )
    return "/".join(segments)


def _project_repo_root(repo_root_path: str | Path | None) -> Path:
    if repo_root_path is None:
        return repo_root(anchor=Path(__file__))
    root = Path(repo_root_path).resolve()
    if not root.exists():
        raise _fail(
            code=AHK5000_PATH_POLICY_VIOLATION,
            message="repo root does not exist",
            details={"repo_root_path": str(repo_root_path)},
        )
    return root


def _coerce_artifact_path(root: Path, raw_path: str | Path) -> Path:
    if not isinstance(raw_path, (str, Path)):
        raise _fail(
            code=AHK5000_PATH_POLICY_VIOLATION,
            message="artifact path must be string or path",
            details={"path": raw_path},
        )
    candidate = Path(raw_path)
    if candidate.is_absolute():
        resolved = candidate.resolve()
        try:
            resolved.relative_to(root.resolve())
        except ValueError as exc:
            raise _fail(
                code=AHK5000_PATH_POLICY_VIOLATION,
                message="absolute artifact path escapes repository root",
                details={"path": str(raw_path)},
            ) from exc
        return resolved
    normalized = _normalize_relative_path(str(raw_path))
    resolved = (root / normalized).resolve()
    try:
        resolved.relative_to(root.resolve())
    except ValueError as exc:
        raise _fail(
            code=AHK5000_PATH_POLICY_VIOLATION,
            message="resolved artifact path escapes repository root",
            details={"path": str(raw_path)},
        ) from exc
    return resolved


def _as_repo_relative_posix(root: Path, path: Path) -> str:
    resolved = path.resolve()
    try:
        return resolved.relative_to(root.resolve()).as_posix()
    except ValueError as exc:
        raise _fail(
            code=AHK5000_PATH_POLICY_VIOLATION,
            message="artifact path escapes repository root",
            details={"path": str(path)},
        ) from exc


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(canonical_json(payload) + "\n", encoding="utf-8")


def _load_json_object(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise _fail(
            code=AHK5000_PATH_POLICY_VIOLATION,
            message="required json path does not exist",
            details={"path": str(path)},
        ) from exc
    except json.JSONDecodeError as exc:
        raise _fail(
            code=AHK5001_JSON_OBJECT_REQUIRED,
            message="json payload is invalid",
            details={"path": str(path), "error": str(exc)},
        ) from exc
    if not isinstance(payload, dict):
        raise _fail(
            code=AHK5001_JSON_OBJECT_REQUIRED,
            message="json payload must decode to an object",
            details={"path": str(path)},
        )
    return payload


def _require_schema(payload: dict[str, Any], *, expected_schema: str, path: Path) -> None:
    observed = payload.get("schema")
    if observed != expected_schema:
        raise _fail(
            code=AHK5002_SCHEMA_MISMATCH,
            message="schema mismatch",
            details={
                "path": str(path),
                "expected_schema": expected_schema,
                "observed_schema": observed,
            },
        )


def _require_string(value: Any, *, field: str, code: str) -> str:
    if not isinstance(value, str) or not value:
        raise _fail(code=code, message=f"{field} must be a non-empty string")
    return value


def _require_sha256(value: Any, *, field: str, code: str) -> str:
    if not isinstance(value, str) or not _SHA256_PATTERN.fullmatch(value):
        raise _fail(code=code, message=f"{field} must be a sha256 hex string")
    return value


def _load_diagnostic_registry(root: Path, registry_rel_path: str | Path) -> None:
    registry_path = _coerce_artifact_path(root, registry_rel_path)
    payload = _load_json_object(registry_path)
    _require_schema(
        payload, expected_schema="taskpack_matrix_diagnostic_registry@1", path=registry_path
    )
    if set(payload.keys()) != {"schema", "codes"}:
        raise _fail(
            code=AHK5008_CONTRACT_REGISTRY_INVALID,
            message="matrix diagnostic registry keys must match frozen grammar",
            details={"path": str(registry_path), "keys": sorted(payload.keys())},
        )
    codes = payload.get("codes")
    if not isinstance(codes, list) or not codes:
        raise _fail(
            code=AHK5008_CONTRACT_REGISTRY_INVALID,
            message="matrix diagnostic registry codes must be a non-empty array",
            details={"path": str(registry_path)},
        )
    seen: set[str] = set()
    for index, entry in enumerate(codes):
        if not isinstance(entry, dict):
            raise _fail(
                code=AHK5008_CONTRACT_REGISTRY_INVALID,
                message="matrix diagnostic registry entry must be an object",
                details={"path": str(registry_path), "index": index},
            )
        if set(entry.keys()) != {"issue_code", "title", "description"}:
            raise _fail(
                code=AHK5008_CONTRACT_REGISTRY_INVALID,
                message="matrix diagnostic registry entry keys must match frozen grammar",
                details={
                    "path": str(registry_path),
                    "index": index,
                    "keys": sorted(entry.keys()),
                },
            )
        issue_code = _require_string(
            entry.get("issue_code"),
            field="issue_code",
            code=AHK5008_CONTRACT_REGISTRY_INVALID,
        )
        if not _DIAGNOSTIC_PREFIX_PATTERN.fullmatch(issue_code):
            raise _fail(
                code=AHK5008_CONTRACT_REGISTRY_INVALID,
                message="matrix diagnostic registry issue_code must use AHK50xx prefix",
                details={"path": str(registry_path), "issue_code": issue_code},
            )
        if issue_code in seen:
            raise _fail(
                code=AHK5008_CONTRACT_REGISTRY_INVALID,
                message="matrix diagnostic registry contains duplicate issue_code",
                details={"path": str(registry_path), "issue_code": issue_code},
            )
        seen.add(issue_code)


def _load_runner_adapter_registry(
    root: Path, adapter_registry_path: str | Path
) -> tuple[list[dict[str, str]], str, str]:
    path = _coerce_artifact_path(root, adapter_registry_path)
    payload = _load_json_object(path)
    _require_schema(payload, expected_schema=RUNNER_ADAPTER_REGISTRY_SCHEMA, path=path)
    try:
        rows = _load_adapter_registry(path)
    except TaskpackRunnerError as exc:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="runner adapter registry is invalid for matrix projection",
            details={
                "path": str(path),
                "runner_error_code": exc.code,
                "runner_error": exc.message,
            },
        ) from exc
    return rows, _as_repo_relative_posix(root, path), sha256_canonical_json(payload)


def _compute_matrix_registry_hash_subject(
    *,
    source_path: str,
    source_hash: str,
    rows: list[dict[str, str]],
) -> dict[str, Any]:
    return {
        "lane_id_tuple": list(LANE_ID_TUPLE),
        "declared_registry_only": True,
        "enabled_row_policy": ENABLED_ROW_POLICY,
        "tuple_order_policy": TUPLE_ORDER_POLICY,
        "deployment_mode_enum": list(DEPLOYMENT_MODES),
        "adapter_id_source_policy": ADAPTER_ID_SOURCE_POLICY,
        "adapter_kind_policy": ADAPTER_KIND_POLICY,
        "runtime_id_policy": RUNTIME_ID_POLICY,
        "singleton_runtime_id": SINGLETON_RUNTIME_ID,
        "runtime_id_source_policy": RUNTIME_ID_SOURCE_POLICY,
        "runtime_id_override_policy": RUNTIME_ID_OVERRIDE_POLICY,
        "lane_pairing_policy": LANE_PAIRING_POLICY,
        "lane_count_authority": LANE_COUNT_AUTHORITY,
        "source_runner_adapter_registry_path": source_path,
        "source_runner_adapter_registry_hash": source_hash,
        "rows": rows,
    }


def _load_adapter_matrix(root: Path, path: Path) -> dict[str, Any]:
    payload = _load_json_object(path)
    _require_schema(payload, expected_schema=ADAPTER_MATRIX_SCHEMA, path=path)
    if set(payload.keys()) != _ADAPTER_MATRIX_KEYS:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
        )
    if tuple(payload.get("lane_id_tuple")) != LANE_ID_TUPLE:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix lane_id_tuple must match frozen tuple order",
            details={"path": str(path), "lane_id_tuple": payload.get("lane_id_tuple")},
        )
    if payload.get("declared_registry_only") is not True:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix declared_registry_only must be true",
            details={"path": str(path)},
        )
    if payload.get("enabled_row_policy") != ENABLED_ROW_POLICY:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix enabled_row_policy must match frozen value",
            details={"path": str(path)},
        )
    if payload.get("tuple_order_policy") != TUPLE_ORDER_POLICY:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix tuple_order_policy must match frozen value",
            details={"path": str(path)},
        )
    if payload.get("deployment_mode_enum") != list(DEPLOYMENT_MODES):
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix deployment_mode_enum must match frozen value",
            details={"path": str(path)},
        )
    if payload.get("adapter_id_source_policy") != ADAPTER_ID_SOURCE_POLICY:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix adapter_id_source_policy must match frozen value",
            details={"path": str(path)},
        )
    if payload.get("adapter_kind_policy") != ADAPTER_KIND_POLICY:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix adapter_kind_policy must match frozen value",
            details={"path": str(path)},
        )
    if payload.get("runtime_id_policy") != RUNTIME_ID_POLICY:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix runtime_id_policy must match frozen value",
            details={"path": str(path)},
        )
    if payload.get("singleton_runtime_id") != SINGLETON_RUNTIME_ID:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix singleton_runtime_id must match frozen value",
            details={"path": str(path)},
        )
    if payload.get("runtime_id_source_policy") != RUNTIME_ID_SOURCE_POLICY:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix runtime_id_source_policy must match frozen value",
            details={"path": str(path)},
        )
    if payload.get("runtime_id_override_policy") != RUNTIME_ID_OVERRIDE_POLICY:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix runtime_id_override_policy must match frozen value",
            details={"path": str(path)},
        )
    if payload.get("lane_pairing_policy") != LANE_PAIRING_POLICY:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix lane_pairing_policy must match frozen value",
            details={"path": str(path)},
        )
    if payload.get("lane_count_authority") != LANE_COUNT_AUTHORITY:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix lane_count_authority must match frozen value",
            details={"path": str(path)},
        )
    source_runner_adapter_registry_path = _require_string(
        payload.get("source_runner_adapter_registry_path"),
        field="source_runner_adapter_registry_path",
        code=AHK5003_MATRIX_REGISTRY_INVALID,
    )
    source_runner_adapter_registry_hash = _require_sha256(
        payload.get("source_runner_adapter_registry_hash"),
        field="source_runner_adapter_registry_hash",
        code=AHK5003_MATRIX_REGISTRY_INVALID,
    )
    matrix_registry_hash = _require_sha256(
        payload.get("matrix_registry_hash"),
        field="matrix_registry_hash",
        code=AHK5003_MATRIX_REGISTRY_INVALID,
    )

    adapters, source_path, source_hash = _load_runner_adapter_registry(
        root,
        source_runner_adapter_registry_path,
    )
    if source_runner_adapter_registry_path != source_path:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix source runner registry path must be repo-relative posix",
            details={
                "path": str(path),
                "observed_source_path": source_runner_adapter_registry_path,
                "expected_source_path": source_path,
            },
        )
    if source_runner_adapter_registry_hash != source_hash:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix source runner registry hash mismatch",
            details={"path": str(path)},
        )
    rows = payload.get("rows")
    if not isinstance(rows, list) or not rows:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix rows must be a non-empty array",
            details={"path": str(path)},
        )
    observed_lanes: list[MatrixLane] = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict) or set(row.keys()) != _ADAPTER_MATRIX_ROW_KEYS:
            raise _fail(
                code=AHK5003_MATRIX_REGISTRY_INVALID,
                message="adapter matrix row keys must match frozen grammar",
                details={"path": str(path), "index": index},
            )
        lane = MatrixLane(
            deployment_mode=_require_string(
                row.get("deployment_mode"),
                field="deployment_mode",
                code=AHK5003_MATRIX_REGISTRY_INVALID,
            ),
            adapter_id=_require_string(
                row.get("adapter_id"),
                field="adapter_id",
                code=AHK5003_MATRIX_REGISTRY_INVALID,
            ),
            runtime_id=_require_string(
                row.get("runtime_id"),
                field="runtime_id",
                code=AHK5003_MATRIX_REGISTRY_INVALID,
            ),
        )
        if lane.deployment_mode not in DEPLOYMENT_MODES:
            raise _fail(
                code=AHK5003_MATRIX_REGISTRY_INVALID,
                message="adapter matrix row has unsupported deployment_mode",
                details={
                    "path": str(path),
                    "index": index,
                    "deployment_mode": lane.deployment_mode,
                },
            )
        if lane.runtime_id != SINGLETON_RUNTIME_ID:
            raise _fail(
                code=AHK5003_MATRIX_REGISTRY_INVALID,
                message="adapter matrix row has unsupported runtime_id",
                details={"path": str(path), "index": index, "runtime_id": lane.runtime_id},
            )
        if row.get("adapter_kind") != "candidate_plan_passthrough":
            raise _fail(
                code=AHK5003_MATRIX_REGISTRY_INVALID,
                message="adapter matrix row has unsupported adapter_kind",
                details={
                    "path": str(path),
                    "index": index,
                    "adapter_kind": row.get("adapter_kind"),
                },
            )
        observed_lanes.append(lane)
    if observed_lanes != sorted(observed_lanes):
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix rows must be in deterministic lexicographic lane order",
            details={"path": str(path)},
        )
    if len(set(observed_lanes)) != len(observed_lanes):
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix contains duplicate lane tuples",
            details={"path": str(path)},
        )
    expected_rows: list[dict[str, str]] = []
    for adapter in adapters:
        for deployment_mode in DEPLOYMENT_MODES:
            expected_rows.append(
                {
                    "deployment_mode": deployment_mode,
                    "adapter_id": adapter["adapter_id"],
                    "runtime_id": SINGLETON_RUNTIME_ID,
                    "adapter_kind": adapter["adapter_kind"],
                }
            )
    expected_rows.sort(
        key=lambda row: (row["deployment_mode"], row["adapter_id"], row["runtime_id"])
    )
    if rows != expected_rows:
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix rows must exactly project the declared runner adapter registry",
            details={"path": str(path)},
        )

    hash_subject = _compute_matrix_registry_hash_subject(
        source_path=source_path,
        source_hash=source_hash,
        rows=rows,
    )
    if matrix_registry_hash != sha256_canonical_json(hash_subject):
        raise _fail(
            code=AHK5003_MATRIX_REGISTRY_INVALID,
            message="adapter matrix registry hash recomputation mismatch",
            details={"path": str(path)},
        )
    return payload


def _load_evaluation_inputs(
    root: Path, evaluation_inputs_path: str | Path
) -> tuple[dict[str, Any], str]:
    path = _coerce_artifact_path(root, evaluation_inputs_path)
    payload = _load_json_object(path)
    _require_schema(payload, expected_schema=ADAPTER_MATRIX_EVALUATION_INPUTS_SCHEMA, path=path)
    if set(payload.keys()) != _EVALUATION_INPUT_KEYS:
        raise _fail(
            code=AHK5004_MATRIX_INPUT_INVALID,
            message="matrix evaluation input keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
        )
    lane_inputs = payload.get("lane_inputs")
    if not isinstance(lane_inputs, list) or not lane_inputs:
        raise _fail(
            code=AHK5004_MATRIX_INPUT_INVALID,
            message="matrix evaluation lane_inputs must be a non-empty array",
            details={"path": str(path)},
        )
    for index, row in enumerate(lane_inputs):
        if not isinstance(row, dict) or set(row.keys()) != _EVALUATION_LANE_KEYS:
            raise _fail(
                code=AHK5004_MATRIX_INPUT_INVALID,
                message="matrix evaluation lane input keys must match frozen grammar",
                details={"path": str(path), "index": index},
            )
    return payload, _as_repo_relative_posix(root, path)


def _load_runner_provenance(path: Path) -> dict[str, Any]:
    payload = _load_json_object(path)
    _require_schema(payload, expected_schema=RUNNER_PROVENANCE_SCHEMA, path=path)
    if set(payload.keys()) != _RUNNER_PROVENANCE_KEYS:
        raise _fail(
            code=AHK5004_MATRIX_INPUT_INVALID,
            message="runner provenance keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
        )
    for field in ("taskpack_manifest_hash", "candidate_change_plan_hash", "provenance_hash"):
        _require_sha256(payload.get(field), field=field, code=AHK5004_MATRIX_INPUT_INVALID)
    _require_string(
        payload.get("adapter_id"), field="adapter_id", code=AHK5004_MATRIX_INPUT_INVALID
    )
    if not isinstance(payload.get("policy_validation_result"), dict):
        raise _fail(
            code=AHK5004_MATRIX_INPUT_INVALID,
            message="runner provenance policy_validation_result must be an object",
            details={"path": str(path)},
        )
    recomputed = sha256_canonical_json(
        {
            "taskpack_manifest_hash": payload["taskpack_manifest_hash"],
            "adapter_id": payload["adapter_id"],
            "candidate_change_plan_hash": payload["candidate_change_plan_hash"],
            "policy_validation_result": payload["policy_validation_result"],
            "exit_status": payload["exit_status"],
        }
    )
    if recomputed != payload["provenance_hash"]:
        raise _fail(
            code=AHK5006_CROSS_ARTIFACT_HASH_MISMATCH,
            message="runner provenance hash recomputation mismatch",
            details={"path": str(path)},
        )
    return payload


def _load_packaging_result(path: Path) -> dict[str, Any]:
    payload = _load_json_object(path)
    _require_schema(payload, expected_schema=PACKAGING_RESULT_SCHEMA, path=path)
    if set(payload.keys()) != _PACKAGING_RESULT_KEYS:
        raise _fail(
            code=AHK5004_MATRIX_INPUT_INVALID,
            message="packaging result keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
        )
    _require_string(
        payload.get("deployment_mode"), field="deployment_mode", code=AHK5004_MATRIX_INPUT_INVALID
    )
    _require_sha256(
        payload.get("packaging_bundle_hash"),
        field="packaging_bundle_hash",
        code=AHK5004_MATRIX_INPUT_INVALID,
    )
    _require_sha256(
        payload.get("packaging_provenance_hash"),
        field="packaging_provenance_hash",
        code=AHK5004_MATRIX_INPUT_INVALID,
    )
    return payload


def _load_packaging_manifest(path: Path) -> dict[str, Any]:
    payload = _load_json_object(path)
    _require_schema(payload, expected_schema=PACKAGING_MANIFEST_SCHEMA, path=path)
    if set(payload.keys()) != _PACKAGING_MANIFEST_KEYS:
        raise _fail(
            code=AHK5005_MATRIX_REPORT_INVALID,
            message="packaging manifest keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
        )
    emitted_files = payload.get("emitted_files")
    if not isinstance(emitted_files, list) or not emitted_files:
        raise _fail(
            code=AHK5005_MATRIX_REPORT_INVALID,
            message="packaging manifest emitted_files must be a non-empty array",
            details={"path": str(path)},
        )
    rows = []
    for index, row in enumerate(emitted_files):
        if not isinstance(row, dict) or set(row.keys()) != {"path", "sha256"}:
            raise _fail(
                code=AHK5005_MATRIX_REPORT_INVALID,
                message="packaging manifest emitted file row must match frozen grammar",
                details={"path": str(path), "index": index},
            )
        rows.append(row)
    if rows != sorted(rows, key=lambda row: row["path"]):
        raise _fail(
            code=AHK5005_MATRIX_REPORT_INVALID,
            message="packaging manifest emitted_files ordering drift detected",
            details={"path": str(path)},
        )
    recomputed_bundle_hash = sha256_canonical_json(
        [{"path": row["path"], "sha256": row["sha256"]} for row in rows]
    )
    if recomputed_bundle_hash != payload["packaging_bundle_hash"]:
        raise _fail(
            code=AHK5006_CROSS_ARTIFACT_HASH_MISMATCH,
            message="packaging manifest bundle hash recomputation mismatch",
            details={"path": str(path)},
        )
    return payload


def _load_packaging_provenance(path: Path) -> dict[str, Any]:
    payload = _load_json_object(path)
    _require_schema(payload, expected_schema=PACKAGING_PROVENANCE_SCHEMA, path=path)
    if set(payload.keys()) != _PACKAGING_PROVENANCE_KEYS:
        raise _fail(
            code=AHK5005_MATRIX_REPORT_INVALID,
            message="packaging provenance keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
        )
    for field in (
        "taskpack_manifest_hash",
        "verified_result_hash",
        "evidence_bundle_hash",
        "provenance_hash",
    ):
        _require_sha256(payload.get(field), field=field, code=AHK5005_MATRIX_REPORT_INVALID)
    parity_result = payload.get("parity_result")
    if not isinstance(parity_result, dict) or set(parity_result.keys()) != _PARITY_RESULT_KEYS:
        raise _fail(
            code=AHK5005_MATRIX_REPORT_INVALID,
            message="packaging provenance parity_result must match frozen grammar",
            details={"path": str(path)},
        )
    if parity_result.get("schema_typed_artifact_validation_passed") is not True:
        raise _fail(
            code=AHK5005_MATRIX_REPORT_INVALID,
            message="schema_typed_artifact_validation_passed must be true",
            details={"path": str(path)},
        )
    if not isinstance(parity_result.get("dry_run"), bool):
        raise _fail(
            code=AHK5005_MATRIX_REPORT_INVALID,
            message="packaging provenance dry_run must be boolean",
            details={"path": str(path)},
        )
    recomputed = sha256_canonical_json(
        {
            "taskpack_manifest_hash": payload["taskpack_manifest_hash"],
            "verified_result_hash": payload["verified_result_hash"],
            "evidence_bundle_hash": payload["evidence_bundle_hash"],
            "deployment_mode": payload["deployment_mode"],
            "parity_result": payload["parity_result"],
            "exit_status": payload["exit_status"],
        }
    )
    if recomputed != payload["provenance_hash"]:
        raise _fail(
            code=AHK5006_CROSS_ARTIFACT_HASH_MISMATCH,
            message="packaging provenance hash recomputation mismatch",
            details={"path": str(path)},
        )
    return payload


def _extract_canonical_subtree_hash(
    *, manifest_payload: dict[str, Any], deployment_mode: str, path: Path
) -> str:
    normalized_rows: list[dict[str, str]] = []
    seen_rel_paths: set[str] = set()
    for row in manifest_payload["emitted_files"]:
        row_path = row["path"]
        sha256 = row["sha256"]
        _require_sha256(sha256, field="sha256", code=AHK5005_MATRIX_REPORT_INVALID)
        path_parts = PurePosixPath(row_path).parts
        match_index = None
        for index, part in enumerate(path_parts[:-1]):
            if (
                part == deployment_mode
                and index + 1 < len(path_parts)
                and path_parts[index + 1] == "canonical"
            ):
                match_index = index
                break
        if match_index is None:
            continue
        rel_parts = path_parts[match_index + 2 :]
        if not rel_parts:
            raise _fail(
                code=AHK5005_MATRIX_REPORT_INVALID,
                message="canonical subtree path must contain a relative artifact path",
                details={"path": str(path), "row_path": row_path},
            )
        rel_path = PurePosixPath(*rel_parts).as_posix()
        if rel_path in seen_rel_paths:
            raise _fail(
                code=AHK5005_MATRIX_REPORT_INVALID,
                message="canonical subtree contains duplicate relative artifact paths",
                details={"path": str(path), "relative_path": rel_path},
            )
        seen_rel_paths.add(rel_path)
        normalized_rows.append({"path": rel_path, "sha256": sha256})
    if not normalized_rows:
        raise _fail(
            code=AHK5005_MATRIX_REPORT_INVALID,
            message="packaging manifest must contain canonical subtree entries",
            details={"path": str(path), "deployment_mode": deployment_mode},
        )
    normalized_rows.sort(key=lambda row: row["path"])
    return sha256_canonical_json(normalized_rows)


def _normalize_posix_path_list(values: Any, *, path: Path, field: str) -> list[str]:
    if not isinstance(values, list):
        raise _fail(
            code=AHK5005_MATRIX_REPORT_INVALID,
            message=f"{field} must be a list",
            details={"path": str(path)},
        )
    normalized = [
        _normalize_relative_path(
            _require_string(value, field=field, code=AHK5005_MATRIX_REPORT_INVALID)
        )
        for value in values
    ]
    canonical = sorted(set(normalized))
    if normalized != canonical:
        raise _fail(
            code=AHK5005_MATRIX_REPORT_INVALID,
            message=f"{field} must be a lexicographically sorted unique normalized posix-path list",
            details={"path": str(path), "field": field},
        )
    return normalized


def _canonicalize_policy_equivalence(payload: Any, *, path: Path) -> tuple[dict[str, Any], str]:
    if not isinstance(payload, dict) or set(payload.keys()) != _POLICY_EQUIVALENCE_KEYS:
        raise _fail(
            code=AHK5005_MATRIX_REPORT_INVALID,
            message="policy_equivalence keys must match frozen grammar",
            details={"path": str(path)},
        )
    issue_code_set = payload.get("issue_code_set")
    if not isinstance(issue_code_set, list) or not all(
        isinstance(value, str) for value in issue_code_set
    ):
        raise _fail(
            code=AHK5005_MATRIX_REPORT_INVALID,
            message="issue_code_set must be a string list",
            details={"path": str(path)},
        )
    canonical_issue_codes = sorted(set(issue_code_set))
    if issue_code_set != canonical_issue_codes:
        raise _fail(
            code=AHK5005_MATRIX_REPORT_INVALID,
            message="issue_code_set must be lexicographically sorted and unique",
            details={"path": str(path)},
        )
    required_evidence_slots_filled = payload.get("required_evidence_slots_filled")
    forbidden_effects_detected = payload.get("forbidden_effects_detected")
    if not isinstance(required_evidence_slots_filled, bool) or not isinstance(
        forbidden_effects_detected, bool
    ):
        raise _fail(
            code=AHK5005_MATRIX_REPORT_INVALID,
            message="policy_equivalence boolean fields are invalid",
            details={"path": str(path)},
        )
    allowlist_violations = _normalize_posix_path_list(
        payload.get("allowlist_violations"),
        path=path,
        field="allowlist_violations",
    )
    canonical_payload = {
        "issue_code_set": canonical_issue_codes,
        "required_evidence_slots_filled": required_evidence_slots_filled,
        "allowlist_violations": allowlist_violations,
        "forbidden_effects_detected": forbidden_effects_detected,
    }
    return canonical_payload, sha256_canonical_json(canonical_payload)


def build_adapter_matrix(
    *,
    adapter_registry_path: str | Path,
    matrix_output_path: str | Path = DEFAULT_MATRIX_REGISTRY_PATH,
    diagnostic_registry_path: str | Path = DEFAULT_DIAGNOSTIC_REGISTRY_PATH,
    repo_root_path: str | Path | None = None,
) -> AdapterMatrixResult:
    _require_deterministic_env()
    root = _project_repo_root(repo_root_path)
    _load_diagnostic_registry(root, diagnostic_registry_path)
    adapters, source_path, source_hash = _load_runner_adapter_registry(root, adapter_registry_path)

    rows: list[dict[str, str]] = []
    for adapter in adapters:
        for deployment_mode in DEPLOYMENT_MODES:
            rows.append(
                {
                    "deployment_mode": deployment_mode,
                    "adapter_id": adapter["adapter_id"],
                    "runtime_id": SINGLETON_RUNTIME_ID,
                    "adapter_kind": adapter["adapter_kind"],
                }
            )
    rows.sort(key=lambda row: (row["deployment_mode"], row["adapter_id"], row["runtime_id"]))

    hash_subject = _compute_matrix_registry_hash_subject(
        source_path=source_path,
        source_hash=source_hash,
        rows=rows,
    )
    registry_hash = sha256_canonical_json(hash_subject)
    payload = {
        "schema": ADAPTER_MATRIX_SCHEMA,
        **hash_subject,
        "matrix_registry_hash": registry_hash,
    }

    output_path = _coerce_artifact_path(root, matrix_output_path)
    _write_json(output_path, payload)
    return AdapterMatrixResult(
        matrix_registry_path=output_path,
        matrix_registry_hash=registry_hash,
    )


def build_adapter_matrix_parity_report(
    *,
    matrix_registry_path: str | Path,
    evaluation_inputs_path: str | Path,
    report_output_path: str | Path = DEFAULT_MATRIX_REPORT_PATH,
    diagnostic_registry_path: str | Path = DEFAULT_DIAGNOSTIC_REGISTRY_PATH,
    repo_root_path: str | Path | None = None,
) -> AdapterMatrixParityReportResult:
    _require_deterministic_env()
    root = _project_repo_root(repo_root_path)
    _load_diagnostic_registry(root, diagnostic_registry_path)
    matrix_path = _coerce_artifact_path(root, matrix_registry_path)
    matrix_payload = _load_adapter_matrix(root, matrix_path)
    eval_payload, eval_path = _load_evaluation_inputs(root, evaluation_inputs_path)

    if eval_payload["matrix_registry_path"] != _as_repo_relative_posix(root, matrix_path):
        raise _fail(
            code=AHK5004_MATRIX_INPUT_INVALID,
            message="evaluation inputs matrix_registry_path must match report builder input",
            details={
                "evaluation_inputs_path": eval_path,
                "declared_matrix_registry_path": eval_payload["matrix_registry_path"],
                "builder_matrix_registry_path": _as_repo_relative_posix(root, matrix_path),
            },
        )

    declared_lanes = [
        MatrixLane(
            deployment_mode=row["deployment_mode"],
            adapter_id=row["adapter_id"],
            runtime_id=row["runtime_id"],
        )
        for row in matrix_payload["rows"]
    ]
    declared_lane_set = set(declared_lanes)

    lane_rows: list[dict[str, Any]] = []
    observed_lanes: list[MatrixLane] = []
    for index, row in enumerate(eval_payload["lane_inputs"]):
        lane = MatrixLane(
            deployment_mode=_require_string(
                row.get("deployment_mode"),
                field="deployment_mode",
                code=AHK5004_MATRIX_INPUT_INVALID,
            ),
            adapter_id=_require_string(
                row.get("adapter_id"),
                field="adapter_id",
                code=AHK5004_MATRIX_INPUT_INVALID,
            ),
            runtime_id=_require_string(
                row.get("runtime_id"),
                field="runtime_id",
                code=AHK5004_MATRIX_INPUT_INVALID,
            ),
        )
        if lane.runtime_id != SINGLETON_RUNTIME_ID:
            raise _fail(
                code=AHK5007_MATRIX_LANE_COMPLETENESS_VIOLATION,
                message="lane runtime_id is outside the frozen singleton",
                details={"index": index, "runtime_id": lane.runtime_id},
            )
        if lane not in declared_lane_set:
            raise _fail(
                code=AHK5007_MATRIX_LANE_COMPLETENESS_VIOLATION,
                message="evaluation input lane is not declared in adapter matrix",
                details={"index": index, "lane_tuple": lane.as_payload()},
            )
        if lane in observed_lanes:
            raise _fail(
                code=AHK5007_MATRIX_LANE_COMPLETENESS_VIOLATION,
                message="evaluation inputs contain duplicate lane tuples",
                details={"index": index, "lane_tuple": lane.as_payload()},
            )

        runner_provenance_path = _coerce_artifact_path(root, row["runner_provenance_path"])
        packaging_result_path = _coerce_artifact_path(root, row["packaging_result_path"])
        runner_provenance = _load_runner_provenance(runner_provenance_path)
        packaging_result = _load_packaging_result(packaging_result_path)
        packaging_manifest_path = _coerce_artifact_path(
            root, packaging_result["packaging_manifest_path"]
        )
        packaging_provenance_path = _coerce_artifact_path(
            root, packaging_result["packaging_provenance_path"]
        )
        packaging_manifest = _load_packaging_manifest(packaging_manifest_path)
        packaging_provenance = _load_packaging_provenance(packaging_provenance_path)

        if runner_provenance["adapter_id"] != lane.adapter_id:
            raise _fail(
                code=AHK5006_CROSS_ARTIFACT_HASH_MISMATCH,
                message="runner provenance adapter_id does not match lane tuple",
                details={"lane_tuple": lane.as_payload(), "path": str(runner_provenance_path)},
            )
        for payload_name, deployment_mode in (
            ("packaging_result", packaging_result["deployment_mode"]),
            ("packaging_manifest", packaging_manifest["deployment_mode"]),
            ("packaging_provenance", packaging_provenance["deployment_mode"]),
        ):
            if deployment_mode != lane.deployment_mode:
                raise _fail(
                    code=AHK5006_CROSS_ARTIFACT_HASH_MISMATCH,
                    message=f"{payload_name} deployment_mode does not match lane tuple",
                    details={
                        "lane_tuple": lane.as_payload(),
                        "observed_deployment_mode": deployment_mode,
                    },
                )

        if packaging_result["packaging_provenance_hash"] != packaging_provenance["provenance_hash"]:
            raise _fail(
                code=AHK5006_CROSS_ARTIFACT_HASH_MISMATCH,
                message="packaging result provenance hash does not match packaging provenance",
                details={"path": str(packaging_result_path)},
            )
        if (
            packaging_provenance["taskpack_manifest_hash"]
            != runner_provenance["taskpack_manifest_hash"]
        ):
            raise _fail(
                code=AHK5006_CROSS_ARTIFACT_HASH_MISMATCH,
                message=(
                    "packaging provenance taskpack manifest hash does not match "
                    "runner provenance"
                ),
                details={"path": str(packaging_provenance_path)},
            )

        canonical_subtree_hash = _extract_canonical_subtree_hash(
            manifest_payload=packaging_manifest,
            deployment_mode=lane.deployment_mode,
            path=packaging_manifest_path,
        )
        policy_equivalence_payload, policy_equivalence_hash = _canonicalize_policy_equivalence(
            packaging_provenance["parity_result"]["policy_equivalence"],
            path=packaging_provenance_path,
        )

        lane_rows.append(
            {
                "deployment_mode": lane.deployment_mode,
                "adapter_id": lane.adapter_id,
                "runtime_id": lane.runtime_id,
                "taskpack_manifest_hash": runner_provenance["taskpack_manifest_hash"],
                "candidate_change_plan_hash": runner_provenance["candidate_change_plan_hash"],
                "runner_provenance_hash": runner_provenance["provenance_hash"],
                "packaging_manifest_path": _as_repo_relative_posix(root, packaging_manifest_path),
                "packaging_provenance_path": _as_repo_relative_posix(
                    root, packaging_provenance_path
                ),
                "canonical_subtree_hash": canonical_subtree_hash,
                "policy_equivalence_hash": policy_equivalence_hash,
            }
        )
        observed_lanes.append(lane)

    if observed_lanes != declared_lanes:
        same_lane_set = len(observed_lanes) == len(declared_lanes) and set(observed_lanes) == set(
            declared_lanes
        )
        raise _fail(
            code=AHK5007_MATRIX_LANE_COMPLETENESS_VIOLATION,
            message=(
                "evaluation inputs must follow the declared lexicographic lane order"
                if same_lane_set
                else "evaluation inputs must cover every declared lane exactly once"
            ),
            details={
                "declared_lanes": [lane.as_payload() for lane in declared_lanes],
                "observed_lanes": [lane.as_payload() for lane in observed_lanes],
            },
        )
    lane_rows.sort(key=lambda row: (row["deployment_mode"], row["adapter_id"], row["runtime_id"]))

    pairwise_parity: list[dict[str, Any]] = []
    grouped: dict[tuple[str, str], list[dict[str, Any]]] = {}
    for row in lane_rows:
        grouped.setdefault((row["adapter_id"], row["runtime_id"]), []).append(row)
    for (adapter_id, runtime_id), rows in sorted(grouped.items()):
        if len(rows) != 2:
            raise _fail(
                code=AHK5007_MATRIX_LANE_COMPLETENESS_VIOLATION,
                message=(
                    "each declared adapter/runtime pair must have exactly two "
                    "deployment mode rows"
                ),
                details={
                    "adapter_id": adapter_id,
                    "runtime_id": runtime_id,
                    "row_count": len(rows),
                },
            )
        modes = [row["deployment_mode"] for row in rows]
        if modes != list(DEPLOYMENT_MODES):
            raise _fail(
                code=AHK5007_MATRIX_LANE_COMPLETENESS_VIOLATION,
                message="matrix report pair must cover both released deployment modes in order",
                details={
                    "adapter_id": adapter_id,
                    "runtime_id": runtime_id,
                    "deployment_modes": modes,
                },
            )
        manifest_hashes = {row["taskpack_manifest_hash"] for row in rows}
        candidate_hashes = {row["candidate_change_plan_hash"] for row in rows}
        canonical_hashes = {row["canonical_subtree_hash"] for row in rows}
        policy_hashes = {row["policy_equivalence_hash"] for row in rows}
        if len(manifest_hashes) != 1 or len(candidate_hashes) != 1:
            raise _fail(
                code=AHK5006_CROSS_ARTIFACT_HASH_MISMATCH,
                message="pairwise lane hashes must agree on taskpack and candidate subjects",
                details={"adapter_id": adapter_id, "runtime_id": runtime_id},
            )
        if len(canonical_hashes) != 1:
            raise _fail(
                code=AHK5005_MATRIX_REPORT_INVALID,
                message="canonical subtree parity mismatch detected",
                details={"adapter_id": adapter_id, "runtime_id": runtime_id},
            )
        if len(policy_hashes) != 1:
            raise _fail(
                code=AHK5005_MATRIX_REPORT_INVALID,
                message="policy equivalence parity mismatch detected",
                details={"adapter_id": adapter_id, "runtime_id": runtime_id},
            )
        pairwise_parity.append(
            {
                "adapter_id": adapter_id,
                "runtime_id": runtime_id,
                "deployment_modes": list(DEPLOYMENT_MODES),
                "taskpack_manifest_hash": rows[0]["taskpack_manifest_hash"],
                "candidate_change_plan_hash": rows[0]["candidate_change_plan_hash"],
                "canonical_subtree_exact_match": True,
                "policy_equivalence_exact_match": True,
            }
        )

    report_hash_subject = {
        "matrix_registry_path": _as_repo_relative_posix(root, matrix_path),
        "matrix_registry_hash": matrix_payload["matrix_registry_hash"],
        "lane_id_tuple": list(LANE_ID_TUPLE),
        "enabled_row_policy": ENABLED_ROW_POLICY,
        "declared_registry_only": True,
        "lexicographic_lane_order_enforced": True,
        "runtime_id_source_policy": RUNTIME_ID_SOURCE_POLICY,
        "runtime_id_host_inference_forbidden": True,
        "canonical_subtree_exact_match_required": True,
        "canonical_subtree_source_policy": CANONICAL_SUBTREE_SOURCE_POLICY,
        "policy_equivalence_exact_match_required": True,
        "policy_equivalence_subject_keys_verified": sorted(_POLICY_EQUIVALENCE_KEYS),
        "policy_equivalence_value_shapes_verified": POLICY_EQUIVALENCE_VALUE_SHAPES,
        "report_covers_all_declared_lanes": True,
        "lane_rows": lane_rows,
        "pairwise_parity": pairwise_parity,
    }
    report_hash = sha256_canonical_json(report_hash_subject)
    report_payload = {
        "schema": ADAPTER_MATRIX_PARITY_REPORT_SCHEMA,
        **report_hash_subject,
        "report_hash": report_hash,
    }
    output_path = _coerce_artifact_path(root, report_output_path)
    _write_json(output_path, report_payload)
    return AdapterMatrixParityReportResult(
        matrix_report_path=output_path,
        matrix_report_hash=report_hash,
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build V50 adapter matrix artifacts.")
    subparsers = parser.add_subparsers(dest="command", required=True)

    registry_parser = subparsers.add_parser("build-registry")
    registry_parser.add_argument("--adapter-registry", required=True)
    registry_parser.add_argument("--out", default=DEFAULT_MATRIX_REGISTRY_PATH)
    registry_parser.add_argument(
        "--diagnostic-registry",
        default=DEFAULT_DIAGNOSTIC_REGISTRY_PATH,
    )
    registry_parser.add_argument("--repo-root", default=None)

    report_parser = subparsers.add_parser("build-report")
    report_parser.add_argument("--matrix-registry", required=True)
    report_parser.add_argument("--evaluation-inputs", required=True)
    report_parser.add_argument("--out", default=DEFAULT_MATRIX_REPORT_PATH)
    report_parser.add_argument(
        "--diagnostic-registry",
        default=DEFAULT_DIAGNOSTIC_REGISTRY_PATH,
    )
    report_parser.add_argument("--repo-root", default=None)

    args = parser.parse_args(argv)
    try:
        if args.command == "build-registry":
            result = build_adapter_matrix(
                adapter_registry_path=args.adapter_registry,
                matrix_output_path=args.out,
                diagnostic_registry_path=args.diagnostic_registry,
                repo_root_path=args.repo_root,
            )
            payload = {
                "schema": ADAPTER_MATRIX_BUILD_RESULT_SCHEMA,
                "matrix_registry_path": result.matrix_registry_path.as_posix(),
                "matrix_registry_hash": result.matrix_registry_hash,
            }
        else:
            result = build_adapter_matrix_parity_report(
                matrix_registry_path=args.matrix_registry,
                evaluation_inputs_path=args.evaluation_inputs,
                report_output_path=args.out,
                diagnostic_registry_path=args.diagnostic_registry,
                repo_root_path=args.repo_root,
            )
            payload = {
                "schema": ADAPTER_MATRIX_REPORT_RESULT_SCHEMA,
                "matrix_report_path": result.matrix_report_path.as_posix(),
                "matrix_report_hash": result.matrix_report_hash,
            }
    except TaskpackMatrixError as exc:
        sys.stderr.write(str(exc) + "\n")
        return 1

    sys.stdout.write(canonical_json(payload) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
