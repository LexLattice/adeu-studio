from __future__ import annotations

import json
import os
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from adeu_ir.repo import repo_root
from urm_runtime.hashing import canonical_json

SIGNING_ERROR_SCHEMA = "taskpack_signing_error@1"
SIGNING_REJECTION_DIAGNOSTIC_SCHEMA = "v34a_signing_rejection_diagnostic@1"
DIAGNOSTIC_REGISTRY_SCHEMA = "taskpack_signing_diagnostic_registry@1"

DEFAULT_DIAGNOSTIC_REGISTRY_PATH = (
    "packages/adeu_agent_harness/src/adeu_agent_harness/diagnostic_registry_v48.json"
)
DEFAULT_REJECTIONS_ROOT = "artifacts/agent_harness/v48/rejections"

POLICY_SOURCE_ENUM_V48 = (
    "taskpack_manifest",
    "signature_envelope",
    "trust_anchor_registry",
    "signature_verification_result",
    "stop_gate_metrics",
)

AHK4800_PATH_POLICY_VIOLATION = "AHK4800"
AHK4801_JSON_OBJECT_REQUIRED = "AHK4801"
AHK4802_SCHEMA_MISMATCH = "AHK4802"
AHK4803_ARTIFACT_INVALID = "AHK4803"
AHK4804_CROSS_ARTIFACT_HASH_MISMATCH = "AHK4804"
AHK4805_ALGORITHM_POLICY_VIOLATION = "AHK4805"
AHK4806_KEY_LIFECYCLE_POLICY_VIOLATION = "AHK4806"
AHK4807_SIGNATURE_VERIFICATION_RESULT_INVALID = "AHK4807"
AHK4808_CONTRACT_REGISTRY_INVALID = "AHK4808"
AHK4809_SIGNING_REJECTION_DIAGNOSTIC_INVALID = "AHK4809"
AHK4810_SIGNATURE_VERIFICATION_FAILED = "AHK4810"
AHK4811_VERIFICATION_FAILURE_WITHOUT_REJECTION_DIAGNOSTIC = "AHK4811"

_AHK48_PATTERN = re.compile(r"AHK48[0-9]{2}")
_SHA256_PATTERN = re.compile(r"[0-9a-f]{64}")
_RFC3339_UTC_Z_SECOND_PRECISION_PATTERN = re.compile(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z")

_REQUIRED_DETERMINISTIC_ENV_V48 = {
    "TZ": "UTC",
    "LC_ALL": "C",
    "PYTHONHASHSEED": "0",
}


@dataclass(frozen=True)
class SigningIssue:
    issue_code: str
    reason: str
    artifact_path: str
    signer_key_id: str
    algorithm: str
    policy_source: str


class TaskpackSigningError(RuntimeError):
    def __init__(
        self,
        *,
        code: str,
        message: str,
        details: dict[str, Any] | None = None,
        issue: SigningIssue | None = None,
    ) -> None:
        self.code = code
        self.message = message
        self.details = details or {}
        self.issue = issue
        payload = {
            "schema": SIGNING_ERROR_SCHEMA,
            "code": code,
            "message": message,
            "details": self.details,
        }
        super().__init__(canonical_json(payload))


def fail(
    *,
    code: str,
    message: str,
    details: dict[str, Any] | None = None,
    artifact_path: str = "",
    signer_key_id: str = "",
    algorithm: str = "",
    policy_source: str = "signature_envelope",
) -> TaskpackSigningError:
    issue_policy_source = (
        policy_source if policy_source in POLICY_SOURCE_ENUM_V48 else "signature_envelope"
    )
    return TaskpackSigningError(
        code=code,
        message=message,
        details=details,
        issue=SigningIssue(
            issue_code=code,
            reason=message,
            artifact_path=artifact_path,
            signer_key_id=signer_key_id,
            algorithm=algorithm,
            policy_source=issue_policy_source,
        ),
    )


def normalize_relative_path(raw_path: str) -> str:
    path_text = raw_path.strip().replace("\\", "/")
    if not path_text:
        raise fail(
            code=AHK4800_PATH_POLICY_VIOLATION,
            message="path must not be empty",
            details={"path": raw_path},
            artifact_path=raw_path,
        )
    if path_text.startswith("/"):
        raise fail(
            code=AHK4800_PATH_POLICY_VIOLATION,
            message="absolute paths are forbidden",
            details={"path": raw_path},
            artifact_path=raw_path,
        )
    if re.match(r"^[A-Za-z]:[\\/]", path_text):
        raise fail(
            code=AHK4800_PATH_POLICY_VIOLATION,
            message="windows absolute paths are forbidden",
            details={"path": raw_path},
            artifact_path=raw_path,
        )

    segments: list[str] = []
    for segment in path_text.split("/"):
        if segment in ("", "."):
            continue
        if segment == "..":
            if not segments:
                raise fail(
                    code=AHK4800_PATH_POLICY_VIOLATION,
                    message="path escapes repository root",
                    details={"path": raw_path},
                    artifact_path=raw_path,
                )
            segments.pop()
            continue
        segments.append(segment)

    if not segments:
        raise fail(
            code=AHK4800_PATH_POLICY_VIOLATION,
            message="path resolves to repository root",
            details={"path": raw_path},
            artifact_path=raw_path,
        )
    return "/".join(segments)


def safe_join(root: Path, rel_path: str) -> Path:
    normalized = normalize_relative_path(rel_path)
    path = (root / normalized).resolve()
    root_resolved = root.resolve()
    try:
        path.relative_to(root_resolved)
    except ValueError as exc:
        raise fail(
            code=AHK4800_PATH_POLICY_VIOLATION,
            message="resolved path escapes repository root",
            details={"path": rel_path},
            artifact_path=rel_path,
        ) from exc
    return path


def coerce_artifact_path(root: Path, raw_path: str) -> Path:
    if not raw_path or not isinstance(raw_path, str):
        raise fail(
            code=AHK4800_PATH_POLICY_VIOLATION,
            message="artifact path must be a non-empty string",
            details={"path": raw_path},
            artifact_path=str(raw_path),
        )
    candidate = Path(raw_path)
    if candidate.is_absolute():
        resolved = candidate.resolve()
        root_resolved = root.resolve()
        try:
            resolved.relative_to(root_resolved)
        except ValueError as exc:
            raise fail(
                code=AHK4800_PATH_POLICY_VIOLATION,
                message="absolute artifact path escapes repository root",
                details={"path": raw_path},
                artifact_path=raw_path,
            ) from exc
        return resolved
    return safe_join(root, raw_path)


def load_json_object(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise fail(
            code=AHK4800_PATH_POLICY_VIOLATION,
            message="required json path does not exist",
            details={"path": str(path)},
            artifact_path=str(path),
        ) from exc
    except json.JSONDecodeError as exc:
        raise fail(
            code=AHK4801_JSON_OBJECT_REQUIRED,
            message="json payload is invalid",
            details={"path": str(path), "error": str(exc)},
            artifact_path=str(path),
        ) from exc
    if not isinstance(payload, dict):
        raise fail(
            code=AHK4801_JSON_OBJECT_REQUIRED,
            message="json payload must decode to an object",
            details={"path": str(path)},
            artifact_path=str(path),
        )
    return payload


def require_schema(payload: dict[str, Any], *, expected_schema: str, path: Path) -> None:
    observed = payload.get("schema")
    if observed != expected_schema:
        raise fail(
            code=AHK4802_SCHEMA_MISMATCH,
            message="schema mismatch",
            details={
                "path": str(path),
                "expected_schema": expected_schema,
                "observed_schema": observed,
            },
            artifact_path=str(path),
        )


def require_string(
    value: Any,
    *,
    field: str,
    artifact_path: str,
    code: str = AHK4803_ARTIFACT_INVALID,
) -> str:
    if not isinstance(value, str) or not value:
        raise fail(
            code=code,
            message="required string field is missing or invalid",
            details={"field": field},
            artifact_path=artifact_path,
        )
    return value


def parse_reference_time_utc(value: Any, *, artifact_path: str) -> datetime:
    text = require_string(
        value,
        field="verification_reference_time_utc",
        artifact_path=artifact_path,
    )
    if not _RFC3339_UTC_Z_SECOND_PRECISION_PATTERN.fullmatch(text):
        raise fail(
            code=AHK4803_ARTIFACT_INVALID,
            message="verification_reference_time_utc must match RFC3339 UTC Z second precision",
            details={"verification_reference_time_utc": text},
            artifact_path=artifact_path,
        )
    try:
        parsed = datetime.strptime(text, "%Y-%m-%dT%H:%M:%SZ")
    except ValueError as exc:
        raise fail(
            code=AHK4803_ARTIFACT_INVALID,
            message="verification_reference_time_utc value is invalid",
            details={"verification_reference_time_utc": text},
            artifact_path=artifact_path,
        ) from exc
    return parsed.replace(tzinfo=timezone.utc)


def is_sha256(value: str) -> bool:
    return bool(_SHA256_PATTERN.fullmatch(value))


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(canonical_json(payload) + "\n", encoding="utf-8")


def project_repo_root(anchor: Path | None) -> Path:
    return repo_root(anchor=anchor)


def require_deterministic_env_v48() -> None:
    observed = {
        key: os.environ.get(key) for key in sorted(_REQUIRED_DETERMINISTIC_ENV_V48.keys())
    }
    if observed != _REQUIRED_DETERMINISTIC_ENV_V48:
        raise fail(
            code=AHK4803_ARTIFACT_INVALID,
            message="deterministic environment contract drift detected",
            details={
                "required_deterministic_env": _REQUIRED_DETERMINISTIC_ENV_V48,
                "observed_deterministic_env": observed,
            },
            artifact_path="environment",
            policy_source="stop_gate_metrics",
        )


def load_diagnostic_registry(
    *, root: Path, registry_rel_path: str
) -> tuple[Path, set[str]]:
    registry_path = safe_join(root, registry_rel_path)
    payload = load_json_object(registry_path)
    require_schema(payload, expected_schema=DIAGNOSTIC_REGISTRY_SCHEMA, path=registry_path)
    if set(payload.keys()) != {"schema", "codes"}:
        raise fail(
            code=AHK4808_CONTRACT_REGISTRY_INVALID,
            message="diagnostic registry keys must match frozen grammar",
            details={"path": str(registry_path), "keys": sorted(payload.keys())},
            artifact_path=str(registry_path),
            policy_source="stop_gate_metrics",
        )

    codes_raw = payload.get("codes")
    if not isinstance(codes_raw, list) or not codes_raw:
        raise fail(
            code=AHK4808_CONTRACT_REGISTRY_INVALID,
            message="diagnostic registry codes must be a non-empty array",
            details={"path": str(registry_path)},
            artifact_path=str(registry_path),
            policy_source="stop_gate_metrics",
        )

    issue_codes: list[str] = []
    for index, entry in enumerate(codes_raw):
        if not isinstance(entry, dict):
            raise fail(
                code=AHK4808_CONTRACT_REGISTRY_INVALID,
                message="diagnostic registry entry must be an object",
                details={"path": str(registry_path), "index": index},
                artifact_path=str(registry_path),
                policy_source="stop_gate_metrics",
            )
        if set(entry.keys()) != {"issue_code", "title", "description"}:
            raise fail(
                code=AHK4808_CONTRACT_REGISTRY_INVALID,
                message="diagnostic registry entry keys must match frozen grammar",
                details={
                    "path": str(registry_path),
                    "index": index,
                    "keys": sorted(entry.keys()),
                },
                artifact_path=str(registry_path),
                policy_source="stop_gate_metrics",
            )
        issue_code = require_string(
            entry.get("issue_code"),
            field="issue_code",
            artifact_path=str(registry_path),
            code=AHK4808_CONTRACT_REGISTRY_INVALID,
        )
        if not _AHK48_PATTERN.fullmatch(issue_code):
            raise fail(
                code=AHK4808_CONTRACT_REGISTRY_INVALID,
                message="diagnostic registry issue_code must match AHK48[0-9]{2}",
                details={"path": str(registry_path), "issue_code": issue_code},
                artifact_path=str(registry_path),
                policy_source="stop_gate_metrics",
            )
        issue_codes.append(issue_code)

    if len(set(issue_codes)) != len(issue_codes):
        raise fail(
            code=AHK4808_CONTRACT_REGISTRY_INVALID,
            message="diagnostic registry issue_code entries must be unique",
            details={"path": str(registry_path)},
            artifact_path=str(registry_path),
            policy_source="stop_gate_metrics",
        )
    if issue_codes != sorted(issue_codes):
        raise fail(
            code=AHK4808_CONTRACT_REGISTRY_INVALID,
            message="diagnostic registry issue_code ordering must be lexicographic",
            details={"path": str(registry_path), "issue_codes": issue_codes},
            artifact_path=str(registry_path),
            policy_source="stop_gate_metrics",
        )
    return registry_path, set(issue_codes)


def _validate_issue(issue: SigningIssue, *, allowed_codes: set[str]) -> None:
    if issue.issue_code not in allowed_codes:
        raise fail(
            code=AHK4808_CONTRACT_REGISTRY_INVALID,
            message="diagnostic issue_code is not present in authoritative registry",
            details={"issue_code": issue.issue_code},
            artifact_path=issue.artifact_path,
            signer_key_id=issue.signer_key_id,
            algorithm=issue.algorithm,
            policy_source="stop_gate_metrics",
        )
    if not _AHK48_PATTERN.fullmatch(issue.issue_code):
        raise fail(
            code=AHK4809_SIGNING_REJECTION_DIAGNOSTIC_INVALID,
            message="diagnostic issue_code must match AHK48[0-9]{2}",
            details={"issue_code": issue.issue_code},
            artifact_path=issue.artifact_path,
            signer_key_id=issue.signer_key_id,
            algorithm=issue.algorithm,
            policy_source="signature_verification_result",
        )
    if issue.policy_source not in POLICY_SOURCE_ENUM_V48:
        raise fail(
            code=AHK4809_SIGNING_REJECTION_DIAGNOSTIC_INVALID,
            message="diagnostic policy_source is outside frozen v48 closed enum",
            details={"policy_source": issue.policy_source},
            artifact_path=issue.artifact_path,
            signer_key_id=issue.signer_key_id,
            algorithm=issue.algorithm,
            policy_source="signature_verification_result",
        )


def emit_rejection_diagnostic(
    *,
    root: Path,
    output_root_rel: str,
    taskpack_manifest_hash: str | None,
    taskpack_bundle_hash: str | None,
    issues: list[SigningIssue],
    allowed_codes: set[str],
) -> Path:
    if not issues:
        raise fail(
            code=AHK4811_VERIFICATION_FAILURE_WITHOUT_REJECTION_DIAGNOSTIC,
            message="rejection diagnostics requested without issues",
            details={},
            policy_source="stop_gate_metrics",
        )

    for issue in issues:
        _validate_issue(issue, allowed_codes=allowed_codes)

    sorted_issues = sorted(
        issues,
        key=lambda row: (
            row.issue_code,
            row.artifact_path,
            row.signer_key_id,
            row.algorithm,
            row.policy_source,
        ),
    )

    manifest_token = (
        taskpack_manifest_hash
        if isinstance(taskpack_manifest_hash, str) and is_sha256(taskpack_manifest_hash)
        else "unknown_manifest"
    )
    bundle_token = (
        taskpack_bundle_hash
        if isinstance(taskpack_bundle_hash, str) and is_sha256(taskpack_bundle_hash)
        else "unknown_bundle"
    )

    diagnostics_dir = safe_join(root, output_root_rel)
    diagnostics_path = diagnostics_dir / f"{manifest_token}_{bundle_token}.json"
    payload: dict[str, Any] = {
        "schema": SIGNING_REJECTION_DIAGNOSTIC_SCHEMA,
        "issues": [
            {
                "issue_code": issue.issue_code,
                "reason": issue.reason,
                "artifact_path": issue.artifact_path,
                "signer_key_id": issue.signer_key_id,
                "algorithm": issue.algorithm,
                "policy_source": issue.policy_source,
            }
            for issue in sorted_issues
        ],
    }
    if isinstance(taskpack_manifest_hash, str):
        payload["taskpack_manifest_hash"] = taskpack_manifest_hash
    if isinstance(taskpack_bundle_hash, str):
        payload["taskpack_bundle_hash"] = taskpack_bundle_hash

    write_json(diagnostics_path, payload)
    loaded = load_json_object(diagnostics_path)
    require_schema(
        loaded,
        expected_schema=SIGNING_REJECTION_DIAGNOSTIC_SCHEMA,
        path=diagnostics_path,
    )
    issues_raw = loaded.get("issues")
    if not isinstance(issues_raw, list) or not issues_raw:
        raise fail(
            code=AHK4809_SIGNING_REJECTION_DIAGNOSTIC_INVALID,
            message="signing rejection diagnostics issues must be a non-empty array",
            details={"path": str(diagnostics_path)},
            artifact_path=str(diagnostics_path),
            policy_source="signature_verification_result",
        )
    return diagnostics_path
