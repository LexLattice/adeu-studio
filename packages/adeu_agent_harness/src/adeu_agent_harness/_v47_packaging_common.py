from __future__ import annotations

import json
import os
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from adeu_ir.repo import repo_root
from urm_runtime.hashing import canonical_json

PACKAGING_ERROR_SCHEMA = "taskpack_packaging_error@1"
PACKAGING_REJECTION_DIAGNOSTIC_SCHEMA = "v33d_packaging_rejection_diagnostic@1"
DIAGNOSTIC_REGISTRY_SCHEMA = "taskpack_packaging_diagnostic_registry@1"

DEFAULT_DIAGNOSTIC_REGISTRY_PATH = (
    "packages/adeu_agent_harness/src/adeu_agent_harness/diagnostic_registry_v47.json"
)
DEFAULT_REJECTIONS_ROOT = "artifacts/agent_harness/v47/rejections"

POLICY_SOURCE_ENUM_V47 = (
    "taskpack_manifest",
    "verified_result",
    "evidence_bundle",
    "verifier_provenance",
    "packaging_manifest",
    "stop_gate_metrics",
)

AHK4700_PATH_POLICY_VIOLATION = "AHK4700"
AHK4701_JSON_OBJECT_REQUIRED = "AHK4701"
AHK4702_SCHEMA_MISMATCH = "AHK4702"
AHK4703_ARTIFACT_INVALID = "AHK4703"
AHK4704_CROSS_ARTIFACT_HASH_MISMATCH = "AHK4704"
AHK4705_DEPLOYMENT_MODE_POLICY_VIOLATION = "AHK4705"
AHK4706_MODE_CONTRACT_IDENTITY_MISMATCH = "AHK4706"
AHK4707_PACKAGING_MANIFEST_INVALID = "AHK4707"
AHK4708_CONTRACT_REGISTRY_INVALID = "AHK4708"
AHK4709_PACKAGING_REJECTION_DIAGNOSTIC_INVALID = "AHK4709"
AHK4710_PACKAGING_PROVENANCE_INVALID = "AHK4710"
AHK4711_SUBPROCESS_MODE_POLICY_VIOLATION = "AHK4711"
AHK4712_CANONICAL_SUBJECT_PATH_NORMALIZATION_DRIFT = "AHK4712"
AHK4713_PACKAGING_FAILURE_WITHOUT_REJECTION_DIAGNOSTIC = "AHK4713"

_AHK47_PATTERN = re.compile(r"AHK47[0-9]{2}")
_SHA256_PATTERN = re.compile(r"[0-9a-f]{64}")

_REQUIRED_DETERMINISTIC_ENV_V47 = {
    "TZ": "UTC",
    "LC_ALL": "C",
    "PYTHONHASHSEED": "0",
}

_NULL_SHA256 = "0" * 64


@dataclass(frozen=True)
class PackagingIssue:
    issue_code: str
    reason: str
    artifact_path: str
    deployment_mode: str
    policy_source: str


class TaskpackPackagingError(RuntimeError):
    def __init__(
        self,
        *,
        code: str,
        message: str,
        details: dict[str, Any] | None = None,
        issue: PackagingIssue | None = None,
    ) -> None:
        self.code = code
        self.message = message
        self.details = details or {}
        self.issue = issue
        payload = {
            "schema": PACKAGING_ERROR_SCHEMA,
            "code": code,
            "message": message,
            "details": self.details,
        }
        super().__init__(canonical_json(payload))


def fail(
    *,
    code: str,
    message: str,
    artifact_path: str,
    details: dict[str, Any] | None = None,
    deployment_mode: str = "",
    policy_source: str = "packaging_manifest",
) -> TaskpackPackagingError:
    issue_policy_source = (
        policy_source if policy_source in POLICY_SOURCE_ENUM_V47 else "packaging_manifest"
    )
    return TaskpackPackagingError(
        code=code,
        message=message,
        details=details,
        issue=PackagingIssue(
            issue_code=code,
            reason=message,
            artifact_path=artifact_path,
            deployment_mode=deployment_mode,
            policy_source=issue_policy_source,
        ),
    )


def normalize_relative_path(raw_path: str) -> str:
    path_text = raw_path.strip().replace("\\", "/")
    if not path_text:
        raise fail(
            code=AHK4700_PATH_POLICY_VIOLATION,
            message="path must not be empty",
            details={"path": raw_path},
            artifact_path=raw_path,
        )
    if path_text.startswith("/"):
        raise fail(
            code=AHK4700_PATH_POLICY_VIOLATION,
            message="absolute paths are forbidden",
            details={"path": raw_path},
            artifact_path=raw_path,
        )
    if re.match(r"^[A-Za-z]:[\\/]", path_text):
        raise fail(
            code=AHK4700_PATH_POLICY_VIOLATION,
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
                    code=AHK4700_PATH_POLICY_VIOLATION,
                    message="path escapes repository root",
                    details={"path": raw_path},
                    artifact_path=raw_path,
                )
            segments.pop()
            continue
        segments.append(segment)

    if not segments:
        raise fail(
            code=AHK4700_PATH_POLICY_VIOLATION,
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
            code=AHK4700_PATH_POLICY_VIOLATION,
            message="resolved path escapes repository root",
            details={"path": rel_path},
            artifact_path=rel_path,
        ) from exc
    return path


def coerce_artifact_path(root: Path, raw_path: str) -> Path:
    if not raw_path or not isinstance(raw_path, str):
        raise fail(
            code=AHK4700_PATH_POLICY_VIOLATION,
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
                code=AHK4700_PATH_POLICY_VIOLATION,
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
            code=AHK4700_PATH_POLICY_VIOLATION,
            message="required json path does not exist",
            details={"path": str(path)},
            artifact_path=str(path),
        ) from exc
    except json.JSONDecodeError as exc:
        raise fail(
            code=AHK4701_JSON_OBJECT_REQUIRED,
            message="json payload is invalid",
            details={"path": str(path), "error": str(exc)},
            artifact_path=str(path),
        ) from exc
    if not isinstance(payload, dict):
        raise fail(
            code=AHK4701_JSON_OBJECT_REQUIRED,
            message="json payload must decode to an object",
            details={"path": str(path)},
            artifact_path=str(path),
        )
    return payload


def require_schema(payload: dict[str, Any], *, expected_schema: str, path: Path) -> None:
    observed = payload.get("schema")
    if observed != expected_schema:
        raise fail(
            code=AHK4702_SCHEMA_MISMATCH,
            message="schema mismatch",
            details={
                "path": str(path),
                "expected_schema": expected_schema,
                "observed_schema": observed,
            },
            artifact_path=str(path),
        )


def is_sha256(value: str) -> bool:
    return bool(_SHA256_PATTERN.fullmatch(value))


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(canonical_json(payload) + "\n", encoding="utf-8")


def project_repo_root(anchor: Path | None) -> Path:
    return repo_root(anchor=anchor)


def require_deterministic_env_v47() -> None:
    observed = {
        key: os.environ.get(key) for key in sorted(_REQUIRED_DETERMINISTIC_ENV_V47.keys())
    }
    if observed != _REQUIRED_DETERMINISTIC_ENV_V47:
        raise fail(
            code=AHK4703_ARTIFACT_INVALID,
            message="deterministic environment contract drift detected",
            details={
                "required_deterministic_env": _REQUIRED_DETERMINISTIC_ENV_V47,
                "observed_deterministic_env": observed,
            },
            artifact_path="environment",
            policy_source="stop_gate_metrics",
        )


def load_diagnostic_registry(*, root: Path, registry_rel_path: str) -> tuple[Path, set[str]]:
    registry_path = safe_join(root, registry_rel_path)
    payload = load_json_object(registry_path)
    require_schema(payload, expected_schema=DIAGNOSTIC_REGISTRY_SCHEMA, path=registry_path)
    if set(payload.keys()) != {"schema", "codes"}:
        raise fail(
            code=AHK4708_CONTRACT_REGISTRY_INVALID,
            message="diagnostic registry keys must match frozen grammar",
            details={"path": str(registry_path), "keys": sorted(payload.keys())},
            artifact_path=str(registry_path),
        )

    codes_raw = payload.get("codes")
    if not isinstance(codes_raw, list) or not codes_raw:
        raise fail(
            code=AHK4708_CONTRACT_REGISTRY_INVALID,
            message="diagnostic registry codes must be a non-empty array",
            details={"path": str(registry_path)},
            artifact_path=str(registry_path),
        )

    issue_codes: list[str] = []
    for index, entry in enumerate(codes_raw):
        if not isinstance(entry, dict):
            raise fail(
                code=AHK4708_CONTRACT_REGISTRY_INVALID,
                message="diagnostic registry entry must be an object",
                details={"path": str(registry_path), "index": index},
                artifact_path=str(registry_path),
            )
        if set(entry.keys()) != {"issue_code", "title", "description"}:
            raise fail(
                code=AHK4708_CONTRACT_REGISTRY_INVALID,
                message="diagnostic registry entry keys must match frozen grammar",
                details={
                    "path": str(registry_path),
                    "index": index,
                    "keys": sorted(entry.keys()),
                },
                artifact_path=str(registry_path),
            )
        issue_code = entry.get("issue_code")
        if not isinstance(issue_code, str) or not _AHK47_PATTERN.fullmatch(issue_code):
            raise fail(
                code=AHK4708_CONTRACT_REGISTRY_INVALID,
                message="diagnostic issue_code violates frozen AHK47xx namespace",
                details={"path": str(registry_path), "index": index, "issue_code": issue_code},
                artifact_path=str(registry_path),
            )
        issue_codes.append(issue_code)

    if issue_codes != sorted(set(issue_codes)):
        raise fail(
            code=AHK4708_CONTRACT_REGISTRY_INVALID,
            message="diagnostic issue codes must be unique and sorted ascending",
            details={"path": str(registry_path), "issue_codes": issue_codes},
            artifact_path=str(registry_path),
        )

    return registry_path, set(issue_codes)


def emit_rejection_diagnostic(
    *,
    root: Path,
    output_root_rel: str,
    taskpack_manifest_hash: str | None,
    verified_result_hash: str | None,
    issues: list[PackagingIssue],
    allowed_codes: set[str],
) -> Path:
    if not issues:
        raise fail(
            code=AHK4709_PACKAGING_REJECTION_DIAGNOSTIC_INVALID,
            message="rejection diagnostics require at least one issue",
            details={},
            artifact_path=output_root_rel,
            policy_source="packaging_manifest",
        )

    if not taskpack_manifest_hash or not is_sha256(taskpack_manifest_hash):
        taskpack_manifest_hash = _NULL_SHA256
    if not verified_result_hash or not is_sha256(verified_result_hash):
        verified_result_hash = _NULL_SHA256

    normalized_issues: list[dict[str, Any]] = []
    for issue in issues:
        if issue.issue_code not in allowed_codes:
            raise fail(
                code=AHK4709_PACKAGING_REJECTION_DIAGNOSTIC_INVALID,
                message="issue code is not in authoritative diagnostic registry",
                details={"issue_code": issue.issue_code},
                artifact_path=output_root_rel,
                deployment_mode=issue.deployment_mode,
                policy_source=issue.policy_source,
            )
        if issue.policy_source not in POLICY_SOURCE_ENUM_V47:
            raise fail(
                code=AHK4709_PACKAGING_REJECTION_DIAGNOSTIC_INVALID,
                message="issue policy_source is outside frozen enum",
                details={"issue_code": issue.issue_code, "policy_source": issue.policy_source},
                artifact_path=output_root_rel,
                deployment_mode=issue.deployment_mode,
                policy_source="packaging_manifest",
            )

        normalized_artifact_path = normalize_relative_path(issue.artifact_path)
        normalized_issues.append(
            {
                "issue_code": issue.issue_code,
                "reason": issue.reason,
                "artifact_path": normalized_artifact_path,
                "deployment_mode": issue.deployment_mode,
                "policy_source": issue.policy_source,
            }
        )

    normalized_issues.sort(
        key=lambda item: (
            item["issue_code"],
            item["artifact_path"],
            item["deployment_mode"],
            item["policy_source"],
        )
    )

    output_root = safe_join(root, output_root_rel)
    output_root.mkdir(parents=True, exist_ok=True)
    out_path = output_root / f"{taskpack_manifest_hash}_{verified_result_hash}.json"
    payload = {
        "schema": PACKAGING_REJECTION_DIAGNOSTIC_SCHEMA,
        "taskpack_manifest_hash": taskpack_manifest_hash,
        "verified_result_hash": verified_result_hash,
        "issues": normalized_issues,
    }
    write_json(out_path, payload)
    return out_path
