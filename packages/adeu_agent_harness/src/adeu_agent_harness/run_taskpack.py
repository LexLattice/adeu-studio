from __future__ import annotations

import argparse
import contextlib
import http.client
import json
import os
import re
import socket
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterator

from adeu_ir.repo import repo_root
from urm_runtime.hashing import canonical_json, sha256_canonical_json

from .compile import verify_taskpack_bundle

TASKPACK_MANIFEST_SCHEMA = "taskpack/manifest@1"
TASKPACK_ALLOWLIST_SCHEMA = "taskpack/allowlist@1"
TASKPACK_FORBIDDEN_SCHEMA = "taskpack/forbidden@1"
TASKPACK_COMMANDS_SCHEMA = "taskpack/commands@1"
RUNNER_ADAPTER_REGISTRY_SCHEMA = "taskpack_runner_adapter_registry@1"
CANDIDATE_CHANGE_PLAN_SCHEMA = "candidate_change_plan@1"
RUNNER_PROVENANCE_SCHEMA = "taskpack_runner_provenance@1"
RUNNER_RESULT_SCHEMA = "taskpack_runner_result@1"
RUNNER_ERROR_SCHEMA = "taskpack_runner_error@1"
REJECTION_DIAGNOSTIC_SCHEMA = "candidate_change_plan_rejection_diagnostic@1"
DRY_RUN_PREVIEW_SCHEMA = "taskpack_runner_dry_run_preview@1"

_SHA256_PATTERN = re.compile(r"[0-9a-f]{64}")
_HUNK_HEADER_PATTERN = re.compile(
    r"^@@ -(?P<old_start>\d+)(?:,(?P<old_count>\d+))? "
    r"\+(?P<new_start>\d+)(?:,(?P<new_count>\d+))? @@(?: .*)?$"
)

_FORBIDDEN_OPERATION_KINDS_CLOSED_ENUM = ("delete", "rename", "chmod")
_ALLOWED_OPERATION_KINDS = ("create", "update", "delete", "rename", "chmod")
_SUPPORTED_ADAPTER_KINDS = ("candidate_plan_passthrough",)

_AHK1001_PATH_POLICY_VIOLATION = "AHK1001"
_AHK1002_JSON_OBJECT_REQUIRED = "AHK1002"
_AHK1003_SCHEMA_MISMATCH = "AHK1003"
_AHK1004_TASKPACK_COMPONENT_INVALID = "AHK1004"
_AHK1005_ADAPTER_REGISTRY_INVALID = "AHK1005"
_AHK1006_ADAPTER_ID_UNKNOWN = "AHK1006"
_AHK1007_ADAPTER_RESOLUTION_AMBIGUOUS = "AHK1007"
_AHK1008_CANDIDATE_PLAN_INVALID = "AHK1008"
_AHK1009_CANDIDATE_PLAN_NORMALIZATION_DRIFT = "AHK1009"
_AHK1010_CANDIDATE_PLAN_POLICY_VIOLATION = "AHK1010"
_AHK1011_COMMAND_AUTHORITY_VIOLATION = "AHK1011"
_AHK1012_DRY_RUN_POLICY_VIOLATION = "AHK1012"
_AHK1013_PATCH_APPLICATION_FAILED = "AHK1013"
_AHK1014_PROVENANCE_INVALID = "AHK1014"
_AHK1015_NETWORK_GUARD_UNAVAILABLE = "AHK1015"
_AHK1016_REJECTION_DIAGNOSTIC_INVALID = "AHK1016"
_AHK1017_CANDIDATE_PLAN_AST_INVALID = "AHK1017"
_AHK1018_FORBIDDEN_EFFECT_DETECTED = "AHK1018"
_REQUIRED_DETERMINISTIC_ENV = {
    "TZ": "UTC",
    "LC_ALL": "C",
    "PYTHONHASHSEED": "0",
}


@dataclass(frozen=True)
class ParsedHunk:
    old_start: int
    old_count: int
    new_start: int
    new_count: int
    lines: tuple[tuple[str, str], ...]


@dataclass(frozen=True)
class ParsedOperation:
    path: str
    operation_kind: str
    old_header: str
    new_header: str
    unified_diff: str
    hunks: tuple[ParsedHunk, ...]


@dataclass(frozen=True)
class CandidateChangePlan:
    schema: str
    file_operations: tuple[ParsedOperation, ...]
    proposed_commands: tuple[str, ...]
    canonical_payload: dict[str, Any]
    candidate_change_plan_hash: str


@dataclass(frozen=True)
class TaskpackRunnerResult:
    candidate_change_plan_hash: str
    dry_run: bool
    dry_run_preview_path: Path | None
    provenance_path: Path
    provenance_hash: str
    rejection_diagnostic_path: Path | None


@dataclass(frozen=True)
class PolicyIssue:
    issue_code: str
    reason: str
    target_path: str
    hunk_index: int
    line_range: tuple[int, int]
    policy_source: str


class TaskpackRunnerError(RuntimeError):
    def __init__(self, *, code: str, message: str, details: dict[str, Any] | None = None) -> None:
        self.code = code
        self.message = message
        self.details = details or {}
        payload = {
            "schema": RUNNER_ERROR_SCHEMA,
            "code": code,
            "message": message,
            "details": self.details,
        }
        super().__init__(canonical_json(payload))


def _fail(
    *, code: str, message: str, details: dict[str, Any] | None = None
) -> TaskpackRunnerError:
    return TaskpackRunnerError(code=code, message=message, details=details)


def _normalize_relative_path(raw_path: str) -> str:
    path_text = raw_path.strip().replace("\\", "/")
    if not path_text:
        raise _fail(
            code=_AHK1001_PATH_POLICY_VIOLATION,
            message="path must not be empty",
            details={"path": raw_path},
        )
    if path_text.startswith("/"):
        raise _fail(
            code=_AHK1001_PATH_POLICY_VIOLATION,
            message="absolute paths are forbidden",
            details={"path": raw_path},
        )
    if re.match(r"^[A-Za-z]:[\\/]", path_text):
        raise _fail(
            code=_AHK1001_PATH_POLICY_VIOLATION,
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
                    code=_AHK1001_PATH_POLICY_VIOLATION,
                    message="path escapes repository root",
                    details={"path": raw_path},
                )
            segments.pop()
            continue
        segments.append(segment)

    if not segments:
        raise _fail(
            code=_AHK1001_PATH_POLICY_VIOLATION,
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
            code=_AHK1001_PATH_POLICY_VIOLATION,
            message="resolved path escapes repository root",
            details={"path": rel_path},
        ) from exc
    return path


def _load_json_object(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise _fail(
            code=_AHK1001_PATH_POLICY_VIOLATION,
            message="required json path does not exist",
            details={"path": str(path)},
        ) from exc
    except json.JSONDecodeError as exc:
        raise _fail(
            code=_AHK1002_JSON_OBJECT_REQUIRED,
            message="json payload is invalid",
            details={"path": str(path), "error": str(exc)},
        ) from exc
    if not isinstance(payload, dict):
        raise _fail(
            code=_AHK1002_JSON_OBJECT_REQUIRED,
            message="json payload must decode to an object",
            details={"path": str(path)},
        )
    return payload


def _require_schema(payload: dict[str, Any], *, expected_schema: str, path: Path) -> None:
    observed = payload.get("schema")
    if observed != expected_schema:
        raise _fail(
            code=_AHK1003_SCHEMA_MISMATCH,
            message="schema mismatch",
            details={
                "path": str(path),
                "expected_schema": expected_schema,
                "observed_schema": observed,
            },
        )


def _require_string(value: Any, *, field: str, code: str = _AHK1008_CANDIDATE_PLAN_INVALID) -> str:
    if not isinstance(value, str) or not value:
        raise _fail(
            code=code,
            message="required string field is missing or invalid",
            details={"field": field},
        )
    return value


def _is_sha256(value: str) -> bool:
    return bool(_SHA256_PATTERN.fullmatch(value))


def _path_matches_prefix(*, path: str, prefix: str) -> bool:
    return path == prefix or path.startswith(f"{prefix}/")


def _normalize_diff_header_path(raw: str) -> str:
    token = raw.split("\t", 1)[0]
    if " " in token:
        token = token.split(" ", 1)[0]
    if not token:
        raise _fail(
            code=_AHK1008_CANDIDATE_PLAN_INVALID,
            message="diff header path token is empty",
            details={"header": raw},
        )
    return token


def _render_hunk_header(*, old_start: int, old_count: int, new_start: int, new_count: int) -> str:
    return f"@@ -{old_start},{old_count} +{new_start},{new_count} @@"


def _render_unified_diff(*, old_header: str, new_header: str, hunks: tuple[ParsedHunk, ...]) -> str:
    lines = [f"--- {old_header}", f"+++ {new_header}"]
    for hunk in hunks:
        lines.append(
            _render_hunk_header(
                old_start=hunk.old_start,
                old_count=hunk.old_count,
                new_start=hunk.new_start,
                new_count=hunk.new_count,
            )
        )
        for tag, text in hunk.lines:
            lines.append(f"{tag}{text}")
    return "\n".join(lines) + "\n"


def _validate_operation_headers(
    *,
    operation_kind: str,
    normalized_path: str,
    old_header: str,
    new_header: str,
) -> None:
    expected_old = f"a/{normalized_path}"
    expected_new = f"b/{normalized_path}"
    if operation_kind == "create":
        if old_header != "/dev/null" or new_header != expected_new:
            raise _fail(
                code=_AHK1017_CANDIDATE_PLAN_AST_INVALID,
                message="create diff headers must be /dev/null -> b/<path>",
                details={
                    "path": normalized_path,
                    "old_header": old_header,
                    "new_header": new_header,
                },
            )
        return
    if operation_kind == "delete":
        if old_header != expected_old or new_header != "/dev/null":
            raise _fail(
                code=_AHK1017_CANDIDATE_PLAN_AST_INVALID,
                message="delete diff headers must be a/<path> -> /dev/null",
                details={
                    "path": normalized_path,
                    "old_header": old_header,
                    "new_header": new_header,
                },
            )
        return
    if operation_kind in ("update", "chmod"):
        if old_header != expected_old or new_header != expected_new:
            raise _fail(
                code=_AHK1017_CANDIDATE_PLAN_AST_INVALID,
                message="update/chmod diff headers must be a/<path> -> b/<path>",
                details={
                    "path": normalized_path,
                    "old_header": old_header,
                    "new_header": new_header,
                },
            )
        return
    if operation_kind == "rename":
        if not old_header.startswith("a/") or not new_header.startswith("b/"):
            raise _fail(
                code=_AHK1017_CANDIDATE_PLAN_AST_INVALID,
                message="rename diff headers must use a/<old> and b/<new>",
                details={
                    "path": normalized_path,
                    "old_header": old_header,
                    "new_header": new_header,
                },
            )
        if old_header == new_header:
            raise _fail(
                code=_AHK1017_CANDIDATE_PLAN_AST_INVALID,
                message="rename diff headers must not be identical",
                details={
                    "path": normalized_path,
                    "old_header": old_header,
                    "new_header": new_header,
                },
            )
        return
    raise _fail(
        code=_AHK1008_CANDIDATE_PLAN_INVALID,
        message="operation_kind is unsupported",
        details={"operation_kind": operation_kind},
    )


def _parse_unified_diff(
    *,
    normalized_path: str,
    operation_kind: str,
    raw_diff: str,
) -> tuple[str, str, tuple[ParsedHunk, ...], str]:
    normalized_text = raw_diff.replace("\r\n", "\n").replace("\r", "\n")
    if "\x00" in normalized_text:
        raise _fail(
            code=_AHK1009_CANDIDATE_PLAN_NORMALIZATION_DRIFT,
            message="unified diff contains NUL bytes",
            details={"path": normalized_path, "operation_kind": operation_kind},
        )

    lines = normalized_text.split("\n")
    if lines and lines[-1] == "":
        lines = lines[:-1]
    if len(lines) < 3:
        raise _fail(
            code=_AHK1017_CANDIDATE_PLAN_AST_INVALID,
            message="unified diff must include headers and at least one hunk",
            details={"path": normalized_path, "operation_kind": operation_kind},
        )
    if not lines[0].startswith("--- ") or not lines[1].startswith("+++ "):
        raise _fail(
            code=_AHK1017_CANDIDATE_PLAN_AST_INVALID,
            message="unified diff must start with ---/+++ headers",
            details={"path": normalized_path, "operation_kind": operation_kind},
        )

    old_header = _normalize_diff_header_path(lines[0][4:])
    new_header = _normalize_diff_header_path(lines[1][4:])
    _validate_operation_headers(
        operation_kind=operation_kind,
        normalized_path=normalized_path,
        old_header=old_header,
        new_header=new_header,
    )

    parsed_hunks: list[ParsedHunk] = []
    cursor = 2
    while cursor < len(lines):
        header = lines[cursor]
        match = _HUNK_HEADER_PATTERN.fullmatch(header)
        if match is None:
            raise _fail(
                code=_AHK1017_CANDIDATE_PLAN_AST_INVALID,
                message="invalid hunk header in unified diff",
                details={
                    "path": normalized_path,
                    "operation_kind": operation_kind,
                    "line": cursor + 1,
                    "value": header,
                },
            )

        old_start = int(match.group("old_start"))
        old_count = int(match.group("old_count") or "1")
        new_start = int(match.group("new_start"))
        new_count = int(match.group("new_count") or "1")
        cursor += 1

        hunk_lines: list[tuple[str, str]] = []
        while cursor < len(lines):
            line = lines[cursor]
            if _HUNK_HEADER_PATTERN.fullmatch(line):
                break
            if line == r"\ No newline at end of file":
                raise _fail(
                    code=_AHK1017_CANDIDATE_PLAN_AST_INVALID,
                    message="diff no-newline marker is unsupported in v45",
                    details={
                        "path": normalized_path,
                        "operation_kind": operation_kind,
                        "line": cursor + 1,
                    },
                )
            if not line or line[0] not in (" ", "+", "-"):
                raise _fail(
                    code=_AHK1017_CANDIDATE_PLAN_AST_INVALID,
                    message="invalid hunk body line in unified diff",
                    details={
                        "path": normalized_path,
                        "operation_kind": operation_kind,
                        "line": cursor + 1,
                        "value": line,
                    },
                )
            hunk_lines.append((line[0], line[1:]))
            cursor += 1

        if not hunk_lines:
            raise _fail(
                code=_AHK1017_CANDIDATE_PLAN_AST_INVALID,
                message="hunk body must not be empty",
                details={"path": normalized_path, "operation_kind": operation_kind},
            )

        observed_old = sum(1 for tag, _ in hunk_lines if tag in (" ", "-"))
        observed_new = sum(1 for tag, _ in hunk_lines if tag in (" ", "+"))
        if observed_old != old_count or observed_new != new_count:
            raise _fail(
                code=_AHK1017_CANDIDATE_PLAN_AST_INVALID,
                message="hunk line counts do not match header counts",
                details={
                    "path": normalized_path,
                    "operation_kind": operation_kind,
                    "old_count_header": old_count,
                    "old_count_observed": observed_old,
                    "new_count_header": new_count,
                    "new_count_observed": observed_new,
                },
            )

        parsed_hunks.append(
            ParsedHunk(
                old_start=old_start,
                old_count=old_count,
                new_start=new_start,
                new_count=new_count,
                lines=tuple(hunk_lines),
            )
        )

    if not parsed_hunks:
        raise _fail(
            code=_AHK1017_CANDIDATE_PLAN_AST_INVALID,
            message="unified diff must contain at least one hunk",
            details={"path": normalized_path, "operation_kind": operation_kind},
        )

    last_old_end = 0
    for hunk in parsed_hunks:
        if hunk.old_count <= 0:
            continue
        old_end = hunk.old_start + hunk.old_count - 1
        if hunk.old_start <= last_old_end:
            raise _fail(
                code=_AHK1017_CANDIDATE_PLAN_AST_INVALID,
                message="overlapping hunks are forbidden",
                details={
                    "path": normalized_path,
                    "operation_kind": operation_kind,
                    "previous_old_end": last_old_end,
                    "current_old_start": hunk.old_start,
                },
            )
        last_old_end = old_end

    normalized_diff = _render_unified_diff(
        old_header=old_header,
        new_header=new_header,
        hunks=tuple(parsed_hunks),
    )
    return old_header, new_header, tuple(parsed_hunks), normalized_diff


def _load_candidate_change_plan(path: Path) -> CandidateChangePlan:
    payload = _load_json_object(path)
    _require_schema(payload, expected_schema=CANDIDATE_CHANGE_PLAN_SCHEMA, path=path)

    if set(payload.keys()) != {"schema", "file_operations", "proposed_commands"}:
        raise _fail(
            code=_AHK1008_CANDIDATE_PLAN_INVALID,
            message="candidate change plan keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
        )

    file_operations_raw = payload.get("file_operations")
    if not isinstance(file_operations_raw, list) or not file_operations_raw:
        raise _fail(
            code=_AHK1008_CANDIDATE_PLAN_INVALID,
            message="file_operations must be a non-empty array",
            details={"path": str(path)},
        )

    parsed_operations: list[ParsedOperation] = []
    for index, operation in enumerate(file_operations_raw):
        if not isinstance(operation, dict):
            raise _fail(
                code=_AHK1008_CANDIDATE_PLAN_INVALID,
                message="file operation entry must be an object",
                details={"path": str(path), "index": index},
            )
        if set(operation.keys()) != {"path", "operation_kind", "unified_diff"}:
            raise _fail(
                code=_AHK1008_CANDIDATE_PLAN_INVALID,
                message="file operation keys must match frozen grammar",
                details={"path": str(path), "index": index, "keys": sorted(operation.keys())},
            )

        normalized_path = _normalize_relative_path(
            _require_string(operation.get("path"), field="path")
        )
        operation_kind = _require_string(operation.get("operation_kind"), field="operation_kind")
        if operation_kind not in _ALLOWED_OPERATION_KINDS:
            raise _fail(
                code=_AHK1008_CANDIDATE_PLAN_INVALID,
                message="operation_kind is not allowed",
                details={
                    "path": str(path),
                    "index": index,
                    "operation_kind": operation_kind,
                },
            )
        raw_diff = _require_string(operation.get("unified_diff"), field="unified_diff")
        old_header, new_header, hunks, normalized_diff = _parse_unified_diff(
            normalized_path=normalized_path,
            operation_kind=operation_kind,
            raw_diff=raw_diff,
        )
        parsed_operations.append(
            ParsedOperation(
                path=normalized_path,
                operation_kind=operation_kind,
                old_header=old_header,
                new_header=new_header,
                unified_diff=normalized_diff,
                hunks=hunks,
            )
        )

    proposed_commands_raw = payload.get("proposed_commands")
    if not isinstance(proposed_commands_raw, list):
        raise _fail(
            code=_AHK1008_CANDIDATE_PLAN_INVALID,
            message="proposed_commands must be an array",
            details={"path": str(path)},
        )
    proposed_commands: list[str] = []
    for index, command in enumerate(proposed_commands_raw):
        if not isinstance(command, str) or not command.strip():
            raise _fail(
                code=_AHK1008_CANDIDATE_PLAN_INVALID,
                message="proposed command must be a non-empty string",
                details={"path": str(path), "index": index},
            )
        proposed_commands.append(command.strip())

    if len(set(proposed_commands)) != len(proposed_commands):
        raise _fail(
            code=_AHK1008_CANDIDATE_PLAN_INVALID,
            message="proposed command values must be unique",
            details={"path": str(path)},
        )

    parsed_operations.sort(key=lambda item: (item.path, item.operation_kind))
    proposed_commands_sorted = tuple(sorted(proposed_commands))
    canonical_payload = {
        "schema": CANDIDATE_CHANGE_PLAN_SCHEMA,
        "file_operations": [
            {
                "path": operation.path,
                "operation_kind": operation.operation_kind,
                "unified_diff": operation.unified_diff,
            }
            for operation in parsed_operations
        ],
        "proposed_commands": list(proposed_commands_sorted),
    }
    candidate_hash = sha256_canonical_json(canonical_payload)

    return CandidateChangePlan(
        schema=CANDIDATE_CHANGE_PLAN_SCHEMA,
        file_operations=tuple(parsed_operations),
        proposed_commands=proposed_commands_sorted,
        canonical_payload=canonical_payload,
        candidate_change_plan_hash=candidate_hash,
    )


def _load_allowlist_payload(path: Path) -> list[str]:
    payload = _load_json_object(path)
    _require_schema(payload, expected_schema=TASKPACK_ALLOWLIST_SCHEMA, path=path)
    if set(payload.keys()) != {"schema", "profile_id", "path_policy", "paths"}:
        raise _fail(
            code=_AHK1004_TASKPACK_COMPONENT_INVALID,
            message="ALLOWLIST payload keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
        )
    if payload.get("path_policy") != "repo_relative_only":
        raise _fail(
            code=_AHK1004_TASKPACK_COMPONENT_INVALID,
            message="ALLOWLIST path_policy mismatch",
            details={"path": str(path), "path_policy": payload.get("path_policy")},
        )
    paths_raw = payload.get("paths")
    if not isinstance(paths_raw, list) or not paths_raw:
        raise _fail(
            code=_AHK1004_TASKPACK_COMPONENT_INVALID,
            message="ALLOWLIST paths must be a non-empty array",
            details={"path": str(path)},
        )
    normalized = [
        _normalize_relative_path(_require_string(item, field="paths[]"))
        for item in paths_raw
    ]
    return sorted(set(normalized))


def _load_forbidden_payload(path: Path) -> tuple[list[str], list[str], tuple[str, ...]]:
    payload = _load_json_object(path)
    _require_schema(payload, expected_schema=TASKPACK_FORBIDDEN_SCHEMA, path=path)
    payload_keys = set(payload.keys())
    allowed_keys = {"schema", "profile_id", "paths", "effects", "operation_kinds"}
    if not payload_keys.issubset(allowed_keys):
        raise _fail(
            code=_AHK1004_TASKPACK_COMPONENT_INVALID,
            message="FORBIDDEN payload contains unsupported keys",
            details={"path": str(path), "keys": sorted(payload_keys)},
        )
    if not {"schema", "profile_id", "paths", "effects"}.issubset(payload_keys):
        raise _fail(
            code=_AHK1004_TASKPACK_COMPONENT_INVALID,
            message="FORBIDDEN payload is missing required keys",
            details={"path": str(path), "keys": sorted(payload_keys)},
        )

    paths_raw = payload.get("paths")
    effects_raw = payload.get("effects")
    if not isinstance(paths_raw, list) or not isinstance(effects_raw, list):
        raise _fail(
            code=_AHK1004_TASKPACK_COMPONENT_INVALID,
            message="FORBIDDEN paths/effects must be arrays",
            details={"path": str(path)},
        )
    normalized_paths = [
        _normalize_relative_path(_require_string(item, field="paths[]")) for item in paths_raw
    ]
    normalized_effects = sorted(
        set(_require_string(item, field="effects[]") for item in effects_raw)
    )

    operation_kinds_raw = payload.get("operation_kinds")
    if operation_kinds_raw is None:
        forbidden_operation_kinds = _FORBIDDEN_OPERATION_KINDS_CLOSED_ENUM
    else:
        if not isinstance(operation_kinds_raw, list):
            raise _fail(
                code=_AHK1004_TASKPACK_COMPONENT_INVALID,
                message="FORBIDDEN operation_kinds must be an array",
                details={"path": str(path)},
            )
        values = tuple(
            sorted(
                set(
                    _require_string(item, field="operation_kinds[]")
                    for item in operation_kinds_raw
                )
            )
        )
        for value in values:
            if value not in _FORBIDDEN_OPERATION_KINDS_CLOSED_ENUM:
                raise _fail(
                    code=_AHK1004_TASKPACK_COMPONENT_INVALID,
                    message="FORBIDDEN operation_kinds contains unsupported value",
                    details={"path": str(path), "operation_kind": value},
                )
        forbidden_operation_kinds = values

    return (
        sorted(set(normalized_paths)),
        normalized_effects,
        tuple(forbidden_operation_kinds),
    )


def _load_commands_payload(path: Path) -> tuple[dict[str, str], dict[str, dict[str, Any]]]:
    payload = _load_json_object(path)
    _require_schema(payload, expected_schema=TASKPACK_COMMANDS_SCHEMA, path=path)
    if set(payload.keys()) != {"schema", "profile_id", "deterministic_env", "commands"}:
        raise _fail(
            code=_AHK1004_TASKPACK_COMPONENT_INVALID,
            message="COMMANDS payload keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
        )

    deterministic_env_raw = payload.get("deterministic_env")
    if not isinstance(deterministic_env_raw, dict):
        raise _fail(
            code=_AHK1004_TASKPACK_COMPONENT_INVALID,
            message="COMMANDS deterministic_env must be an object",
            details={"path": str(path)},
        )
    deterministic_env: dict[str, str] = {}
    for key in sorted(deterministic_env_raw.keys()):
        value = deterministic_env_raw[key]
        if not isinstance(key, str) or not key or not isinstance(value, str):
            raise _fail(
                code=_AHK1004_TASKPACK_COMPONENT_INVALID,
                message="COMMANDS deterministic_env entries must be string:string",
                details={"path": str(path)},
            )
        deterministic_env[key] = value
    if deterministic_env != _REQUIRED_DETERMINISTIC_ENV:
        raise _fail(
            code=_AHK1004_TASKPACK_COMPONENT_INVALID,
            message="COMMANDS deterministic_env must match frozen deterministic env contract",
            details={
                "path": str(path),
                "required_deterministic_env": _REQUIRED_DETERMINISTIC_ENV,
                "observed_deterministic_env": deterministic_env,
            },
        )

    commands_raw = payload.get("commands")
    if not isinstance(commands_raw, list) or not commands_raw:
        raise _fail(
            code=_AHK1004_TASKPACK_COMPONENT_INVALID,
            message="COMMANDS commands must be a non-empty array",
            details={"path": str(path)},
        )

    commands_by_run: dict[str, dict[str, Any]] = {}
    for index, command in enumerate(commands_raw):
        if not isinstance(command, dict):
            raise _fail(
                code=_AHK1004_TASKPACK_COMPONENT_INVALID,
                message="command entry must be an object",
                details={"path": str(path), "index": index},
            )
        if set(command.keys()) != {
            "command_id",
            "run",
            "working_directory_or_repo_root",
            "env_overrides",
        }:
            raise _fail(
                code=_AHK1004_TASKPACK_COMPONENT_INVALID,
                message="command entry keys must match frozen grammar",
                details={"path": str(path), "index": index, "keys": sorted(command.keys())},
            )
        run = _require_string(
            command.get("run"),
            field="run",
            code=_AHK1004_TASKPACK_COMPONENT_INVALID,
        ).strip()
        if run in commands_by_run:
            raise _fail(
                code=_AHK1004_TASKPACK_COMPONENT_INVALID,
                message="command run values must be unique",
                details={"path": str(path), "run": run},
            )
        working_dir = _require_string(
            command.get("working_directory_or_repo_root"),
            field="working_directory_or_repo_root",
            code=_AHK1004_TASKPACK_COMPONENT_INVALID,
        )
        if working_dir != "repo_root":
            working_dir = _normalize_relative_path(working_dir)

        env_overrides_raw = command.get("env_overrides")
        if not isinstance(env_overrides_raw, dict):
            raise _fail(
                code=_AHK1004_TASKPACK_COMPONENT_INVALID,
                message="command env_overrides must be an object",
                details={"path": str(path), "run": run},
            )
        env_overrides: dict[str, str] = {}
        for key in sorted(env_overrides_raw.keys()):
            value = env_overrides_raw[key]
            if not isinstance(key, str) or not key or not isinstance(value, str):
                raise _fail(
                    code=_AHK1004_TASKPACK_COMPONENT_INVALID,
                    message="command env_overrides entries must be string:string",
                    details={"path": str(path), "run": run},
                )
            if key in _REQUIRED_DETERMINISTIC_ENV and value != _REQUIRED_DETERMINISTIC_ENV[key]:
                raise _fail(
                    code=_AHK1004_TASKPACK_COMPONENT_INVALID,
                    message="command env_overrides may not drift frozen deterministic env values",
                    details={
                        "path": str(path),
                        "run": run,
                        "env_key": key,
                        "required_value": _REQUIRED_DETERMINISTIC_ENV[key],
                        "observed_value": value,
                    },
                )
            env_overrides[key] = value

        commands_by_run[run] = {
            "command_id": _require_string(
                command.get("command_id"),
                field="command_id",
                code=_AHK1004_TASKPACK_COMPONENT_INVALID,
            ),
            "run": run,
            "working_directory_or_repo_root": working_dir,
            "env_overrides": env_overrides,
        }

    return deterministic_env, commands_by_run


def _load_adapter_registry(path: Path) -> list[dict[str, str]]:
    payload = _load_json_object(path)
    _require_schema(payload, expected_schema=RUNNER_ADAPTER_REGISTRY_SCHEMA, path=path)
    if set(payload.keys()) != {"schema", "adapters"}:
        raise _fail(
            code=_AHK1005_ADAPTER_REGISTRY_INVALID,
            message="adapter registry keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload.keys())},
        )

    adapters_raw = payload.get("adapters")
    if not isinstance(adapters_raw, list) or not adapters_raw:
        raise _fail(
            code=_AHK1005_ADAPTER_REGISTRY_INVALID,
            message="adapter registry adapters must be a non-empty array",
            details={"path": str(path)},
        )

    adapters: list[dict[str, str]] = []
    seen_ids: set[str] = set()
    for index, entry in enumerate(adapters_raw):
        if not isinstance(entry, dict):
            raise _fail(
                code=_AHK1005_ADAPTER_REGISTRY_INVALID,
                message="adapter registry entry must be an object",
                details={"path": str(path), "index": index},
            )
        if set(entry.keys()) != {"adapter_id", "adapter_kind"}:
            raise _fail(
                code=_AHK1005_ADAPTER_REGISTRY_INVALID,
                message="adapter registry entry keys must match frozen grammar",
                details={"path": str(path), "index": index, "keys": sorted(entry.keys())},
            )
        adapter_id = _require_string(
            entry.get("adapter_id"),
            field="adapter_id",
            code=_AHK1005_ADAPTER_REGISTRY_INVALID,
        )
        adapter_kind = _require_string(
            entry.get("adapter_kind"),
            field="adapter_kind",
            code=_AHK1005_ADAPTER_REGISTRY_INVALID,
        )
        if adapter_kind not in _SUPPORTED_ADAPTER_KINDS:
            raise _fail(
                code=_AHK1005_ADAPTER_REGISTRY_INVALID,
                message="adapter registry entry has unsupported adapter_kind",
                details={"path": str(path), "adapter_kind": adapter_kind},
            )
        if adapter_id in seen_ids:
            raise _fail(
                code=_AHK1007_ADAPTER_RESOLUTION_AMBIGUOUS,
                message="adapter registry contains duplicate adapter_id",
                details={"path": str(path), "adapter_id": adapter_id},
            )
        seen_ids.add(adapter_id)
        adapters.append({"adapter_id": adapter_id, "adapter_kind": adapter_kind})

    adapter_ids = [entry["adapter_id"] for entry in adapters]
    if adapter_ids != sorted(adapter_ids):
        raise _fail(
            code=_AHK1005_ADAPTER_REGISTRY_INVALID,
            message="adapter registry adapter_id order must be deterministic lexicographic",
            details={"path": str(path), "adapter_ids": adapter_ids},
        )
    return adapters


def _select_adapter(*, adapters: list[dict[str, str]], adapter_id: str) -> dict[str, str]:
    matches = [entry for entry in adapters if entry["adapter_id"] == adapter_id]
    if len(matches) > 1:
        raise _fail(
            code=_AHK1007_ADAPTER_RESOLUTION_AMBIGUOUS,
            message="adapter selection is ambiguous",
            details={"adapter_id": adapter_id, "match_count": len(matches)},
        )
    if not matches:
        raise _fail(
            code=_AHK1006_ADAPTER_ID_UNKNOWN,
            message="adapter_id is not present in adapter registry",
            details={"adapter_id": adapter_id},
        )
    return matches[0]


@contextlib.contextmanager
def _dry_run_network_guard() -> Iterator[None]:
    original_socket = socket.socket
    original_create_connection = socket.create_connection
    original_http = http.client.HTTPConnection
    original_https = http.client.HTTPSConnection

    def _blocked_socket(*_: Any, **__: Any) -> socket.socket:
        raise _fail(
            code=_AHK1012_DRY_RUN_POLICY_VIOLATION,
            message="dry-run outbound socket creation is forbidden",
            details={"guard": "socket"},
        )

    def _blocked_create_connection(*_: Any, **__: Any) -> socket.socket:
        raise _fail(
            code=_AHK1012_DRY_RUN_POLICY_VIOLATION,
            message="dry-run outbound network connection is forbidden",
            details={"guard": "create_connection"},
        )

    class _BlockedHTTPConnection:  # pragma: no cover - exercised via behavior, not internals.
        def __init__(self, *args: Any, **kwargs: Any) -> None:
            del args, kwargs
            raise _fail(
                code=_AHK1012_DRY_RUN_POLICY_VIOLATION,
                message="dry-run outbound HTTP client calls are forbidden",
                details={"guard": "http_client"},
            )

    try:
        socket.socket = _blocked_socket  # type: ignore[assignment]
        socket.create_connection = _blocked_create_connection  # type: ignore[assignment]
        http.client.HTTPConnection = _BlockedHTTPConnection  # type: ignore[assignment]
        http.client.HTTPSConnection = _BlockedHTTPConnection  # type: ignore[assignment]
    except Exception as exc:  # pragma: no cover - defensive.
        raise _fail(
            code=_AHK1015_NETWORK_GUARD_UNAVAILABLE,
            message="failed to initialize dry-run network guard",
            details={"error": str(exc)},
        ) from exc

    try:
        yield
    finally:
        socket.socket = original_socket  # type: ignore[assignment]
        socket.create_connection = original_create_connection  # type: ignore[assignment]
        http.client.HTTPConnection = original_http  # type: ignore[assignment]
        http.client.HTTPSConnection = original_https  # type: ignore[assignment]


def _validate_policy(
    *,
    plan: CandidateChangePlan,
    allowlist_paths: list[str],
    forbidden_paths: list[str],
    forbidden_operation_kinds: tuple[str, ...],
    allowed_commands: dict[str, dict[str, Any]],
    dry_run: bool,
) -> list[PolicyIssue]:
    def _issue_location(operation: ParsedOperation) -> tuple[int, tuple[int, int]]:
        if not operation.hunks:
            return -1, (0, 0)
        first_hunk = operation.hunks[0]
        start = first_hunk.old_start
        end = start + max(first_hunk.old_count - 1, 0)
        return 0, (start, end)

    issues: list[PolicyIssue] = []
    for operation in plan.file_operations:
        hunk_index, line_range = _issue_location(operation)
        if not any(
            _path_matches_prefix(path=operation.path, prefix=allow_prefix)
            for allow_prefix in allowlist_paths
        ):
            issues.append(
                PolicyIssue(
                    issue_code="allowlist_violation",
                    reason="operation path is not under allowlist paths",
                    target_path=operation.path,
                    hunk_index=hunk_index,
                    line_range=line_range,
                    policy_source="ALLOWLIST.json",
                )
            )
        if any(
            _path_matches_prefix(path=operation.path, prefix=forbidden_prefix)
            for forbidden_prefix in forbidden_paths
        ):
            issues.append(
                PolicyIssue(
                    issue_code="forbidden_path_violation",
                    reason="operation path is under forbidden paths",
                    target_path=operation.path,
                    hunk_index=hunk_index,
                    line_range=line_range,
                    policy_source="FORBIDDEN.json",
                )
            )
        if operation.operation_kind in forbidden_operation_kinds:
            issues.append(
                PolicyIssue(
                    issue_code="forbidden_operation_kind",
                    reason="operation kind is forbidden in v45 policy scope",
                    target_path=operation.path,
                    hunk_index=hunk_index,
                    line_range=line_range,
                    policy_source="FORBIDDEN.json",
                )
            )

    allowed_command_runs = set(allowed_commands.keys())
    for command in plan.proposed_commands:
        if command not in allowed_command_runs:
            issues.append(
                PolicyIssue(
                    issue_code="model_suggested_command_execution_detected",
                    reason="proposed command is not present in COMMANDS.json authority",
                    target_path="COMMANDS.json",
                    hunk_index=-1,
                    line_range=(0, 0),
                    policy_source="COMMANDS.json",
                )
            )
    if dry_run and plan.proposed_commands:
        issues.append(
            PolicyIssue(
                issue_code="dry_run_subprocess_execution_detected",
                reason="dry-run forbids subprocess execution in v45",
                target_path="COMMANDS.json",
                hunk_index=-1,
                line_range=(0, 0),
                policy_source="dry_run_enforcement_policy",
            )
        )
    return sorted(
        issues,
        key=lambda row: (row.issue_code, row.target_path, row.hunk_index),
    )


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(canonical_json(payload) + "\n", encoding="utf-8")


def _emit_rejection_diagnostics(
    *,
    root: Path,
    plan: CandidateChangePlan,
    taskpack_manifest_hash: str,
    issues: list[PolicyIssue],
    dry_run: bool,
    preview_root: str,
) -> Path:
    if not issues:
        raise _fail(
            code=_AHK1016_REJECTION_DIAGNOSTIC_INVALID,
            message="rejection diagnostics requested without policy issues",
            details={},
        )

    if dry_run:
        diagnostics_dir = _safe_join(root, f"{preview_root}/rejections")
    else:
        diagnostics_dir = _safe_join(root, "artifacts/agent_harness/v45/rejections")
    diagnostics_path = (
        diagnostics_dir / f"{taskpack_manifest_hash}_{plan.candidate_change_plan_hash}.json"
    )

    payload = {
        "schema": REJECTION_DIAGNOSTIC_SCHEMA,
        "taskpack_manifest_hash": taskpack_manifest_hash,
        "candidate_change_plan_hash": plan.candidate_change_plan_hash,
        "issues": [
            {
                "issue_code": issue.issue_code,
                "reason": issue.reason,
                "target_path": issue.target_path,
                "hunk_index": issue.hunk_index,
                "line_range": [issue.line_range[0], issue.line_range[1]],
                "policy_source": issue.policy_source,
            }
            for issue in issues
        ],
    }
    _write_json(diagnostics_path, payload)

    loaded = _load_json_object(diagnostics_path)
    _require_schema(loaded, expected_schema=REJECTION_DIAGNOSTIC_SCHEMA, path=diagnostics_path)
    issues_raw = loaded.get("issues")
    if not isinstance(issues_raw, list) or not issues_raw:
        raise _fail(
            code=_AHK1016_REJECTION_DIAGNOSTIC_INVALID,
            message="rejection diagnostics issues must be a non-empty array",
            details={"path": str(diagnostics_path)},
        )
    return diagnostics_path


def _lines_from_file(path: Path) -> list[str]:
    if not path.exists():
        return []
    content = path.read_text(encoding="utf-8")
    return content.splitlines()


def _render_lines(lines: list[str]) -> str:
    if not lines:
        return ""
    return "\n".join(lines) + "\n"


def _apply_hunks_to_lines(
    *,
    old_lines: list[str],
    hunks: tuple[ParsedHunk, ...],
    operation: ParsedOperation,
) -> list[str]:
    cursor = 0
    new_lines: list[str] = []

    for hunk_index, hunk in enumerate(hunks):
        hunk_start_index = max(hunk.old_start - 1, 0)
        if hunk_start_index < cursor:
            raise _fail(
                code=_AHK1013_PATCH_APPLICATION_FAILED,
                message="hunk overlaps previously consumed source region",
                details={
                    "path": operation.path,
                    "hunk_index": hunk_index,
                    "old_start": hunk.old_start,
                },
            )
        if hunk_start_index > len(old_lines):
            raise _fail(
                code=_AHK1013_PATCH_APPLICATION_FAILED,
                message="hunk start exceeds source length",
                details={
                    "path": operation.path,
                    "hunk_index": hunk_index,
                    "old_start": hunk.old_start,
                    "source_line_count": len(old_lines),
                },
            )

        new_lines.extend(old_lines[cursor:hunk_start_index])
        source_index = hunk_start_index
        for tag, text in hunk.lines:
            if tag in (" ", "-"):
                if source_index >= len(old_lines) or old_lines[source_index] != text:
                    raise _fail(
                        code=_AHK1013_PATCH_APPLICATION_FAILED,
                        message="hunk source line does not match canonical source",
                        details={
                            "path": operation.path,
                            "hunk_index": hunk_index,
                            "source_index": source_index,
                            "expected_line": text,
                        },
                    )
                if tag == " ":
                    new_lines.append(text)
                source_index += 1
                continue
            if tag == "+":
                new_lines.append(text)
                continue
            raise _fail(
                code=_AHK1013_PATCH_APPLICATION_FAILED,
                message="invalid diff line tag encountered during apply",
                details={
                    "path": operation.path,
                    "hunk_index": hunk_index,
                    "tag": tag,
                },
            )

        consumed_source = source_index - hunk_start_index
        if consumed_source != hunk.old_count:
            raise _fail(
                code=_AHK1013_PATCH_APPLICATION_FAILED,
                message="hunk old_count mismatch during apply",
                details={
                    "path": operation.path,
                    "hunk_index": hunk_index,
                    "expected_old_count": hunk.old_count,
                    "observed_old_count": consumed_source,
                },
            )
        cursor = source_index

    new_lines.extend(old_lines[cursor:])
    return new_lines


def _apply_candidate_plan(*, root: Path, plan: CandidateChangePlan) -> None:
    for operation in plan.file_operations:
        target_path = _safe_join(root, operation.path)
        if operation.operation_kind in ("rename", "chmod"):
            raise _fail(
                code=_AHK1018_FORBIDDEN_EFFECT_DETECTED,
                message="operation kind is outside v45 apply scope",
                details={
                    "path": operation.path,
                    "operation_kind": operation.operation_kind,
                },
            )

        old_lines = _lines_from_file(target_path)
        if operation.operation_kind == "create" and target_path.exists():
            raise _fail(
                code=_AHK1013_PATCH_APPLICATION_FAILED,
                message="create operation target already exists",
                details={"path": operation.path},
            )
        if operation.operation_kind in ("update", "delete") and not target_path.exists():
            raise _fail(
                code=_AHK1013_PATCH_APPLICATION_FAILED,
                message="update/delete operation target does not exist",
                details={"path": operation.path},
            )

        patched_lines = _apply_hunks_to_lines(
            old_lines=old_lines,
            hunks=operation.hunks,
            operation=operation,
        )

        if operation.operation_kind == "delete":
            if patched_lines:
                raise _fail(
                    code=_AHK1013_PATCH_APPLICATION_FAILED,
                    message="delete operation must produce empty target content",
                    details={"path": operation.path},
                )
            target_path.unlink()
            continue

        target_path.parent.mkdir(parents=True, exist_ok=True)
        target_path.write_text(_render_lines(patched_lines), encoding="utf-8")


def _execute_authorized_commands(
    *,
    root: Path,
    proposed_commands: tuple[str, ...],
    deterministic_env: dict[str, str],
    commands_by_run: dict[str, dict[str, Any]],
    dry_run: bool,
) -> None:
    if dry_run and proposed_commands:
        raise _fail(
            code=_AHK1012_DRY_RUN_POLICY_VIOLATION,
            message="dry-run forbids subprocess execution",
            details={"proposed_commands_count": len(proposed_commands)},
        )
    for run in proposed_commands:
        if run not in commands_by_run:
            raise _fail(
                code=_AHK1011_COMMAND_AUTHORITY_VIOLATION,
                message="proposed command is not present in COMMANDS.json authority",
                details={"run": run},
            )
        command = commands_by_run[run]
        working_dir = command["working_directory_or_repo_root"]
        cwd = root if working_dir == "repo_root" else _safe_join(root, working_dir)
        env = os.environ.copy()
        env.update(deterministic_env)
        env.update(dict(command["env_overrides"]))
        subprocess_run = getattr(subprocess, "run", None)
        if not callable(subprocess_run):
            raise _fail(
                code=_AHK1011_COMMAND_AUTHORITY_VIOLATION,
                message="command execution interception is unavailable",
                details={"run": run},
            )
        try:
            process = subprocess_run(
                run,
                shell=True,
                cwd=cwd,
                env=env,
                check=False,
                capture_output=True,
                text=True,
            )
        except Exception as exc:
            raise _fail(
                code=_AHK1011_COMMAND_AUTHORITY_VIOLATION,
                message="command execution interception failed",
                details={"run": run, "error": str(exc)},
            ) from exc
        if process.returncode != 0:
            raise _fail(
                code=_AHK1011_COMMAND_AUTHORITY_VIOLATION,
                message="authorized command failed",
                details={
                    "run": run,
                    "returncode": process.returncode,
                    "stdout": process.stdout,
                    "stderr": process.stderr,
                },
            )


def _emit_dry_run_preview(
    *,
    root: Path,
    preview_root: str,
    taskpack_manifest_hash: str,
    adapter_id: str,
    plan: CandidateChangePlan,
) -> Path:
    preview_dir = _safe_join(root, preview_root)
    preview_path = preview_dir / f"{taskpack_manifest_hash}_{plan.candidate_change_plan_hash}.json"
    payload = {
        "schema": DRY_RUN_PREVIEW_SCHEMA,
        "taskpack_manifest_hash": taskpack_manifest_hash,
        "adapter_id": adapter_id,
        "candidate_change_plan_hash": plan.candidate_change_plan_hash,
        "candidate_change_plan": plan.canonical_payload,
    }
    _write_json(preview_path, payload)
    return preview_path


def _emit_provenance(
    *,
    root: Path,
    dry_run: bool,
    preview_root: str,
    taskpack_manifest_hash: str,
    adapter_id: str,
    plan: CandidateChangePlan,
    policy_validation_result: dict[str, Any],
    exit_status: str,
) -> tuple[Path, str]:
    payload = {
        "schema": RUNNER_PROVENANCE_SCHEMA,
        "taskpack_manifest_hash": taskpack_manifest_hash,
        "adapter_id": adapter_id,
        "candidate_change_plan_hash": plan.candidate_change_plan_hash,
        "policy_validation_result": policy_validation_result,
        "exit_status": exit_status,
    }
    hashed_subject = {
        "taskpack_manifest_hash": payload["taskpack_manifest_hash"],
        "adapter_id": payload["adapter_id"],
        "candidate_change_plan_hash": payload["candidate_change_plan_hash"],
        "policy_validation_result": payload["policy_validation_result"],
        "exit_status": payload["exit_status"],
    }
    provenance_hash = sha256_canonical_json(hashed_subject)
    payload["provenance_hash"] = provenance_hash

    if dry_run:
        provenance_dir = _safe_join(root, f"{preview_root}/provenance")
    else:
        provenance_dir = _safe_join(root, "artifacts/agent_harness/v45/provenance")
    provenance_path = (
        provenance_dir / f"{taskpack_manifest_hash}_{plan.candidate_change_plan_hash}.json"
    )
    _write_json(provenance_path, payload)

    loaded = _load_json_object(provenance_path)
    _require_schema(loaded, expected_schema=RUNNER_PROVENANCE_SCHEMA, path=provenance_path)
    loaded_hash = loaded.get("provenance_hash")
    if not isinstance(loaded_hash, str) or not _is_sha256(loaded_hash):
        raise _fail(
            code=_AHK1014_PROVENANCE_INVALID,
            message="provenance hash field is missing or invalid",
            details={"path": str(provenance_path)},
        )
    if loaded_hash != provenance_hash:
        raise _fail(
            code=_AHK1014_PROVENANCE_INVALID,
            message="provenance hash drift detected",
            details={"path": str(provenance_path)},
        )
    return provenance_path, provenance_hash


def run_taskpack(
    *,
    taskpack_dir: str | Path,
    adapter_registry_path: str | Path,
    adapter_id: str,
    candidate_change_plan_path: str | Path,
    dry_run: bool,
    repo_root_path: str | Path | None = None,
) -> TaskpackRunnerResult:
    root = repo_root(anchor=Path(repo_root_path) if repo_root_path is not None else Path.cwd())

    taskpack_rel = _normalize_relative_path(str(taskpack_dir))
    taskpack_path = _safe_join(root, taskpack_rel)
    taskpack_manifest_hash = verify_taskpack_bundle(
        out_dir=taskpack_rel,
        repo_root_path=root,
    )

    allowlist_paths = _load_allowlist_payload(taskpack_path / "ALLOWLIST.json")
    forbidden_paths, _forbidden_effects, forbidden_operation_kinds = _load_forbidden_payload(
        taskpack_path / "FORBIDDEN.json"
    )
    deterministic_env, commands_by_run = _load_commands_payload(taskpack_path / "COMMANDS.json")

    adapter_registry_rel = _normalize_relative_path(str(adapter_registry_path))
    adapter_registry = _load_adapter_registry(_safe_join(root, adapter_registry_rel))
    selected_adapter = _select_adapter(adapters=adapter_registry, adapter_id=adapter_id)
    if selected_adapter["adapter_kind"] != "candidate_plan_passthrough":
        raise _fail(
            code=_AHK1005_ADAPTER_REGISTRY_INVALID,
            message="selected adapter_kind is unsupported in v45 T1",
            details={"adapter_id": adapter_id, "adapter_kind": selected_adapter["adapter_kind"]},
        )

    candidate_plan_rel = _normalize_relative_path(str(candidate_change_plan_path))
    plan = _load_candidate_change_plan(_safe_join(root, candidate_plan_rel))

    preview_root = "artifacts/agent_harness/v45/dry_run_preview"
    rejection_diagnostic_path: Path | None = None
    dry_run_preview_path: Path | None = None
    dry_run_guard: contextlib.AbstractContextManager[None]
    dry_run_guard = _dry_run_network_guard() if dry_run else contextlib.nullcontext()
    with dry_run_guard:
        policy_issues = _validate_policy(
            plan=plan,
            allowlist_paths=allowlist_paths,
            forbidden_paths=forbidden_paths,
            forbidden_operation_kinds=forbidden_operation_kinds,
            allowed_commands=commands_by_run,
            dry_run=dry_run,
        )
        if policy_issues:
            rejection_diagnostic_path = _emit_rejection_diagnostics(
                root=root,
                plan=plan,
                taskpack_manifest_hash=taskpack_manifest_hash,
                issues=policy_issues,
                dry_run=dry_run,
                preview_root=preview_root,
            )
            provenance_path, provenance_hash = _emit_provenance(
                root=root,
                dry_run=dry_run,
                preview_root=preview_root,
                taskpack_manifest_hash=taskpack_manifest_hash,
                adapter_id=adapter_id,
                plan=plan,
                policy_validation_result={
                    "passed": False,
                    "issues": [
                        {
                            "issue_code": issue.issue_code,
                            "target_path": issue.target_path,
                            "hunk_index": issue.hunk_index,
                        }
                        for issue in policy_issues
                    ],
                },
                exit_status="policy_validation_failed",
            )
            raise _fail(
                code=_AHK1010_CANDIDATE_PLAN_POLICY_VIOLATION,
                message="candidate change plan failed policy validation",
                details={
                    "taskpack_manifest_hash": taskpack_manifest_hash,
                    "candidate_change_plan_hash": plan.candidate_change_plan_hash,
                    "policy_issue_count": len(policy_issues),
                    "rejection_diagnostic_path": rejection_diagnostic_path.as_posix(),
                    "provenance_path": provenance_path.as_posix(),
                    "provenance_hash": provenance_hash,
                },
            )

        if dry_run:
            dry_run_preview_path = _emit_dry_run_preview(
                root=root,
                preview_root=preview_root,
                taskpack_manifest_hash=taskpack_manifest_hash,
                adapter_id=adapter_id,
                plan=plan,
            )
        else:
            _apply_candidate_plan(root=root, plan=plan)
            _execute_authorized_commands(
                root=root,
                proposed_commands=plan.proposed_commands,
                deterministic_env=deterministic_env,
                commands_by_run=commands_by_run,
                dry_run=dry_run,
            )

        provenance_path, provenance_hash = _emit_provenance(
            root=root,
            dry_run=dry_run,
            preview_root=preview_root,
            taskpack_manifest_hash=taskpack_manifest_hash,
            adapter_id=adapter_id,
            plan=plan,
            policy_validation_result={"passed": True, "issues": []},
            exit_status="success",
        )

    return TaskpackRunnerResult(
        candidate_change_plan_hash=plan.candidate_change_plan_hash,
        dry_run=dry_run,
        dry_run_preview_path=dry_run_preview_path,
        provenance_path=provenance_path,
        provenance_hash=provenance_hash,
        rejection_diagnostic_path=rejection_diagnostic_path,
    )


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run deterministic V33-B taskpack execution with canonical candidate "
            "change plan policy validation."
        ),
    )
    parser.add_argument(
        "--taskpack-dir",
        required=True,
        help="Repo-relative taskpack directory containing manifest/components.",
    )
    parser.add_argument(
        "--adapter-registry",
        required=True,
        help="Repo-relative path to taskpack_runner_adapter_registry@1 JSON.",
    )
    parser.add_argument(
        "--adapter-id",
        required=True,
        help="Adapter ID selected via exact case-sensitive match.",
    )
    parser.add_argument(
        "--candidate-change-plan",
        required=True,
        help="Repo-relative path to candidate_change_plan@1 JSON artifact.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Run in model-free dry-run mode with no apply and no subprocess execution.",
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
        result = run_taskpack(
            taskpack_dir=args.taskpack_dir,
            adapter_registry_path=args.adapter_registry,
            adapter_id=args.adapter_id,
            candidate_change_plan_path=args.candidate_change_plan,
            dry_run=bool(args.dry_run),
            repo_root_path=args.repo_root,
        )
    except TaskpackRunnerError as exc:
        sys.stderr.write(str(exc) + "\n")
        return 1

    payload = {
        "schema": RUNNER_RESULT_SCHEMA,
        "dry_run": result.dry_run,
        "candidate_change_plan_hash": result.candidate_change_plan_hash,
        "dry_run_preview_path": (
            result.dry_run_preview_path.as_posix() if result.dry_run_preview_path else None
        ),
        "provenance_path": result.provenance_path.as_posix(),
        "provenance_hash": result.provenance_hash,
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
