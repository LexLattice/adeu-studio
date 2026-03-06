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

TASKPACK_PROFILE_REGISTRY_SCHEMA = "taskpack_profile_registry@1"
PIPELINE_PROFILE_SCHEMA = "taskpack/pipeline_profile@1"
TASKPACK_ACCEPTANCE_SCHEMA = "taskpack/acceptance@1"
TASKPACK_ALLOWLIST_SCHEMA = "taskpack/allowlist@1"
TASKPACK_FORBIDDEN_SCHEMA = "taskpack/forbidden@1"
TASKPACK_COMMANDS_SCHEMA = "taskpack/commands@1"
TASKPACK_EVIDENCE_SLOTS_SCHEMA = "taskpack/evidence_slots@1"
TASKPACK_MANIFEST_SCHEMA = "taskpack/manifest@1"
TASKPACK_MARKDOWN_SCHEMA = "taskpack/taskpack_markdown@1"

SEMANTIC_COMPILER_EVIDENCE_MANIFEST_SCHEMA = "semantic_compiler_evidence_manifest@0.1"
SEMANTIC_COMPILER_SURFACE_DIFF_SCHEMA = "semantic_compiler_surface_diff@0.1"
COMMITMENTS_IR_SCHEMA = "adeu_commitments_ir@0.1"

AHP_MARKER_PATTERN = re.compile(
    r"^<!-- adeu:source_schema_id=(?P<schema>[^;]+);"
    r"source_component_hash=(?P<hash>[0-9a-f]{64}) -->$"
)

_DETERMINISTIC_ENV = {
    "TZ": "UTC",
    "LC_ALL": "C",
    "PYTHONHASHSEED": "0",
}

_AHK0001_PATH_POLICY_VIOLATION = "AHK0001"
_AHK0002_JSON_OBJECT_REQUIRED = "AHK0002"
_AHK0003_SCHEMA_MISMATCH = "AHK0003"
_AHK0004_PROFILE_NOT_FOUND = "AHK0004"
_AHK0005_PROFILE_ID_MISMATCH = "AHK0005"
_AHK0006_PROFILE_REGISTRY_HASH_MISMATCH = "AHK0006"
_AHK0007_PROFILE_REGISTRY_INVALID = "AHK0007"
_AHK0008_AUTHORITY_INPUT_MISSING = "AHK0008"
_AHK0009_AUTHORITY_INPUT_VERSION_SELECTION_AMBIGUOUS = "AHK0009"
_AHK0010_TASKPACK_MARKDOWN_ATTRIBUTION_MISSING = "AHK0010"
_AHK0011_TASKPACK_MARKDOWN_ATTRIBUTION_POSITION_INVALID = "AHK0011"
_AHK0012_TASKPACK_MARKDOWN_ATTRIBUTION_SPOOF_DETECTED = "AHK0012"
_AHK0013_TASKPACK_SECTION_ORDER_DRIFT = "AHK0013"
_AHK0014_PROFILE_REGISTRY_DUPLICATE_PROFILE_ID = "AHK0014"
_AHK0015_PROFILE_REGISTRY_ORDER_INVALID = "AHK0015"
_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID = "AHK0016"
_AHK0017_TASKPACK_COMPONENT_MISSING = "AHK0017"
_AHK0018_TASKPACK_COMPONENT_SCHEMA_ID_DRIFT = "AHK0018"
_AHK0019_TASKPACK_MANIFEST_COMPONENT_HASH_MISMATCH = "AHK0019"
_AHK0020_TASKPACK_BUNDLE_HASH_SUBJECT_DRIFT = "AHK0020"

_SHA256_LOWER_PATTERN = re.compile(r"[0-9a-f]{64}")
_TASKPACK_SCHEMA_ID_PATTERN = re.compile(r"taskpack/[a-z_]+@[0-9]+")
_REQUIRED_COMPONENTS_BY_PATH = {
    "TASKPACK.md": {
        "component_name": "TASKPACK.md",
        "schema_id": TASKPACK_MARKDOWN_SCHEMA,
    },
    "ACCEPTANCE.json": {
        "component_name": "ACCEPTANCE.json",
        "schema_id": TASKPACK_ACCEPTANCE_SCHEMA,
    },
    "ALLOWLIST.json": {
        "component_name": "ALLOWLIST.json",
        "schema_id": TASKPACK_ALLOWLIST_SCHEMA,
    },
    "FORBIDDEN.json": {
        "component_name": "FORBIDDEN.json",
        "schema_id": TASKPACK_FORBIDDEN_SCHEMA,
    },
    "COMMANDS.json": {
        "component_name": "COMMANDS.json",
        "schema_id": TASKPACK_COMMANDS_SCHEMA,
    },
    "EVIDENCE_SLOTS.json": {
        "component_name": "EVIDENCE_SLOTS.json",
        "schema_id": TASKPACK_EVIDENCE_SLOTS_SCHEMA,
    },
}


@dataclass(frozen=True)
class TaskpackCompileResult:
    out_dir: Path
    taskpack_markdown_path: Path
    acceptance_path: Path
    allowlist_path: Path
    forbidden_path: Path
    commands_path: Path
    evidence_slots_path: Path
    manifest_path: Path
    taskpack_manifest_sha256: str


@dataclass(frozen=True)
class VerifiedTaskpackSnapshot:
    repo_root: Path
    out_dir: Path
    manifest_path: Path
    manifest_bytes: bytes
    manifest_payload: dict[str, Any]
    manifest_hash: str
    bundle_hash: str
    component_bytes_by_path: dict[str, bytes]


class TaskpackCompileError(RuntimeError):
    def __init__(self, *, code: str, message: str, details: dict[str, Any] | None = None) -> None:
        self.code = code
        self.message = message
        self.details = details or {}
        payload = {
            "schema": "taskpack_compile_error@1",
            "code": code,
            "message": message,
            "details": self.details,
        }
        super().__init__(canonical_json(payload))


def _fail(
    *, code: str, message: str, details: dict[str, Any] | None = None
) -> TaskpackCompileError:
    return TaskpackCompileError(code=code, message=message, details=details)


def _serialize_payload(payload: dict[str, Any]) -> bytes:
    return (canonical_json(payload) + "\n").encode("utf-8")


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _normalize_relative_path(raw_path: str) -> str:
    path_text = raw_path.strip().replace("\\", "/")
    if not path_text:
        raise _fail(
            code=_AHK0001_PATH_POLICY_VIOLATION,
            message="path must not be empty",
            details={"path": raw_path},
        )
    if path_text.startswith("/"):
        raise _fail(
            code=_AHK0001_PATH_POLICY_VIOLATION,
            message="absolute paths are forbidden",
            details={"path": raw_path},
        )
    if re.match(r"^[A-Za-z]:[\\/]", path_text):
        raise _fail(
            code=_AHK0001_PATH_POLICY_VIOLATION,
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
                    code=_AHK0001_PATH_POLICY_VIOLATION,
                    message="path escapes repository root",
                    details={"path": raw_path},
                )
            segments.pop()
            continue
        segments.append(segment)

    if not segments:
        raise _fail(
            code=_AHK0001_PATH_POLICY_VIOLATION,
            message="path resolves to repository root",
            details={"path": raw_path},
        )
    return "/".join(segments)


def _load_json_object(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise _fail(
            code=_AHK0008_AUTHORITY_INPUT_MISSING,
            message="required input path does not exist",
            details={"path": str(path)},
        ) from exc
    except json.JSONDecodeError as exc:
        raise _fail(
            code=_AHK0002_JSON_OBJECT_REQUIRED,
            message="json payload is invalid",
            details={"path": str(path), "error": str(exc)},
        ) from exc
    if not isinstance(payload, dict):
        raise _fail(
            code=_AHK0002_JSON_OBJECT_REQUIRED,
            message="json payload must decode to an object",
            details={"path": str(path)},
        )
    return payload


def _require_schema(payload: dict[str, Any], *, expected_schema: str, path: Path) -> None:
    observed = payload.get("schema")
    if observed != expected_schema:
        raise _fail(
            code=_AHK0003_SCHEMA_MISMATCH,
            message="input schema mismatch",
            details={
                "path": str(path),
                "expected_schema": expected_schema,
                "observed_schema": observed,
            },
        )


def _require_string(value: Any, *, field: str) -> str:
    if not isinstance(value, str) or not value:
        raise _fail(
            code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
            message="required string field is missing or invalid",
            details={"field": field},
        )
    return value


def _sanitize_marker_like_text(value: str) -> str:
    return value.replace("<!-- adeu:", "<!-- adeu_disabled:")


def _normalize_string_list(values: Any, *, field: str) -> list[str]:
    if not isinstance(values, list) or not values:
        raise _fail(
            code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
            message="required list field is missing or empty",
            details={"field": field},
        )
    normalized: list[str] = []
    for item in values:
        if not isinstance(item, str) or not item:
            raise _fail(
                code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
                message="list field contains invalid value",
                details={"field": field},
            )
        normalized.append(item)
    return normalized


def _validate_registry_payload(payload: dict[str, Any], *, path: Path) -> list[dict[str, str]]:
    _require_schema(payload, expected_schema=TASKPACK_PROFILE_REGISTRY_SCHEMA, path=path)

    keys = set(payload.keys())
    if keys != {"schema", "profiles"}:
        raise _fail(
            code=_AHK0007_PROFILE_REGISTRY_INVALID,
            message="profile registry keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(keys)},
        )

    profiles = payload.get("profiles")
    if not isinstance(profiles, list) or not profiles:
        raise _fail(
            code=_AHK0007_PROFILE_REGISTRY_INVALID,
            message="profile registry profiles must be a non-empty array",
            details={"path": str(path)},
        )

    normalized: list[dict[str, str]] = []
    seen: set[str] = set()
    ids_in_order: list[str] = []
    for index, entry in enumerate(profiles):
        if not isinstance(entry, dict):
            raise _fail(
                code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
                message="profile registry entry must be an object",
                details={"path": str(path), "index": index},
            )
        if set(entry.keys()) != {"profile_id", "profile_sha256", "profile_payload_path"}:
            raise _fail(
                code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
                message="profile registry entry keys must match frozen grammar",
                details={"path": str(path), "index": index, "keys": sorted(entry.keys())},
            )
        profile_id = _require_string(entry.get("profile_id"), field="profile_id")
        profile_sha256 = _require_string(entry.get("profile_sha256"), field="profile_sha256")
        if not re.fullmatch(r"[0-9a-f]{64}", profile_sha256):
            raise _fail(
                code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
                message="profile_sha256 must be lowercase 64-char sha256",
                details={"path": str(path), "index": index},
            )
        payload_path = _normalize_relative_path(
            _require_string(entry.get("profile_payload_path"), field="profile_payload_path")
        )
        if profile_id in seen:
            raise _fail(
                code=_AHK0014_PROFILE_REGISTRY_DUPLICATE_PROFILE_ID,
                message="profile registry contains duplicate profile_id",
                details={"path": str(path), "profile_id": profile_id},
            )
        seen.add(profile_id)
        ids_in_order.append(profile_id)
        normalized.append(
            {
                "profile_id": profile_id,
                "profile_sha256": profile_sha256,
                "profile_payload_path": payload_path,
            }
        )

    if ids_in_order != sorted(ids_in_order):
        raise _fail(
            code=_AHK0015_PROFILE_REGISTRY_ORDER_INVALID,
            message="profile registry profile_id order must be deterministic lexicographic",
            details={"path": str(path), "profile_ids": ids_in_order},
        )

    return normalized


def _validate_profile_payload(
    payload: dict[str, Any], *, expected_profile_id: str, path: Path
) -> dict[str, Any]:
    _require_schema(payload, expected_schema=PIPELINE_PROFILE_SCHEMA, path=path)

    required_keys = {
        "schema",
        "profile_id",
        "task_scope_title",
        "task_scope_summary",
        "compiled_commitments_ir_path",
        "acceptance_criteria",
        "allowlist_paths",
        "forbidden_paths",
        "forbidden_effects",
        "commands",
        "evidence_slots",
    }
    payload_keys = set(payload.keys())
    if payload_keys != required_keys:
        raise _fail(
            code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
            message="pipeline profile keys must match frozen grammar",
            details={"path": str(path), "keys": sorted(payload_keys)},
        )

    profile_id = payload.get("profile_id")
    if profile_id != expected_profile_id:
        raise _fail(
            code=_AHK0005_PROFILE_ID_MISMATCH,
            message="resolved profile_id does not match requested profile_id",
            details={"expected": expected_profile_id, "actual": profile_id},
        )

    task_scope_title = _sanitize_marker_like_text(
        _require_string(payload.get("task_scope_title"), field="task_scope_title")
    )
    task_scope_summary = _sanitize_marker_like_text(
        _require_string(payload.get("task_scope_summary"), field="task_scope_summary")
    )

    commitments_path = _normalize_relative_path(
        _require_string(
            payload.get("compiled_commitments_ir_path"), field="compiled_commitments_ir_path"
        )
    )

    acceptance_criteria = [
        _sanitize_marker_like_text(item)
        for item in _normalize_string_list(
            payload.get("acceptance_criteria"), field="acceptance_criteria"
        )
    ]
    allowlist_paths = sorted(
        set(
            _normalize_relative_path(item)
            for item in _normalize_string_list(
                payload.get("allowlist_paths"), field="allowlist_paths"
            )
        )
    )
    forbidden_paths = sorted(
        set(
            _normalize_relative_path(item)
            for item in _normalize_string_list(
                payload.get("forbidden_paths"), field="forbidden_paths"
            )
        )
    )
    forbidden_effects = sorted(
        set(_normalize_string_list(payload.get("forbidden_effects"), field="forbidden_effects"))
    )

    commands_raw = payload.get("commands")
    if not isinstance(commands_raw, list) or not commands_raw:
        raise _fail(
            code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
            message="commands must be a non-empty array",
            details={"path": str(path)},
        )
    commands: list[dict[str, Any]] = []
    seen_command_ids: set[str] = set()
    for index, command in enumerate(commands_raw):
        if not isinstance(command, dict):
            raise _fail(
                code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
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
                code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
                message="command entry keys must match frozen grammar",
                details={"path": str(path), "index": index, "keys": sorted(command.keys())},
            )
        command_id = _require_string(command.get("command_id"), field="command_id")
        if command_id in seen_command_ids:
            raise _fail(
                code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
                message="command_id values must be unique",
                details={"path": str(path), "command_id": command_id},
            )
        seen_command_ids.add(command_id)
        run = _sanitize_marker_like_text(_require_string(command.get("run"), field="run").strip())
        working_directory_or_repo_root = _require_string(
            command.get("working_directory_or_repo_root"),
            field="working_directory_or_repo_root",
        )
        if working_directory_or_repo_root != "repo_root":
            working_directory_or_repo_root = _normalize_relative_path(
                working_directory_or_repo_root
            )

        env_overrides_raw = command.get("env_overrides")
        if not isinstance(env_overrides_raw, dict):
            raise _fail(
                code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
                message="env_overrides must be an object",
                details={"path": str(path), "command_id": command_id},
            )
        env_overrides: dict[str, str] = {}
        for key in sorted(env_overrides_raw.keys()):
            value = env_overrides_raw[key]
            if not isinstance(key, str) or not key or not isinstance(value, str):
                raise _fail(
                    code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
                    message="env_overrides entries must be string:string",
                    details={"path": str(path), "command_id": command_id},
                )
            env_overrides[key] = value

        commands.append(
            {
                "command_id": command_id,
                "run": run,
                "working_directory_or_repo_root": working_directory_or_repo_root,
                "env_overrides": env_overrides,
            }
        )

    commands.sort(key=lambda item: item["command_id"])

    evidence_slots_raw = payload.get("evidence_slots")
    if not isinstance(evidence_slots_raw, list) or not evidence_slots_raw:
        raise _fail(
            code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
            message="evidence_slots must be a non-empty array",
            details={"path": str(path)},
        )
    evidence_slots: list[dict[str, Any]] = []
    seen_slot_ids: set[str] = set()
    for index, slot in enumerate(evidence_slots_raw):
        if not isinstance(slot, dict):
            raise _fail(
                code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
                message="evidence slot entry must be an object",
                details={"path": str(path), "index": index},
            )
        if set(slot.keys()) != {"slot_id", "description", "required"}:
            raise _fail(
                code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
                message="evidence slot keys must match frozen grammar",
                details={"path": str(path), "index": index, "keys": sorted(slot.keys())},
            )
        slot_id = _require_string(slot.get("slot_id"), field="slot_id")
        if slot_id in seen_slot_ids:
            raise _fail(
                code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
                message="slot_id values must be unique",
                details={"path": str(path), "slot_id": slot_id},
            )
        seen_slot_ids.add(slot_id)
        description = _sanitize_marker_like_text(
            _require_string(slot.get("description"), field="description")
        )
        required = slot.get("required")
        if not isinstance(required, bool):
            raise _fail(
                code=_AHK0016_PROFILE_REGISTRY_ENTRY_INVALID,
                message="slot required must be boolean",
                details={"path": str(path), "slot_id": slot_id},
            )
        evidence_slots.append(
            {
                "slot_id": slot_id,
                "description": description,
                "required": required,
            }
        )

    evidence_slots.sort(key=lambda item: item["slot_id"])

    return {
        "schema": PIPELINE_PROFILE_SCHEMA,
        "profile_id": profile_id,
        "task_scope_title": task_scope_title,
        "task_scope_summary": task_scope_summary,
        "compiled_commitments_ir_path": commitments_path,
        "acceptance_criteria": acceptance_criteria,
        "allowlist_paths": allowlist_paths,
        "forbidden_paths": forbidden_paths,
        "forbidden_effects": forbidden_effects,
        "commands": commands,
        "evidence_slots": evidence_slots,
    }


def _resolve_semantic_authority_inputs(
    *,
    root: Path,
    source_semantic_arc: str,
) -> tuple[Path, Path]:
    if not re.fullmatch(r"v[0-9]+", source_semantic_arc):
        raise _fail(
            code=_AHK0009_AUTHORITY_INPUT_VERSION_SELECTION_AMBIGUOUS,
            message="source_semantic_arc must match v<digits>",
            details={"source_semantic_arc": source_semantic_arc},
        )

    all_evidence = sorted(
        (root / "artifacts" / "semantic_compiler").glob("*/evidence_manifest.json")
    )
    all_surface_diff = sorted(
        (root / "artifacts" / "semantic_compiler").glob("*/surface_diff.json")
    )

    selected_evidence = [path for path in all_evidence if path.parent.name == source_semantic_arc]
    selected_surface_diff = [
        path for path in all_surface_diff if path.parent.name == source_semantic_arc
    ]

    if len(selected_evidence) != 1 or len(selected_surface_diff) != 1:
        raise _fail(
            code=_AHK0009_AUTHORITY_INPUT_VERSION_SELECTION_AMBIGUOUS,
            message=(
                "source_semantic_arc must resolve exactly one evidence_manifest "
                "and one surface_diff"
            ),
            details={
                "source_semantic_arc": source_semantic_arc,
                "evidence_matches": [str(path) for path in selected_evidence],
                "surface_diff_matches": [str(path) for path in selected_surface_diff],
            },
        )

    return selected_evidence[0], selected_surface_diff[0]


def _to_repo_relative(path: Path, *, root: Path) -> str:
    return path.resolve().relative_to(root.resolve()).as_posix()


def _render_marker(*, source_schema_id: str, source_component_hash: str) -> str:
    return (
        "<!-- adeu:"
        f"source_schema_id={source_schema_id};"
        f"source_component_hash={source_component_hash}"
        " -->"
    )


def _render_taskpack_markdown(
    *,
    profile_payload: dict[str, Any],
    source_semantic_arc: str,
    component_hashes: dict[str, str],
) -> tuple[str, list[tuple[str, str, str]]]:
    headings = {
        "taskpack_header": "TaskPack",
        "task_scope": "Task Scope",
        "acceptance": "Acceptance",
        "allowlist": "Allowlist",
        "forbidden": "Forbidden",
        "commands": "Commands",
        "evidence_slots": "Evidence Slots",
        "attribution": "Attribution",
    }

    markers = [
        ("taskpack_header", PIPELINE_PROFILE_SCHEMA, component_hashes["PIPELINE_PROFILE"]),
        ("task_scope", PIPELINE_PROFILE_SCHEMA, component_hashes["PIPELINE_PROFILE"]),
        ("acceptance", TASKPACK_ACCEPTANCE_SCHEMA, component_hashes["ACCEPTANCE"]),
        ("allowlist", TASKPACK_ALLOWLIST_SCHEMA, component_hashes["ALLOWLIST"]),
        ("forbidden", TASKPACK_FORBIDDEN_SCHEMA, component_hashes["FORBIDDEN"]),
        ("commands", TASKPACK_COMMANDS_SCHEMA, component_hashes["COMMANDS"]),
        ("evidence_slots", TASKPACK_EVIDENCE_SLOTS_SCHEMA, component_hashes["EVIDENCE_SLOTS"]),
        (
            "attribution",
            TASKPACK_MANIFEST_SCHEMA,
            component_hashes["SEMANTIC_EVIDENCE_MANIFEST"],
        ),
    ]

    lines: list[str] = [
        f"# {headings['taskpack_header']}",
        "",
        "Deterministic taskpack compiled from authoritative ASC artifacts and profile contracts.",
        "",
        _render_marker(
            source_schema_id=PIPELINE_PROFILE_SCHEMA,
            source_component_hash=component_hashes["PIPELINE_PROFILE"],
        ),
        "",
        f"## {headings['task_scope']}",
        "",
        f"- `profile_id`: `{profile_payload['profile_id']}`",
        f"- `source_semantic_arc`: `{source_semantic_arc}`",
        f"- `title`: {profile_payload['task_scope_title']}",
        f"- `summary`: {profile_payload['task_scope_summary']}",
        "",
        _render_marker(
            source_schema_id=PIPELINE_PROFILE_SCHEMA,
            source_component_hash=component_hashes["PIPELINE_PROFILE"],
        ),
        "",
        f"## {headings['acceptance']}",
        "",
    ]

    for index, criterion in enumerate(profile_payload["acceptance_criteria"], start=1):
        lines.append(f"{index}. {criterion}")
    lines.extend(
        [
            "",
            _render_marker(
                source_schema_id=TASKPACK_ACCEPTANCE_SCHEMA,
                source_component_hash=component_hashes["ACCEPTANCE"],
            ),
            "",
            f"## {headings['allowlist']}",
            "",
        ]
    )
    for path in profile_payload["allowlist_paths"]:
        lines.append(f"- `{path}`")
    lines.extend(
        [
            "",
            _render_marker(
                source_schema_id=TASKPACK_ALLOWLIST_SCHEMA,
                source_component_hash=component_hashes["ALLOWLIST"],
            ),
            "",
            f"## {headings['forbidden']}",
            "",
            "Paths:",
            "",
        ]
    )
    for path in profile_payload["forbidden_paths"]:
        lines.append(f"- `{path}`")
    lines.extend(["", "Effects:", ""])
    for effect in profile_payload["forbidden_effects"]:
        lines.append(f"- `{effect}`")
    lines.extend(
        [
            "",
            _render_marker(
                source_schema_id=TASKPACK_FORBIDDEN_SCHEMA,
                source_component_hash=component_hashes["FORBIDDEN"],
            ),
            "",
            f"## {headings['commands']}",
            "",
            "```text",
        ]
    )
    for command in profile_payload["commands"]:
        lines.append(f"[{command['command_id']}] {command['run']}")
    lines.extend(
        [
            "```",
            "",
            _render_marker(
                source_schema_id=TASKPACK_COMMANDS_SCHEMA,
                source_component_hash=component_hashes["COMMANDS"],
            ),
            "",
            f"## {headings['evidence_slots']}",
            "",
        ]
    )
    for slot in profile_payload["evidence_slots"]:
        required = "required" if slot["required"] else "optional"
        lines.append(f"- `{slot['slot_id']}` ({required}): {slot['description']}")
    lines.extend(
        [
            "",
            _render_marker(
                source_schema_id=TASKPACK_EVIDENCE_SLOTS_SCHEMA,
                source_component_hash=component_hashes["EVIDENCE_SLOTS"],
            ),
            "",
            f"## {headings['attribution']}",
            "",
            "Attribution markers bind each semantic section to authoritative source schema + hash.",
            "",
            _render_marker(
                source_schema_id=TASKPACK_MANIFEST_SCHEMA,
                source_component_hash=component_hashes["SEMANTIC_EVIDENCE_MANIFEST"],
            ),
            "",
        ]
    )

    return "\n".join(lines), markers


def _verify_taskpack_markdown(
    *,
    markdown_text: str,
    expected_markers: list[tuple[str, str, str]],
) -> None:
    expected_section_order = [
        "task_scope",
        "acceptance",
        "allowlist",
        "forbidden",
        "commands",
        "evidence_slots",
        "attribution",
    ]
    heading_to_section = {
        "Task Scope": "task_scope",
        "Acceptance": "acceptance",
        "Allowlist": "allowlist",
        "Forbidden": "forbidden",
        "Commands": "commands",
        "Evidence Slots": "evidence_slots",
        "Attribution": "attribution",
    }

    expected_by_section = {
        section: (schema_id, component_hash)
        for section, schema_id, component_hash in expected_markers
    }

    lines = markdown_text.splitlines()
    in_code_fence = False
    current_section = "taskpack_header"
    found: dict[str, tuple[str, str]] = {}
    seen_title = False
    seen_section_order: list[str] = []

    for index, raw_line in enumerate(lines):
        stripped = raw_line.strip()
        if stripped.startswith("```"):
            in_code_fence = not in_code_fence
            continue
        if in_code_fence:
            continue
        if raw_line.lstrip().startswith(">"):
            continue

        if stripped.startswith("# "):
            if stripped != "# TaskPack":
                raise _fail(
                    code=_AHK0013_TASKPACK_SECTION_ORDER_DRIFT,
                    message="taskpack title heading must be # TaskPack",
                    details={"line": index + 1, "value": stripped},
                )
            if seen_title:
                raise _fail(
                    code=_AHK0013_TASKPACK_SECTION_ORDER_DRIFT,
                    message="taskpack title heading must appear exactly once",
                    details={"line": index + 1, "value": stripped},
                )
            seen_title = True
            continue

        if stripped.startswith("## "):
            heading = stripped[3:]
            current_section = heading_to_section.get(heading, "")
            if not current_section:
                raise _fail(
                    code=_AHK0013_TASKPACK_SECTION_ORDER_DRIFT,
                    message="taskpack markdown contains unexpected section heading",
                    details={"line": index + 1, "heading": heading},
                )
            seen_section_order.append(current_section)
            continue

        if "<!-- adeu:" not in stripped:
            continue

        marker_match = AHP_MARKER_PATTERN.fullmatch(stripped)
        if marker_match is None:
            raise _fail(
                code=_AHK0012_TASKPACK_MARKDOWN_ATTRIBUTION_SPOOF_DETECTED,
                message="marker-like text detected outside authoritative marker grammar",
                details={"line": index + 1, "value": stripped},
            )

        if current_section not in expected_by_section:
            raise _fail(
                code=_AHK0011_TASKPACK_MARKDOWN_ATTRIBUTION_POSITION_INVALID,
                message="attribution marker appears in non-authoritative section",
                details={"line": index + 1, "section": current_section},
            )
        if current_section in found:
            raise _fail(
                code=_AHK0012_TASKPACK_MARKDOWN_ATTRIBUTION_SPOOF_DETECTED,
                message="duplicate attribution marker detected for section",
                details={"line": index + 1, "section": current_section},
            )

        expected_schema_id, expected_hash = expected_by_section[current_section]
        observed_schema_id = marker_match.group("schema")
        observed_hash = marker_match.group("hash")
        if observed_schema_id != expected_schema_id or observed_hash != expected_hash:
            raise _fail(
                code=_AHK0012_TASKPACK_MARKDOWN_ATTRIBUTION_SPOOF_DETECTED,
                message="attribution marker payload does not match expected source binding",
                details={
                    "line": index + 1,
                    "section": current_section,
                    "expected_schema_id": expected_schema_id,
                    "observed_schema_id": observed_schema_id,
                },
            )

        lookahead = index + 1
        while lookahead < len(lines) and lines[lookahead].strip() == "":
            lookahead += 1
        if lookahead < len(lines):
            next_line = lines[lookahead].strip()
            if not next_line.startswith("## "):
                raise _fail(
                    code=_AHK0011_TASKPACK_MARKDOWN_ATTRIBUTION_POSITION_INVALID,
                    message="attribution marker must terminate a semantic section",
                    details={"line": index + 1, "next_line": next_line},
                )

        found[current_section] = (observed_schema_id, observed_hash)

    missing = sorted(set(expected_by_section.keys()) - set(found.keys()))
    if missing:
        raise _fail(
            code=_AHK0010_TASKPACK_MARKDOWN_ATTRIBUTION_MISSING,
            message="taskpack markdown is missing required attribution markers",
            details={"missing_sections": missing},
        )
    if not seen_title:
        raise _fail(
            code=_AHK0013_TASKPACK_SECTION_ORDER_DRIFT,
            message="taskpack title heading is missing",
            details={},
        )
    if seen_section_order != expected_section_order:
        raise _fail(
            code=_AHK0013_TASKPACK_SECTION_ORDER_DRIFT,
            message="taskpack markdown section order drifted from frozen profile",
            details={
                "expected_order": expected_section_order,
                "observed_order": seen_section_order,
            },
        )


def _write_bytes(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)


def verify_taskpack_bundle(
    *,
    out_dir: str | Path,
    expected_manifest_sha256: str | None = None,
    repo_root_path: str | Path | None = None,
) -> str:
    snapshot = load_verified_taskpack_snapshot(out_dir=out_dir, repo_root_path=repo_root_path)
    observed_manifest_sha256 = snapshot.manifest_hash
    if expected_manifest_sha256 is not None:
        if not _SHA256_LOWER_PATTERN.fullmatch(expected_manifest_sha256):
            raise _fail(
                code=_AHK0020_TASKPACK_BUNDLE_HASH_SUBJECT_DRIFT,
                message="expected manifest sha256 must be lowercase 64-char sha256",
                details={"expected_manifest_sha256": expected_manifest_sha256},
            )
        if observed_manifest_sha256 != expected_manifest_sha256:
            raise _fail(
                code=_AHK0020_TASKPACK_BUNDLE_HASH_SUBJECT_DRIFT,
                message="taskpack bundle hash subject drift detected",
                details={
                    "expected_manifest_sha256": expected_manifest_sha256,
                    "observed_manifest_sha256": observed_manifest_sha256,
                },
            )
    return observed_manifest_sha256


def load_verified_taskpack_snapshot(
    *,
    out_dir: str | Path,
    repo_root_path: str | Path | None = None,
) -> VerifiedTaskpackSnapshot:
    root = repo_root(anchor=Path(repo_root_path) if repo_root_path is not None else Path.cwd())
    out_rel = _normalize_relative_path(str(out_dir))
    out_path = root / out_rel
    manifest_path = out_path / "taskpack_manifest.json"
    manifest_payload = _load_json_object(manifest_path)
    manifest_bytes = manifest_path.read_bytes()
    _require_schema(
        manifest_payload,
        expected_schema=TASKPACK_MANIFEST_SCHEMA,
        path=manifest_path,
    )

    components_raw = manifest_payload.get("components")
    if not isinstance(components_raw, list):
        raise _fail(
            code=_AHK0017_TASKPACK_COMPONENT_MISSING,
            message="taskpack manifest components must be a list",
            details={"path": str(manifest_path)},
        )

    components_by_path: dict[str, dict[str, Any]] = {}
    for index, component in enumerate(components_raw):
        if not isinstance(component, dict):
            raise _fail(
                code=_AHK0017_TASKPACK_COMPONENT_MISSING,
                message="taskpack component entry must be an object",
                details={"path": str(manifest_path), "index": index},
            )
        if set(component.keys()) != {"component", "schema_id", "relative_path", "sha256"}:
            raise _fail(
                code=_AHK0017_TASKPACK_COMPONENT_MISSING,
                message="taskpack component entry keys must match frozen grammar",
                details={
                    "path": str(manifest_path),
                    "index": index,
                    "keys": sorted(component.keys()),
                },
            )
        relative_path_raw = component.get("relative_path")
        if not isinstance(relative_path_raw, str):
            raise _fail(
                code=_AHK0017_TASKPACK_COMPONENT_MISSING,
                message="taskpack component relative_path must be a string",
                details={"path": str(manifest_path), "index": index},
            )
        relative_path = _normalize_relative_path(relative_path_raw)
        if relative_path in components_by_path:
            raise _fail(
                code=_AHK0017_TASKPACK_COMPONENT_MISSING,
                message="taskpack component relative_path values must be unique",
                details={"path": str(manifest_path), "relative_path": relative_path},
            )
        components_by_path[relative_path] = component

    expected_paths = sorted(_REQUIRED_COMPONENTS_BY_PATH.keys())
    observed_paths = sorted(components_by_path.keys())
    if observed_paths != expected_paths:
        raise _fail(
            code=_AHK0017_TASKPACK_COMPONENT_MISSING,
            message="taskpack required component set mismatch",
            details={
                "expected_paths": expected_paths,
                "observed_paths": observed_paths,
            },
        )

    component_bytes_by_path: dict[str, bytes] = {}
    for relative_path in expected_paths:
        expected_component = _REQUIRED_COMPONENTS_BY_PATH[relative_path]
        component = components_by_path[relative_path]
        component_name = component.get("component")
        if component_name != expected_component["component_name"]:
            raise _fail(
                code=_AHK0018_TASKPACK_COMPONENT_SCHEMA_ID_DRIFT,
                message="taskpack component name drift detected",
                details={
                    "relative_path": relative_path,
                    "expected_component_name": expected_component["component_name"],
                    "observed_component_name": component_name,
                },
            )

        schema_id = component.get("schema_id")
        if not isinstance(schema_id, str) or not _TASKPACK_SCHEMA_ID_PATTERN.fullmatch(schema_id):
            raise _fail(
                code=_AHK0018_TASKPACK_COMPONENT_SCHEMA_ID_DRIFT,
                message="taskpack component schema_id violates frozen format",
                details={"relative_path": relative_path, "observed_schema_id": schema_id},
            )
        if schema_id != expected_component["schema_id"]:
            raise _fail(
                code=_AHK0018_TASKPACK_COMPONENT_SCHEMA_ID_DRIFT,
                message="taskpack component schema_id drift detected",
                details={
                    "relative_path": relative_path,
                    "expected_schema_id": expected_component["schema_id"],
                    "observed_schema_id": schema_id,
                },
            )

        recorded_sha256 = component.get("sha256")
        if not isinstance(recorded_sha256, str) or not _SHA256_LOWER_PATTERN.fullmatch(
            recorded_sha256
        ):
            raise _fail(
                code=_AHK0019_TASKPACK_MANIFEST_COMPONENT_HASH_MISMATCH,
                message="taskpack component sha256 field is invalid",
                details={"relative_path": relative_path, "recorded_sha256": recorded_sha256},
            )

        component_path = out_path / relative_path
        if not component_path.is_file():
            raise _fail(
                code=_AHK0017_TASKPACK_COMPONENT_MISSING,
                message="taskpack component file is missing",
                details={"relative_path": relative_path, "path": str(component_path)},
            )
        component_bytes = component_path.read_bytes()
        component_bytes_by_path[relative_path] = component_bytes
        computed_sha256 = _sha256_bytes(component_bytes)
        if computed_sha256 != recorded_sha256:
            raise _fail(
                code=_AHK0019_TASKPACK_MANIFEST_COMPONENT_HASH_MISMATCH,
                message="taskpack component sha256 mismatch",
                details={
                    "relative_path": relative_path,
                    "recorded_sha256": recorded_sha256,
                    "computed_sha256": computed_sha256,
                },
            )

    observed_manifest_sha256 = sha256_canonical_json(manifest_payload)
    bundle_subject = [
        {
            "path": relative_path,
            "sha256": components_by_path[relative_path]["sha256"],
        }
        for relative_path in expected_paths
    ]

    return VerifiedTaskpackSnapshot(
        repo_root=root,
        out_dir=out_path,
        manifest_path=manifest_path,
        manifest_bytes=manifest_bytes,
        manifest_payload=manifest_payload,
        manifest_hash=observed_manifest_sha256,
        bundle_hash=sha256_canonical_json(bundle_subject),
        component_bytes_by_path=component_bytes_by_path,
    )


def compile_taskpack(
    *,
    profile_registry_path: str | Path,
    profile_id: str,
    source_semantic_arc: str,
    out_dir: str | Path,
    repo_root_path: str | Path | None = None,
) -> TaskpackCompileResult:
    root = repo_root(anchor=Path(repo_root_path) if repo_root_path is not None else Path.cwd())

    registry_rel = _normalize_relative_path(str(profile_registry_path))
    registry_path = root / registry_rel
    registry_payload = _load_json_object(registry_path)
    registry_entries = _validate_registry_payload(registry_payload, path=registry_path)

    selected_entry = next(
        (entry for entry in registry_entries if entry["profile_id"] == profile_id), None
    )
    if selected_entry is None:
        raise _fail(
            code=_AHK0004_PROFILE_NOT_FOUND,
            message="profile_id is not present in registry",
            details={"profile_id": profile_id, "registry_path": registry_rel},
        )

    profile_path = root / selected_entry["profile_payload_path"]
    profile_payload_raw = _load_json_object(profile_path)
    profile_hash = sha256_canonical_json(profile_payload_raw)
    if profile_hash != selected_entry["profile_sha256"]:
        raise _fail(
            code=_AHK0006_PROFILE_REGISTRY_HASH_MISMATCH,
            message="resolved profile hash does not match registry declared hash",
            details={
                "profile_id": profile_id,
                "expected_profile_sha256": selected_entry["profile_sha256"],
                "actual_profile_sha256": profile_hash,
            },
        )
    profile_payload = _validate_profile_payload(
        profile_payload_raw,
        expected_profile_id=profile_id,
        path=profile_path,
    )

    evidence_manifest_path, surface_diff_path = _resolve_semantic_authority_inputs(
        root=root,
        source_semantic_arc=source_semantic_arc,
    )
    evidence_manifest_payload = _load_json_object(evidence_manifest_path)
    _require_schema(
        evidence_manifest_payload,
        expected_schema=SEMANTIC_COMPILER_EVIDENCE_MANIFEST_SCHEMA,
        path=evidence_manifest_path,
    )

    surface_diff_payload = _load_json_object(surface_diff_path)
    _require_schema(
        surface_diff_payload,
        expected_schema=SEMANTIC_COMPILER_SURFACE_DIFF_SCHEMA,
        path=surface_diff_path,
    )

    commitments_ir_path = root / profile_payload["compiled_commitments_ir_path"]
    commitments_ir_payload = _load_json_object(commitments_ir_path)
    _require_schema(
        commitments_ir_payload,
        expected_schema=COMMITMENTS_IR_SCHEMA,
        path=commitments_ir_path,
    )

    acceptance_payload = {
        "schema": TASKPACK_ACCEPTANCE_SCHEMA,
        "profile_id": profile_id,
        "source_semantic_arc": source_semantic_arc,
        "criteria": [
            {"id": f"AC{index:02d}", "text": text}
            for index, text in enumerate(profile_payload["acceptance_criteria"], start=1)
        ],
        "authority_inputs": {
            "semantic_compiler_evidence_manifest_path": _to_repo_relative(
                evidence_manifest_path,
                root=root,
            ),
            "semantic_compiler_surface_diff_path": _to_repo_relative(surface_diff_path, root=root),
            "compiled_commitments_ir_path": _to_repo_relative(commitments_ir_path, root=root),
        },
    }

    allowlist_payload = {
        "schema": TASKPACK_ALLOWLIST_SCHEMA,
        "profile_id": profile_id,
        "path_policy": "repo_relative_only",
        "paths": profile_payload["allowlist_paths"],
    }

    forbidden_payload = {
        "schema": TASKPACK_FORBIDDEN_SCHEMA,
        "profile_id": profile_id,
        "paths": profile_payload["forbidden_paths"],
        "effects": profile_payload["forbidden_effects"],
    }

    commands_payload = {
        "schema": TASKPACK_COMMANDS_SCHEMA,
        "profile_id": profile_id,
        "deterministic_env": dict(_DETERMINISTIC_ENV),
        "commands": profile_payload["commands"],
    }

    evidence_slots_payload = {
        "schema": TASKPACK_EVIDENCE_SLOTS_SCHEMA,
        "profile_id": profile_id,
        "required_count": sum(1 for slot in profile_payload["evidence_slots"] if slot["required"]),
        "slots": profile_payload["evidence_slots"],
    }

    component_bytes = {
        "ACCEPTANCE": _serialize_payload(acceptance_payload),
        "ALLOWLIST": _serialize_payload(allowlist_payload),
        "FORBIDDEN": _serialize_payload(forbidden_payload),
        "COMMANDS": _serialize_payload(commands_payload),
        "EVIDENCE_SLOTS": _serialize_payload(evidence_slots_payload),
    }

    component_hashes = {key: _sha256_bytes(value) for key, value in component_bytes.items()}
    component_hashes["PIPELINE_PROFILE"] = profile_hash
    component_hashes["SEMANTIC_EVIDENCE_MANIFEST"] = sha256_canonical_json(
        evidence_manifest_payload
    )

    taskpack_markdown, expected_markers = _render_taskpack_markdown(
        profile_payload=profile_payload,
        source_semantic_arc=source_semantic_arc,
        component_hashes=component_hashes,
    )
    _verify_taskpack_markdown(markdown_text=taskpack_markdown, expected_markers=expected_markers)
    taskpack_markdown_bytes = (taskpack_markdown + "\n").encode("utf-8")
    taskpack_markdown_hash = _sha256_bytes(taskpack_markdown_bytes)

    manifest_payload = {
        "schema": TASKPACK_MANIFEST_SCHEMA,
        "profile_id": profile_id,
        "source_semantic_arc": source_semantic_arc,
        "compiler_entrypoint": "python -m adeu_agent_harness.compile",
        "profile_registry": {
            "schema": TASKPACK_PROFILE_REGISTRY_SCHEMA,
            "registry_path": registry_rel,
            "profile_id": selected_entry["profile_id"],
            "profile_payload_path": selected_entry["profile_payload_path"],
            "profile_sha256": selected_entry["profile_sha256"],
        },
        "authority_inputs": {
            "semantic_compiler_evidence_manifest": {
                "path": _to_repo_relative(evidence_manifest_path, root=root),
                "schema": SEMANTIC_COMPILER_EVIDENCE_MANIFEST_SCHEMA,
                "sha256_canonical_json": sha256_canonical_json(evidence_manifest_payload),
            },
            "semantic_compiler_surface_diff": {
                "path": _to_repo_relative(surface_diff_path, root=root),
                "schema": SEMANTIC_COMPILER_SURFACE_DIFF_SCHEMA,
                "sha256_canonical_json": sha256_canonical_json(surface_diff_payload),
            },
            "compiled_commitments_ir": {
                "path": _to_repo_relative(commitments_ir_path, root=root),
                "schema": COMMITMENTS_IR_SCHEMA,
                "sha256_canonical_json": sha256_canonical_json(commitments_ir_payload),
            },
        },
        "components": [
            {
                "component": "TASKPACK.md",
                "schema_id": TASKPACK_MARKDOWN_SCHEMA,
                "relative_path": "TASKPACK.md",
                "sha256": taskpack_markdown_hash,
            },
            {
                "component": "ACCEPTANCE.json",
                "schema_id": TASKPACK_ACCEPTANCE_SCHEMA,
                "relative_path": "ACCEPTANCE.json",
                "sha256": component_hashes["ACCEPTANCE"],
            },
            {
                "component": "ALLOWLIST.json",
                "schema_id": TASKPACK_ALLOWLIST_SCHEMA,
                "relative_path": "ALLOWLIST.json",
                "sha256": component_hashes["ALLOWLIST"],
            },
            {
                "component": "FORBIDDEN.json",
                "schema_id": TASKPACK_FORBIDDEN_SCHEMA,
                "relative_path": "FORBIDDEN.json",
                "sha256": component_hashes["FORBIDDEN"],
            },
            {
                "component": "COMMANDS.json",
                "schema_id": TASKPACK_COMMANDS_SCHEMA,
                "relative_path": "COMMANDS.json",
                "sha256": component_hashes["COMMANDS"],
            },
            {
                "component": "EVIDENCE_SLOTS.json",
                "schema_id": TASKPACK_EVIDENCE_SLOTS_SCHEMA,
                "relative_path": "EVIDENCE_SLOTS.json",
                "sha256": component_hashes["EVIDENCE_SLOTS"],
            },
        ],
        "markdown_projection_policy": {
            "required_section_order_ids": [
                "taskpack_header",
                "task_scope",
                "acceptance",
                "allowlist",
                "forbidden",
                "commands",
                "evidence_slots",
                "attribution",
            ],
            "attribution_marker_syntax": "<!-- adeu:... -->",
            "attribution_marker_position_rule": (
                "exactly_one_root_scope_eof_marker_per_semantic_section"
            ),
            "markdown_parser_scope": "root_scope_excluding_code_fence_and_blockquote_content",
        },
    }

    manifest_bytes = _serialize_payload(manifest_payload)
    manifest_hash = sha256_canonical_json(manifest_payload)

    out_rel = _normalize_relative_path(str(out_dir))
    out_path = root / out_rel
    taskpack_markdown_path = out_path / "TASKPACK.md"
    acceptance_path = out_path / "ACCEPTANCE.json"
    allowlist_path = out_path / "ALLOWLIST.json"
    forbidden_path = out_path / "FORBIDDEN.json"
    commands_path = out_path / "COMMANDS.json"
    evidence_slots_path = out_path / "EVIDENCE_SLOTS.json"
    manifest_path = out_path / "taskpack_manifest.json"

    _write_bytes(taskpack_markdown_path, taskpack_markdown_bytes)
    _write_bytes(acceptance_path, component_bytes["ACCEPTANCE"])
    _write_bytes(allowlist_path, component_bytes["ALLOWLIST"])
    _write_bytes(forbidden_path, component_bytes["FORBIDDEN"])
    _write_bytes(commands_path, component_bytes["COMMANDS"])
    _write_bytes(evidence_slots_path, component_bytes["EVIDENCE_SLOTS"])
    _write_bytes(manifest_path, manifest_bytes)
    verify_taskpack_bundle(
        out_dir=out_rel,
        expected_manifest_sha256=manifest_hash,
        repo_root_path=root,
    )

    return TaskpackCompileResult(
        out_dir=out_path,
        taskpack_markdown_path=taskpack_markdown_path,
        acceptance_path=acceptance_path,
        allowlist_path=allowlist_path,
        forbidden_path=forbidden_path,
        commands_path=commands_path,
        evidence_slots_path=evidence_slots_path,
        manifest_path=manifest_path,
        taskpack_manifest_sha256=manifest_hash,
    )


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Compile deterministic V33-A taskpack artifacts from authoritative "
            "profile and semantic inputs."
        ),
    )
    parser.add_argument(
        "--profile-registry",
        required=True,
        help="Repo-relative path to taskpack_profile_registry@1 JSON.",
    )
    parser.add_argument(
        "--profile-id", required=True, help="Profile ID resolved via registry-only policy."
    )
    parser.add_argument(
        "--source-semantic-arc",
        required=True,
        help="Semantic artifact arc directory (for example: v41).",
    )
    parser.add_argument(
        "--out-dir", required=True, help="Repo-relative output directory for taskpack bundle."
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
        result = compile_taskpack(
            profile_registry_path=args.profile_registry,
            profile_id=args.profile_id,
            source_semantic_arc=args.source_semantic_arc,
            out_dir=args.out_dir,
            repo_root_path=args.repo_root,
        )
    except TaskpackCompileError as exc:
        sys.stderr.write(str(exc) + "\n")
        return 1

    payload = {
        "schema": "taskpack_compile_result@1",
        "out_dir": result.out_dir.as_posix(),
        "taskpack_manifest_path": result.manifest_path.as_posix(),
        "taskpack_manifest_sha256": result.taskpack_manifest_sha256,
    }
    sys.stdout.write(canonical_json(payload) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
