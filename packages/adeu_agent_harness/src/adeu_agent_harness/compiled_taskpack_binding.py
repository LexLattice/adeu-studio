from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

from adeu_ir.repo import repo_root
from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import canonical_json, sha256_canonical_json

from .compile import (
    COMMITMENTS_IR_SCHEMA,
    PIPELINE_PROFILE_SCHEMA,
    SEMANTIC_COMPILER_EVIDENCE_MANIFEST_SCHEMA,
    SEMANTIC_COMPILER_SURFACE_DIFF_SCHEMA,
    TASKPACK_PROFILE_REGISTRY_SCHEMA,
    TaskpackCompileError,
    compile_taskpack,
    load_verified_taskpack_snapshot,
)
from .taskpack_binding import (
    ANM_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA,
    ANM_TASKPACK_BINDING_PROFILE_SCHEMA,
    REPO_DESCRIPTIVE_NORMATIVE_BINDING_FRAME_SCHEMA,
    AnmTaskpackBindingProfile,
)

COMPILED_POLICY_TASKPACK_BINDING_SCHEMA = "compiled_policy_taskpack_binding@1"
COMPILED_POLICY_TASKPACK_BINDING_ERROR_SCHEMA = "compiled_policy_taskpack_binding_error@1"
RELEASED_TASKPACK_COMPILER_SELECTION = "python -m adeu_agent_harness.compile"

BindingProfileSourceKind = Literal["released_anm_taskpack_binding_profile_ref"]
CompilerSelectionKind = Literal["released_adeu_agent_harness_taskpack_compiler"]
KernelBridgePosture = Literal["released_pipeline_profile_and_registry_then_compile_taskpack"]
CompiledComponentSetKind = Literal["released_taskpack_bundle_component_set"]
CompiledBoundaryIdentityPosture = Literal["binding_lineage_plus_task_identity_hash"]
UnsupportedCompilationPosture = Literal["fail_closed"]
WorkerSubjectKind = Literal["repo_internal_single_codex_worker"]

AHK5701_INPUT_INVALID = "AHK5701"
AHK5702_SCHEMA_MISMATCH = "AHK5702"
AHK5703_CARDINALITY_VIOLATION = "AHK5703"
AHK5704_LINEAGE_UNRESOLVED = "AHK5704"
AHK5705_LINEAGE_MISMATCH = "AHK5705"
AHK5706_BRIDGE_INVALID = "AHK5706"
AHK5707_HASH_DRIFT = "AHK5707"
AHK5708_UNSUPPORTED_COMPILATION = "AHK5708"

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"^[A-Za-z]:[\\/]")
_SOURCE_ARC_RE = re.compile(r"v[0-9]+")
_POLICY_ROW_FRAGMENT_RE = re.compile(r"consumer_rows\[(?P<index>\d+)\]")
_SCOPE_SCHEMA_TO_BINDING_KIND = {
    "repo_schema_family_registry@1": (
        "repo_schema_family_registry",
        "bound_schema_family_registry_ref",
    ),
    "repo_optimization_register@1": (
        "repo_optimization_register",
        "bound_optimization_register_ref",
    ),
    "repo_test_intent_matrix@1": (
        "repo_test_intent_matrix",
        "bound_test_intent_matrix_ref",
    ),
    "repo_entity_catalog@1": (
        "repo_entity_catalog",
        "bound_entity_catalog_ref",
    ),
    "repo_symbol_catalog@1": (
        "repo_symbol_catalog",
        "bound_symbol_catalog_ref",
    ),
    "repo_dependency_graph@1": (
        "repo_dependency_graph",
        "bound_dependency_graph_ref",
    ),
}


def _stable_payload_hash(value: Any) -> str:
    return sha256_canonical_json(value)


def _serialize_payload(payload: dict[str, Any]) -> str:
    return canonical_json(payload) + "\n"


class CompiledPolicyTaskpackBinding(BaseModel):
    model_config = ConfigDict(extra="forbid", str_strip_whitespace=True)

    schema: Literal["compiled_policy_taskpack_binding@1"] = COMPILED_POLICY_TASKPACK_BINDING_SCHEMA
    compiled_binding_id: str = Field(min_length=1)
    snapshot_id: str = Field(min_length=1)
    snapshot_sha256: str = Field(min_length=1)
    binding_profile_source_kind: BindingProfileSourceKind
    binding_profile_ref: str = Field(min_length=1)
    binding_profile_semantic_hash: str = Field(min_length=1)
    policy_lineage_hash: str = Field(min_length=1)
    scope_lineage_hash: str = Field(min_length=1)
    binding_subject_id: str = Field(min_length=1)
    worker_subject_kind: WorkerSubjectKind
    worker_subject_ref: str = Field(min_length=1)
    compiler_selection_kind: CompilerSelectionKind
    compiler_selection: str = Field(min_length=1)
    source_semantic_arc: str = Field(min_length=1)
    declared_task_identity: str = Field(min_length=1)
    kernel_bridge_posture: KernelBridgePosture
    pipeline_profile_ref: str = Field(min_length=1)
    pipeline_profile_sha256: str = Field(min_length=1)
    profile_registry_ref: str = Field(min_length=1)
    profile_registry_sha256: str = Field(min_length=1)
    compiled_commitments_ir_path: str = Field(min_length=1)
    semantic_compiler_evidence_manifest_path: str = Field(min_length=1)
    semantic_compiler_surface_diff_path: str = Field(min_length=1)
    compiled_boundary_identity_posture: CompiledBoundaryIdentityPosture
    compiled_boundary_identity_hash: str = Field(min_length=1)
    compiled_component_set_kind: CompiledComponentSetKind
    taskpack_markdown_ref: str = Field(min_length=1)
    acceptance_ref: str = Field(min_length=1)
    allowlist_ref: str = Field(min_length=1)
    forbidden_ref: str = Field(min_length=1)
    commands_ref: str = Field(min_length=1)
    evidence_slots_ref: str = Field(min_length=1)
    taskpack_manifest_ref: str = Field(min_length=1)
    manifest_sha256: str = Field(min_length=1)
    bundle_hash: str = Field(min_length=1)
    unsupported_compilation_posture: UnsupportedCompilationPosture
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "CompiledPolicyTaskpackBinding":
        payload = self.model_dump(mode="json", exclude={"semantic_hash"})
        self.semantic_hash = _stable_payload_hash(payload)
        return self


@dataclass(frozen=True)
class CompiledPolicyTaskpackBindingResult:
    compiled_binding: CompiledPolicyTaskpackBinding
    compiled_binding_path: Path
    pipeline_profile_path: Path
    profile_registry_path: Path


class CompiledPolicyTaskpackBindingError(RuntimeError):
    def __init__(self, *, code: str, message: str, details: dict[str, Any] | None = None) -> None:
        self.code = code
        self.message = message
        self.details = details or {}
        payload = {
            "schema": COMPILED_POLICY_TASKPACK_BINDING_ERROR_SCHEMA,
            "code": code,
            "message": message,
            "details": self.details,
        }
        super().__init__(canonical_json(payload))


def _fail(
    *,
    code: str,
    message: str,
    details: dict[str, Any] | None = None,
) -> CompiledPolicyTaskpackBindingError:
    return CompiledPolicyTaskpackBindingError(code=code, message=message, details=details)


def _normalize_relative_path(raw_path: str) -> str:
    path_text = raw_path.strip().replace("\\", "/")
    if not path_text:
        raise _fail(
            code=AHK5701_INPUT_INVALID,
            message="path must not be empty",
            details={"path": raw_path},
        )
    if path_text.startswith("/"):
        raise _fail(
            code=AHK5701_INPUT_INVALID,
            message="absolute paths are forbidden",
            details={"path": raw_path},
        )
    if _WINDOWS_ABSOLUTE_PATH_RE.match(path_text):
        raise _fail(
            code=AHK5701_INPUT_INVALID,
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
                    code=AHK5701_INPUT_INVALID,
                    message="path escapes repository root",
                    details={"path": raw_path},
                )
            segments.pop()
            continue
        segments.append(segment)

    if not segments:
        raise _fail(
            code=AHK5701_INPUT_INVALID,
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
            code=AHK5701_INPUT_INVALID,
            message="resolved path escapes repository root",
            details={"path": rel_path},
        ) from exc
    return path


def _resolve_under(base_dir: Path, candidate: Path, *, details: dict[str, Any]) -> Path:
    resolved = candidate.resolve()
    base_resolved = base_dir.resolve()
    try:
        resolved.relative_to(base_resolved)
    except ValueError as exc:
        raise _fail(
            code=AHK5704_LINEAGE_UNRESOLVED,
            message="resolved path escapes allowed base directory",
            details=details,
        ) from exc
    return resolved


def _to_repo_relative(path: Path, *, root: Path) -> str:
    return path.resolve().relative_to(root.resolve()).as_posix()


def _write_json(path: Path, payload: dict[str, Any]) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    serialized = _serialize_payload(payload)
    path.write_text(serialized, encoding="utf-8")
    return _stable_payload_hash(payload)


def _load_json_object(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise _fail(
            code=AHK5704_LINEAGE_UNRESOLVED,
            message="required json path does not exist",
            details={"path": str(path)},
        ) from exc
    except OSError as exc:
        raise _fail(
            code=AHK5704_LINEAGE_UNRESOLVED,
            message="required json path cannot be read",
            details={"path": str(path), "error": str(exc)},
        ) from exc
    except json.JSONDecodeError as exc:
        raise _fail(
            code=AHK5701_INPUT_INVALID,
            message="json payload is invalid",
            details={"path": str(path), "error": str(exc)},
        ) from exc
    if not isinstance(payload, dict):
        raise _fail(
            code=AHK5701_INPUT_INVALID,
            message="json payload must decode to an object",
            details={"path": str(path)},
        )
    return payload


def _require_exactly_one(values: list[str], *, field_name: str) -> str:
    if not isinstance(values, list) or len(values) != 1:
        count = len(values) if isinstance(values, list) else None
        raise _fail(
            code=AHK5703_CARDINALITY_VIOLATION,
            message=f"{field_name} must contain exactly one value",
            details={"field_name": field_name, "count": count},
        )
    value = values[0]
    if not isinstance(value, str) or not value.strip():
        raise _fail(
            code=AHK5701_INPUT_INVALID,
            message=f"{field_name} must contain exactly one non-empty string",
            details={"field_name": field_name},
        )
    return value.strip()


def _require_non_empty(value: str, *, field_name: str) -> str:
    normalized = value.strip()
    if not normalized:
        raise _fail(
            code=AHK5701_INPUT_INVALID,
            message=f"{field_name} must not be empty",
            details={"field_name": field_name},
        )
    return normalized


def _split_json_ref(raw_ref: str, *, field_name: str) -> tuple[str, str]:
    if "#" not in raw_ref:
        raise _fail(
            code=AHK5704_LINEAGE_UNRESOLVED,
            message=f"{field_name} must include a # fragment",
            details={"field_name": field_name, "ref": raw_ref},
        )
    path_text, fragment = raw_ref.split("#", 1)
    normalized_path = _normalize_relative_path(path_text)
    fragment = fragment.strip()
    if not fragment:
        raise _fail(
            code=AHK5704_LINEAGE_UNRESOLVED,
            message=f"{field_name} fragment must not be empty",
            details={"field_name": field_name, "ref": raw_ref},
        )
    return normalized_path, fragment


def _resolve_policy_row(root: Path, raw_ref: str) -> tuple[dict[str, Any], dict[str, Any]]:
    path_text, fragment = _split_json_ref(raw_ref, field_name="binding_profile_ref")
    match = _POLICY_ROW_FRAGMENT_RE.fullmatch(fragment)
    if match is None:
        raise _fail(
            code=AHK5704_LINEAGE_UNRESOLVED,
            message="policy source ref fragment must match consumer_rows[<index>]",
            details={"ref": raw_ref},
        )
    index = int(match.group("index"))
    payload = _load_json_object(_safe_join(root, path_text))
    if payload.get("schema") != ANM_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA:
        raise _fail(
            code=AHK5702_SCHEMA_MISMATCH,
            message="policy source profile schema mismatch",
            details={
                "path": path_text,
                "expected_schema": ANM_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA,
                "observed_schema": payload.get("schema"),
            },
        )
    rows = payload.get("consumer_rows")
    if not isinstance(rows, list) or not (0 <= index < len(rows)):
        raise _fail(
            code=AHK5704_LINEAGE_UNRESOLVED,
            message="policy source row ref does not resolve to a consumer row",
            details={"ref": raw_ref},
        )
    row = rows[index]
    if not isinstance(row, dict):
        raise _fail(
            code=AHK5704_LINEAGE_UNRESOLVED,
            message="resolved policy source row is invalid",
            details={"ref": raw_ref},
        )
    return payload, row


def _resolve_binding_entry(root: Path, raw_ref: str) -> tuple[dict[str, Any], dict[str, Any]]:
    path_text, entry_id = _split_json_ref(raw_ref, field_name="scope_binding_entry_ref")
    payload = _load_json_object(_safe_join(root, path_text))
    if payload.get("schema") != REPO_DESCRIPTIVE_NORMATIVE_BINDING_FRAME_SCHEMA:
        raise _fail(
            code=AHK5702_SCHEMA_MISMATCH,
            message="scope binding frame schema mismatch",
            details={
                "path": path_text,
                "expected_schema": REPO_DESCRIPTIVE_NORMATIVE_BINDING_FRAME_SCHEMA,
                "observed_schema": payload.get("schema"),
            },
        )
    entries = payload.get("binding_entries")
    if not isinstance(entries, list):
        raise _fail(
            code=AHK5704_LINEAGE_UNRESOLVED,
            message="binding frame does not contain binding_entries",
            details={"path": path_text},
        )
    for entry in entries:
        if isinstance(entry, dict) and entry.get("entry_id") == entry_id:
            return payload, entry
    raise _fail(
        code=AHK5704_LINEAGE_UNRESOLVED,
        message="scope binding entry ref does not resolve to a binding entry",
        details={"ref": raw_ref},
    )


def _resolve_semantic_authority_inputs(
    *,
    root: Path,
    source_semantic_arc: str,
) -> tuple[Path, Path]:
    if not _SOURCE_ARC_RE.fullmatch(source_semantic_arc):
        raise _fail(
            code=AHK5703_CARDINALITY_VIOLATION,
            message="source_semantic_arc must match v<digits>",
            details={"source_semantic_arc": source_semantic_arc},
        )

    semantic_compiler_root = _safe_join(root, "artifacts/semantic_compiler")
    evidence_candidate = semantic_compiler_root / source_semantic_arc / "evidence_manifest.json"
    surface_diff_candidate = semantic_compiler_root / source_semantic_arc / "surface_diff.json"

    evidence_path = _resolve_under(
        semantic_compiler_root,
        evidence_candidate,
        details={
            "source_semantic_arc": source_semantic_arc,
            "candidate": str(evidence_candidate),
        },
    )
    surface_diff_path = _resolve_under(
        semantic_compiler_root,
        surface_diff_candidate,
        details={
            "source_semantic_arc": source_semantic_arc,
            "candidate": str(surface_diff_candidate),
        },
    )
    if not evidence_path.is_file() or not surface_diff_path.is_file():
        raise _fail(
            code=AHK5704_LINEAGE_UNRESOLVED,
            message=(
                "source_semantic_arc must resolve exactly one evidence_manifest "
                "and one surface_diff"
            ),
            details={
                "source_semantic_arc": source_semantic_arc,
                "evidence_path": str(evidence_path),
                "surface_diff_path": str(surface_diff_path),
            },
        )
    return evidence_path, surface_diff_path


def _coerce_binding_profile(
    *,
    root: Path,
    binding_profile_ref: str,
    binding_profile_semantic_hash: str,
) -> AnmTaskpackBindingProfile:
    binding_profile_path = _safe_join(root, binding_profile_ref)
    payload = _load_json_object(binding_profile_path)
    if payload.get("schema") != ANM_TASKPACK_BINDING_PROFILE_SCHEMA:
        raise _fail(
            code=AHK5702_SCHEMA_MISMATCH,
            message="binding profile schema mismatch",
            details={
                "binding_profile_ref": binding_profile_ref,
                "expected_schema": ANM_TASKPACK_BINDING_PROFILE_SCHEMA,
                "observed_schema": payload.get("schema"),
            },
        )
    try:
        profile = AnmTaskpackBindingProfile.model_validate(payload)
    except ValueError as exc:
        raise _fail(
            code=AHK5701_INPUT_INVALID,
            message="binding profile payload is invalid",
            details={"binding_profile_ref": binding_profile_ref, "error": str(exc)},
        ) from exc

    observed_payload_hash = payload.get("semantic_hash")
    if observed_payload_hash != profile.semantic_hash:
        raise _fail(
            code=AHK5707_HASH_DRIFT,
            message="binding profile semantic_hash field drift detected",
            details={
                "binding_profile_ref": binding_profile_ref,
                "payload_semantic_hash": observed_payload_hash,
                "computed_semantic_hash": profile.semantic_hash,
            },
        )
    if binding_profile_semantic_hash != profile.semantic_hash:
        raise _fail(
            code=AHK5705_LINEAGE_MISMATCH,
            message="binding profile semantic hash does not match the resolved profile",
            details={
                "binding_profile_ref": binding_profile_ref,
                "expected_binding_profile_semantic_hash": binding_profile_semantic_hash,
                "resolved_binding_profile_semantic_hash": profile.semantic_hash,
            },
        )
    return profile


def _revalidate_binding_profile_lineage(root: Path, profile: AnmTaskpackBindingProfile) -> None:
    scope_payload = _load_json_object(_safe_join(root, profile.scope_source_ref))
    scope_schema = scope_payload.get("schema")
    if scope_schema not in _SCOPE_SCHEMA_TO_BINDING_KIND:
        raise _fail(
            code=AHK5705_LINEAGE_MISMATCH,
            message="binding profile scope source must resolve to a supported released V45 surface",
            details={
                "scope_source_ref": profile.scope_source_ref,
                "observed_schema": scope_schema,
            },
        )
    descriptive_input_kind, bound_ref_field = _SCOPE_SCHEMA_TO_BINDING_KIND[scope_schema]
    if (
        scope_payload.get("repo_snapshot_id") != profile.snapshot_id
        or scope_payload.get("repo_snapshot_hash") != profile.snapshot_sha256
    ):
        raise _fail(
            code=AHK5705_LINEAGE_MISMATCH,
            message="binding profile snapshot must match the resolved scope surface",
            details={
                "binding_profile_ref": profile.binding_profile_id,
                "scope_source_ref": profile.scope_source_ref,
            },
        )

    _, policy_row = _resolve_policy_row(root, profile.policy_source_ref)
    if (
        policy_row.get("consumer_world_kind") != "released_v45_descriptive_artifact_world"
        or policy_row.get("consumer_ref_kind") != "released_v45_artifact_ref"
    ):
        raise _fail(
            code=AHK5705_LINEAGE_MISMATCH,
            message=(
                "binding profile policy carrier must resolve to a released "
                "V45 descriptive consumer row"
            ),
            details={"policy_source_ref": profile.policy_source_ref},
        )
    if policy_row.get("consumer_ref") != profile.scope_source_ref:
        raise _fail(
            code=AHK5705_LINEAGE_MISMATCH,
            message="resolved policy row must bind the same released scope surface",
            details={
                "policy_source_ref": profile.policy_source_ref,
                "scope_source_ref": profile.scope_source_ref,
                "row_consumer_ref": policy_row.get("consumer_ref"),
            },
        )
    if policy_row.get("policy_source_ref_kind") != "d1_clause_ref":
        raise _fail(
            code=AHK5705_LINEAGE_MISMATCH,
            message="resolved policy row must bind exactly one released D-IR clause ref",
            details={"policy_source_ref": profile.policy_source_ref},
        )
    if policy_row.get("policy_source_ref") != profile.policy_authority_clause_ref:
        raise _fail(
            code=AHK5705_LINEAGE_MISMATCH,
            message="binding profile policy authority clause ref drift detected",
            details={
                "policy_source_ref": profile.policy_source_ref,
                "binding_profile_clause_ref": profile.policy_authority_clause_ref,
                "resolved_clause_ref": policy_row.get("policy_source_ref"),
            },
        )

    binding_frame_payload, binding_entry = _resolve_binding_entry(
        root,
        profile.scope_binding_entry_ref,
    )
    if binding_entry.get("consumer_class") != "policy_consumer":
        raise _fail(
            code=AHK5705_LINEAGE_MISMATCH,
            message="binding profile scope entry must admit policy_consumer posture",
            details={"scope_binding_entry_ref": profile.scope_binding_entry_ref},
        )
    if binding_entry.get("descriptive_input_kind") != descriptive_input_kind:
        raise _fail(
            code=AHK5705_LINEAGE_MISMATCH,
            message="binding profile scope entry must admit the same descriptive scope kind",
            details={
                "scope_binding_entry_ref": profile.scope_binding_entry_ref,
                "expected_descriptive_input_kind": descriptive_input_kind,
                "observed_descriptive_input_kind": binding_entry.get("descriptive_input_kind"),
            },
        )
    bound_scope_anchor = binding_frame_payload.get(bound_ref_field)
    if not isinstance(bound_scope_anchor, str) or not bound_scope_anchor:
        raise _fail(
            code=AHK5704_LINEAGE_UNRESOLVED,
            message="binding frame is missing the bound scope anchor required by the entry",
            details={
                "scope_binding_entry_ref": profile.scope_binding_entry_ref,
                "bound_ref_field": bound_ref_field,
            },
        )


def _derive_policy_lineage_hash(profile: AnmTaskpackBindingProfile) -> str:
    return _stable_payload_hash(
        {
            "policy_binding_source_kind": profile.policy_binding_source_kind,
            "policy_source_ref": profile.policy_source_ref,
            "policy_authority_clause_ref": profile.policy_authority_clause_ref,
        }
    )


def _derive_scope_lineage_hash(profile: AnmTaskpackBindingProfile) -> str:
    return _stable_payload_hash(
        {
            "scope_binding_source_kind": profile.scope_binding_source_kind,
            "scope_source_ref": profile.scope_source_ref,
            "scope_binding_authority_kind": profile.scope_binding_authority_kind,
            "scope_binding_entry_ref": profile.scope_binding_entry_ref,
        }
    )


def _derive_compiled_boundary_identity_hash(
    *,
    binding_profile_semantic_hash: str,
    policy_lineage_hash: str,
    scope_lineage_hash: str,
    compiler_selection: str,
    declared_task_identity: str,
) -> str:
    return _stable_payload_hash(
        {
            "binding_profile_semantic_hash": binding_profile_semantic_hash,
            "policy_lineage_hash": policy_lineage_hash,
            "scope_lineage_hash": scope_lineage_hash,
            "compiler_selection": compiler_selection,
            "declared_task_identity": declared_task_identity,
        }
    )


def _build_pipeline_profile_payload(
    *,
    profile_id: str,
    binding_profile: AnmTaskpackBindingProfile,
    declared_task_identity: str,
    compiled_commitments_ir_path: str,
) -> dict[str, Any]:
    return {
        "schema": PIPELINE_PROFILE_SCHEMA,
        "profile_id": profile_id,
        "task_scope_title": (
            f"Compiled taskpack binding {binding_profile.binding_profile_id} "
            f"for {declared_task_identity}"
        ),
        "task_scope_summary": binding_profile.task_scope_summary,
        "compiled_commitments_ir_path": compiled_commitments_ir_path,
        "acceptance_criteria": [
            (
                f"Stay inside the allowlist projection carried by "
                f"{binding_profile.binding_profile_id}."
            ),
            (
                f"Avoid forbidden paths and forbidden effects carried by "
                f"{binding_profile.binding_profile_id}."
            ),
            (
                f"Use only the declared commands mapped from "
                f"{binding_profile.binding_profile_id}."
            ),
            (
                f"Populate the required evidence slots mapped from "
                f"{binding_profile.binding_profile_id} for {declared_task_identity}."
            ),
        ],
        "allowlist_paths": list(binding_profile.allowlist_projection),
        "forbidden_paths": list(binding_profile.forbidden_projection.forbidden_paths),
        "forbidden_effects": list(binding_profile.forbidden_projection.forbidden_effects),
        "commands": [
            {
                "command_id": command.command_id,
                "run": command.run,
                "working_directory_or_repo_root": command.working_directory_or_repo_root,
                "env_overrides": dict(command.env_overrides),
            }
            for command in binding_profile.command_projection
        ],
        "evidence_slots": [
            {
                "slot_id": slot.slot_id,
                "description": slot.description,
                "required": slot.required,
            }
            for slot in binding_profile.evidence_slot_projection
        ],
    }


def _build_profile_registry_payload(
    *,
    profile_id: str,
    profile_path: str,
    profile_sha256: str,
) -> dict[str, Any]:
    return {
        "schema": TASKPACK_PROFILE_REGISTRY_SCHEMA,
        "profiles": [
            {
                "profile_id": profile_id,
                "profile_payload_path": profile_path,
                "profile_sha256": profile_sha256,
            }
        ],
    }


def _map_compile_error(exc: TaskpackCompileError) -> CompiledPolicyTaskpackBindingError:
    code = AHK5706_BRIDGE_INVALID
    if exc.code in {"AHK0008", "AHK0009"}:
        code = AHK5704_LINEAGE_UNRESOLVED
    elif exc.code in {"AHK0006", "AHK0019", "AHK0020"}:
        code = AHK5707_HASH_DRIFT
    elif exc.code in {"AHK0015", "AHK0016"}:
        code = AHK5706_BRIDGE_INVALID
    return _fail(
        code=code,
        message=f"released compile_taskpack failed closed: {exc.message}",
        details={"compile_error_code": exc.code, **exc.details},
    )


def compile_v48b_taskpack_binding(
    *,
    binding_profile_refs: list[str],
    binding_profile_semantic_hash: str,
    compiler_selections: list[str],
    declared_task_identities: list[str],
    source_semantic_arcs: list[str],
    compiled_commitments_ir_path: str,
    out_dir: str | Path,
    repo_root_path: Path | None = None,
) -> CompiledPolicyTaskpackBindingResult:
    root = repo_root(anchor=repo_root_path or Path(__file__))
    binding_profile_ref = _require_exactly_one(
        binding_profile_refs,
        field_name="binding_profile_refs",
    )
    compiler_selection = _require_exactly_one(
        compiler_selections,
        field_name="compiler_selections",
    )
    declared_task_identity = _require_exactly_one(
        declared_task_identities,
        field_name="declared_task_identities",
    )
    source_semantic_arc = _require_exactly_one(
        source_semantic_arcs,
        field_name="source_semantic_arcs",
    )
    binding_profile_semantic_hash = _require_non_empty(
        binding_profile_semantic_hash,
        field_name="binding_profile_semantic_hash",
    )
    compiled_commitments_ir_path = _normalize_relative_path(compiled_commitments_ir_path)
    out_rel = _normalize_relative_path(str(out_dir))
    out_path = _safe_join(root, out_rel)

    if compiler_selection != RELEASED_TASKPACK_COMPILER_SELECTION:
        raise _fail(
            code=AHK5708_UNSUPPORTED_COMPILATION,
            message="compiler_selection must resolve to the released taskpack compiler entrypoint",
            details={"compiler_selection": compiler_selection},
        )

    binding_profile = _coerce_binding_profile(
        root=root,
        binding_profile_ref=binding_profile_ref,
        binding_profile_semantic_hash=binding_profile_semantic_hash,
    )
    _revalidate_binding_profile_lineage(root, binding_profile)

    commitments_ir_payload = _load_json_object(_safe_join(root, compiled_commitments_ir_path))
    if commitments_ir_payload.get("schema") != COMMITMENTS_IR_SCHEMA:
        raise _fail(
            code=AHK5702_SCHEMA_MISMATCH,
            message="compiled_commitments_ir_path schema mismatch",
            details={
                "compiled_commitments_ir_path": compiled_commitments_ir_path,
                "expected_schema": COMMITMENTS_IR_SCHEMA,
                "observed_schema": commitments_ir_payload.get("schema"),
            },
        )

    evidence_manifest_path, surface_diff_path = _resolve_semantic_authority_inputs(
        root=root,
        source_semantic_arc=source_semantic_arc,
    )
    evidence_manifest_payload = _load_json_object(evidence_manifest_path)
    if evidence_manifest_payload.get("schema") != SEMANTIC_COMPILER_EVIDENCE_MANIFEST_SCHEMA:
        raise _fail(
            code=AHK5702_SCHEMA_MISMATCH,
            message="semantic compiler evidence manifest schema mismatch",
            details={
                "path": _to_repo_relative(evidence_manifest_path, root=root),
                "expected_schema": SEMANTIC_COMPILER_EVIDENCE_MANIFEST_SCHEMA,
                "observed_schema": evidence_manifest_payload.get("schema"),
            },
        )
    surface_diff_payload = _load_json_object(surface_diff_path)
    if surface_diff_payload.get("schema") != SEMANTIC_COMPILER_SURFACE_DIFF_SCHEMA:
        raise _fail(
            code=AHK5702_SCHEMA_MISMATCH,
            message="semantic compiler surface diff schema mismatch",
            details={
                "path": _to_repo_relative(surface_diff_path, root=root),
                "expected_schema": SEMANTIC_COMPILER_SURFACE_DIFF_SCHEMA,
                "observed_schema": surface_diff_payload.get("schema"),
            },
        )

    policy_lineage_hash = _derive_policy_lineage_hash(binding_profile)
    scope_lineage_hash = _derive_scope_lineage_hash(binding_profile)
    compiled_boundary_identity_hash = _derive_compiled_boundary_identity_hash(
        binding_profile_semantic_hash=binding_profile.semantic_hash,
        policy_lineage_hash=policy_lineage_hash,
        scope_lineage_hash=scope_lineage_hash,
        compiler_selection=compiler_selection,
        declared_task_identity=declared_task_identity,
    )
    profile_id = f"v48b_{compiled_boundary_identity_hash[:12]}"

    pipeline_profile_path = out_path / "pipeline_profile.json"
    profile_registry_path = out_path / "taskpack_profile_registry.json"
    compiled_binding_path = out_path / "compiled_policy_taskpack_binding.json"

    pipeline_payload = _build_pipeline_profile_payload(
        profile_id=profile_id,
        binding_profile=binding_profile,
        declared_task_identity=declared_task_identity,
        compiled_commitments_ir_path=compiled_commitments_ir_path,
    )
    pipeline_profile_sha256 = _write_json(pipeline_profile_path, pipeline_payload)
    pipeline_profile_ref = _to_repo_relative(pipeline_profile_path, root=root)

    profile_registry_payload = _build_profile_registry_payload(
        profile_id=profile_id,
        profile_path=pipeline_profile_ref,
        profile_sha256=pipeline_profile_sha256,
    )
    profile_registry_sha256 = _write_json(profile_registry_path, profile_registry_payload)
    profile_registry_ref = _to_repo_relative(profile_registry_path, root=root)

    try:
        compile_result = compile_taskpack(
            profile_registry_path=profile_registry_ref,
            profile_id=profile_id,
            source_semantic_arc=source_semantic_arc,
            out_dir=out_rel,
            repo_root_path=root,
        )
    except TaskpackCompileError as exc:
        raise _map_compile_error(exc) from exc

    verified_snapshot = load_verified_taskpack_snapshot(
        out_dir=out_rel,
        repo_root_path=root,
    )
    if compile_result.taskpack_manifest_sha256 != verified_snapshot.manifest_hash:
        raise _fail(
            code=AHK5707_HASH_DRIFT,
            message="compiled manifest sha256 drift detected after verification replay",
            details={
                "compile_result_manifest_sha256": compile_result.taskpack_manifest_sha256,
                "verified_manifest_sha256": verified_snapshot.manifest_hash,
            },
        )

    try:
        compiled_binding = CompiledPolicyTaskpackBinding.model_validate(
            {
                "schema": COMPILED_POLICY_TASKPACK_BINDING_SCHEMA,
                "compiled_binding_id": (
                    f"compiled-taskpack-binding:{compiled_boundary_identity_hash[:12]}"
                ),
                "snapshot_id": binding_profile.snapshot_id,
                "snapshot_sha256": binding_profile.snapshot_sha256,
                "binding_profile_source_kind": "released_anm_taskpack_binding_profile_ref",
                "binding_profile_ref": binding_profile_ref,
                "binding_profile_semantic_hash": binding_profile.semantic_hash,
                "policy_lineage_hash": policy_lineage_hash,
                "scope_lineage_hash": scope_lineage_hash,
                "binding_subject_id": binding_profile.binding_subject_id,
                "worker_subject_kind": binding_profile.worker_subject_kind,
                "worker_subject_ref": binding_profile.worker_subject_ref,
                "compiler_selection_kind": "released_adeu_agent_harness_taskpack_compiler",
                "compiler_selection": compiler_selection,
                "source_semantic_arc": source_semantic_arc,
                "declared_task_identity": declared_task_identity,
                "kernel_bridge_posture": (
                    "released_pipeline_profile_and_registry_then_compile_taskpack"
                ),
                "pipeline_profile_ref": pipeline_profile_ref,
                "pipeline_profile_sha256": pipeline_profile_sha256,
                "profile_registry_ref": profile_registry_ref,
                "profile_registry_sha256": profile_registry_sha256,
                "compiled_commitments_ir_path": compiled_commitments_ir_path,
                "semantic_compiler_evidence_manifest_path": _to_repo_relative(
                    evidence_manifest_path,
                    root=root,
                ),
                "semantic_compiler_surface_diff_path": _to_repo_relative(
                    surface_diff_path,
                    root=root,
                ),
                "compiled_boundary_identity_posture": "binding_lineage_plus_task_identity_hash",
                "compiled_boundary_identity_hash": compiled_boundary_identity_hash,
                "compiled_component_set_kind": "released_taskpack_bundle_component_set",
                "taskpack_markdown_ref": _to_repo_relative(
                    compile_result.taskpack_markdown_path,
                    root=root,
                ),
                "acceptance_ref": _to_repo_relative(compile_result.acceptance_path, root=root),
                "allowlist_ref": _to_repo_relative(compile_result.allowlist_path, root=root),
                "forbidden_ref": _to_repo_relative(compile_result.forbidden_path, root=root),
                "commands_ref": _to_repo_relative(compile_result.commands_path, root=root),
                "evidence_slots_ref": _to_repo_relative(
                    compile_result.evidence_slots_path,
                    root=root,
                ),
                "taskpack_manifest_ref": _to_repo_relative(compile_result.manifest_path, root=root),
                "manifest_sha256": verified_snapshot.manifest_hash,
                "bundle_hash": verified_snapshot.bundle_hash,
                "unsupported_compilation_posture": "fail_closed",
                "semantic_hash": "derived-by-model-validator",
            }
        )
    except ValueError as exc:
        raise _fail(
            code=AHK5706_BRIDGE_INVALID,
            message="compiled binding payload failed validation",
            details={"error": str(exc)},
        ) from exc

    compiled_binding_path.parent.mkdir(parents=True, exist_ok=True)
    compiled_binding_path.write_text(
        _serialize_payload(compiled_binding.model_dump(mode="json", exclude_none=True)),
        encoding="utf-8",
    )

    return CompiledPolicyTaskpackBindingResult(
        compiled_binding=compiled_binding,
        compiled_binding_path=compiled_binding_path,
        pipeline_profile_path=pipeline_profile_path,
        profile_registry_path=profile_registry_path,
    )
