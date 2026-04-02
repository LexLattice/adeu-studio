from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, Literal

from adeu_ir.repo import repo_root
from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import canonical_json, sha256_canonical_json

ANM_TASKPACK_BINDING_PROFILE_SCHEMA = "anm_taskpack_binding_profile@1"
TASKPACK_BINDING_ERROR_SCHEMA = "taskpack_binding_error@1"

PolicyBindingSourceKind = Literal["released_v47e_policy_consumer_row_ref"]
ScopeBindingSourceKind = Literal["released_v45_scope_surface_ref"]
ScopeBindingAuthorityKind = Literal["released_v45f_binding_entry_ref"]
WorkerSubjectKind = Literal["repo_internal_single_codex_worker"]
PromptProjectionPosture = Literal["projection_only_non_authoritative"]
LineageResolutionPosture = Literal["fail_closed_on_unresolved_or_stale_lineage"]
UnsupportedMappingPosture = Literal["fail_closed"]

ANM_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA = "anm_policy_consumer_binding_profile@1"
REPO_DESCRIPTIVE_NORMATIVE_BINDING_FRAME_SCHEMA = "repo_descriptive_normative_binding_frame@1"

_JSON_REF_SPLIT = "#"
_POLICY_ROW_FRAGMENT_RE = re.compile(r"consumer_rows\[(?P<index>\d+)\]")
_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"^[A-Za-z]:[\\/]")

AHK5601_INPUT_INVALID = "AHK5601"
AHK5602_SCHEMA_MISMATCH = "AHK5602"
AHK5603_CARDINALITY_VIOLATION = "AHK5603"
AHK5604_LINEAGE_UNRESOLVED = "AHK5604"
AHK5605_LINEAGE_MISMATCH = "AHK5605"
AHK5606_PROJECTION_CONFLICT = "AHK5606"
AHK5607_PROMPT_AUTHORITY_DRIFT = "AHK5607"
AHK5608_UNSUPPORTED_MAPPING = "AHK5608"

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


def _require_non_empty(value: str, *, field_name: str) -> str:
    normalized = value.strip()
    if not normalized:
        raise ValueError(f"{field_name} must not be empty")
    return normalized


def _require_sorted_unique(values: list[str], *, field_name: str) -> None:
    if any(not item for item in values):
        raise ValueError(f"{field_name} must not contain empty values")
    if values != sorted(values):
        raise ValueError(f"{field_name} must be lexicographically sorted")
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")


class TaskpackCommandProjection(BaseModel):
    model_config = ConfigDict(extra="forbid")

    command_id: str = Field(min_length=1)
    run: str = Field(min_length=1)
    working_directory_or_repo_root: str = Field(min_length=1)
    env_overrides: dict[str, str] = Field(default_factory=dict)

    @model_validator(mode="after")
    def _validate_contract(self) -> "TaskpackCommandProjection":
        self.command_id = _require_non_empty(self.command_id, field_name="command_id")
        self.run = _require_non_empty(self.run, field_name="run")
        self.working_directory_or_repo_root = _require_non_empty(
            self.working_directory_or_repo_root,
            field_name="working_directory_or_repo_root",
        )
        for key, value in sorted(self.env_overrides.items()):
            if not key or not value:
                raise ValueError("env_overrides must contain only non-empty string pairs")
        return self


class TaskpackEvidenceSlotProjection(BaseModel):
    model_config = ConfigDict(extra="forbid")

    slot_id: str = Field(min_length=1)
    description: str = Field(min_length=1)
    required: bool

    @model_validator(mode="after")
    def _validate_contract(self) -> "TaskpackEvidenceSlotProjection":
        self.slot_id = _require_non_empty(self.slot_id, field_name="slot_id")
        self.description = _require_non_empty(self.description, field_name="description")
        return self


class TaskpackForbiddenProjection(BaseModel):
    model_config = ConfigDict(extra="forbid")

    forbidden_paths: list[str] = Field(min_length=1)
    forbidden_effects: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "TaskpackForbiddenProjection":
        _require_sorted_unique(self.forbidden_paths, field_name="forbidden_paths")
        _require_sorted_unique(self.forbidden_effects, field_name="forbidden_effects")
        return self


class AnmTaskpackBindingProfile(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: Literal["anm_taskpack_binding_profile@1"] = ANM_TASKPACK_BINDING_PROFILE_SCHEMA
    binding_profile_id: str = Field(min_length=1)
    snapshot_id: str = Field(min_length=1)
    snapshot_sha256: str = Field(min_length=1)
    binding_subject_id: str = Field(min_length=1)
    task_scope_summary: str = Field(min_length=1)
    policy_binding_source_kind: PolicyBindingSourceKind
    policy_source_ref: str = Field(min_length=1)
    policy_authority_clause_ref: str = Field(min_length=1)
    scope_binding_source_kind: ScopeBindingSourceKind
    scope_source_ref: str = Field(min_length=1)
    scope_binding_authority_kind: ScopeBindingAuthorityKind
    scope_binding_entry_ref: str = Field(min_length=1)
    worker_subject_kind: WorkerSubjectKind
    worker_subject_ref: str = Field(min_length=1)
    allowlist_projection: list[str] = Field(min_length=1)
    forbidden_projection: TaskpackForbiddenProjection
    command_projection: list[TaskpackCommandProjection] = Field(min_length=1)
    evidence_slot_projection: list[TaskpackEvidenceSlotProjection] = Field(min_length=1)
    prompt_projection_posture: PromptProjectionPosture
    lineage_resolution_posture: LineageResolutionPosture
    unsupported_mapping_posture: UnsupportedMappingPosture
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmTaskpackBindingProfile":
        self.binding_profile_id = _require_non_empty(
            self.binding_profile_id,
            field_name="binding_profile_id",
        )
        self.snapshot_id = _require_non_empty(self.snapshot_id, field_name="snapshot_id")
        self.snapshot_sha256 = _require_non_empty(
            self.snapshot_sha256,
            field_name="snapshot_sha256",
        )
        self.binding_subject_id = _require_non_empty(
            self.binding_subject_id,
            field_name="binding_subject_id",
        )
        self.task_scope_summary = _require_non_empty(
            self.task_scope_summary,
            field_name="task_scope_summary",
        )
        self.policy_source_ref = _require_non_empty(
            self.policy_source_ref,
            field_name="policy_source_ref",
        )
        self.policy_authority_clause_ref = _require_non_empty(
            self.policy_authority_clause_ref,
            field_name="policy_authority_clause_ref",
        )
        self.scope_source_ref = _require_non_empty(
            self.scope_source_ref,
            field_name="scope_source_ref",
        )
        self.scope_binding_entry_ref = _require_non_empty(
            self.scope_binding_entry_ref,
            field_name="scope_binding_entry_ref",
        )
        self.worker_subject_ref = _require_non_empty(
            self.worker_subject_ref,
            field_name="worker_subject_ref",
        )
        _require_sorted_unique(self.allowlist_projection, field_name="allowlist_projection")

        if set(self.allowlist_projection) & set(self.forbidden_projection.forbidden_paths):
            raise ValueError(
                "allowlist_projection and forbidden_projection.forbidden_paths must not overlap"
            )

        command_ids = [row.command_id for row in self.command_projection]
        if command_ids != sorted(command_ids):
            raise ValueError("command_projection must be sorted by command_id")
        if len(command_ids) != len(set(command_ids)):
            raise ValueError("command_projection command_id values must be unique")

        slot_ids = [row.slot_id for row in self.evidence_slot_projection]
        if slot_ids != sorted(slot_ids):
            raise ValueError("evidence_slot_projection must be sorted by slot_id")
        if len(slot_ids) != len(set(slot_ids)):
            raise ValueError("evidence_slot_projection slot_id values must be unique")

        payload = self.model_dump(mode="json", exclude={"semantic_hash"})
        self.semantic_hash = _stable_payload_hash(payload)
        return self


class PromptProjectionInput(BaseModel):
    model_config = ConfigDict(extra="forbid")

    source_kind: Literal["prompt_text", "chat_prose", "agents_md"]
    text: str = Field(min_length=1)
    path_mentions: list[str] = Field(default_factory=list)
    command_ids_mentioned: list[str] = Field(default_factory=list)
    evidence_slot_ids_mentioned: list[str] = Field(default_factory=list)
    extra_authority_claims: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "PromptProjectionInput":
        self.text = _require_non_empty(self.text, field_name="text")
        _require_sorted_unique(self.path_mentions, field_name="path_mentions")
        _require_sorted_unique(
            self.command_ids_mentioned,
            field_name="command_ids_mentioned",
        )
        _require_sorted_unique(
            self.evidence_slot_ids_mentioned,
            field_name="evidence_slot_ids_mentioned",
        )
        _require_sorted_unique(
            self.extra_authority_claims,
            field_name="extra_authority_claims",
        )
        return self


class TaskpackBindingError(RuntimeError):
    def __init__(self, *, code: str, message: str, details: dict[str, Any] | None = None) -> None:
        self.code = code
        self.message = message
        self.details = details or {}
        payload = {
            "schema": TASKPACK_BINDING_ERROR_SCHEMA,
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
) -> TaskpackBindingError:
    return TaskpackBindingError(code=code, message=message, details=details)


def _normalize_relative_path(raw_path: str) -> str:
    path_text = raw_path.strip().replace("\\", "/")
    if not path_text:
        raise _fail(
            code=AHK5601_INPUT_INVALID,
            message="path must not be empty",
            details={"path": raw_path},
        )
    if path_text.startswith("/"):
        raise _fail(
            code=AHK5601_INPUT_INVALID,
            message="absolute paths are forbidden",
            details={"path": raw_path},
        )
    if _WINDOWS_ABSOLUTE_PATH_RE.match(path_text):
        raise _fail(
            code=AHK5601_INPUT_INVALID,
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
                    code=AHK5601_INPUT_INVALID,
                    message="path escapes repository root",
                    details={"path": raw_path},
                )
            segments.pop()
            continue
        segments.append(segment)

    if not segments:
        raise _fail(
            code=AHK5601_INPUT_INVALID,
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
            code=AHK5601_INPUT_INVALID,
            message="resolved path escapes repository root",
            details={"path": rel_path},
        ) from exc
    return path


def _load_json_object(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise _fail(
            code=AHK5604_LINEAGE_UNRESOLVED,
            message="required json path does not exist",
            details={"path": str(path)},
        ) from exc
    except OSError as exc:
        raise _fail(
            code=AHK5604_LINEAGE_UNRESOLVED,
            message="required json path cannot be read",
            details={"path": str(path), "error": str(exc)},
        ) from exc
    except json.JSONDecodeError as exc:
        raise _fail(
            code=AHK5601_INPUT_INVALID,
            message="json payload is invalid",
            details={"path": str(path), "error": str(exc)},
        ) from exc
    if not isinstance(payload, dict):
        raise _fail(
            code=AHK5601_INPUT_INVALID,
            message="json payload must decode to an object",
            details={"path": str(path)},
        )
    return payload


def _require_exactly_one(values: list[str], *, field_name: str) -> str:
    if not isinstance(values, list) or len(values) != 1:
        count = len(values) if isinstance(values, list) else None
        raise _fail(
            code=AHK5603_CARDINALITY_VIOLATION,
            message=f"{field_name} must contain exactly one value",
            details={"field_name": field_name, "count": count},
        )
    value = values[0]
    if not isinstance(value, str) or not value.strip():
        raise _fail(
            code=AHK5601_INPUT_INVALID,
            message=f"{field_name} must contain exactly one non-empty string",
            details={"field_name": field_name},
        )
    return value.strip()


def _split_json_ref(raw_ref: str, *, field_name: str) -> tuple[str, str]:
    if _JSON_REF_SPLIT not in raw_ref:
        raise _fail(
            code=AHK5604_LINEAGE_UNRESOLVED,
            message=f"{field_name} must include a # fragment",
            details={"field_name": field_name, "ref": raw_ref},
        )
    path_text, fragment = raw_ref.split(_JSON_REF_SPLIT, 1)
    normalized_path = _normalize_relative_path(path_text)
    fragment = fragment.strip()
    if not fragment:
        raise _fail(
            code=AHK5604_LINEAGE_UNRESOLVED,
            message=f"{field_name} fragment must not be empty",
            details={"field_name": field_name, "ref": raw_ref},
        )
    return normalized_path, fragment


def _resolve_policy_row(root: Path, raw_ref: str) -> tuple[str, dict[str, Any]]:
    path_text, fragment = _split_json_ref(raw_ref, field_name="policy_source_refs")
    match = _POLICY_ROW_FRAGMENT_RE.fullmatch(fragment)
    if match is None:
        raise _fail(
            code=AHK5604_LINEAGE_UNRESOLVED,
            message="policy_source_ref fragment must match consumer_rows[<index>]",
            details={"ref": raw_ref},
        )
    index = int(match.group("index"))
    path = _safe_join(root, path_text)
    payload = _load_json_object(path)
    if payload.get("schema") != ANM_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA:
        raise _fail(
            code=AHK5602_SCHEMA_MISMATCH,
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
            code=AHK5604_LINEAGE_UNRESOLVED,
            message="policy source row ref does not resolve to a consumer row",
            details={"ref": raw_ref},
        )
    row = rows[index]
    if not isinstance(row, dict):
        raise _fail(
            code=AHK5604_LINEAGE_UNRESOLVED,
            message="resolved consumer row is invalid",
            details={"ref": raw_ref},
        )
    return path_text, row


def _resolve_binding_entry(root: Path, raw_ref: str) -> tuple[str, dict[str, Any], dict[str, Any]]:
    path_text, entry_id = _split_json_ref(raw_ref, field_name="scope_binding_entry_refs")
    path = _safe_join(root, path_text)
    payload = _load_json_object(path)
    if payload.get("schema") != REPO_DESCRIPTIVE_NORMATIVE_BINDING_FRAME_SCHEMA:
        raise _fail(
            code=AHK5602_SCHEMA_MISMATCH,
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
            code=AHK5604_LINEAGE_UNRESOLVED,
            message="binding frame does not contain binding_entries",
            details={"path": path_text},
        )
    for entry in entries:
        if isinstance(entry, dict) and entry.get("entry_id") == entry_id:
            return path_text, payload, entry
    raise _fail(
        code=AHK5604_LINEAGE_UNRESOLVED,
        message="scope binding entry ref does not resolve to a binding entry",
        details={"ref": raw_ref},
    )


def _sorted_commands(values: list[dict[str, Any]]) -> list[dict[str, Any]]:
    normalized = []
    for value in values:
        env_overrides = value.get("env_overrides", {})
        normalized.append(
            {
                "command_id": value["command_id"],
                "run": value["run"],
                "working_directory_or_repo_root": value["working_directory_or_repo_root"],
                "env_overrides": {
                    key: env_overrides[key]
                    for key in sorted(env_overrides)
                },
            }
        )
    return sorted(normalized, key=lambda item: item["command_id"])


def _sorted_evidence_slots(values: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return sorted(
        [
            {
                "slot_id": value["slot_id"],
                "description": value["description"],
                "required": value["required"],
            }
            for value in values
        ],
        key=lambda item: item["slot_id"],
    )


def _validate_prompt_projection_inputs(
    prompt_projection_inputs: list[dict[str, Any]],
    *,
    allowed_paths: set[str],
    command_ids: set[str],
    evidence_slot_ids: set[str],
) -> None:
    for raw_input in prompt_projection_inputs:
        prompt_input = PromptProjectionInput.model_validate(raw_input)
        if prompt_input.extra_authority_claims:
            raise _fail(
                code=AHK5607_PROMPT_AUTHORITY_DRIFT,
                message="prompt projection inputs must not add authority beyond the typed boundary",
                details={"source_kind": prompt_input.source_kind},
            )
        if not set(prompt_input.path_mentions).issubset(allowed_paths):
            raise _fail(
                code=AHK5607_PROMPT_AUTHORITY_DRIFT,
                message="prompt projection path mentions must be a subset of typed boundary paths",
                details={
                    "source_kind": prompt_input.source_kind,
                    "path_mentions": prompt_input.path_mentions,
                },
            )
        if not set(prompt_input.command_ids_mentioned).issubset(command_ids):
            raise _fail(
                code=AHK5607_PROMPT_AUTHORITY_DRIFT,
                message="prompt projection command mentions must be a subset of typed commands",
                details={
                    "source_kind": prompt_input.source_kind,
                    "command_ids_mentioned": prompt_input.command_ids_mentioned,
                },
            )
        if not set(prompt_input.evidence_slot_ids_mentioned).issubset(evidence_slot_ids):
            raise _fail(
                code=AHK5607_PROMPT_AUTHORITY_DRIFT,
                message="prompt projection evidence-slot mentions must be a subset of typed slots",
                details={
                    "source_kind": prompt_input.source_kind,
                    "evidence_slot_ids_mentioned": prompt_input.evidence_slot_ids_mentioned,
                },
            )


def build_v48a_taskpack_binding_profile(
    *,
    binding_profile_id: str,
    snapshot_id: str,
    snapshot_sha256: str,
    binding_subject_ids: list[str],
    task_scope_summary: str,
    policy_source_refs: list[str],
    scope_source_refs: list[str],
    scope_binding_entry_refs: list[str],
    worker_subject_refs: list[str],
    allowlist_projection: list[str],
    forbidden_projection: dict[str, Any],
    command_projection: list[dict[str, Any]],
    evidence_slot_projection: list[dict[str, Any]],
    prompt_projection_inputs: list[dict[str, Any]] | None = None,
    repo_root_path: Path | None = None,
) -> AnmTaskpackBindingProfile:
    root = repo_root_path or repo_root(anchor=Path(__file__))
    binding_subject_id = _require_exactly_one(
        binding_subject_ids,
        field_name="binding_subject_ids",
    )
    policy_source_ref = _require_exactly_one(
        policy_source_refs,
        field_name="policy_source_refs",
    )
    scope_source_ref = _require_exactly_one(
        scope_source_refs,
        field_name="scope_source_refs",
    )
    scope_binding_entry_ref = _require_exactly_one(
        scope_binding_entry_refs,
        field_name="scope_binding_entry_refs",
    )
    worker_subject_ref = _require_exactly_one(
        worker_subject_refs,
        field_name="worker_subject_refs",
    )

    scope_path = _safe_join(root, scope_source_ref)
    scope_payload = _load_json_object(scope_path)
    scope_schema = scope_payload.get("schema")
    if scope_schema not in _SCOPE_SCHEMA_TO_BINDING_KIND:
        raise _fail(
            code=AHK5608_UNSUPPORTED_MAPPING,
            message="scope source ref must resolve to a supported released V45 surface",
            details={"scope_source_ref": scope_source_ref, "observed_schema": scope_schema},
        )
    descriptive_input_kind, bound_ref_field = _SCOPE_SCHEMA_TO_BINDING_KIND[scope_schema]

    observed_snapshot_id = scope_payload.get("repo_snapshot_id")
    observed_snapshot_sha256 = scope_payload.get("repo_snapshot_hash")
    if observed_snapshot_id != snapshot_id or observed_snapshot_sha256 != snapshot_sha256:
        raise _fail(
            code=AHK5605_LINEAGE_MISMATCH,
            message="binding profile snapshot must match the bound released V45 scope surface",
            details={
                "scope_source_ref": scope_source_ref,
                "expected_snapshot_id": observed_snapshot_id,
                "expected_snapshot_sha256": observed_snapshot_sha256,
                "snapshot_id": snapshot_id,
                "snapshot_sha256": snapshot_sha256,
            },
        )

    _, policy_row = _resolve_policy_row(root, policy_source_ref)
    if (
        policy_row.get("consumer_world_kind") != "released_v45_descriptive_artifact_world"
        or policy_row.get("consumer_ref_kind") != "released_v45_artifact_ref"
    ):
        raise _fail(
            code=AHK5605_LINEAGE_MISMATCH,
            message="V48-A policy carrier must resolve to a released V45 descriptive consumer row",
            details={"policy_source_ref": policy_source_ref},
        )
    if policy_row.get("consumer_ref") != scope_source_ref:
        raise _fail(
            code=AHK5605_LINEAGE_MISMATCH,
            message="resolved V47-E consumer row must bind the same released scope surface",
            details={
                "policy_source_ref": policy_source_ref,
                "row_consumer_ref": policy_row.get("consumer_ref"),
                "scope_source_ref": scope_source_ref,
            },
        )
    if policy_row.get("policy_source_ref_kind") != "d1_clause_ref":
        raise _fail(
            code=AHK5605_LINEAGE_MISMATCH,
            message="resolved V47-E consumer row must bind exactly one released D-IR clause ref",
            details={"policy_source_ref": policy_source_ref},
        )
    policy_authority_clause_ref = policy_row.get("policy_source_ref")
    if not isinstance(policy_authority_clause_ref, str) or not policy_authority_clause_ref.strip():
        raise _fail(
            code=AHK5605_LINEAGE_MISMATCH,
            message="resolved V47-E consumer row must carry a non-empty bound D-IR clause ref",
            details={"policy_source_ref": policy_source_ref},
        )

    _, binding_frame_payload, binding_entry = _resolve_binding_entry(root, scope_binding_entry_ref)
    if binding_entry.get("consumer_class") != "policy_consumer":
        raise _fail(
            code=AHK5605_LINEAGE_MISMATCH,
            message="V45-F binding entry must admit policy_consumer posture for V48-A",
            details={"scope_binding_entry_ref": scope_binding_entry_ref},
        )
    if binding_entry.get("descriptive_input_kind") != descriptive_input_kind:
        raise _fail(
            code=AHK5605_LINEAGE_MISMATCH,
            message="V45-F binding entry must admit the same descriptive scope kind",
            details={
                "scope_binding_entry_ref": scope_binding_entry_ref,
                "expected_descriptive_input_kind": descriptive_input_kind,
                "observed_descriptive_input_kind": binding_entry.get("descriptive_input_kind"),
            },
        )
    bound_scope_anchor = binding_frame_payload.get(bound_ref_field)
    if not isinstance(bound_scope_anchor, str) or not bound_scope_anchor:
        raise _fail(
            code=AHK5604_LINEAGE_UNRESOLVED,
            message="V45-F binding frame is missing the bound scope anchor required by the entry",
            details={
                "scope_binding_entry_ref": scope_binding_entry_ref,
                "bound_ref_field": bound_ref_field,
            },
        )

    sorted_allowlist = sorted({_normalize_relative_path(path) for path in allowlist_projection})
    raw_forbidden_paths = forbidden_projection.get("forbidden_paths", [])
    normalized_forbidden = {
        "forbidden_paths": sorted(
            {_normalize_relative_path(path) for path in raw_forbidden_paths}
        ),
        "forbidden_effects": sorted(
            {
                _require_non_empty(effect, field_name="forbidden_effect")
                for effect in forbidden_projection.get("forbidden_effects", [])
            }
        ),
    }
    sorted_commands = _sorted_commands(command_projection)
    sorted_slots = _sorted_evidence_slots(evidence_slot_projection)

    overlapping_paths = sorted(set(sorted_allowlist) & set(normalized_forbidden["forbidden_paths"]))
    if set(sorted_allowlist) & set(normalized_forbidden["forbidden_paths"]):
        raise _fail(
            code=AHK5606_PROJECTION_CONFLICT,
            message="allowlist_projection and forbidden_projection paths must not overlap",
            details={"overlap": overlapping_paths},
        )

    _validate_prompt_projection_inputs(
        prompt_projection_inputs or [],
        allowed_paths=set(sorted_allowlist) | set(normalized_forbidden["forbidden_paths"]),
        command_ids={item["command_id"] for item in sorted_commands},
        evidence_slot_ids={item["slot_id"] for item in sorted_slots},
    )

    try:
        return AnmTaskpackBindingProfile.model_validate(
            {
                "schema": ANM_TASKPACK_BINDING_PROFILE_SCHEMA,
                "binding_profile_id": binding_profile_id,
                "snapshot_id": snapshot_id,
                "snapshot_sha256": snapshot_sha256,
                "binding_subject_id": binding_subject_id,
                "task_scope_summary": task_scope_summary,
                "policy_binding_source_kind": "released_v47e_policy_consumer_row_ref",
                "policy_source_ref": policy_source_ref,
                "policy_authority_clause_ref": policy_authority_clause_ref,
                "scope_binding_source_kind": "released_v45_scope_surface_ref",
                "scope_source_ref": scope_source_ref,
                "scope_binding_authority_kind": "released_v45f_binding_entry_ref",
                "scope_binding_entry_ref": scope_binding_entry_ref,
                "worker_subject_kind": "repo_internal_single_codex_worker",
                "worker_subject_ref": worker_subject_ref,
                "allowlist_projection": sorted_allowlist,
                "forbidden_projection": normalized_forbidden,
                "command_projection": sorted_commands,
                "evidence_slot_projection": sorted_slots,
                "prompt_projection_posture": "projection_only_non_authoritative",
                "lineage_resolution_posture": "fail_closed_on_unresolved_or_stale_lineage",
                "unsupported_mapping_posture": "fail_closed",
                "semantic_hash": "derived-by-model-validator",
            }
        )
    except ValueError as exc:
        raise _fail(
            code=AHK5606_PROJECTION_CONFLICT,
            message=str(exc),
        ) from exc
