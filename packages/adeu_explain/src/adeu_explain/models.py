from __future__ import annotations

from typing import Any

from adeu_ir import SourceSpan, ValidatorAtomRef
from adeu_ir.models import JsonPatchOp
from pydantic import BaseModel, ConfigDict, Field


class AtomRef(BaseModel):
    model_config = ConfigDict(extra="forbid")
    object_id: str | None = None
    json_path: str | None = None


class ValidatorRunInput(BaseModel):
    model_config = ConfigDict(extra="forbid")
    run_id: str | None = None
    created_at: str | None = None
    backend: str | None = None
    backend_version: str | None = None
    timeout_ms: int | None = None
    options_json: dict[str, Any] = Field(default_factory=dict)
    request_hash: str | None = None
    formula_hash: str | None = None
    status: str | None = None
    evidence_json: dict[str, Any] = Field(default_factory=dict)
    atom_map_json: dict[str, AtomRef] | list[ValidatorAtomRef] = Field(default_factory=dict)


class ValidatorRunRef(BaseModel):
    model_config = ConfigDict(extra="forbid")
    run_id: str | None = None
    created_at: str | None = None
    backend: str | None = None
    backend_version: str | None = None
    timeout_ms: int | None = None
    options_json: dict[str, Any] = Field(default_factory=dict)
    request_hash: str | None = None
    formula_hash: str | None = None
    status: str | None = None
    evidence_json: dict[str, Any] = Field(default_factory=dict)
    atom_map_json: dict[str, AtomRef] = Field(default_factory=dict)


class CoreDelta(BaseModel):
    model_config = ConfigDict(extra="forbid")
    added_atoms: list[str] = Field(default_factory=list)
    removed_atoms: list[str] = Field(default_factory=list)


class ModelAssignment(BaseModel):
    model_config = ConfigDict(extra="forbid")
    atom: str
    value: str


class ModelAssignmentChange(BaseModel):
    model_config = ConfigDict(extra="forbid")
    atom: str
    left_value: str
    right_value: str


class ModelDelta(BaseModel):
    model_config = ConfigDict(extra="forbid")
    added_assignments: list[ModelAssignment] = Field(default_factory=list)
    removed_assignments: list[ModelAssignment] = Field(default_factory=list)
    changed_assignments: list[ModelAssignmentChange] = Field(default_factory=list)
    changed_atoms: list[str] = Field(default_factory=list)


class SolverDiff(BaseModel):
    model_config = ConfigDict(extra="forbid")
    left_runs: list[ValidatorRunRef] = Field(default_factory=list)
    right_runs: list[ValidatorRunRef] = Field(default_factory=list)
    status_flip: str
    core_delta: CoreDelta
    model_delta: ModelDelta
    request_hash_changed: bool
    formula_hash_changed: bool
    unpaired_left_hashes: list[str] = Field(default_factory=list)
    unpaired_right_hashes: list[str] = Field(default_factory=list)


class StructuralDiff(BaseModel):
    model_config = ConfigDict(extra="forbid")
    json_patches: list[JsonPatchOp] = Field(default_factory=list)
    changed_paths: list[str] = Field(default_factory=list)
    changed_object_ids: list[str] = Field(default_factory=list)


class ExplanationItem(BaseModel):
    model_config = ConfigDict(extra="forbid")
    atom_name: str
    object_id: str | None = None
    json_path: str | None = None
    span: SourceSpan | None = None


class CausalSlice(BaseModel):
    model_config = ConfigDict(extra="forbid")
    touched_atoms: list[str] = Field(default_factory=list)
    touched_object_ids: list[str] = Field(default_factory=list)
    touched_json_paths: list[str] = Field(default_factory=list)
    explanation_items: list[ExplanationItem] = Field(default_factory=list)


class DiffSummary(BaseModel):
    model_config = ConfigDict(extra="forbid")
    status_flip: str
    structural_patch_count: str
    solver_touched_atom_count: str
    causal_atom_count: str
    run_source: str = "unknown"
    recompute_mode: str | None = None
    left_backend: str | None = None
    right_backend: str | None = None
    left_timeout_ms: int | None = None
    right_timeout_ms: int | None = None


class DiffReport(BaseModel):
    model_config = ConfigDict(extra="forbid")
    left_id: str
    right_id: str
    structural: StructuralDiff
    solver: SolverDiff
    causal_slice: CausalSlice
    summary: DiffSummary
