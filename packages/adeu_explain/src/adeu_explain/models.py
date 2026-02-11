from __future__ import annotations

from typing import Any, Literal

from adeu_ir import MappingTrust, SourceSpan, ValidatorAtomRef
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
    solver_pairing_state: str = "NO_RUNS"
    mapping_trust: MappingTrust | None = None
    solver_trust: str = "kernel_only"
    proof_trust: str | None = None
    unpaired_left_keys: list[str] = Field(default_factory=list)
    unpaired_right_keys: list[str] = Field(default_factory=list)
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


class PrimaryChange(BaseModel):
    model_config = ConfigDict(extra="forbid")
    object_kind: str
    object_id: str | None = None
    changed_paths: list[str] = Field(default_factory=list)
    patch_count: int = 0


class EvidenceChange(BaseModel):
    model_config = ConfigDict(extra="forbid")
    atom_name: str
    evidence_kind: Literal[
        "core_added",
        "core_removed",
        "model_added",
        "model_removed",
        "model_changed",
    ]
    severity: Literal["ERROR", "WARN", "INFO"]
    object_kind: str
    object_id: str | None = None
    json_path: str | None = None
    left_span: SourceSpan | None = None
    right_span: SourceSpan | None = None


class CauseChainItem(BaseModel):
    model_config = ConfigDict(extra="forbid")
    severity: Literal["ERROR", "WARN", "INFO"]
    object_kind: str
    object_id: str | None = None
    json_path: str | None = None
    atom_name: str
    evidence_kind: Literal[
        "core_added",
        "core_removed",
        "model_added",
        "model_removed",
        "model_changed",
    ]
    message: str
    left_span: SourceSpan | None = None
    right_span: SourceSpan | None = None


class RepairHint(BaseModel):
    model_config = ConfigDict(extra="forbid")
    object_kind: str
    object_id: str | None = None
    json_path: str | None = None
    hint: str


class FlipExplanation(BaseModel):
    model_config = ConfigDict(extra="forbid")
    flip_kind: str
    check_status_flip: str
    solver_status_flip: str
    primary_changes: list[PrimaryChange] = Field(default_factory=list)
    evidence_changes: list[EvidenceChange] = Field(default_factory=list)
    cause_chain: list[CauseChainItem] = Field(default_factory=list)
    repair_hints: list[RepairHint] = Field(default_factory=list)


class ForcedEdgeKey(BaseModel):
    model_config = ConfigDict(extra="forbid")
    src_sense_id: str
    dst_sense_id: str
    kind: str


class ConceptAnalysisDelta(BaseModel):
    model_config = ConfigDict(extra="forbid")
    mic_delta_status: str | None = None
    forced_delta_status: str | None = None
    mic_atoms_added: list[str] = Field(default_factory=list)
    mic_atoms_removed: list[str] = Field(default_factory=list)
    forced_edges_added: list[ForcedEdgeKey] = Field(default_factory=list)
    forced_edges_removed: list[ForcedEdgeKey] = Field(default_factory=list)
    countermodel_edges_changed: list[ForcedEdgeKey] = Field(default_factory=list)
