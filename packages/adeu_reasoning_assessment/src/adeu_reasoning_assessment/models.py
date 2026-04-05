from __future__ import annotations

from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import canonical_json, sha256_canonical_json

ADEU_REASONING_TEMPLATE_PROBE_SCHEMA = "adeu_reasoning_template_probe@1"
ADEU_STRUCTURAL_REASONING_TRACE_SCHEMA = "adeu_structural_reasoning_trace@1"
ADEU_STRUCTURAL_FAILURE_TAXONOMY_SCHEMA = "adeu_structural_failure_taxonomy@1"
ADEU_STRUCTURAL_REASONING_DIFFERENTIAL_SCHEMA = "adeu_structural_reasoning_differential@1"
ADEU_REASONING_PROBE_SUITE_SCHEMA = "adeu_reasoning_probe_suite@1"
ADEU_RECURSIVE_REASONING_ASSESSMENT_SCHEMA = "adeu_recursive_reasoning_assessment@1"

LANE_ORDER = ("O", "E", "D", "U")
TEMPLATE_CLASS_VOCABULARY = (
    "lane_preserving_decomposition",
    "branching_under_uncertainty",
    "local_repair_continuation",
    "invariance_under_surface_variation",
)
SURFACE_VARIATION_KIND_VOCABULARY = (
    "paraphrase_preserving",
    "presentation_shift_preserving",
)
REPAIR_LOCALITY_POSTURE_VOCABULARY = ("local_only",)
CONSUMER_COMPATIBILITY_REF_VOCABULARY = (
    ADEU_STRUCTURAL_FAILURE_TAXONOMY_SCHEMA,
    ADEU_STRUCTURAL_REASONING_DIFFERENTIAL_SCHEMA,
)
TRACE_EVENT_VOCABULARY = (
    "step_activate",
    "step_complete",
    "branch_select",
    "blocked",
    "invalid_early_closure",
    "repair_enter",
    "repair_exit",
    "return_to_parent",
)
TERMINAL_TRACE_STATUS_VOCABULARY = (
    "completed_clean",
    "completed_with_structural_break",
    "blocked",
    "invalid_early_closure",
)
STRUCTURAL_FAILURE_TAXONOMY_STATUS_VOCABULARY = (
    "completed_clean_no_failure",
    "blocked_lawful_insufficiency",
    "normalized_structural_failure",
)
FAILURE_FAMILY_VOCABULARY = (
    "lane_collapse",
    "branch_collapse",
    "plan_spine_drift",
    "active_step_decomposition_failure",
    "reintegration_failure",
    "invalid_early_closure",
    "non_local_repair_drift",
)
CONDITION_ROLE_VOCABULARY = (
    "supplied_knowledge",
    "withheld_knowledge",
    "injected_knowledge_continuation",
)
DIFFERENTIAL_STATUS_VOCABULARY = (
    "paired_conditions_complete",
    "paired_conditions_incomplete",
    "paired_conditions_incompatible",
)
DIFFERENTIAL_JUDGMENT_VOCABULARY = (
    "knowledge_deficit_supported",
    "procedural_discipline_deficit_supported",
    "mixed_or_ambiguous",
    "paired_condition_insufficient",
)
RECURSIVE_DEPTH_MODE_VOCABULARY = ("single_bounded_recursive_reentry",)
RECURSIVE_STATUS_VOCABULARY = (
    "recursive_closure_stable",
    "recursive_closure_degraded",
    "recursive_early_closure_invalid",
)
CLOSURE_JUDGMENT_VOCABULARY = (
    "recursive_extension_lawful",
    "recursive_extension_structurally_degraded",
    "recursive_extension_insufficient",
    "recursive_extension_invalid_early_closure",
)
TRACE_ROLE_VOCABULARY = ("baseline", "recursive_extension")

MODEL_CONFIG = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

TemplateClass = Literal[
    "lane_preserving_decomposition",
    "branching_under_uncertainty",
    "local_repair_continuation",
    "invariance_under_surface_variation",
]
SurfaceVariationKind = Literal[
    "paraphrase_preserving",
    "presentation_shift_preserving",
]
RepairLocalityPosture = Literal["local_only"]
ConsumerCompatibilityRef = Literal[
    "adeu_structural_failure_taxonomy@1",
    "adeu_structural_reasoning_differential@1",
]
LaneId = Literal["O", "E", "D", "U"]
HierarchyPosture = Literal["flat", "single_level_parent_child"]
ChildOrderPolicy = Literal["ordered", "unordered"]
PairedConditionMode = Literal["standalone", "paired_reference"]
TraceEventKind = Literal[
    "step_activate",
    "step_complete",
    "branch_select",
    "blocked",
    "invalid_early_closure",
    "repair_enter",
    "repair_exit",
    "return_to_parent",
]
TerminalTraceStatus = Literal[
    "completed_clean",
    "completed_with_structural_break",
    "blocked",
    "invalid_early_closure",
]
StructuralFailureTaxonomyStatus = Literal[
    "completed_clean_no_failure",
    "blocked_lawful_insufficiency",
    "normalized_structural_failure",
]
FailureFamily = Literal[
    "lane_collapse",
    "branch_collapse",
    "plan_spine_drift",
    "active_step_decomposition_failure",
    "reintegration_failure",
    "invalid_early_closure",
    "non_local_repair_drift",
]
ConditionRole = Literal[
    "supplied_knowledge",
    "withheld_knowledge",
    "injected_knowledge_continuation",
]
DifferentialStatus = Literal[
    "paired_conditions_complete",
    "paired_conditions_incomplete",
    "paired_conditions_incompatible",
]
DifferentialJudgment = Literal[
    "knowledge_deficit_supported",
    "procedural_discipline_deficit_supported",
    "mixed_or_ambiguous",
    "paired_condition_insufficient",
]
RecursiveDepthMode = Literal["single_bounded_recursive_reentry"]
RecursiveStatus = Literal[
    "recursive_closure_stable",
    "recursive_closure_degraded",
    "recursive_early_closure_invalid",
]
ClosureJudgment = Literal[
    "recursive_extension_lawful",
    "recursive_extension_structurally_degraded",
    "recursive_extension_insufficient",
    "recursive_extension_invalid_early_closure",
]
TraceRole = Literal["baseline", "recursive_extension"]


def _assert_non_empty_text(value: str, *, field_name: str) -> str:
    normalized = value.strip()
    if not normalized:
        raise ValueError(f"{field_name} must be non-empty")
    return normalized


def _sorted_unique_texts(
    values: list[str], *, field_name: str, sort_values: bool = True
) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must be unique")
    return sorted(normalized) if sort_values else normalized


def _sorted_unique_ints(values: list[int], *, field_name: str) -> list[int]:
    normalized = list(values)
    if any(value < 0 for value in normalized):
        raise ValueError(f"{field_name} must be non-negative")
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must be unique")
    return sorted(normalized)


def _template_class_sort_key(value: str) -> tuple[int, str]:
    order = {item: index for index, item in enumerate(TEMPLATE_CLASS_VOCABULARY)}
    return (order.get(value, len(order)), value)


def _surface_variation_sort_key(value: str | None) -> tuple[int, int, str]:
    if value is None:
        return (0, -1, "")
    order = {
        item: index for index, item in enumerate(SURFACE_VARIATION_KIND_VOCABULARY)
    }
    return (1, order.get(value, len(order)), value)


def _consumer_compatibility_sort_key(value: str) -> tuple[int, str]:
    order = {
        item: index for index, item in enumerate(CONSUMER_COMPATIBILITY_REF_VOCABULARY)
    }
    return (order.get(value, len(order)), value)


def _sorted_unique_template_classes(
    values: list[TemplateClass], *, field_name: str
) -> list[TemplateClass]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must be unique")
    return list(sorted(normalized, key=_template_class_sort_key))  # type: ignore[return-value]


def _sorted_unique_surface_variation_kinds(
    values: list[SurfaceVariationKind], *, field_name: str
) -> list[SurfaceVariationKind]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must be unique")
    return list(
        sorted(normalized, key=lambda item: _surface_variation_sort_key(item))
    )  # type: ignore[return-value]


def _sorted_unique_consumer_compatibility_refs(
    values: list[ConsumerCompatibilityRef], *, field_name: str
) -> list[ConsumerCompatibilityRef]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must be unique")
    return list(
        sorted(normalized, key=_consumer_compatibility_sort_key)
    )  # type: ignore[return-value]


def _ordered_unique_template_classes_from_members(
    values: list[TemplateClass], *, field_name: str
) -> list[TemplateClass]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    ordered: list[str] = []
    for value in sorted(normalized, key=_template_class_sort_key):
        if value not in ordered:
            ordered.append(value)
    return ordered  # type: ignore[return-value]


def _ordered_unique_surface_variation_kinds_from_members(
    values: list[SurfaceVariationKind], *, field_name: str
) -> list[SurfaceVariationKind]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    ordered: list[str] = []
    for value in sorted(normalized, key=lambda item: _surface_variation_sort_key(item)):
        if value not in ordered:
            ordered.append(value)
    return ordered  # type: ignore[return-value]


def _condition_role_sort_key(role: str) -> tuple[int, str]:
    order = {value: index for index, value in enumerate(CONDITION_ROLE_VOCABULARY)}
    return (order.get(role, len(order)), role)


def _trace_role_sort_key(role: str) -> tuple[int, str]:
    order = {value: index for index, value in enumerate(TRACE_ROLE_VOCABULARY)}
    return (order.get(role, len(order)), role)


def _sorted_unique_condition_roles(
    values: list[ConditionRole], *, field_name: str
) -> list[ConditionRole]:
    normalized = [
        _assert_non_empty_text(value, field_name=field_name)  # type: ignore[arg-type]
        for value in values
    ]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must be unique")
    return list(sorted(normalized, key=_condition_role_sort_key))  # type: ignore[return-value]


def _canonical_condition_ref_map(
    mapping: dict[ConditionRole, str], *, field_name: str
) -> dict[ConditionRole, str]:
    normalized: dict[ConditionRole, str] = {}
    for role, ref in mapping.items():
        normalized[role] = _assert_non_empty_text(ref, field_name=f"{field_name}.{role}")
    return {
        role: normalized[role]
        for role in sorted(normalized, key=_condition_role_sort_key)
    }


def _canonical_step_sort_key(step: "ReasoningTemplateStep") -> tuple[int, int, str]:
    return (0 if step.parent_step_ref is None else 1, step.order_index, step.step_ref)


def _trace_event_basis(event: "StructuralReasoningTraceEvent") -> dict[str, object]:
    return {
        "event_index": event.event_index,
        "event_kind": event.event_kind,
        "step_ref": event.step_ref,
        "lane_ref": event.lane_ref,
        "target_step_ref": event.target_step_ref,
        "break_tags": event.break_tags,
    }


def _structural_break_basis(break_record: "StructuralBreakRecord") -> dict[str, object]:
    return {
        "step_ref": break_record.step_ref,
        "lane_ref": break_record.lane_ref,
        "break_tags": break_record.break_tags,
        "supporting_event_indexes": break_record.supporting_event_indexes,
        "detail": break_record.detail,
    }


def _probe_id_basis_from_model(model: "ReasoningTemplateProbe") -> dict[str, object]:
    return {
        "schema": model.schema,
        "template_class": model.template_class,
        "probe_label": model.probe_label,
        "lane_order": model.lane_order,
        "template_steps": [step.identity_basis() for step in model.template_steps],
        "acceptance_posture": model.acceptance_posture.identity_basis(),
        "paired_condition_compatibility": model.paired_condition_compatibility.identity_basis(),
        "hierarchy_posture": model.hierarchy_posture,
        "plan_spine_step_ids": model.plan_spine_step_ids,
        "active_plan_step_ref": model.active_plan_step_ref,
        "child_step_refs": model.child_step_refs,
        "child_order_policy": model.child_order_policy,
        "return_to_parent_required": model.return_to_parent_required,
    }


def _trace_id_basis_from_model(model: "StructuralReasoningTrace") -> dict[str, object]:
    return {
        "schema": model.schema,
        "probe_ref": model.probe_ref,
        "subject_label": model.subject_label,
        "trace_events": [_trace_event_basis(event) for event in model.trace_events],
        "terminal_trace_status": model.terminal_trace_status,
        "structural_breaks": [
            _structural_break_basis(break_record) for break_record in model.structural_breaks
        ],
        "open_questions": model.open_questions,
    }


def _taxonomy_id_basis_from_model(model: "StructuralFailureTaxonomy") -> dict[str, object]:
    return {
        "schema": model.schema,
        "probe_ref": model.probe_ref,
        "trace_ref": model.trace_ref,
        "taxonomy_status": model.taxonomy_status,
        "terminal_trace_status": model.terminal_trace_status,
        "failure_families": model.failure_families,
        "primary_failure_family": model.primary_failure_family,
        "supporting_break_refs": model.supporting_break_refs,
        "supporting_event_indexes": model.supporting_event_indexes,
        "open_questions": model.open_questions,
    }


def _supporting_trace_event_ref_basis(
    ref: "SupportingTraceEventRef",
) -> dict[str, object]:
    return {
        "condition_role": ref.condition_role,
        "trace_ref": ref.trace_ref,
        "event_index": ref.event_index,
    }


def _recursive_supporting_trace_event_ref_basis(
    ref: "RecursiveSupportingTraceEventRef",
) -> dict[str, object]:
    return {
        "trace_role": ref.trace_role,
        "trace_ref": ref.trace_ref,
        "event_index": ref.event_index,
    }


def _differential_id_basis_from_model(
    model: "StructuralReasoningDifferential",
) -> dict[str, object]:
    return {
        "schema": model.schema,
        "probe_template_ref": model.probe_template_ref,
        "condition_trace_refs": model.condition_trace_refs,
        "condition_taxonomy_refs": model.condition_taxonomy_refs,
        "condition_roles_present": model.condition_roles_present,
        "differential_status": model.differential_status,
        "differential_judgment": model.differential_judgment,
        "supporting_failure_families": model.supporting_failure_families,
        "supporting_trace_event_refs": [
            _supporting_trace_event_ref_basis(ref)
            for ref in model.supporting_trace_event_refs
        ],
        "open_questions": model.open_questions,
    }


def _probe_suite_member_basis(member: "ReasoningProbeSuiteMember") -> dict[str, object]:
    return {
        "probe_ref": member.probe_ref,
        "template_class": member.template_class,
        "surface_variation_kind": member.surface_variation_kind,
        "repair_locality_posture": member.repair_locality_posture,
        "consumer_compatibility_refs": member.consumer_compatibility_refs,
        "paired_condition_compatible": member.paired_condition_compatible,
    }


def _probe_suite_id_basis_from_model(model: "ReasoningProbeSuite") -> dict[str, object]:
    return {
        "schema": model.schema,
        "suite_label": model.suite_label,
        "suite_members": [_probe_suite_member_basis(member) for member in model.suite_members],
        "template_classes_included": model.template_classes_included,
        "accepted_surface_variation_kinds": model.accepted_surface_variation_kinds,
        "repair_locality_posture": model.repair_locality_posture,
    }


def _recursive_assessment_id_basis_from_model(
    model: "RecursiveReasoningAssessment",
) -> dict[str, object]:
    return {
        "schema": model.schema,
        "suite_member_ref": model.suite_member_ref,
        "baseline_probe_ref": model.baseline_probe_ref,
        "baseline_trace_ref": model.baseline_trace_ref,
        "baseline_taxonomy_ref": model.baseline_taxonomy_ref,
        "recursive_probe_ref": model.recursive_probe_ref,
        "recursive_trace_ref": model.recursive_trace_ref,
        "recursive_taxonomy_ref": model.recursive_taxonomy_ref,
        "recursive_depth_mode": model.recursive_depth_mode,
        "recursive_status": model.recursive_status,
        "closure_judgment": model.closure_judgment,
        "supporting_trace_event_refs": [
            _recursive_supporting_trace_event_ref_basis(ref)
            for ref in model.supporting_trace_event_refs
        ],
        "supporting_failure_families": model.supporting_failure_families,
        "open_questions": model.open_questions,
    }


def compute_probe_id(basis: dict[str, object]) -> str:
    return f"reasoning_probe:{sha256_canonical_json(basis)[:16]}"


def compute_structural_break_ref(basis: dict[str, object]) -> str:
    return f"reasoning_break:{sha256_canonical_json(basis)[:16]}"


def compute_trace_id(basis: dict[str, object]) -> str:
    return f"reasoning_trace:{sha256_canonical_json(basis)[:16]}"


def compute_taxonomy_id(basis: dict[str, object]) -> str:
    return f"reasoning_taxonomy:{sha256_canonical_json(basis)[:16]}"


def compute_differential_id(basis: dict[str, object]) -> str:
    return f"reasoning_differential:{sha256_canonical_json(basis)[:16]}"


def compute_probe_suite_hash(basis: dict[str, object]) -> str:
    return sha256_canonical_json(basis)


def compute_probe_suite_id(basis: dict[str, object]) -> str:
    return f"reasoning_probe_suite:{compute_probe_suite_hash(basis)[:16]}"


def compute_probe_suite_member_ref(*, suite_id: str, probe_ref: str) -> str:
    basis = {
        "suite_id": _assert_non_empty_text(suite_id, field_name="suite_id"),
        "probe_ref": _assert_non_empty_text(probe_ref, field_name="probe_ref"),
    }
    return f"reasoning_probe_suite_member:{sha256_canonical_json(basis)[:16]}"


def compute_recursive_assessment_id(basis: dict[str, object]) -> str:
    return f"reasoning_recursive_assessment:{sha256_canonical_json(basis)[:16]}"


class ReasoningTemplateStep(BaseModel):
    model_config = MODEL_CONFIG

    step_ref: str
    step_label: str
    lane_id: LaneId
    order_index: int = Field(ge=0)
    parent_step_ref: str | None = None
    completion_boundary: str
    local_constraints: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate(self) -> "ReasoningTemplateStep":
        object.__setattr__(
            self, "step_ref", _assert_non_empty_text(self.step_ref, field_name="step_ref")
        )
        object.__setattr__(
            self, "step_label", _assert_non_empty_text(self.step_label, field_name="step_label")
        )
        object.__setattr__(
            self,
            "completion_boundary",
            _assert_non_empty_text(self.completion_boundary, field_name="completion_boundary"),
        )
        object.__setattr__(
            self,
            "local_constraints",
            _sorted_unique_texts(self.local_constraints, field_name="local_constraints"),
        )
        if self.parent_step_ref is not None:
            object.__setattr__(
                self,
                "parent_step_ref",
                _assert_non_empty_text(self.parent_step_ref, field_name="parent_step_ref"),
            )
            if self.parent_step_ref == self.step_ref:
                raise ValueError("parent_step_ref must differ from step_ref")
        return self

    def identity_basis(self) -> dict[str, object]:
        return {
            "step_ref": self.step_ref,
            "step_label": self.step_label,
            "lane_id": self.lane_id,
            "order_index": self.order_index,
            "parent_step_ref": self.parent_step_ref,
            "completion_boundary": self.completion_boundary,
            "local_constraints": self.local_constraints,
        }


class ReasoningAcceptancePosture(BaseModel):
    model_config = MODEL_CONFIG

    completion_requires_all_top_level_steps: Literal[True] = True
    blocked_is_lawful: Literal[True] = True
    invalid_early_closure_rejected: Literal[True] = True
    return_to_parent_evidence_required_when_hierarchical: Literal[True] = True

    def identity_basis(self) -> dict[str, object]:
        return self.model_dump(mode="json")


class PairedConditionCompatibility(BaseModel):
    model_config = MODEL_CONFIG

    mode: PairedConditionMode = "standalone"
    paired_suite_key: str | None = None
    condition_variant_key: str | None = None

    @model_validator(mode="after")
    def _validate(self) -> "PairedConditionCompatibility":
        if self.mode == "standalone":
            if self.paired_suite_key is not None or self.condition_variant_key is not None:
                raise ValueError(
                    "standalone paired_condition_compatibility may not declare paired refs"
                )
            return self
        if self.paired_suite_key is None or self.condition_variant_key is None:
            raise ValueError(
                "paired_reference paired_condition_compatibility requires suite and variant keys"
            )
        object.__setattr__(
            self,
            "paired_suite_key",
            _assert_non_empty_text(self.paired_suite_key, field_name="paired_suite_key"),
        )
        object.__setattr__(
            self,
            "condition_variant_key",
            _assert_non_empty_text(self.condition_variant_key, field_name="condition_variant_key"),
        )
        return self

    def identity_basis(self) -> dict[str, object]:
        return self.model_dump(mode="json", exclude_none=True)


class StructuralReasoningTraceEvent(BaseModel):
    model_config = MODEL_CONFIG

    event_index: int = Field(ge=0)
    event_kind: TraceEventKind
    step_ref: str
    lane_ref: LaneId | None = None
    target_step_ref: str | None = None
    break_tags: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate(self) -> "StructuralReasoningTraceEvent":
        object.__setattr__(
            self, "step_ref", _assert_non_empty_text(self.step_ref, field_name="step_ref")
        )
        object.__setattr__(
            self, "break_tags", _sorted_unique_texts(self.break_tags, field_name="break_tags")
        )
        if self.target_step_ref is not None:
            object.__setattr__(
                self,
                "target_step_ref",
                _assert_non_empty_text(self.target_step_ref, field_name="target_step_ref"),
            )
        if self.event_kind == "return_to_parent":
            if self.target_step_ref is None:
                raise ValueError("return_to_parent event requires target_step_ref")
            if self.target_step_ref == self.step_ref:
                raise ValueError("return_to_parent target_step_ref must differ from step_ref")
        elif self.target_step_ref is not None:
            raise ValueError("only return_to_parent events may declare target_step_ref")
        return self


class StructuralBreakRecord(BaseModel):
    model_config = MODEL_CONFIG

    break_ref: str
    step_ref: str
    lane_ref: LaneId | None = None
    break_tags: list[str] = Field(min_length=1)
    supporting_event_indexes: list[int] = Field(min_length=1)
    detail: str

    @model_validator(mode="after")
    def _validate(self) -> "StructuralBreakRecord":
        object.__setattr__(
            self, "step_ref", _assert_non_empty_text(self.step_ref, field_name="step_ref")
        )
        object.__setattr__(self, "detail", _assert_non_empty_text(self.detail, field_name="detail"))
        object.__setattr__(
            self, "break_tags", _sorted_unique_texts(self.break_tags, field_name="break_tags")
        )
        object.__setattr__(
            self,
            "supporting_event_indexes",
            _sorted_unique_ints(
                self.supporting_event_indexes, field_name="supporting_event_indexes"
            ),
        )
        expected_break_ref = compute_structural_break_ref(_structural_break_basis(self))
        if self.break_ref != expected_break_ref:
            raise ValueError("break_ref must match canonical structural break identity")
        return self


class ReasoningTemplateProbe(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_REASONING_TEMPLATE_PROBE_SCHEMA] = Field(
        default=ADEU_REASONING_TEMPLATE_PROBE_SCHEMA,
        alias="schema",
    )
    probe_id: str
    template_class: TemplateClass
    probe_label: str
    lane_order: list[LaneId] = Field(min_length=4, max_length=4)
    template_steps: list[ReasoningTemplateStep] = Field(min_length=1)
    acceptance_posture: ReasoningAcceptancePosture
    paired_condition_compatibility: PairedConditionCompatibility
    hierarchy_posture: HierarchyPosture
    plan_spine_step_ids: list[str] = Field(min_length=1)
    active_plan_step_ref: str
    child_step_refs: list[str] = Field(default_factory=list)
    child_order_policy: ChildOrderPolicy = "ordered"
    return_to_parent_required: bool

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "ReasoningTemplateProbe":
        object.__setattr__(
            self, "probe_label", _assert_non_empty_text(self.probe_label, field_name="probe_label")
        )
        object.__setattr__(
            self,
            "active_plan_step_ref",
            _assert_non_empty_text(self.active_plan_step_ref, field_name="active_plan_step_ref"),
        )
        if list(self.lane_order) != list(LANE_ORDER):
            raise ValueError(f"lane_order must equal {list(LANE_ORDER)}")

        normalized_steps = sorted(self.template_steps, key=_canonical_step_sort_key)
        step_refs = [step.step_ref for step in normalized_steps]
        if len(step_refs) != len(set(step_refs)):
            raise ValueError("template_steps step_ref values must be unique")
        object.__setattr__(self, "template_steps", normalized_steps)

        top_level_steps = [step for step in normalized_steps if step.parent_step_ref is None]
        child_steps = [step for step in normalized_steps if step.parent_step_ref is not None]
        if not top_level_steps:
            raise ValueError("template_steps must include at least one top-level step")

        canonical_plan_spine = [step.step_ref for step in top_level_steps]
        normalized_plan_spine = _sorted_unique_texts(
            self.plan_spine_step_ids,
            field_name="plan_spine_step_ids",
            sort_values=False,
        )
        if normalized_plan_spine != canonical_plan_spine:
            raise ValueError("plan_spine_step_ids must match top-level step order")
        object.__setattr__(self, "plan_spine_step_ids", normalized_plan_spine)

        if self.active_plan_step_ref not in normalized_plan_spine:
            raise ValueError("active_plan_step_ref must refer to a top-level plan step")

        active_children = [
            step for step in child_steps if step.parent_step_ref == self.active_plan_step_ref
        ]
        non_active_children = [
            step for step in child_steps if step.parent_step_ref != self.active_plan_step_ref
        ]
        if non_active_children:
            raise ValueError(
                "V44-A hierarchical probes may only attach child steps to active_plan_step_ref"
            )

        if self.child_order_policy == "ordered":
            normalized_child_refs = _sorted_unique_texts(
                self.child_step_refs,
                field_name="child_step_refs",
                sort_values=False,
            )
            expected_child_refs = [step.step_ref for step in active_children]
        else:
            normalized_child_refs = _sorted_unique_texts(
                self.child_step_refs,
                field_name="child_step_refs",
                sort_values=True,
            )
            expected_child_refs = sorted(step.step_ref for step in active_children)

        if normalized_child_refs != expected_child_refs:
            raise ValueError("child_step_refs must match canonical child-step membership/order")
        object.__setattr__(self, "child_step_refs", normalized_child_refs)

        if self.hierarchy_posture == "flat":
            if child_steps or normalized_child_refs:
                raise ValueError("flat hierarchy_posture may not declare child steps")
            if self.return_to_parent_required:
                raise ValueError("flat hierarchy_posture may not require return_to_parent")
        else:
            if not active_children or not normalized_child_refs:
                raise ValueError(
                    "single_level_parent_child hierarchy requires explicit child steps"
                )
            if not self.return_to_parent_required:
                raise ValueError(
                    "single_level_parent_child hierarchy must require return_to_parent"
                )

        expected_probe_id = compute_probe_id(_probe_id_basis_from_model(self))
        if self.probe_id != expected_probe_id:
            raise ValueError("probe_id must match canonical reasoning template probe identity")
        return self


class StructuralReasoningTrace(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_STRUCTURAL_REASONING_TRACE_SCHEMA] = Field(
        default=ADEU_STRUCTURAL_REASONING_TRACE_SCHEMA,
        alias="schema",
    )
    trace_id: str
    probe_ref: str
    subject_label: str
    trace_events: list[StructuralReasoningTraceEvent] = Field(min_length=1)
    terminal_trace_status: TerminalTraceStatus
    structural_breaks: list[StructuralBreakRecord] = Field(default_factory=list)
    open_questions: list[str] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "StructuralReasoningTrace":
        object.__setattr__(
            self, "probe_ref", _assert_non_empty_text(self.probe_ref, field_name="probe_ref")
        )
        object.__setattr__(
            self,
            "subject_label",
            _assert_non_empty_text(self.subject_label, field_name="subject_label"),
        )
        object.__setattr__(
            self,
            "open_questions",
            _sorted_unique_texts(self.open_questions, field_name="open_questions"),
        )

        observed_indexes = [event.event_index for event in self.trace_events]
        if observed_indexes != list(range(len(self.trace_events))):
            raise ValueError("trace_events event_index values must be contiguous from 0")

        normalized_breaks = sorted(
            self.structural_breaks,
            key=lambda item: (
                item.supporting_event_indexes[0],
                item.step_ref,
                item.break_ref,
            ),
        )
        object.__setattr__(self, "structural_breaks", normalized_breaks)

        event_kinds = [event.event_kind for event in self.trace_events]
        has_blocked = "blocked" in event_kinds
        has_invalid_early_closure = "invalid_early_closure" in event_kinds

        if self.terminal_trace_status == "completed_clean":
            if has_blocked or has_invalid_early_closure:
                raise ValueError(
                    "completed_clean trace may not contain blocked or invalid_early_closure events"
                )
            if self.structural_breaks:
                raise ValueError("completed_clean trace may not carry structural_breaks")
        elif self.terminal_trace_status == "completed_with_structural_break":
            if has_blocked or has_invalid_early_closure:
                raise ValueError(
                    "completed_with_structural_break trace may not contain blocked "
                    "or invalid_early_closure events"
                )
            if not self.structural_breaks:
                raise ValueError("completed_with_structural_break trace requires structural_breaks")
        elif self.terminal_trace_status == "blocked":
            if not has_blocked:
                raise ValueError("blocked trace requires at least one blocked event")
            if has_invalid_early_closure or self.structural_breaks:
                raise ValueError(
                    "blocked trace may not contain invalid_early_closure events "
                    "or structural_breaks"
                )
        else:
            if not has_invalid_early_closure:
                raise ValueError(
                    "invalid_early_closure trace requires at least one invalid_early_closure event"
                )
            if has_blocked or self.structural_breaks:
                raise ValueError(
                    "invalid_early_closure trace may not contain blocked events "
                    "or structural_breaks"
                )

        max_event_index = len(self.trace_events) - 1
        for break_record in self.structural_breaks:
            for event_index in break_record.supporting_event_indexes:
                if event_index > max_event_index:
                    raise ValueError("structural_breaks may not reference missing trace events")

        expected_trace_id = compute_trace_id(_trace_id_basis_from_model(self))
        if self.trace_id != expected_trace_id:
            raise ValueError("trace_id must match canonical structural reasoning trace identity")
        return self


class StructuralFailureTaxonomy(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_STRUCTURAL_FAILURE_TAXONOMY_SCHEMA] = Field(
        default=ADEU_STRUCTURAL_FAILURE_TAXONOMY_SCHEMA,
        alias="schema",
    )
    taxonomy_id: str
    probe_ref: str
    trace_ref: str
    taxonomy_status: StructuralFailureTaxonomyStatus
    terminal_trace_status: TerminalTraceStatus
    failure_families: list[FailureFamily] = Field(default_factory=list)
    primary_failure_family: FailureFamily | None = None
    supporting_break_refs: list[str] = Field(default_factory=list)
    supporting_event_indexes: list[int] = Field(default_factory=list)
    open_questions: list[str] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "StructuralFailureTaxonomy":
        object.__setattr__(
            self, "probe_ref", _assert_non_empty_text(self.probe_ref, field_name="probe_ref")
        )
        object.__setattr__(
            self, "trace_ref", _assert_non_empty_text(self.trace_ref, field_name="trace_ref")
        )
        object.__setattr__(
            self,
            "failure_families",
            _sorted_unique_texts(
                self.failure_families,
                field_name="failure_families",
                sort_values=False,
            ),
        )
        object.__setattr__(
            self,
            "supporting_break_refs",
            _sorted_unique_texts(
                self.supporting_break_refs,
                field_name="supporting_break_refs",
                sort_values=False,
            ),
        )
        object.__setattr__(
            self,
            "supporting_event_indexes",
            _sorted_unique_ints(
                self.supporting_event_indexes, field_name="supporting_event_indexes"
            ),
        )
        object.__setattr__(
            self,
            "open_questions",
            _sorted_unique_texts(self.open_questions, field_name="open_questions"),
        )

        if self.primary_failure_family is not None:
            object.__setattr__(
                self,
                "primary_failure_family",
                _assert_non_empty_text(
                    self.primary_failure_family, field_name="primary_failure_family"
                ),
            )

        if self.taxonomy_status == "completed_clean_no_failure":
            if self.terminal_trace_status != "completed_clean":
                raise ValueError(
                    "completed_clean_no_failure taxonomy requires "
                    "terminal_trace_status completed_clean"
                )
            if (
                self.failure_families
                or self.primary_failure_family is not None
                or self.supporting_break_refs
                or self.supporting_event_indexes
            ):
                raise ValueError(
                    "completed_clean_no_failure taxonomy may not carry "
                    "failure families or supporting refs"
                )
        elif self.taxonomy_status == "blocked_lawful_insufficiency":
            if self.terminal_trace_status != "blocked":
                raise ValueError(
                    "blocked_lawful_insufficiency taxonomy requires terminal_trace_status blocked"
                )
            if (
                self.failure_families
                or self.primary_failure_family is not None
                or self.supporting_break_refs
                or self.supporting_event_indexes
            ):
                raise ValueError(
                    "blocked_lawful_insufficiency taxonomy may not carry "
                    "failure families or supporting refs"
                )
        else:
            if self.terminal_trace_status not in (
                "completed_with_structural_break",
                "invalid_early_closure",
            ):
                raise ValueError(
                    "normalized_structural_failure taxonomy requires "
                    "completed_with_structural_break or invalid_early_closure "
                    "terminal status"
                )
            if not self.failure_families:
                raise ValueError(
                    "normalized_structural_failure taxonomy requires non-empty failure_families"
                )
            if self.primary_failure_family is not None and (
                self.primary_failure_family not in self.failure_families
            ):
                raise ValueError(
                    "primary_failure_family must be a member of failure_families"
                )
            if not self.supporting_event_indexes:
                raise ValueError(
                    "normalized_structural_failure taxonomy requires supporting_event_indexes"
                )
            if self.terminal_trace_status == "completed_with_structural_break":
                if not self.supporting_break_refs:
                    raise ValueError(
                        "completed_with_structural_break taxonomy requires supporting_break_refs"
                    )
            else:
                if self.failure_families != ["invalid_early_closure"]:
                    raise ValueError(
                        "invalid_early_closure taxonomy may normalize only to invalid_early_closure"
                    )
                if self.supporting_break_refs:
                    raise ValueError(
                        "invalid_early_closure taxonomy may not carry supporting_break_refs"
                    )

        expected_taxonomy_id = compute_taxonomy_id(_taxonomy_id_basis_from_model(self))
        if self.taxonomy_id != expected_taxonomy_id:
            raise ValueError(
                "taxonomy_id must match canonical structural failure taxonomy identity"
            )
        return self


class SupportingTraceEventRef(BaseModel):
    model_config = MODEL_CONFIG

    condition_role: ConditionRole
    trace_ref: str
    event_index: int = Field(ge=0)

    @model_validator(mode="after")
    def _validate(self) -> "SupportingTraceEventRef":
        object.__setattr__(
            self, "trace_ref", _assert_non_empty_text(self.trace_ref, field_name="trace_ref")
        )
        return self


class StructuralReasoningDifferential(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_STRUCTURAL_REASONING_DIFFERENTIAL_SCHEMA] = Field(
        default=ADEU_STRUCTURAL_REASONING_DIFFERENTIAL_SCHEMA,
        alias="schema",
    )
    differential_id: str
    probe_template_ref: str
    condition_trace_refs: dict[ConditionRole, str]
    condition_taxonomy_refs: dict[ConditionRole, str]
    condition_roles_present: list[ConditionRole] = Field(min_length=1)
    differential_status: DifferentialStatus
    differential_judgment: DifferentialJudgment
    supporting_failure_families: list[FailureFamily] = Field(default_factory=list)
    supporting_trace_event_refs: list[SupportingTraceEventRef] = Field(default_factory=list)
    open_questions: list[str] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "StructuralReasoningDifferential":
        object.__setattr__(
            self,
            "probe_template_ref",
            _assert_non_empty_text(self.probe_template_ref, field_name="probe_template_ref"),
        )
        object.__setattr__(
            self,
            "condition_roles_present",
            _sorted_unique_condition_roles(
                self.condition_roles_present, field_name="condition_roles_present"
            ),
        )
        object.__setattr__(
            self,
            "condition_trace_refs",
            _canonical_condition_ref_map(
                self.condition_trace_refs, field_name="condition_trace_refs"
            ),
        )
        object.__setattr__(
            self,
            "condition_taxonomy_refs",
            _canonical_condition_ref_map(
                self.condition_taxonomy_refs, field_name="condition_taxonomy_refs"
            ),
        )
        object.__setattr__(
            self,
            "supporting_failure_families",
            _sorted_unique_texts(
                self.supporting_failure_families,
                field_name="supporting_failure_families",
                sort_values=False,
            ),
        )
        object.__setattr__(
            self,
            "open_questions",
            _sorted_unique_texts(self.open_questions, field_name="open_questions"),
        )

        role_set = set(self.condition_roles_present)
        if set(self.condition_trace_refs) != role_set:
            raise ValueError(
                "condition_trace_refs keys must match condition_roles_present exactly"
            )
        if set(self.condition_taxonomy_refs) != role_set:
            raise ValueError(
                "condition_taxonomy_refs keys must match condition_roles_present exactly"
            )

        if self.differential_status in (
            "paired_conditions_incomplete",
            "paired_conditions_incompatible",
        ):
            if self.differential_judgment != "paired_condition_insufficient":
                raise ValueError(
                    "incomplete or incompatible differential status may only emit "
                    "paired_condition_insufficient"
                )

        if self.differential_judgment == "knowledge_deficit_supported":
            if self.supporting_failure_families or self.supporting_trace_event_refs:
                raise ValueError(
                    "knowledge_deficit_supported may not carry supporting failure families "
                    "or supporting trace event refs in the starter slice"
                )

        if self.differential_judgment == "paired_condition_insufficient":
            if self.supporting_failure_families or self.supporting_trace_event_refs:
                raise ValueError(
                    "paired_condition_insufficient may not carry supporting failure "
                    "families or supporting trace event refs"
                )

        seen_support_keys: set[tuple[ConditionRole, str, int]] = set()
        for ref in self.supporting_trace_event_refs:
            if ref.condition_role not in role_set:
                raise ValueError(
                    "supporting_trace_event_refs condition_role must be present in "
                    "condition_roles_present"
                )
            expected_trace_ref = self.condition_trace_refs[ref.condition_role]
            if ref.trace_ref != expected_trace_ref:
                raise ValueError(
                    "supporting_trace_event_refs trace_ref must match "
                    "condition_trace_refs for the same condition_role"
                )
            key = (ref.condition_role, ref.trace_ref, ref.event_index)
            if key in seen_support_keys:
                raise ValueError("supporting_trace_event_refs must be unique")
            seen_support_keys.add(key)

        expected_differential_id = compute_differential_id(
            _differential_id_basis_from_model(self)
        )
        if self.differential_id != expected_differential_id:
            raise ValueError(
                "differential_id must match canonical structural reasoning differential identity"
            )
        return self


class ReasoningProbeSuiteMember(BaseModel):
    model_config = MODEL_CONFIG

    probe_ref: str
    template_class: TemplateClass
    surface_variation_kind: SurfaceVariationKind | None = None
    repair_locality_posture: RepairLocalityPosture | None = None
    consumer_compatibility_refs: list[ConsumerCompatibilityRef] = Field(min_length=1)
    paired_condition_compatible: bool

    @model_validator(mode="after")
    def _validate(self) -> "ReasoningProbeSuiteMember":
        object.__setattr__(
            self, "probe_ref", _assert_non_empty_text(self.probe_ref, field_name="probe_ref")
        )
        object.__setattr__(
            self,
            "consumer_compatibility_refs",
            _sorted_unique_consumer_compatibility_refs(
                self.consumer_compatibility_refs,
                field_name="consumer_compatibility_refs",
            ),
        )

        if self.template_class == "invariance_under_surface_variation":
            if self.surface_variation_kind is None:
                raise ValueError(
                    "invariance_under_surface_variation members require surface_variation_kind"
                )
        elif self.surface_variation_kind is not None:
            raise ValueError(
                "only invariance_under_surface_variation members may declare surface_variation_kind"
            )

        if self.template_class == "local_repair_continuation":
            if self.repair_locality_posture != "local_only":
                raise ValueError(
                    "local_repair_continuation members require repair_locality_posture local_only"
                )
        elif self.repair_locality_posture is not None:
            raise ValueError(
                "only local_repair_continuation members may declare repair_locality_posture"
            )

        if (
            ADEU_STRUCTURAL_REASONING_DIFFERENTIAL_SCHEMA in self.consumer_compatibility_refs
            and not self.paired_condition_compatible
        ):
            raise ValueError(
                "differential compatibility requires paired_condition_compatible = true"
            )
        if (
            ADEU_STRUCTURAL_REASONING_DIFFERENTIAL_SCHEMA in self.consumer_compatibility_refs
            and ADEU_STRUCTURAL_FAILURE_TAXONOMY_SCHEMA
            not in self.consumer_compatibility_refs
        ):
            raise ValueError(
                "differential compatibility requires taxonomy compatibility in the starter slice"
            )
        if self.paired_condition_compatible and (
            ADEU_STRUCTURAL_REASONING_DIFFERENTIAL_SCHEMA
            not in self.consumer_compatibility_refs
        ):
            raise ValueError(
                "paired_condition_compatible members must declare differential compatibility"
            )
        return self


class ReasoningProbeSuite(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_REASONING_PROBE_SUITE_SCHEMA] = Field(
        default=ADEU_REASONING_PROBE_SUITE_SCHEMA,
        alias="schema",
    )
    suite_id: str
    suite_label: str
    suite_members: list[ReasoningProbeSuiteMember] = Field(min_length=6)
    template_classes_included: list[TemplateClass] = Field(min_length=4, max_length=4)
    accepted_surface_variation_kinds: list[SurfaceVariationKind] = Field(
        min_length=2, max_length=2
    )
    repair_locality_posture: RepairLocalityPosture
    suite_hash: str

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "ReasoningProbeSuite":
        object.__setattr__(
            self, "suite_label", _assert_non_empty_text(self.suite_label, field_name="suite_label")
        )
        normalized_members = sorted(
            self.suite_members,
            key=lambda member: (
                _template_class_sort_key(member.template_class),
                _surface_variation_sort_key(member.surface_variation_kind),
                member.probe_ref,
            ),
        )
        object.__setattr__(self, "suite_members", normalized_members)

        probe_refs = [member.probe_ref for member in normalized_members]
        if len(probe_refs) != len(set(probe_refs)):
            raise ValueError("suite_members probe_ref values must be unique")

        normalized_classes = _sorted_unique_template_classes(
            self.template_classes_included,
            field_name="template_classes_included",
        )
        derived_classes = _ordered_unique_template_classes_from_members(
            [member.template_class for member in normalized_members],
            field_name="derived_template_classes_included",
        )
        if normalized_classes != derived_classes:
            raise ValueError(
                "template_classes_included must match the canonical class set "
                "present in suite_members"
            )
        if normalized_classes != list(TEMPLATE_CLASS_VOCABULARY):
            raise ValueError(
                "template_classes_included must match the frozen V44-D starter template classes"
            )
        object.__setattr__(self, "template_classes_included", normalized_classes)

        normalized_variation_kinds = _sorted_unique_surface_variation_kinds(
            self.accepted_surface_variation_kinds,
            field_name="accepted_surface_variation_kinds",
        )
        derived_variation_kinds = _ordered_unique_surface_variation_kinds_from_members(
            [
                member.surface_variation_kind
                for member in normalized_members
                if member.surface_variation_kind is not None
            ],
            field_name="derived_accepted_surface_variation_kinds",
        )
        if normalized_variation_kinds != derived_variation_kinds:
            raise ValueError(
                "accepted_surface_variation_kinds must match the canonical "
                "variation kinds present in suite_members"
            )
        if normalized_variation_kinds != list(SURFACE_VARIATION_KIND_VOCABULARY):
            raise ValueError(
                "accepted_surface_variation_kinds must match the frozen "
                "V44-D starter variation kinds"
            )
        object.__setattr__(
            self, "accepted_surface_variation_kinds", normalized_variation_kinds
        )

        expected_suite_hash = compute_probe_suite_hash(_probe_suite_id_basis_from_model(self))
        if self.suite_hash != expected_suite_hash:
            raise ValueError("suite_hash must match canonical probe-suite hash subject")

        expected_suite_id = compute_probe_suite_id(_probe_suite_id_basis_from_model(self))
        if self.suite_id != expected_suite_id:
            raise ValueError("suite_id must match canonical probe-suite identity")
        return self


class RecursiveSupportingTraceEventRef(BaseModel):
    model_config = MODEL_CONFIG

    trace_role: TraceRole
    trace_ref: str
    event_index: int = Field(ge=0)

    @model_validator(mode="after")
    def _validate(self) -> "RecursiveSupportingTraceEventRef":
        object.__setattr__(
            self, "trace_ref", _assert_non_empty_text(self.trace_ref, field_name="trace_ref")
        )
        return self


class RecursiveReasoningAssessment(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_RECURSIVE_REASONING_ASSESSMENT_SCHEMA] = Field(
        default=ADEU_RECURSIVE_REASONING_ASSESSMENT_SCHEMA,
        alias="schema",
    )
    assessment_id: str
    suite_member_ref: str
    baseline_probe_ref: str
    baseline_trace_ref: str
    baseline_taxonomy_ref: str
    recursive_probe_ref: str
    recursive_trace_ref: str
    recursive_taxonomy_ref: str
    recursive_depth_mode: RecursiveDepthMode
    recursive_status: RecursiveStatus
    closure_judgment: ClosureJudgment
    supporting_trace_event_refs: list[RecursiveSupportingTraceEventRef] = Field(
        default_factory=list
    )
    supporting_failure_families: list[FailureFamily] = Field(default_factory=list)
    open_questions: list[str] = Field(default_factory=list)

    @property
    def schema(self) -> str:
        return self.schema_id

    @model_validator(mode="after")
    def _validate(self) -> "RecursiveReasoningAssessment":
        for field_name in (
            "suite_member_ref",
            "baseline_probe_ref",
            "baseline_trace_ref",
            "baseline_taxonomy_ref",
            "recursive_probe_ref",
            "recursive_trace_ref",
            "recursive_taxonomy_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )

        normalized_supporting_refs = sorted(
            self.supporting_trace_event_refs,
            key=lambda ref: (
                _trace_role_sort_key(ref.trace_role),
                ref.event_index,
                ref.trace_ref,
            ),
        )
        object.__setattr__(self, "supporting_trace_event_refs", normalized_supporting_refs)
        object.__setattr__(
            self,
            "supporting_failure_families",
            _sorted_unique_texts(
                self.supporting_failure_families,
                field_name="supporting_failure_families",
                sort_values=False,
            ),
        )
        object.__setattr__(
            self,
            "open_questions",
            _sorted_unique_texts(self.open_questions, field_name="open_questions"),
        )

        if self.recursive_status == "recursive_closure_stable":
            if self.closure_judgment not in (
                "recursive_extension_lawful",
                "recursive_extension_insufficient",
            ):
                raise ValueError(
                    "recursive_closure_stable may emit only lawful or insufficient judgments"
                )
            if self.supporting_failure_families:
                raise ValueError(
                    "recursive_closure_stable may not carry supporting_failure_families"
                )
        elif self.recursive_status == "recursive_closure_degraded":
            if self.closure_judgment not in (
                "recursive_extension_structurally_degraded",
                "recursive_extension_insufficient",
            ):
                raise ValueError(
                    "recursive_closure_degraded may emit only degraded or insufficient judgments"
                )
            if not self.supporting_failure_families:
                raise ValueError(
                    "recursive_closure_degraded requires supporting_failure_families"
                )
        else:
            if self.closure_judgment != "recursive_extension_invalid_early_closure":
                raise ValueError(
                    "recursive_early_closure_invalid may emit only "
                    "recursive_extension_invalid_early_closure"
                )
            if self.supporting_failure_families != ["invalid_early_closure"]:
                raise ValueError(
                    "recursive_early_closure_invalid requires "
                    "supporting_failure_families = ['invalid_early_closure']"
                )

        expected_trace_refs = {
            "baseline": self.baseline_trace_ref,
            "recursive_extension": self.recursive_trace_ref,
        }
        seen_support_keys: set[tuple[TraceRole, str, int]] = set()
        for ref in self.supporting_trace_event_refs:
            expected_trace_ref = expected_trace_refs[ref.trace_role]
            if ref.trace_ref != expected_trace_ref:
                raise ValueError(
                    "supporting_trace_event_refs trace_ref must match the trace ref "
                    "for the same trace_role"
                )
            key = (ref.trace_role, ref.trace_ref, ref.event_index)
            if key in seen_support_keys:
                raise ValueError("supporting_trace_event_refs must be unique")
            seen_support_keys.add(key)

        expected_assessment_id = compute_recursive_assessment_id(
            _recursive_assessment_id_basis_from_model(self)
        )
        if self.assessment_id != expected_assessment_id:
            raise ValueError(
                "assessment_id must match canonical recursive reasoning assessment identity"
            )
        return self


def validate_trace_against_probe(
    *,
    probe: ReasoningTemplateProbe,
    trace: StructuralReasoningTrace,
) -> None:
    if trace.probe_ref != probe.probe_id:
        raise ValueError("trace.probe_ref must match probe.probe_id")

    step_map = {step.step_ref: step for step in probe.template_steps}
    child_step_set = set(probe.child_step_refs)
    plan_spine_set = set(probe.plan_spine_step_ids)

    for event in trace.trace_events:
        step = step_map.get(event.step_ref)
        if step is None:
            raise ValueError(f"trace event references unknown step_ref: {event.step_ref}")
        if event.lane_ref is not None and event.lane_ref != step.lane_id:
            raise ValueError("trace event lane_ref must match probe step lane_id")
        if event.event_kind == "return_to_parent":
            if event.step_ref not in child_step_set:
                raise ValueError("return_to_parent events must originate from child steps")
            if event.target_step_ref != probe.active_plan_step_ref:
                raise ValueError("return_to_parent events must target active_plan_step_ref")
        elif event.target_step_ref is not None:
            raise ValueError("only return_to_parent events may declare target_step_ref")

    for break_record in trace.structural_breaks:
        step = step_map.get(break_record.step_ref)
        if step is None:
            raise ValueError("structural_break step_ref must exist in probe template_steps")
        if break_record.lane_ref is not None and break_record.lane_ref != step.lane_id:
            raise ValueError("structural_break lane_ref must match probe step lane_id")
        for event_index in break_record.supporting_event_indexes:
            if trace.trace_events[event_index].step_ref != break_record.step_ref:
                raise ValueError(
                    "structural_break supporting_event_indexes must point at "
                    "matching step_ref events"
                )

    seen_top_level: list[str] = []
    for event in trace.trace_events:
        if event.event_kind != "step_activate" or event.step_ref not in plan_spine_set:
            continue
        if event.step_ref in seen_top_level:
            continue
        seen_top_level.append(event.step_ref)
    expected_prefix = probe.plan_spine_step_ids[: len(seen_top_level)]
    if seen_top_level != expected_prefix:
        raise ValueError("trace top-level activation order must follow probe plan_spine_step_ids")
    if trace.terminal_trace_status in (
        "completed_clean",
        "completed_with_structural_break",
    ) and seen_top_level != probe.plan_spine_step_ids:
        raise ValueError("completed traces must activate the full top-level plan spine")

    if probe.hierarchy_posture == "flat":
        if any(event.step_ref in child_step_set for event in trace.trace_events):
            raise ValueError("flat probe may not emit child-step trace events")
        return

    child_activity_indexes = [
        index
        for index, event in enumerate(trace.trace_events)
        if event.step_ref in child_step_set and event.event_kind != "return_to_parent"
    ]
    if not child_activity_indexes:
        return

    parent_complete_index = next(
        (
            index
            for index, event in enumerate(trace.trace_events)
            if event.event_kind == "step_complete" and event.step_ref == probe.active_plan_step_ref
        ),
        len(trace.trace_events),
    )
    valid_return_indexes = [
        index
        for index, event in enumerate(trace.trace_events)
        if event.event_kind == "return_to_parent"
        and event.target_step_ref == probe.active_plan_step_ref
        and event.step_ref in child_step_set
    ]
    if not valid_return_indexes:
        raise ValueError("hierarchical trace missing return_to_parent evidence")

    if not any(
        child_activity_indexes[-1] < return_index < parent_complete_index
        for return_index in valid_return_indexes
    ):
        raise ValueError(
            "hierarchical trace must return_to_parent to active_plan_step_ref "
            "before parent completion"
        )


__all__ = [
    "ADEU_REASONING_PROBE_SUITE_SCHEMA",
    "ADEU_RECURSIVE_REASONING_ASSESSMENT_SCHEMA",
    "ADEU_STRUCTURAL_REASONING_DIFFERENTIAL_SCHEMA",
    "ADEU_STRUCTURAL_FAILURE_TAXONOMY_SCHEMA",
    "ADEU_REASONING_TEMPLATE_PROBE_SCHEMA",
    "ADEU_STRUCTURAL_REASONING_TRACE_SCHEMA",
    "CLOSURE_JUDGMENT_VOCABULARY",
    "CONDITION_ROLE_VOCABULARY",
    "CONSUMER_COMPATIBILITY_REF_VOCABULARY",
    "ClosureJudgment",
    "ConsumerCompatibilityRef",
    "DIFFERENTIAL_JUDGMENT_VOCABULARY",
    "DIFFERENTIAL_STATUS_VOCABULARY",
    "FAILURE_FAMILY_VOCABULARY",
    "LANE_ORDER",
    "RECURSIVE_DEPTH_MODE_VOCABULARY",
    "RECURSIVE_STATUS_VOCABULARY",
    "RecursiveDepthMode",
    "RecursiveReasoningAssessment",
    "RecursiveStatus",
    "RecursiveSupportingTraceEventRef",
    "ReasoningProbeSuite",
    "ReasoningProbeSuiteMember",
    "REPAIR_LOCALITY_POSTURE_VOCABULARY",
    "RepairLocalityPosture",
    "STRUCTURAL_FAILURE_TAXONOMY_STATUS_VOCABULARY",
    "SupportingTraceEventRef",
    "SURFACE_VARIATION_KIND_VOCABULARY",
    "SurfaceVariationKind",
    "TEMPLATE_CLASS_VOCABULARY",
    "TRACE_ROLE_VOCABULARY",
    "TRACE_EVENT_VOCABULARY",
    "TERMINAL_TRACE_STATUS_VOCABULARY",
    "PairedConditionCompatibility",
    "ReasoningAcceptancePosture",
    "ReasoningTemplateProbe",
    "ReasoningTemplateStep",
    "StructuralReasoningDifferential",
    "StructuralFailureTaxonomy",
    "StructuralBreakRecord",
    "StructuralReasoningTrace",
    "StructuralReasoningTraceEvent",
    "canonical_json",
    "compute_differential_id",
    "compute_probe_id",
    "compute_probe_suite_hash",
    "compute_probe_suite_id",
    "compute_probe_suite_member_ref",
    "compute_recursive_assessment_id",
    "compute_structural_break_ref",
    "compute_taxonomy_id",
    "compute_trace_id",
    "sha256_canonical_json",
    "validate_trace_against_probe",
]
