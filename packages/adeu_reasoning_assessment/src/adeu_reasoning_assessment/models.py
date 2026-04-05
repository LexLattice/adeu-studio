from __future__ import annotations

from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import canonical_json, sha256_canonical_json

ADEU_REASONING_TEMPLATE_PROBE_SCHEMA = "adeu_reasoning_template_probe@1"
ADEU_STRUCTURAL_REASONING_TRACE_SCHEMA = "adeu_structural_reasoning_trace@1"

LANE_ORDER = ("O", "E", "D", "U")
TEMPLATE_CLASS_VOCABULARY = (
    "lane_preserving_decomposition",
    "branching_under_uncertainty",
    "local_repair_continuation",
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

MODEL_CONFIG = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

TemplateClass = Literal[
    "lane_preserving_decomposition",
    "branching_under_uncertainty",
    "local_repair_continuation",
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


def compute_probe_id(basis: dict[str, object]) -> str:
    return f"reasoning_probe:{sha256_canonical_json(basis)[:16]}"


def compute_structural_break_ref(basis: dict[str, object]) -> str:
    return f"reasoning_break:{sha256_canonical_json(basis)[:16]}"


def compute_trace_id(basis: dict[str, object]) -> str:
    return f"reasoning_trace:{sha256_canonical_json(basis)[:16]}"


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
            "hierarchical trace must return to active_plan_step_ref before parent completion"
        )


__all__ = [
    "ADEU_REASONING_TEMPLATE_PROBE_SCHEMA",
    "ADEU_STRUCTURAL_REASONING_TRACE_SCHEMA",
    "LANE_ORDER",
    "TEMPLATE_CLASS_VOCABULARY",
    "TRACE_EVENT_VOCABULARY",
    "TERMINAL_TRACE_STATUS_VOCABULARY",
    "PairedConditionCompatibility",
    "ReasoningAcceptancePosture",
    "ReasoningTemplateProbe",
    "ReasoningTemplateStep",
    "StructuralBreakRecord",
    "StructuralReasoningTrace",
    "StructuralReasoningTraceEvent",
    "canonical_json",
    "compute_probe_id",
    "compute_structural_break_ref",
    "compute_trace_id",
    "sha256_canonical_json",
    "validate_trace_against_probe",
]
