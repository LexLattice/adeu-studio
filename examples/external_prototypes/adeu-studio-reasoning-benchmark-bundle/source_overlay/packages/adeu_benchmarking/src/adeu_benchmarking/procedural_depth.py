from __future__ import annotations

from collections import Counter, defaultdict
from copy import deepcopy
from typing import Any, Callable, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from ._hashing import sha256_canonical_json

from .family import DominantFailureFamily

MODEL_CONFIG = ConfigDict(extra="forbid", frozen=True, protected_namespaces=())

PROCEDURAL_DEPTH_INSTANCE_SCHEMA = "procedural_depth_instance@1"
PROCEDURAL_DEPTH_GOLD_TRACE_SCHEMA = "procedural_depth_gold_trace@1"
PROCEDURAL_DEPTH_RUN_TRACE_SCHEMA = "procedural_depth_run_trace@1"
PROCEDURAL_DEPTH_METRICS_SCHEMA = "procedural_depth_metrics@1"
PROCEDURAL_DEPTH_DIAGNOSTIC_REPORT_SCHEMA = "procedural_depth_diagnostic_report@1"

ChildOrderPolicy = Literal["ordered", "unordered"]
TraceEventType = Literal["activate", "complete", "return"]
AxisPosture = Literal["clean", "degraded"]
FailureFamily = Literal[
    "horizontal_plan_spine",
    "vertical_active_step_compilation",
    "reintegration",
]
EpistemicPosture = Literal["derived_deterministically_from_run_and_gold"]


def _assert_non_empty_text(value: str, *, field_name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{field_name} must be a string")
    if not value:
        raise ValueError(f"{field_name} must not be empty")
    if value != value.strip():
        raise ValueError(f"{field_name} must not include leading/trailing whitespace")
    return value


def _sorted_unique_texts(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must not contain duplicates")
    return sorted(normalized)


def _canonical_model_payload(model: BaseModel) -> dict[str, Any]:
    return model.model_dump(mode="json", exclude_none=True)


def _prepare_payload(
    payload: dict[str, Any],
    *,
    id_field: str,
    compute_id: Callable[[dict[str, Any]], str],
) -> dict[str, Any]:
    materialized = deepcopy(payload)
    materialized.setdefault(id_field, compute_id(materialized))
    return materialized


def _rounded_score(value: float) -> float:
    return round(value, 4)


def _assert_contiguous_event_indexes(
    events: list[BaseModel], *, field_name: str
) -> list[BaseModel]:
    observed = [int(getattr(event, "event_index")) for event in events]
    if observed != list(range(len(events))):
        raise ValueError(f"{field_name} event_index values must be contiguous from 0")
    return events


def _children_by_parent(
    step_specs: list["ProceduralDepthStepSpec"],
) -> dict[str | None, list["ProceduralDepthStepSpec"]]:
    grouped: dict[str | None, list[ProceduralDepthStepSpec]] = defaultdict(list)
    for step in step_specs:
        grouped[step.parent_step_id].append(step)
    for entries in grouped.values():
        entries.sort(key=lambda step: (step.order_index, step.step_id))
    return grouped


def _step_map(
    step_specs: list["ProceduralDepthStepSpec"],
) -> dict[str, "ProceduralDepthStepSpec"]:
    return {step.step_id: step for step in step_specs}


def _descendants(
    step_id: str,
    children_by_parent: dict[str | None, list["ProceduralDepthStepSpec"]],
) -> set[str]:
    result: set[str] = set()
    for child in children_by_parent.get(step_id, []):
        result.add(child.step_id)
        result.update(_descendants(child.step_id, children_by_parent))
    return result


def _canonical_step_order(
    top_level_spine: list[str],
    children_by_parent: dict[str | None, list["ProceduralDepthStepSpec"]],
) -> list[str]:
    ordered: list[str] = []

    def _walk(step_id: str) -> None:
        ordered.append(step_id)
        for child in children_by_parent.get(step_id, []):
            _walk(child.step_id)

    for top_level_step in top_level_spine:
        _walk(top_level_step)
    return ordered


def _first_event_index(
    events: list["ProceduralDepthTraceEvent"],
    *,
    event_type: TraceEventType,
    step_id: str,
    start: int = 0,
    stop: int | None = None,
) -> int | None:
    upper_bound = len(events) if stop is None else stop
    for index in range(start, upper_bound):
        event = events[index]
        if event.event_type == event_type and event.step_id == step_id:
            return index
    return None


def _observed_top_level_activation_sequence(
    *,
    events: list["ProceduralDepthTraceEvent"],
    top_level_spine: list[str],
) -> list[str]:
    seen: set[str] = set()
    observed: list[str] = []
    top_level_set = set(top_level_spine)
    for event in events:
        if event.event_type != "activate" or event.step_id not in top_level_set:
            continue
        if event.step_id in seen:
            continue
        seen.add(event.step_id)
        observed.append(event.step_id)
    return observed


def _longest_correct_prefix(observed: list[str], expected: list[str]) -> int:
    prefix = 0
    for observed_value, expected_value in zip(observed, expected):
        if observed_value != expected_value:
            break
        prefix += 1
    return prefix


def _parent_window(
    *,
    parent_step_id: str,
    events: list["ProceduralDepthTraceEvent"],
    children_by_parent: dict[str | None, list["ProceduralDepthStepSpec"]],
) -> tuple[int, int] | None:
    start_index = _first_event_index(events, event_type="activate", step_id=parent_step_id)
    if start_index is None:
        return None
    descendant_ids = _descendants(parent_step_id, children_by_parent)
    for index in range(start_index + 1, len(events)):
        event = events[index]
        if event.event_type != "activate":
            continue
        if event.step_id == parent_step_id or event.step_id in descendant_ids:
            continue
        return start_index, index
    return start_index, len(events)


def _search_return_before_boundary(
    *,
    events: list["ProceduralDepthTraceEvent"],
    child_step_id: str,
    parent_step_id: str,
    start: int,
    stop: int,
) -> tuple[bool, int | None]:
    for index in range(start, stop):
        event = events[index]
        if (
            event.event_type == "return"
            and event.step_id == child_step_id
            and event.target_step_id == parent_step_id
        ):
            return True, index
        if event.event_type == "activate":
            return False, index
        if event.event_type == "complete" and event.step_id == parent_step_id:
            return False, index
    return False, None


def _build_failure(
    *,
    failure_family: FailureFamily,
    failure_code: str,
    step_id: str,
    expected: str | None = None,
    observed: str | None = None,
    supporting_event_index: int | None = None,
) -> dict[str, Any]:
    return {
        "failure_family": failure_family,
        "failure_code": failure_code,
        "step_id": step_id,
        "expected": expected,
        "observed": observed,
        "supporting_event_index": supporting_event_index,
    }


class ProceduralDepthStepSpec(BaseModel):
    model_config = MODEL_CONFIG

    step_id: str
    label: str
    parent_step_id: str | None = None
    order_index: int = Field(ge=0)
    required_child_step_ids: list[str] = Field(default_factory=list)
    child_order_policy: ChildOrderPolicy = "ordered"
    local_constraints: list[str] = Field(default_factory=list)
    completion_boundary: str
    return_to_parent_step_id: str | None = None

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthStepSpec":
        for field_name in ("step_id", "label", "completion_boundary"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        if self.parent_step_id is not None:
            object.__setattr__(
                self,
                "parent_step_id",
                _assert_non_empty_text(self.parent_step_id, field_name="parent_step_id"),
            )
        if self.child_order_policy == "unordered":
            normalized_children = _sorted_unique_texts(
                self.required_child_step_ids,
                field_name="required_child_step_ids",
            )
        else:
            normalized_children = [
                _assert_non_empty_text(step_id, field_name="required_child_step_ids")
                for step_id in self.required_child_step_ids
            ]
            if len(normalized_children) != len(set(normalized_children)):
                raise ValueError("required_child_step_ids must not contain duplicates")
        object.__setattr__(self, "required_child_step_ids", normalized_children)
        object.__setattr__(
            self,
            "local_constraints",
            _sorted_unique_texts(self.local_constraints, field_name="local_constraints"),
        )
        if self.return_to_parent_step_id is not None:
            object.__setattr__(
                self,
                "return_to_parent_step_id",
                _assert_non_empty_text(
                    self.return_to_parent_step_id,
                    field_name="return_to_parent_step_id",
                ),
            )
        if self.parent_step_id is None and self.return_to_parent_step_id is not None:
            raise ValueError("top-level step may not declare return_to_parent_step_id")
        if (
            self.parent_step_id is not None
            and self.return_to_parent_step_id != self.parent_step_id
        ):
            raise ValueError(
                "return_to_parent_step_id must match parent_step_id for nested steps"
            )
        return self


class ProceduralDepthTraceEvent(BaseModel):
    model_config = MODEL_CONFIG

    event_index: int = Field(ge=0)
    event_type: TraceEventType
    step_id: str
    target_step_id: str | None = None

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthTraceEvent":
        object.__setattr__(
            self,
            "step_id",
            _assert_non_empty_text(self.step_id, field_name="step_id"),
        )
        if self.event_type == "return":
            if self.target_step_id is None:
                raise ValueError("return event must declare target_step_id")
            object.__setattr__(
                self,
                "target_step_id",
                _assert_non_empty_text(self.target_step_id, field_name="target_step_id"),
            )
            if self.target_step_id == self.step_id:
                raise ValueError("return event target_step_id must differ from step_id")
        elif self.target_step_id is not None:
            raise ValueError("non-return events may not declare target_step_id")
        return self


class ProceduralDepthInstance(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[PROCEDURAL_DEPTH_INSTANCE_SCHEMA] = PROCEDURAL_DEPTH_INSTANCE_SCHEMA
    procedural_depth_instance_id: str
    benchmark_projection_spec_ref: str
    instance_family_label: str
    instance_label: str
    repo_snapshot_ref: str
    source_surface_refs: list[str] = Field(min_length=1)
    instruction_constitution: str
    benchmark_tags: list[str] = Field(min_length=1)
    top_level_spine: list[str] = Field(min_length=1)
    expected_final_step_id: str
    step_specs: list[ProceduralDepthStepSpec] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthInstance":
        for field_name in (
            "procedural_depth_instance_id",
            "benchmark_projection_spec_ref",
            "instance_family_label",
            "instance_label",
            "repo_snapshot_ref",
            "instruction_constitution",
            "expected_final_step_id",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "source_surface_refs",
            _sorted_unique_texts(
                self.source_surface_refs,
                field_name="source_surface_refs",
            ),
        )
        object.__setattr__(
            self,
            "benchmark_tags",
            _sorted_unique_texts(self.benchmark_tags, field_name="benchmark_tags"),
        )
        if len(self.top_level_spine) != len(set(self.top_level_spine)):
            raise ValueError("top_level_spine must not contain duplicates")
        object.__setattr__(
            self,
            "top_level_spine",
            [
                _assert_non_empty_text(step_id, field_name="top_level_spine")
                for step_id in self.top_level_spine
            ],
        )
        step_map = _step_map(self.step_specs)
        if len(step_map) != len(self.step_specs):
            raise ValueError("step_specs step_id values must be unique")
        for step in self.step_specs:
            if step.parent_step_id is not None and step.parent_step_id not in step_map:
                raise ValueError("every parent_step_id must resolve inside step_specs")
        children_by_parent = _children_by_parent(self.step_specs)
        root_step_ids = [step.step_id for step in children_by_parent.get(None, [])]
        if self.top_level_spine != root_step_ids:
            raise ValueError("top_level_spine must match canonical ordered root step sequence")
        for parent_id, children in children_by_parent.items():
            if parent_id is None:
                continue
            parent = step_map[parent_id]
            expected_child_ids = [step.step_id for step in children]
            if parent.child_order_policy == "ordered":
                if parent.required_child_step_ids != expected_child_ids:
                    raise ValueError(
                        "ordered parent required_child_step_ids must match canonical child order"
                    )
            elif sorted(parent.required_child_step_ids) != sorted(expected_child_ids):
                raise ValueError(
                    "unordered parent required_child_step_ids must match direct children"
                )
        for step in self.step_specs:
            if step.step_id not in children_by_parent and step.required_child_step_ids:
                raise ValueError("leaf step required_child_step_ids must be empty")
        if self.expected_final_step_id != self.top_level_spine[-1]:
            raise ValueError("expected_final_step_id must match the final top-level spine step")
        canonical_step_ids = _canonical_step_order(self.top_level_spine, children_by_parent)
        ordered_steps = [step_map[step_id] for step_id in canonical_step_ids]
        object.__setattr__(self, "step_specs", ordered_steps)
        expected_id = compute_procedural_depth_instance_id(_canonical_model_payload(self))
        if self.procedural_depth_instance_id != expected_id:
            raise ValueError(
                "procedural_depth_instance_id must match canonical instance identity"
            )
        return self


class ProceduralDepthGoldTrace(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[PROCEDURAL_DEPTH_GOLD_TRACE_SCHEMA] = PROCEDURAL_DEPTH_GOLD_TRACE_SCHEMA
    procedural_depth_gold_trace_id: str
    procedural_depth_instance_ref: str
    top_level_spine: list[str] = Field(min_length=1)
    gold_events: list[ProceduralDepthTraceEvent] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthGoldTrace":
        for field_name in (
            "procedural_depth_gold_trace_id",
            "procedural_depth_instance_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        if len(self.top_level_spine) != len(set(self.top_level_spine)):
            raise ValueError("top_level_spine must not contain duplicates")
        object.__setattr__(
            self,
            "top_level_spine",
            [
                _assert_non_empty_text(step_id, field_name="top_level_spine")
                for step_id in self.top_level_spine
            ],
        )
        object.__setattr__(
            self,
            "gold_events",
            _assert_contiguous_event_indexes(self.gold_events, field_name="gold_events"),
        )
        expected_id = compute_procedural_depth_gold_trace_id(_canonical_model_payload(self))
        if self.procedural_depth_gold_trace_id != expected_id:
            raise ValueError(
                "procedural_depth_gold_trace_id must match canonical gold trace identity"
            )
        return self


class ProceduralDepthRunTrace(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[PROCEDURAL_DEPTH_RUN_TRACE_SCHEMA] = PROCEDURAL_DEPTH_RUN_TRACE_SCHEMA
    procedural_depth_run_trace_id: str
    procedural_depth_instance_ref: str
    benchmark_execution_context_ref: str
    run_label: str
    observed_events: list[ProceduralDepthTraceEvent] = Field(min_length=1)
    observed_final_output_summary: str | None = None
    trace_notes: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthRunTrace":
        for field_name in (
            "procedural_depth_run_trace_id",
            "procedural_depth_instance_ref",
            "benchmark_execution_context_ref",
            "run_label",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "observed_events",
            _assert_contiguous_event_indexes(
                self.observed_events,
                field_name="observed_events",
            ),
        )
        if self.observed_final_output_summary is not None:
            object.__setattr__(
                self,
                "observed_final_output_summary",
                _assert_non_empty_text(
                    self.observed_final_output_summary,
                    field_name="observed_final_output_summary",
                ),
            )
        object.__setattr__(
            self,
            "trace_notes",
            _sorted_unique_texts(self.trace_notes, field_name="trace_notes"),
        )
        expected_id = compute_procedural_depth_run_trace_id(_canonical_model_payload(self))
        if self.procedural_depth_run_trace_id != expected_id:
            raise ValueError(
                "procedural_depth_run_trace_id must match canonical run trace identity"
            )
        return self


class ProceduralDepthMetrics(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[PROCEDURAL_DEPTH_METRICS_SCHEMA] = PROCEDURAL_DEPTH_METRICS_SCHEMA
    procedural_depth_metrics_id: str
    procedural_depth_run_trace_ref: str
    procedural_depth_gold_trace_ref: str
    expected_top_level_spine: list[str] = Field(min_length=1)
    observed_top_level_activation_sequence: list[str] = Field(min_length=1)
    plan_spine_fidelity_score: float = Field(ge=0.0, le=1.0)
    active_step_compilation_score: float = Field(ge=0.0, le=1.0)
    reintegration_fidelity_score: float = Field(ge=0.0, le=1.0)
    overall_structural_fidelity_score: float = Field(ge=0.0, le=1.0)
    top_level_longest_correct_prefix: int = Field(ge=0)
    evaluated_parent_steps: int = Field(ge=0)
    required_child_completion_rate: float = Field(ge=0.0, le=1.0)
    return_event_success_rate: float = Field(ge=0.0, le=1.0)
    plan_spine_posture: AxisPosture
    active_step_compilation_posture: AxisPosture
    reintegration_posture: AxisPosture

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthMetrics":
        for field_name in (
            "procedural_depth_metrics_id",
            "procedural_depth_run_trace_ref",
            "procedural_depth_gold_trace_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "expected_top_level_spine",
            "observed_top_level_activation_sequence",
        ):
            values = list(getattr(self, field_name))
            if len(values) != len(set(values)):
                raise ValueError(f"{field_name} must not contain duplicates")
            object.__setattr__(
                self,
                field_name,
                [_assert_non_empty_text(value, field_name=field_name) for value in values],
            )
        expected_overall = _rounded_score(
            (
                self.plan_spine_fidelity_score
                + self.active_step_compilation_score
                + self.reintegration_fidelity_score
            )
            / 3.0
        )
        if self.overall_structural_fidelity_score != expected_overall:
            raise ValueError(
                "overall_structural_fidelity_score must equal rounded mean of the three axes"
            )
        for axis_name, score, posture in (
            (
                "plan_spine_fidelity_score",
                self.plan_spine_fidelity_score,
                self.plan_spine_posture,
            ),
            (
                "active_step_compilation_score",
                self.active_step_compilation_score,
                self.active_step_compilation_posture,
            ),
            (
                "reintegration_fidelity_score",
                self.reintegration_fidelity_score,
                self.reintegration_posture,
            ),
        ):
            expected_posture = "clean" if score == 1.0 else "degraded"
            if posture != expected_posture:
                raise ValueError(
                    f"{axis_name} posture must match score-derived clean/degraded state"
                )
        expected_id = compute_procedural_depth_metrics_id(_canonical_model_payload(self))
        if self.procedural_depth_metrics_id != expected_id:
            raise ValueError(
                "procedural_depth_metrics_id must match canonical metrics identity"
            )
        return self


class ProceduralDepthFailureRecord(BaseModel):
    model_config = MODEL_CONFIG

    failure_record_id: str
    failure_family: FailureFamily
    failure_code: str
    step_id: str
    expected: str | None = None
    observed: str | None = None
    supporting_event_index: int | None = Field(default=None, ge=0)

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthFailureRecord":
        for field_name in ("failure_record_id", "failure_code", "step_id"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        if self.expected is not None:
            object.__setattr__(
                self,
                "expected",
                _assert_non_empty_text(self.expected, field_name="expected"),
            )
        if self.observed is not None:
            object.__setattr__(
                self,
                "observed",
                _assert_non_empty_text(self.observed, field_name="observed"),
            )
        expected_id = compute_procedural_depth_failure_record_id(_canonical_model_payload(self))
        if self.failure_record_id != expected_id:
            raise ValueError("failure_record_id must match canonical failure identity")
        return self


class ProceduralDepthDiagnosticReport(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[PROCEDURAL_DEPTH_DIAGNOSTIC_REPORT_SCHEMA] = (
        PROCEDURAL_DEPTH_DIAGNOSTIC_REPORT_SCHEMA
    )
    procedural_depth_diagnostic_report_id: str
    procedural_depth_run_trace_ref: str
    procedural_depth_metrics_ref: str
    dominant_failure_family: DominantFailureFamily
    epistemic_posture: EpistemicPosture
    failure_records: list[ProceduralDepthFailureRecord] = Field(default_factory=list)
    diagnostic_summary: str

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthDiagnosticReport":
        for field_name in (
            "procedural_depth_diagnostic_report_id",
            "procedural_depth_run_trace_ref",
            "procedural_depth_metrics_ref",
            "diagnostic_summary",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        ordered_failures = sorted(
            self.failure_records,
            key=lambda entry: (
                entry.failure_family,
                entry.step_id,
                entry.failure_code,
                entry.supporting_event_index if entry.supporting_event_index is not None else -1,
            ),
        )
        object.__setattr__(self, "failure_records", ordered_failures)
        if self.dominant_failure_family == "clean_success" and self.failure_records:
            raise ValueError("clean_success diagnostic report may not carry failure_records")
        expected_id = compute_procedural_depth_diagnostic_report_id(
            _canonical_model_payload(self)
        )
        if self.procedural_depth_diagnostic_report_id != expected_id:
            raise ValueError(
                "procedural_depth_diagnostic_report_id must match canonical diagnostic identity"
            )
        return self


def compute_procedural_depth_instance_id(payload: dict[str, Any]) -> str:
    material = {
        "benchmark_projection_spec_ref": payload.get("benchmark_projection_spec_ref"),
        "instance_family_label": payload.get("instance_family_label"),
        "instance_label": payload.get("instance_label"),
        "repo_snapshot_ref": payload.get("repo_snapshot_ref"),
        "source_surface_refs": payload.get("source_surface_refs"),
        "instruction_constitution": payload.get("instruction_constitution"),
        "benchmark_tags": payload.get("benchmark_tags"),
        "top_level_spine": payload.get("top_level_spine"),
        "expected_final_step_id": payload.get("expected_final_step_id"),
        "step_specs": payload.get("step_specs"),
    }
    return f"pdepthinst_{sha256_canonical_json(material)[:32]}"


def compute_procedural_depth_gold_trace_id(payload: dict[str, Any]) -> str:
    material = {
        "procedural_depth_instance_ref": payload.get("procedural_depth_instance_ref"),
        "top_level_spine": payload.get("top_level_spine"),
        "gold_events": payload.get("gold_events"),
    }
    return f"pdepthgold_{sha256_canonical_json(material)[:32]}"


def compute_procedural_depth_run_trace_id(payload: dict[str, Any]) -> str:
    material = {
        "procedural_depth_instance_ref": payload.get("procedural_depth_instance_ref"),
        "benchmark_execution_context_ref": payload.get("benchmark_execution_context_ref"),
        "run_label": payload.get("run_label"),
        "observed_events": payload.get("observed_events"),
        "observed_final_output_summary": payload.get("observed_final_output_summary"),
        "trace_notes": payload.get("trace_notes"),
    }
    return f"pdepthrun_{sha256_canonical_json(material)[:32]}"


def compute_procedural_depth_metrics_id(payload: dict[str, Any]) -> str:
    material = {
        "procedural_depth_run_trace_ref": payload.get("procedural_depth_run_trace_ref"),
        "procedural_depth_gold_trace_ref": payload.get("procedural_depth_gold_trace_ref"),
        "expected_top_level_spine": payload.get("expected_top_level_spine"),
        "observed_top_level_activation_sequence": payload.get(
            "observed_top_level_activation_sequence"
        ),
        "plan_spine_fidelity_score": payload.get("plan_spine_fidelity_score"),
        "active_step_compilation_score": payload.get("active_step_compilation_score"),
        "reintegration_fidelity_score": payload.get("reintegration_fidelity_score"),
        "overall_structural_fidelity_score": payload.get(
            "overall_structural_fidelity_score"
        ),
        "top_level_longest_correct_prefix": payload.get("top_level_longest_correct_prefix"),
        "evaluated_parent_steps": payload.get("evaluated_parent_steps"),
        "required_child_completion_rate": payload.get("required_child_completion_rate"),
        "return_event_success_rate": payload.get("return_event_success_rate"),
        "plan_spine_posture": payload.get("plan_spine_posture"),
        "active_step_compilation_posture": payload.get(
            "active_step_compilation_posture"
        ),
        "reintegration_posture": payload.get("reintegration_posture"),
    }
    return f"pdepthmetrics_{sha256_canonical_json(material)[:32]}"


def compute_procedural_depth_failure_record_id(payload: dict[str, Any]) -> str:
    material = {
        "failure_family": payload.get("failure_family"),
        "failure_code": payload.get("failure_code"),
        "step_id": payload.get("step_id"),
        "expected": payload.get("expected"),
        "observed": payload.get("observed"),
        "supporting_event_index": payload.get("supporting_event_index"),
    }
    return f"pdepthfail_{sha256_canonical_json(material)[:32]}"


def compute_procedural_depth_diagnostic_report_id(payload: dict[str, Any]) -> str:
    material = {
        "procedural_depth_run_trace_ref": payload.get("procedural_depth_run_trace_ref"),
        "procedural_depth_metrics_ref": payload.get("procedural_depth_metrics_ref"),
        "dominant_failure_family": payload.get("dominant_failure_family"),
        "epistemic_posture": payload.get("epistemic_posture"),
        "failure_records": payload.get("failure_records"),
        "diagnostic_summary": payload.get("diagnostic_summary"),
    }
    return f"pdepthdiag_{sha256_canonical_json(material)[:32]}"


def materialize_procedural_depth_instance_payload(payload: dict[str, Any]) -> dict[str, Any]:
    prepared = _prepare_payload(
        payload,
        id_field="procedural_depth_instance_id",
        compute_id=compute_procedural_depth_instance_id,
    )
    return _canonical_model_payload(ProceduralDepthInstance.model_validate(prepared))


def canonicalize_procedural_depth_instance_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return _canonical_model_payload(ProceduralDepthInstance.model_validate(payload))


def materialize_procedural_depth_gold_trace_payload(payload: dict[str, Any]) -> dict[str, Any]:
    prepared = _prepare_payload(
        payload,
        id_field="procedural_depth_gold_trace_id",
        compute_id=compute_procedural_depth_gold_trace_id,
    )
    return _canonical_model_payload(ProceduralDepthGoldTrace.model_validate(prepared))


def canonicalize_procedural_depth_gold_trace_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return _canonical_model_payload(ProceduralDepthGoldTrace.model_validate(payload))


def materialize_procedural_depth_run_trace_payload(payload: dict[str, Any]) -> dict[str, Any]:
    prepared = _prepare_payload(
        payload,
        id_field="procedural_depth_run_trace_id",
        compute_id=compute_procedural_depth_run_trace_id,
    )
    return _canonical_model_payload(ProceduralDepthRunTrace.model_validate(prepared))


def canonicalize_procedural_depth_run_trace_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return _canonical_model_payload(ProceduralDepthRunTrace.model_validate(payload))


def materialize_procedural_depth_metrics_payload(payload: dict[str, Any]) -> dict[str, Any]:
    prepared = _prepare_payload(
        payload,
        id_field="procedural_depth_metrics_id",
        compute_id=compute_procedural_depth_metrics_id,
    )
    return _canonical_model_payload(ProceduralDepthMetrics.model_validate(prepared))


def canonicalize_procedural_depth_metrics_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return _canonical_model_payload(ProceduralDepthMetrics.model_validate(payload))


def materialize_procedural_depth_diagnostic_report_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = deepcopy(payload)
    failures: list[dict[str, Any]] = []
    for failure_payload in prepared.get("failure_records", []):
        failure_material = deepcopy(failure_payload)
        failure_material.setdefault(
            "failure_record_id",
            compute_procedural_depth_failure_record_id(failure_material),
        )
        failures.append(
            _canonical_model_payload(ProceduralDepthFailureRecord.model_validate(failure_material))
        )
    prepared["failure_records"] = failures
    prepared.setdefault(
        "procedural_depth_diagnostic_report_id",
        compute_procedural_depth_diagnostic_report_id(prepared),
    )
    return _canonical_model_payload(ProceduralDepthDiagnosticReport.model_validate(prepared))


def canonicalize_procedural_depth_diagnostic_report_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    return _canonical_model_payload(ProceduralDepthDiagnosticReport.model_validate(payload))


def derive_procedural_depth_gold_trace(
    *,
    instance_payload: dict[str, Any],
) -> dict[str, Any]:
    instance = ProceduralDepthInstance.model_validate(instance_payload)
    children_by_parent = _children_by_parent(instance.step_specs)
    events: list[dict[str, Any]] = []

    def _emit_event(
        *,
        event_type: TraceEventType,
        step_id: str,
        target_step_id: str | None = None,
    ) -> None:
        payload: dict[str, Any] = {
            "event_index": len(events),
            "event_type": event_type,
            "step_id": step_id,
        }
        if target_step_id is not None:
            payload["target_step_id"] = target_step_id
        events.append(payload)

    def _walk(step_id: str) -> None:
        _emit_event(event_type="activate", step_id=step_id)
        for child in children_by_parent.get(step_id, []):
            _walk(child.step_id)
            _emit_event(
                event_type="return",
                step_id=child.step_id,
                target_step_id=step_id,
            )
        _emit_event(event_type="complete", step_id=step_id)

    for top_level_step in instance.top_level_spine:
        _walk(top_level_step)

    return materialize_procedural_depth_gold_trace_payload(
        {
            "procedural_depth_instance_ref": instance.procedural_depth_instance_id,
            "top_level_spine": instance.top_level_spine,
            "gold_events": events,
        }
    )


def validate_procedural_depth_gold_trace_against_instance(
    *,
    instance_payload: dict[str, Any],
    gold_trace_payload: dict[str, Any],
) -> tuple[ProceduralDepthInstance, ProceduralDepthGoldTrace]:
    instance = ProceduralDepthInstance.model_validate(instance_payload)
    gold_trace = ProceduralDepthGoldTrace.model_validate(gold_trace_payload)
    if gold_trace.procedural_depth_instance_ref != instance.procedural_depth_instance_id:
        raise ValueError("gold trace must reference the supplied procedural depth instance")
    if gold_trace.top_level_spine != instance.top_level_spine:
        raise ValueError("gold trace top_level_spine must match the instance top_level_spine")
    expected_gold = ProceduralDepthGoldTrace.model_validate(
        derive_procedural_depth_gold_trace(instance_payload=_canonical_model_payload(instance))
    )
    if gold_trace.gold_events != expected_gold.gold_events:
        raise ValueError("gold trace events must match deterministic derivation from the instance")
    return instance, gold_trace


def validate_procedural_depth_run_trace_against_instance(
    *,
    instance_payload: dict[str, Any],
    run_trace_payload: dict[str, Any],
) -> tuple[ProceduralDepthInstance, ProceduralDepthRunTrace]:
    instance = ProceduralDepthInstance.model_validate(instance_payload)
    run_trace = ProceduralDepthRunTrace.model_validate(run_trace_payload)
    if run_trace.procedural_depth_instance_ref != instance.procedural_depth_instance_id:
        raise ValueError("run trace must reference the supplied procedural depth instance")
    step_map = _step_map(instance.step_specs)
    for event in run_trace.observed_events:
        if event.step_id not in step_map:
            raise ValueError("run trace event step_id must resolve inside instance step_specs")
        if event.event_type == "return":
            assert event.target_step_id is not None
            if event.target_step_id not in step_map:
                raise ValueError(
                    "run trace return target_step_id must resolve inside instance step_specs"
                )
    return instance, run_trace


def score_procedural_depth_run(
    *,
    instance_payload: dict[str, Any],
    gold_trace_payload: dict[str, Any],
    run_trace_payload: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    instance, gold_trace = validate_procedural_depth_gold_trace_against_instance(
        instance_payload=instance_payload,
        gold_trace_payload=gold_trace_payload,
    )
    _, run_trace = validate_procedural_depth_run_trace_against_instance(
        instance_payload=_canonical_model_payload(instance),
        run_trace_payload=run_trace_payload,
    )
    step_map = _step_map(instance.step_specs)
    children_by_parent = _children_by_parent(instance.step_specs)
    observed_events = run_trace.observed_events

    failures: list[dict[str, Any]] = []

    expected_spine = instance.top_level_spine
    observed_spine = _observed_top_level_activation_sequence(
        events=observed_events,
        top_level_spine=expected_spine,
    )
    top_level_prefix = _longest_correct_prefix(observed_spine, expected_spine)
    plan_score = _rounded_score(top_level_prefix / len(expected_spine))
    mismatch_recorded = False
    for index, expected_step_id in enumerate(expected_spine):
        if index >= len(observed_spine):
            failures.append(
                _build_failure(
                    failure_family="horizontal_plan_spine",
                    failure_code="missing_top_level_step",
                    step_id=expected_step_id,
                    expected=expected_step_id,
                )
            )
            mismatch_recorded = True
            break
        observed_step_id = observed_spine[index]
        if observed_step_id != expected_step_id:
            failures.append(
                _build_failure(
                    failure_family="horizontal_plan_spine",
                    failure_code="top_level_order_mismatch",
                    step_id=expected_step_id,
                    expected=expected_step_id,
                    observed=observed_step_id,
                )
            )
            mismatch_recorded = True
            break
    if not mismatch_recorded and len(observed_spine) > len(expected_spine):
        for extra_step_id in observed_spine[len(expected_spine) :]:
            failures.append(
                _build_failure(
                    failure_family="horizontal_plan_spine",
                    failure_code="unexpected_extra_top_level_step",
                    step_id=extra_step_id,
                    observed=extra_step_id,
                )
            )

    evaluated_parent_steps = 0
    total_required_child_slots = 0
    matched_required_child_slots = 0
    total_vertical_checks = 0
    matched_vertical_checks = 0
    total_return_checks = 0
    matched_return_checks = 0

    for parent in instance.step_specs:
        if not parent.required_child_step_ids:
            continue
        window = _parent_window(
            parent_step_id=parent.step_id,
            events=observed_events,
            children_by_parent=children_by_parent,
        )
        if window is None:
            continue
        evaluated_parent_steps += 1
        start_index, stop_index = window
        child_ids = list(parent.required_child_step_ids)
        child_completion_indexes: dict[str, int] = {}
        order_ok = True
        last_completion_index = -1
        total_required_child_slots += len(child_ids)
        total_vertical_checks += len(child_ids) + 1
        for child_id in child_ids:
            completion_index = _first_event_index(
                observed_events,
                event_type="complete",
                step_id=child_id,
                start=start_index,
                stop=stop_index,
            )
            if completion_index is None:
                failures.append(
                    _build_failure(
                        failure_family="vertical_active_step_compilation",
                        failure_code="missing_required_child_completion",
                        step_id=parent.step_id,
                        expected=child_id,
                    )
                )
                continue
            child_completion_indexes[child_id] = completion_index
            if parent.child_order_policy == "ordered" and completion_index <= last_completion_index:
                order_ok = False
                failures.append(
                    _build_failure(
                        failure_family="vertical_active_step_compilation",
                        failure_code="child_completion_order_violation",
                        step_id=parent.step_id,
                        expected=child_id,
                        supporting_event_index=completion_index,
                    )
                )
                continue
            matched_required_child_slots += 1
            matched_vertical_checks += 1
            last_completion_index = completion_index
        parent_complete_index = _first_event_index(
            observed_events,
            event_type="complete",
            step_id=parent.step_id,
            start=start_index,
            stop=stop_index,
        )
        boundary_ok = (
            parent_complete_index is not None
            and len(child_completion_indexes) == len(child_ids)
            and order_ok
            and all(index < parent_complete_index for index in child_completion_indexes.values())
        )
        if boundary_ok:
            matched_vertical_checks += 1
        elif parent_complete_index is None:
            failures.append(
                _build_failure(
                    failure_family="vertical_active_step_compilation",
                    failure_code="missing_parent_completion_boundary",
                    step_id=parent.step_id,
                )
            )
        else:
            failures.append(
                _build_failure(
                    failure_family="vertical_active_step_compilation",
                    failure_code="parent_completed_before_required_children",
                    step_id=parent.step_id,
                    supporting_event_index=parent_complete_index,
                )
            )
        for child_id, completion_index in child_completion_indexes.items():
            total_return_checks += 1
            found_return, boundary_index = _search_return_before_boundary(
                events=observed_events,
                child_step_id=child_id,
                parent_step_id=parent.step_id,
                start=completion_index + 1,
                stop=stop_index,
            )
            if found_return:
                matched_return_checks += 1
                continue
            failures.append(
                _build_failure(
                    failure_family="reintegration",
                    failure_code="missing_return_to_parent_before_progression",
                    step_id=parent.step_id,
                    expected=child_id,
                    supporting_event_index=boundary_index,
                )
            )

    active_step_score = 1.0
    required_child_completion_rate = 1.0
    if total_vertical_checks:
        active_step_score = _rounded_score(matched_vertical_checks / total_vertical_checks)
    if total_required_child_slots:
        required_child_completion_rate = _rounded_score(
            matched_required_child_slots / total_required_child_slots
        )
    reintegration_score = 1.0
    return_event_success_rate = 1.0
    if total_return_checks:
        reintegration_score = _rounded_score(matched_return_checks / total_return_checks)
        return_event_success_rate = reintegration_score

    metrics_payload = materialize_procedural_depth_metrics_payload(
        {
            "procedural_depth_run_trace_ref": run_trace.procedural_depth_run_trace_id,
            "procedural_depth_gold_trace_ref": gold_trace.procedural_depth_gold_trace_id,
            "expected_top_level_spine": expected_spine,
            "observed_top_level_activation_sequence": observed_spine or [expected_spine[0]],
            "plan_spine_fidelity_score": plan_score,
            "active_step_compilation_score": active_step_score,
            "reintegration_fidelity_score": reintegration_score,
            "overall_structural_fidelity_score": _rounded_score(
                (plan_score + active_step_score + reintegration_score) / 3.0
            ),
            "top_level_longest_correct_prefix": top_level_prefix,
            "evaluated_parent_steps": evaluated_parent_steps,
            "required_child_completion_rate": required_child_completion_rate,
            "return_event_success_rate": return_event_success_rate,
            "plan_spine_posture": "clean" if plan_score == 1.0 else "degraded",
            "active_step_compilation_posture": (
                "clean" if active_step_score == 1.0 else "degraded"
            ),
            "reintegration_posture": "clean" if reintegration_score == 1.0 else "degraded",
        }
    )

    if not failures:
        dominant_family: DominantFailureFamily = "clean_success"
        diagnostic_summary = (
            "Run preserved the top-level spine, compiled nested active steps, and returned "
            "cleanly to the parent plan."
        )
    else:
        counts = Counter(entry["failure_family"] for entry in failures)
        max_count = max(counts.values())
        leaders = sorted(family for family, count in counts.items() if count == max_count)
        if len(leaders) == 1:
            dominant_family = leaders[0]
        else:
            dominant_family = "mixed"
        diagnostic_summary = (
            f"{dominant_family} failure topology derived deterministically from run/gold "
            f"comparison with {len(failures)} failure record(s)."
        )

    diagnostic_payload = materialize_procedural_depth_diagnostic_report_payload(
        {
            "procedural_depth_run_trace_ref": run_trace.procedural_depth_run_trace_id,
            "procedural_depth_metrics_ref": metrics_payload["procedural_depth_metrics_id"],
            "dominant_failure_family": dominant_family,
            "epistemic_posture": "derived_deterministically_from_run_and_gold",
            "failure_records": failures,
            "diagnostic_summary": diagnostic_summary,
        }
    )
    return metrics_payload, diagnostic_payload


__all__ = [
    "PROCEDURAL_DEPTH_DIAGNOSTIC_REPORT_SCHEMA",
    "PROCEDURAL_DEPTH_GOLD_TRACE_SCHEMA",
    "PROCEDURAL_DEPTH_INSTANCE_SCHEMA",
    "PROCEDURAL_DEPTH_METRICS_SCHEMA",
    "PROCEDURAL_DEPTH_RUN_TRACE_SCHEMA",
    "AxisPosture",
    "ChildOrderPolicy",
    "FailureFamily",
    "ProceduralDepthDiagnosticReport",
    "ProceduralDepthFailureRecord",
    "ProceduralDepthGoldTrace",
    "ProceduralDepthInstance",
    "ProceduralDepthMetrics",
    "ProceduralDepthRunTrace",
    "ProceduralDepthStepSpec",
    "ProceduralDepthTraceEvent",
    "canonicalize_procedural_depth_diagnostic_report_payload",
    "canonicalize_procedural_depth_gold_trace_payload",
    "canonicalize_procedural_depth_instance_payload",
    "canonicalize_procedural_depth_metrics_payload",
    "canonicalize_procedural_depth_run_trace_payload",
    "compute_procedural_depth_diagnostic_report_id",
    "compute_procedural_depth_failure_record_id",
    "compute_procedural_depth_gold_trace_id",
    "compute_procedural_depth_instance_id",
    "compute_procedural_depth_metrics_id",
    "compute_procedural_depth_run_trace_id",
    "derive_procedural_depth_gold_trace",
    "materialize_procedural_depth_diagnostic_report_payload",
    "materialize_procedural_depth_gold_trace_payload",
    "materialize_procedural_depth_instance_payload",
    "materialize_procedural_depth_metrics_payload",
    "materialize_procedural_depth_run_trace_payload",
    "score_procedural_depth_run",
    "validate_procedural_depth_gold_trace_against_instance",
    "validate_procedural_depth_run_trace_against_instance",
]
