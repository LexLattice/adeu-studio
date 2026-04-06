from __future__ import annotations

from copy import deepcopy
from typing import Any, Callable, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

ADEU_BENCHMARK_FAMILY_SPEC_SCHEMA = "adeu_benchmark_family_spec@1"
ADEU_BENCHMARK_PROJECTION_SPEC_SCHEMA = "adeu_benchmark_projection_spec@1"
ADEU_BENCHMARK_EXECUTION_CONTEXT_SCHEMA = "adeu_benchmark_execution_context@1"
ADEU_BENCHMARK_VALIDATION_REPORT_SCHEMA = "adeu_benchmark_validation_report@1"
ADEU_PROCEDURAL_DEPTH_INSTANCE_SCHEMA = "adeu_procedural_depth_instance@1"
ADEU_PROCEDURAL_DEPTH_GOLD_TRACE_SCHEMA = "adeu_procedural_depth_gold_trace@1"
ADEU_PROCEDURAL_DEPTH_RUN_TRACE_SCHEMA = "adeu_procedural_depth_run_trace@1"
ADEU_PROCEDURAL_DEPTH_METRICS_SCHEMA = "adeu_procedural_depth_metrics@1"
ADEU_PROCEDURAL_DEPTH_DIAGNOSTIC_REPORT_SCHEMA = "adeu_procedural_depth_diagnostic_report@1"

SUBJECT_UNDER_TEST_CLASS_VOCABULARY = [
    "base_model",
    "prompted_model",
    "routed_runtime",
    "multi_agent_system",
    "adeu_runtime_surface",
]
BENCHMARK_OUTPUT_EPISTEMIC_POSTURE_VOCABULARY = [
    "observed",
    "derived_deterministically",
    "inferred_interpretively",
    "adjudicated",
    "settled",
]
DIAGNOSTIC_POSTURE_VOCABULARY = ["diagnostic_only"]
IMPLEMENTATION_POSTURE_VOCABULARY = ["bounded_repo_owned_non_promotional"]
CONTEXT_BUDGET_POSTURE_VOCABULARY = ["fixed_context_budget_declared"]
DETERMINISM_POSTURE_VOCABULARY = [
    "deterministic_fixed_context",
    "stochastic_context",
]
VALIDATION_SCOPE_VOCABULARY = ["tiny_reference_fixture_bundle"]
SCORER_DETERMINISM_POSTURE_VOCABULARY = ["deterministic_fixture_replay_confirmed"]
DOMINANT_FAILURE_FAMILY_VOCABULARY = [
    "clean_success",
    "horizontal_plan_spine",
    "vertical_active_step_compilation",
    "reintegration",
    "mixed",
]
REFERENCE_CHAIN_KEY_VOCABULARY = ["hierarchical_3x3"]
EVENT_KIND_VOCABULARY = ["activate", "complete", "return"]
STEP_ROLE_VOCABULARY = ["top_level", "active_parent", "child"]
EXPECTED_TERMINAL_POSTURE_VOCABULARY = ["complete_after_required_return"]
PROCEDURAL_DEPTH_TERMINAL_TRACE_STATUS_VOCABULARY = [
    "completed_clean",
    "completed_with_structural_break",
]
TRACE_ROLE_VOCABULARY = ["gold", "run"]
PROCEDURAL_DEPTH_DIAGNOSTIC_EPISTEMIC_POSTURE_VOCABULARY = [
    "inferred_interpretively"
]

SubjectUnderTestClass = Literal[
    "base_model",
    "prompted_model",
    "routed_runtime",
    "multi_agent_system",
    "adeu_runtime_surface",
]
BenchmarkOutputEpistemicPosture = Literal[
    "observed",
    "derived_deterministically",
    "inferred_interpretively",
    "adjudicated",
    "settled",
]
DiagnosticPosture = Literal["diagnostic_only"]
ImplementationPosture = Literal["bounded_repo_owned_non_promotional"]
ContextBudgetPosture = Literal["fixed_context_budget_declared"]
DeterminismPosture = Literal["deterministic_fixed_context", "stochastic_context"]
ValidationScope = Literal["tiny_reference_fixture_bundle"]
ScorerDeterminismPosture = Literal["deterministic_fixture_replay_confirmed"]
DominantFailureFamily = Literal[
    "clean_success",
    "horizontal_plan_spine",
    "vertical_active_step_compilation",
    "reintegration",
    "mixed",
]
ReferenceChainKey = Literal["hierarchical_3x3"]
EventKind = Literal["activate", "complete", "return"]
StepRole = Literal["top_level", "active_parent", "child"]
ExpectedTerminalPosture = Literal["complete_after_required_return"]
ProceduralDepthTerminalTraceStatus = Literal[
    "completed_clean",
    "completed_with_structural_break",
]
TraceRole = Literal["gold", "run"]
ProceduralDepthDiagnosticEpistemicPosture = Literal["inferred_interpretively"]


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


def _ordered_unique_texts(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must not contain duplicates")
    return normalized


def _ordered_subset(
    values: list[str],
    *,
    allowed_order: list[str],
    field_name: str,
) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must not contain duplicates")
    unsupported = sorted(set(normalized) - set(allowed_order))
    if unsupported:
        raise ValueError(f"{field_name} contains unsupported values: {unsupported}")
    return [value for value in allowed_order if value in set(normalized)]


def _exact_ordered_vocabulary(
    values: list[str],
    *,
    expected_order: list[str],
    field_name: str,
) -> list[str]:
    ordered = _ordered_subset(values, allowed_order=expected_order, field_name=field_name)
    if ordered != expected_order:
        raise ValueError(f"{field_name} must equal the starter vocabulary exactly")
    return ordered


def _canonical_model_payload(model: BaseModel) -> dict[str, Any]:
    return model.model_dump(mode="json", by_alias=True, exclude_none=True)


def _prepare_payload(
    payload: dict[str, Any],
    *,
    id_field: str,
    compute_id: Callable[[dict[str, Any]], str],
) -> dict[str, Any]:
    prepared = deepcopy(payload)
    prepared.setdefault(id_field, compute_id(prepared))
    return prepared


def _assert_contiguous_event_indexes(
    events: list["ProceduralDepthTraceEvent"], *, field_name: str
) -> list["ProceduralDepthTraceEvent"]:
    observed = [event.event_index for event in events]
    if observed != list(range(len(events))):
        raise ValueError(f"{field_name} event_index values must be contiguous from 0")
    return events


def _procedural_step_map(
    step_specs: list["ProceduralDepthStepSpec"],
) -> dict[str, "ProceduralDepthStepSpec"]:
    return {step.step_ref: step for step in step_specs}


def _procedural_children_by_parent(
    step_specs: list["ProceduralDepthStepSpec"],
) -> dict[str | None, list["ProceduralDepthStepSpec"]]:
    grouped: dict[str | None, list[ProceduralDepthStepSpec]] = {}
    for step in step_specs:
        grouped.setdefault(step.parent_step_ref, []).append(step)
    for entries in grouped.values():
        entries.sort(key=lambda step: (step.order_index, step.step_ref))
    return grouped


def _procedural_canonical_step_order(
    top_level_plan_spine: list[str],
    children_by_parent: dict[str | None, list["ProceduralDepthStepSpec"]],
) -> list[str]:
    ordered: list[str] = []
    for root_ref in top_level_plan_spine:
        ordered.append(root_ref)
        for child in children_by_parent.get(root_ref, []):
            ordered.append(child.step_ref)
    return ordered


def compute_benchmark_family_spec_id(payload: dict[str, Any]) -> str:
    material = {
        "family_key": payload.get("family_key"),
        "family_label": payload.get("family_label"),
        "doctrinal_source_refs": _sorted_unique_texts(
            list(payload.get("doctrinal_source_refs", [])),
            field_name="doctrinal_source_refs",
        ),
        "capability_axes": _sorted_unique_texts(
            list(payload.get("capability_axes", [])),
            field_name="capability_axes",
        ),
        "baseline_regime_summary": payload.get("baseline_regime_summary"),
        "perturbation_axis_posture": payload.get("perturbation_axis_posture"),
        "reliability_policy_summary": payload.get("reliability_policy_summary"),
        "non_regression_policy_summary": payload.get("non_regression_policy_summary"),
        "subject_under_test_classes": _exact_ordered_vocabulary(
            list(payload.get("subject_under_test_classes", [])),
            expected_order=SUBJECT_UNDER_TEST_CLASS_VOCABULARY,
            field_name="subject_under_test_classes",
        ),
        "benchmark_output_epistemic_postures": _exact_ordered_vocabulary(
            list(payload.get("benchmark_output_epistemic_postures", [])),
            expected_order=BENCHMARK_OUTPUT_EPISTEMIC_POSTURE_VOCABULARY,
            field_name="benchmark_output_epistemic_postures",
        ),
        "diagnostic_posture": payload.get("diagnostic_posture"),
        "implementation_posture": payload.get("implementation_posture"),
    }
    return f"benchfam_{sha256_canonical_json(material)[:32]}"


def compute_benchmark_projection_spec_id(payload: dict[str, Any]) -> str:
    material = {
        "benchmark_family_spec_ref": payload.get("benchmark_family_spec_ref"),
        "projection_key": payload.get("projection_key"),
        "projection_label": payload.get("projection_label"),
        "constraint_source_refs": _sorted_unique_texts(
            list(payload.get("constraint_source_refs", [])),
            field_name="constraint_source_refs",
        ),
        "target_capability_axes": _sorted_unique_texts(
            list(payload.get("target_capability_axes", [])),
            field_name="target_capability_axes",
        ),
        "target_subject_under_test_classes": _ordered_subset(
            list(payload.get("target_subject_under_test_classes", [])),
            allowed_order=SUBJECT_UNDER_TEST_CLASS_VOCABULARY,
            field_name="target_subject_under_test_classes",
        ),
        "hierarchical_trace_required": payload.get("hierarchical_trace_required"),
        "explicit_reintegration_trace_required": payload.get(
            "explicit_reintegration_trace_required"
        ),
        "projection_validity_posture": payload.get("projection_validity_posture"),
        "interpretation_boundary_summary": payload.get("interpretation_boundary_summary"),
        "declared_instance_contract_id": payload.get("declared_instance_contract_id"),
        "declared_gold_trace_contract_id": payload.get("declared_gold_trace_contract_id"),
        "declared_run_trace_contract_id": payload.get("declared_run_trace_contract_id"),
        "declared_metrics_contract_id": payload.get("declared_metrics_contract_id"),
        "declared_diagnostic_report_contract_id": payload.get(
            "declared_diagnostic_report_contract_id"
        ),
        "projection_notes": _sorted_unique_texts(
            list(payload.get("projection_notes", [])),
            field_name="projection_notes",
        ),
    }
    return f"benchproj_{sha256_canonical_json(material)[:32]}"


def compute_benchmark_execution_context_id(payload: dict[str, Any]) -> str:
    material = {
        "subject_under_test_class": payload.get("subject_under_test_class"),
        "subject_label": payload.get("subject_label"),
        "subject_version": payload.get("subject_version"),
        "prompt_wrapper_ref": payload.get("prompt_wrapper_ref"),
        "tool_availability": _sorted_unique_texts(
            list(payload.get("tool_availability", [])),
            field_name="tool_availability",
        ),
        "context_budget_posture": payload.get("context_budget_posture"),
        "determinism_posture": payload.get("determinism_posture"),
        "repo_snapshot_ref": payload.get("repo_snapshot_ref"),
        "orchestration_topology_ref": payload.get("orchestration_topology_ref"),
        "notes": _sorted_unique_texts(
            list(payload.get("notes", [])),
            field_name="notes",
        ),
    }
    return f"benchctx_{sha256_canonical_json(material)[:32]}"


def compute_benchmark_validation_case_result_id(payload: dict[str, Any]) -> str:
    material = {
        "case_label": payload.get("case_label"),
        "case_ref": payload.get("case_ref"),
        "expected_dominant_failure_family": payload.get("expected_dominant_failure_family"),
        "observed_dominant_failure_family": payload.get("observed_dominant_failure_family"),
        "match": payload.get("match"),
    }
    return f"benchvalcase_{sha256_canonical_json(material)[:32]}"


def compute_benchmark_validation_report_id(payload: dict[str, Any]) -> str:
    case_material = [
        {
            "case_label": case.get("case_label"),
            "case_ref": case.get("case_ref"),
            "expected_dominant_failure_family": case.get(
                "expected_dominant_failure_family"
            ),
            "observed_dominant_failure_family": case.get(
                "observed_dominant_failure_family"
            ),
            "match": case.get("match"),
        }
        for case in sorted(
            payload.get("validation_case_results", []),
            key=lambda item: item.get("case_label", ""),
        )
    ]
    material = {
        "benchmark_projection_spec_ref": payload.get("benchmark_projection_spec_ref"),
        "validation_label": payload.get("validation_label"),
        "validation_scope": payload.get("validation_scope"),
        "scorer_determinism_posture": payload.get("scorer_determinism_posture"),
        "validation_case_results": case_material,
        "all_expected_diagnostics_matched": payload.get(
            "all_expected_diagnostics_matched"
        ),
        "benchmark_limitations": _sorted_unique_texts(
            list(payload.get("benchmark_limitations", [])),
            field_name="benchmark_limitations",
        ),
    }
    return f"benchval_{sha256_canonical_json(material)[:32]}"


def _canonicalize_procedural_depth_gold_trace_material(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = deepcopy(payload)
    prepared["procedural_depth_instance_ref"] = _assert_non_empty_text(
        prepared["procedural_depth_instance_ref"],
        field_name="procedural_depth_instance_ref",
    )
    prepared["gold_events"] = _canonicalize_trace_events(
        list(prepared.get("gold_events", [])),
        field_name="gold_events",
    )
    prepared["derivation_notes"] = _sorted_unique_texts(
        list(prepared.get("derivation_notes", [])),
        field_name="derivation_notes",
    )
    prepared.setdefault("terminal_trace_status", "completed_clean")
    return prepared


def _canonicalize_procedural_depth_run_trace_material(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = deepcopy(payload)
    prepared["procedural_depth_instance_ref"] = _assert_non_empty_text(
        prepared["procedural_depth_instance_ref"],
        field_name="procedural_depth_instance_ref",
    )
    prepared["observed_output_summary"] = _assert_non_empty_text(
        prepared["observed_output_summary"],
        field_name="observed_output_summary",
    )
    prepared["observed_events"] = _canonicalize_trace_events(
        list(prepared.get("observed_events", [])),
        field_name="observed_events",
    )
    prepared["trace_notes"] = _sorted_unique_texts(
        list(prepared.get("trace_notes", [])),
        field_name="trace_notes",
    )
    return prepared


def _canonicalize_procedural_depth_metrics_material(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = deepcopy(payload)
    prepared["procedural_depth_run_trace_ref"] = _assert_non_empty_text(
        prepared["procedural_depth_run_trace_ref"],
        field_name="procedural_depth_run_trace_ref",
    )
    prepared["procedural_depth_gold_trace_ref"] = _assert_non_empty_text(
        prepared["procedural_depth_gold_trace_ref"],
        field_name="procedural_depth_gold_trace_ref",
    )
    prepared["supporting_event_refs"] = _canonicalize_supporting_event_refs(
        list(prepared.get("supporting_event_refs", []))
    )
    prepared["scoring_notes"] = _sorted_unique_texts(
        list(prepared.get("scoring_notes", [])),
        field_name="scoring_notes",
    )
    return prepared


def _canonicalize_procedural_depth_diagnostic_report_material(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = deepcopy(payload)
    for field_name in (
        "procedural_depth_run_trace_ref",
        "procedural_depth_metrics_ref",
        "diagnostic_summary",
    ):
        prepared[field_name] = _assert_non_empty_text(
            prepared[field_name], field_name=field_name
        )
    prepared["supporting_event_refs"] = _canonicalize_supporting_event_refs(
        list(prepared.get("supporting_event_refs", []))
    )
    prepared["limitations"] = _sorted_unique_texts(
        list(prepared.get("limitations", [])),
        field_name="limitations",
    )
    prepared.setdefault("benchmark_output_epistemic_posture", "inferred_interpretively")
    return prepared


def compute_procedural_depth_instance_id(payload: dict[str, Any]) -> str:
    prepared = _canonicalize_instance_material(payload)
    material = {
        "benchmark_projection_spec_ref": prepared.get("benchmark_projection_spec_ref"),
        "benchmark_execution_context_ref": prepared.get(
            "benchmark_execution_context_ref"
        ),
        "instance_label": prepared.get("instance_label"),
        "repo_snapshot_ref": prepared.get("repo_snapshot_ref"),
        "reference_chain_key": prepared.get("reference_chain_key"),
        "top_level_plan_spine": prepared.get("top_level_plan_spine"),
        "step_specs": prepared.get("step_specs"),
        "expected_terminal_posture": prepared.get("expected_terminal_posture"),
        "gold_trace_derivation_posture": prepared.get("gold_trace_derivation_posture"),
        "notes": prepared.get("notes"),
    }
    return f"pdepthinst_{sha256_canonical_json(material)[:32]}"


def compute_procedural_depth_gold_trace_id(payload: dict[str, Any]) -> str:
    prepared = _canonicalize_procedural_depth_gold_trace_material(payload)
    material = {
        "procedural_depth_instance_ref": prepared.get("procedural_depth_instance_ref"),
        "gold_events": prepared.get("gold_events"),
        "terminal_trace_status": prepared.get("terminal_trace_status"),
        "derivation_notes": prepared.get("derivation_notes"),
    }
    return f"pdepthgold_{sha256_canonical_json(material)[:32]}"


def compute_procedural_depth_run_trace_id(payload: dict[str, Any]) -> str:
    prepared = _canonicalize_procedural_depth_run_trace_material(payload)
    material = {
        "procedural_depth_instance_ref": prepared.get("procedural_depth_instance_ref"),
        "observed_events": prepared.get("observed_events"),
        "terminal_trace_status": prepared.get("terminal_trace_status"),
        "observed_output_summary": prepared.get("observed_output_summary"),
        "trace_notes": prepared.get("trace_notes"),
    }
    return f"pdepthrun_{sha256_canonical_json(material)[:32]}"


def compute_procedural_depth_metrics_id(payload: dict[str, Any]) -> str:
    prepared = _canonicalize_procedural_depth_metrics_material(payload)
    material = {
        "procedural_depth_run_trace_ref": prepared.get("procedural_depth_run_trace_ref"),
        "procedural_depth_gold_trace_ref": prepared.get(
            "procedural_depth_gold_trace_ref"
        ),
        "plan_spine_fidelity": prepared.get("plan_spine_fidelity"),
        "active_step_compilation_fidelity": prepared.get(
            "active_step_compilation_fidelity"
        ),
        "reintegration_fidelity": prepared.get("reintegration_fidelity"),
        "dominant_failure_family": prepared.get("dominant_failure_family"),
        "supporting_event_refs": prepared.get("supporting_event_refs"),
        "scoring_notes": prepared.get("scoring_notes"),
    }
    return f"pdepthmetrics_{sha256_canonical_json(material)[:32]}"


def compute_procedural_depth_diagnostic_report_id(payload: dict[str, Any]) -> str:
    prepared = _canonicalize_procedural_depth_diagnostic_report_material(payload)
    material = {
        "procedural_depth_run_trace_ref": prepared.get("procedural_depth_run_trace_ref"),
        "procedural_depth_metrics_ref": prepared.get("procedural_depth_metrics_ref"),
        "dominant_failure_family": prepared.get("dominant_failure_family"),
        "supporting_event_refs": prepared.get("supporting_event_refs"),
        "benchmark_output_epistemic_posture": prepared.get(
            "benchmark_output_epistemic_posture"
        ),
        "limitations": prepared.get("limitations"),
        "diagnostic_summary": prepared.get("diagnostic_summary"),
    }
    return f"pdepthdiag_{sha256_canonical_json(material)[:32]}"


class BenchmarkFamilySpec(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_BENCHMARK_FAMILY_SPEC_SCHEMA] = Field(
        default=ADEU_BENCHMARK_FAMILY_SPEC_SCHEMA,
        alias="schema",
    )
    benchmark_family_spec_id: str
    family_key: str
    family_label: str
    doctrinal_source_refs: list[str] = Field(min_length=1)
    capability_axes: list[str] = Field(min_length=1)
    baseline_regime_summary: str
    perturbation_axis_posture: str
    reliability_policy_summary: str
    non_regression_policy_summary: str
    subject_under_test_classes: list[SubjectUnderTestClass] = Field(min_length=1)
    benchmark_output_epistemic_postures: list[BenchmarkOutputEpistemicPosture] = Field(
        min_length=1
    )
    diagnostic_posture: DiagnosticPosture
    implementation_posture: ImplementationPosture

    @model_validator(mode="after")
    def _validate_model(self) -> "BenchmarkFamilySpec":
        for field_name in (
            "benchmark_family_spec_id",
            "family_key",
            "family_label",
            "baseline_regime_summary",
            "perturbation_axis_posture",
            "reliability_policy_summary",
            "non_regression_policy_summary",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "doctrinal_source_refs",
            _sorted_unique_texts(
                self.doctrinal_source_refs,
                field_name="doctrinal_source_refs",
            ),
        )
        object.__setattr__(
            self,
            "capability_axes",
            _sorted_unique_texts(self.capability_axes, field_name="capability_axes"),
        )
        object.__setattr__(
            self,
            "subject_under_test_classes",
            _exact_ordered_vocabulary(
                list(self.subject_under_test_classes),
                expected_order=SUBJECT_UNDER_TEST_CLASS_VOCABULARY,
                field_name="subject_under_test_classes",
            ),
        )
        object.__setattr__(
            self,
            "benchmark_output_epistemic_postures",
            _exact_ordered_vocabulary(
                list(self.benchmark_output_epistemic_postures),
                expected_order=BENCHMARK_OUTPUT_EPISTEMIC_POSTURE_VOCABULARY,
                field_name="benchmark_output_epistemic_postures",
            ),
        )
        expected_id = compute_benchmark_family_spec_id(_canonical_model_payload(self))
        if self.benchmark_family_spec_id != expected_id:
            raise ValueError(
                "benchmark_family_spec_id must match canonical family spec identity"
            )
        return self


class BenchmarkProjectionSpec(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_BENCHMARK_PROJECTION_SPEC_SCHEMA] = Field(
        default=ADEU_BENCHMARK_PROJECTION_SPEC_SCHEMA,
        alias="schema",
    )
    benchmark_projection_spec_id: str
    benchmark_family_spec_ref: str
    projection_key: str
    projection_label: str
    constraint_source_refs: list[str] = Field(min_length=1)
    target_capability_axes: list[str] = Field(min_length=1)
    target_subject_under_test_classes: list[SubjectUnderTestClass] = Field(min_length=1)
    hierarchical_trace_required: bool
    explicit_reintegration_trace_required: bool
    projection_validity_posture: str
    interpretation_boundary_summary: str
    declared_instance_contract_id: str
    declared_gold_trace_contract_id: str
    declared_run_trace_contract_id: str
    declared_metrics_contract_id: str
    declared_diagnostic_report_contract_id: str
    projection_notes: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_model(self) -> "BenchmarkProjectionSpec":
        for field_name in (
            "benchmark_projection_spec_id",
            "benchmark_family_spec_ref",
            "projection_key",
            "projection_label",
            "projection_validity_posture",
            "interpretation_boundary_summary",
            "declared_instance_contract_id",
            "declared_gold_trace_contract_id",
            "declared_run_trace_contract_id",
            "declared_metrics_contract_id",
            "declared_diagnostic_report_contract_id",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "constraint_source_refs",
            _sorted_unique_texts(
                self.constraint_source_refs,
                field_name="constraint_source_refs",
            ),
        )
        object.__setattr__(
            self,
            "target_capability_axes",
            _sorted_unique_texts(
                self.target_capability_axes,
                field_name="target_capability_axes",
            ),
        )
        object.__setattr__(
            self,
            "target_subject_under_test_classes",
            _ordered_subset(
                list(self.target_subject_under_test_classes),
                allowed_order=SUBJECT_UNDER_TEST_CLASS_VOCABULARY,
                field_name="target_subject_under_test_classes",
            ),
        )
        object.__setattr__(
            self,
            "projection_notes",
            _sorted_unique_texts(
                self.projection_notes,
                field_name="projection_notes",
            ),
        )
        if (
            self.explicit_reintegration_trace_required
            and not self.hierarchical_trace_required
        ):
            raise ValueError(
                "explicit_reintegration_trace_required requires hierarchical_trace_required"
            )
        expected_id = compute_benchmark_projection_spec_id(_canonical_model_payload(self))
        if self.benchmark_projection_spec_id != expected_id:
            raise ValueError(
                "benchmark_projection_spec_id must match canonical projection identity"
            )
        return self


class BenchmarkExecutionContext(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_BENCHMARK_EXECUTION_CONTEXT_SCHEMA] = Field(
        default=ADEU_BENCHMARK_EXECUTION_CONTEXT_SCHEMA,
        alias="schema",
    )
    benchmark_execution_context_id: str
    subject_under_test_class: SubjectUnderTestClass
    subject_label: str
    subject_version: str
    prompt_wrapper_ref: str | None = None
    tool_availability: list[str] = Field(min_length=1)
    context_budget_posture: ContextBudgetPosture
    determinism_posture: DeterminismPosture
    repo_snapshot_ref: str
    orchestration_topology_ref: str | None = None
    notes: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_model(self) -> "BenchmarkExecutionContext":
        for field_name in (
            "benchmark_execution_context_id",
            "subject_label",
            "subject_version",
            "repo_snapshot_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        if self.prompt_wrapper_ref is not None:
            object.__setattr__(
                self,
                "prompt_wrapper_ref",
                _assert_non_empty_text(
                    self.prompt_wrapper_ref,
                    field_name="prompt_wrapper_ref",
                ),
            )
        if self.orchestration_topology_ref is not None:
            object.__setattr__(
                self,
                "orchestration_topology_ref",
                _assert_non_empty_text(
                    self.orchestration_topology_ref,
                    field_name="orchestration_topology_ref",
                ),
            )
        object.__setattr__(
            self,
            "tool_availability",
            _sorted_unique_texts(
                self.tool_availability,
                field_name="tool_availability",
            ),
        )
        object.__setattr__(
            self,
            "notes",
            _sorted_unique_texts(self.notes, field_name="notes"),
        )
        expected_id = compute_benchmark_execution_context_id(_canonical_model_payload(self))
        if self.benchmark_execution_context_id != expected_id:
            raise ValueError(
                "benchmark_execution_context_id must match canonical execution context identity"
            )
        return self


class BenchmarkValidationCaseResult(BaseModel):
    model_config = MODEL_CONFIG

    validation_case_result_id: str
    case_label: str
    case_ref: str
    expected_dominant_failure_family: DominantFailureFamily
    observed_dominant_failure_family: DominantFailureFamily
    match: bool

    @model_validator(mode="after")
    def _validate_model(self) -> "BenchmarkValidationCaseResult":
        for field_name in (
            "validation_case_result_id",
            "case_label",
            "case_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        expected_match = (
            self.expected_dominant_failure_family
            == self.observed_dominant_failure_family
        )
        if self.match != expected_match:
            raise ValueError(
                "match must equal equality of expected and observed dominant failure family"
            )
        expected_id = compute_benchmark_validation_case_result_id(
            _canonical_model_payload(self)
        )
        if self.validation_case_result_id != expected_id:
            raise ValueError(
                "validation_case_result_id must match canonical validation case identity"
            )
        return self


class BenchmarkValidationReport(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_BENCHMARK_VALIDATION_REPORT_SCHEMA] = Field(
        default=ADEU_BENCHMARK_VALIDATION_REPORT_SCHEMA,
        alias="schema",
    )
    benchmark_validation_report_id: str
    benchmark_projection_spec_ref: str
    validation_label: str
    validation_scope: ValidationScope
    scorer_determinism_posture: ScorerDeterminismPosture
    validation_case_results: list[BenchmarkValidationCaseResult] = Field(min_length=1)
    all_expected_diagnostics_matched: bool
    benchmark_limitations: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_model(self) -> "BenchmarkValidationReport":
        for field_name in (
            "benchmark_validation_report_id",
            "benchmark_projection_spec_ref",
            "validation_label",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        ordered_cases = sorted(
            self.validation_case_results,
            key=lambda item: item.case_label,
        )
        case_labels = [item.case_label for item in ordered_cases]
        if len(case_labels) != len(set(case_labels)):
            raise ValueError("validation_case_results case_label values must be unique")
        object.__setattr__(self, "validation_case_results", ordered_cases)
        object.__setattr__(
            self,
            "benchmark_limitations",
            _sorted_unique_texts(
                self.benchmark_limitations,
                field_name="benchmark_limitations",
            ),
        )
        expected_all_matched = all(item.match for item in self.validation_case_results)
        if self.all_expected_diagnostics_matched != expected_all_matched:
            raise ValueError(
                "all_expected_diagnostics_matched must equal conjunction of case matches"
            )
        expected_id = compute_benchmark_validation_report_id(
            _canonical_model_payload(self)
        )
        if self.benchmark_validation_report_id != expected_id:
            raise ValueError(
                "benchmark_validation_report_id must match canonical validation report identity"
            )
        return self


class ProceduralDepthStepSpec(BaseModel):
    model_config = MODEL_CONFIG

    step_ref: str
    step_role: StepRole
    step_label: str
    order_index: int = Field(ge=0)
    parent_step_ref: str | None = None
    required_child_step_refs: list[str] = Field(default_factory=list)
    return_target_step_ref: str | None = None

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthStepSpec":
        for field_name in ("step_ref", "step_label"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "required_child_step_refs",
            _ordered_unique_texts(
                self.required_child_step_refs,
                field_name="required_child_step_refs",
            ),
        )
        if self.parent_step_ref is not None:
            object.__setattr__(
                self,
                "parent_step_ref",
                _assert_non_empty_text(
                    self.parent_step_ref,
                    field_name="parent_step_ref",
                ),
            )
        if self.return_target_step_ref is not None:
            object.__setattr__(
                self,
                "return_target_step_ref",
                _assert_non_empty_text(
                    self.return_target_step_ref,
                    field_name="return_target_step_ref",
                ),
            )
        if self.step_role == "child":
            if self.parent_step_ref is None:
                raise ValueError("child step must declare parent_step_ref")
            if self.return_target_step_ref != self.parent_step_ref:
                raise ValueError(
                    "child step return_target_step_ref must equal parent_step_ref"
                )
            if self.required_child_step_refs:
                raise ValueError("child step may not declare required_child_step_refs")
        else:
            if self.parent_step_ref is not None:
                raise ValueError("non-child step may not declare parent_step_ref")
            if self.return_target_step_ref is not None:
                raise ValueError("non-child step may not declare return_target_step_ref")
        if self.step_role == "top_level" and self.required_child_step_refs:
            raise ValueError("top_level step may not declare required_child_step_refs")
        if self.step_role == "active_parent" and not self.required_child_step_refs:
            raise ValueError("active_parent step must declare required_child_step_refs")
        return self


class ProceduralDepthTraceEvent(BaseModel):
    model_config = MODEL_CONFIG

    event_index: int = Field(ge=0)
    event_kind: EventKind
    step_ref: str
    step_role: StepRole
    parent_step_ref: str | None = None
    return_target_step_ref: str | None = None

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthTraceEvent":
        object.__setattr__(
            self,
            "step_ref",
            _assert_non_empty_text(self.step_ref, field_name="step_ref"),
        )
        if self.parent_step_ref is not None:
            object.__setattr__(
                self,
                "parent_step_ref",
                _assert_non_empty_text(
                    self.parent_step_ref,
                    field_name="parent_step_ref",
                ),
            )
        if self.return_target_step_ref is not None:
            object.__setattr__(
                self,
                "return_target_step_ref",
                _assert_non_empty_text(
                    self.return_target_step_ref,
                    field_name="return_target_step_ref",
                ),
            )
        if self.step_role == "child":
            if self.parent_step_ref is None:
                raise ValueError("child event must declare parent_step_ref")
        elif self.parent_step_ref is not None:
            raise ValueError("non-child event may not declare parent_step_ref")
        if self.event_kind == "return":
            if self.step_role != "child":
                raise ValueError("return event must target a child step")
            if self.return_target_step_ref is None:
                raise ValueError("return event must declare return_target_step_ref")
        elif self.return_target_step_ref is not None:
            raise ValueError("non-return event may not declare return_target_step_ref")
        return self


class ProceduralDepthSupportingEventRef(BaseModel):
    model_config = MODEL_CONFIG

    trace_role: TraceRole
    trace_ref: str
    event_index: int = Field(ge=0)

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthSupportingEventRef":
        object.__setattr__(
            self,
            "trace_ref",
            _assert_non_empty_text(self.trace_ref, field_name="trace_ref"),
        )
        return self


class ProceduralDepthInstance(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_PROCEDURAL_DEPTH_INSTANCE_SCHEMA] = Field(
        default=ADEU_PROCEDURAL_DEPTH_INSTANCE_SCHEMA,
        alias="schema",
    )
    procedural_depth_instance_id: str
    benchmark_projection_spec_ref: str
    benchmark_execution_context_ref: str
    instance_label: str
    repo_snapshot_ref: str
    reference_chain_key: ReferenceChainKey
    top_level_plan_spine: list[str] = Field(min_length=1)
    step_specs: list[ProceduralDepthStepSpec] = Field(min_length=1)
    expected_terminal_posture: ExpectedTerminalPosture
    gold_trace_derivation_posture: Literal["deterministically_derived_from_instance"]
    notes: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthInstance":
        for field_name in (
            "procedural_depth_instance_id",
            "benchmark_projection_spec_ref",
            "benchmark_execution_context_ref",
            "instance_label",
            "repo_snapshot_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "top_level_plan_spine",
            _ordered_unique_texts(
                self.top_level_plan_spine,
                field_name="top_level_plan_spine",
            ),
        )
        object.__setattr__(self, "notes", _sorted_unique_texts(self.notes, field_name="notes"))
        step_map = _procedural_step_map(self.step_specs)
        if len(step_map) != len(self.step_specs):
            raise ValueError("step_specs step_ref values must be unique")
        children_by_parent = _procedural_children_by_parent(self.step_specs)
        root_steps = children_by_parent.get(None, [])
        root_refs = [step.step_ref for step in root_steps]
        if self.top_level_plan_spine != root_refs:
            raise ValueError(
                "top_level_plan_spine must match canonical ordered root step sequence"
            )
        if self.reference_chain_key != "hierarchical_3x3":
            raise ValueError("reference_chain_key must equal hierarchical_3x3")
        if len(root_steps) != 3 or len(self.top_level_plan_spine) != 3:
            raise ValueError("hierarchical_3x3 requires exactly three top-level steps")
        active_parents = [step for step in root_steps if step.step_role == "active_parent"]
        if len(active_parents) != 1:
            raise ValueError("hierarchical_3x3 requires exactly one active_parent root step")
        active_parent = active_parents[0]
        top_level_steps = [step for step in root_steps if step.step_role == "top_level"]
        if len(top_level_steps) != 2:
            raise ValueError("hierarchical_3x3 requires exactly two top_level root steps")
        child_steps = children_by_parent.get(active_parent.step_ref, [])
        if len(child_steps) != 3:
            raise ValueError("hierarchical_3x3 requires exactly three child steps")
        child_refs = [step.step_ref for step in child_steps]
        if active_parent.required_child_step_refs != child_refs:
            raise ValueError(
                "active_parent required_child_step_refs must match canonical child order"
            )
        for step in child_steps:
            if step.step_role != "child":
                raise ValueError("active_parent descendants must all carry child step_role")
            if step.parent_step_ref != active_parent.step_ref:
                raise ValueError("child parent_step_ref must equal active_parent step_ref")
            if step.return_target_step_ref != active_parent.step_ref:
                raise ValueError(
                    "child return_target_step_ref must equal active_parent step_ref"
                )
        for step in top_level_steps:
            if step.required_child_step_refs:
                raise ValueError("top_level root steps may not declare child refs")
        other_children = {
            parent_ref: entries
            for parent_ref, entries in children_by_parent.items()
            if parent_ref not in (None, active_parent.step_ref)
        }
        if any(other_children.values()):
            raise ValueError("hierarchical_3x3 forbids deeper nested descendants")
        canonical_order = _procedural_canonical_step_order(
            self.top_level_plan_spine,
            children_by_parent,
        )
        object.__setattr__(self, "step_specs", [step_map[step_ref] for step_ref in canonical_order])
        expected_id = compute_procedural_depth_instance_id(_canonical_model_payload(self))
        if self.procedural_depth_instance_id != expected_id:
            raise ValueError(
                "procedural_depth_instance_id must match canonical instance identity"
            )
        return self


class ProceduralDepthGoldTrace(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_PROCEDURAL_DEPTH_GOLD_TRACE_SCHEMA] = Field(
        default=ADEU_PROCEDURAL_DEPTH_GOLD_TRACE_SCHEMA,
        alias="schema",
    )
    procedural_depth_gold_trace_id: str
    procedural_depth_instance_ref: str
    gold_events: list[ProceduralDepthTraceEvent] = Field(min_length=1)
    terminal_trace_status: ProceduralDepthTerminalTraceStatus
    derivation_notes: list[str] = Field(default_factory=list)

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
        object.__setattr__(
            self,
            "gold_events",
            _assert_contiguous_event_indexes(self.gold_events, field_name="gold_events"),
        )
        object.__setattr__(
            self,
            "derivation_notes",
            _sorted_unique_texts(self.derivation_notes, field_name="derivation_notes"),
        )
        if self.terminal_trace_status != "completed_clean":
            raise ValueError("gold trace terminal_trace_status must equal completed_clean")
        expected_id = compute_procedural_depth_gold_trace_id(_canonical_model_payload(self))
        if self.procedural_depth_gold_trace_id != expected_id:
            raise ValueError(
                "procedural_depth_gold_trace_id must match canonical gold trace identity"
            )
        return self


class ProceduralDepthRunTrace(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_PROCEDURAL_DEPTH_RUN_TRACE_SCHEMA] = Field(
        default=ADEU_PROCEDURAL_DEPTH_RUN_TRACE_SCHEMA,
        alias="schema",
    )
    procedural_depth_run_trace_id: str
    procedural_depth_instance_ref: str
    observed_events: list[ProceduralDepthTraceEvent] = Field(min_length=1)
    terminal_trace_status: ProceduralDepthTerminalTraceStatus
    observed_output_summary: str
    trace_notes: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthRunTrace":
        for field_name in (
            "procedural_depth_run_trace_id",
            "procedural_depth_instance_ref",
            "observed_output_summary",
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

    schema_id: Literal[ADEU_PROCEDURAL_DEPTH_METRICS_SCHEMA] = Field(
        default=ADEU_PROCEDURAL_DEPTH_METRICS_SCHEMA,
        alias="schema",
    )
    procedural_depth_metrics_id: str
    procedural_depth_run_trace_ref: str
    procedural_depth_gold_trace_ref: str
    plan_spine_fidelity: bool
    active_step_compilation_fidelity: bool
    reintegration_fidelity: bool
    dominant_failure_family: DominantFailureFamily
    supporting_event_refs: list[ProceduralDepthSupportingEventRef] = Field(min_length=1)
    scoring_notes: list[str] = Field(min_length=1)

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
        ordered_refs = sorted(
            self.supporting_event_refs,
            key=lambda entry: (
                0 if entry.trace_role == "gold" else 1,
                entry.event_index,
                entry.trace_ref,
            ),
        )
        object.__setattr__(self, "supporting_event_refs", ordered_refs)
        object.__setattr__(
            self,
            "scoring_notes",
            _sorted_unique_texts(self.scoring_notes, field_name="scoring_notes"),
        )
        false_axes = [
            not self.plan_spine_fidelity,
            not self.active_step_compilation_fidelity,
            not self.reintegration_fidelity,
        ]
        false_count = sum(false_axes)
        if false_count == 0:
            expected_family: DominantFailureFamily = "clean_success"
        elif false_count >= 2:
            expected_family = "mixed"
        elif not self.plan_spine_fidelity:
            expected_family = "horizontal_plan_spine"
        elif not self.active_step_compilation_fidelity:
            expected_family = "vertical_active_step_compilation"
        else:
            expected_family = "reintegration"
        if self.dominant_failure_family != expected_family:
            raise ValueError(
                "dominant_failure_family must match the starter boolean component-fidelity law"
            )
        expected_id = compute_procedural_depth_metrics_id(_canonical_model_payload(self))
        if self.procedural_depth_metrics_id != expected_id:
            raise ValueError(
                "procedural_depth_metrics_id must match canonical metrics identity"
            )
        return self


class ProceduralDepthDiagnosticReport(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_PROCEDURAL_DEPTH_DIAGNOSTIC_REPORT_SCHEMA] = Field(
        default=ADEU_PROCEDURAL_DEPTH_DIAGNOSTIC_REPORT_SCHEMA,
        alias="schema",
    )
    procedural_depth_diagnostic_report_id: str
    procedural_depth_run_trace_ref: str
    procedural_depth_metrics_ref: str
    dominant_failure_family: DominantFailureFamily
    supporting_event_refs: list[ProceduralDepthSupportingEventRef] = Field(min_length=1)
    benchmark_output_epistemic_posture: ProceduralDepthDiagnosticEpistemicPosture
    limitations: list[str] = Field(min_length=1)
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
        ordered_refs = sorted(
            self.supporting_event_refs,
            key=lambda entry: (
                0 if entry.trace_role == "gold" else 1,
                entry.event_index,
                entry.trace_ref,
            ),
        )
        object.__setattr__(self, "supporting_event_refs", ordered_refs)
        object.__setattr__(
            self,
            "limitations",
            _sorted_unique_texts(self.limitations, field_name="limitations"),
        )
        expected_id = compute_procedural_depth_diagnostic_report_id(
            _canonical_model_payload(self)
        )
        if self.procedural_depth_diagnostic_report_id != expected_id:
            raise ValueError(
                "procedural_depth_diagnostic_report_id must match canonical diagnostic identity"
            )
        return self


def materialize_benchmark_family_spec_payload(payload: dict[str, Any]) -> dict[str, Any]:
    prepared = _prepare_payload(
        payload,
        id_field="benchmark_family_spec_id",
        compute_id=compute_benchmark_family_spec_id,
    )
    return _canonical_model_payload(BenchmarkFamilySpec.model_validate(prepared))


def canonicalize_benchmark_family_spec_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return _canonical_model_payload(BenchmarkFamilySpec.model_validate(payload))


def materialize_benchmark_projection_spec_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = _prepare_payload(
        payload,
        id_field="benchmark_projection_spec_id",
        compute_id=compute_benchmark_projection_spec_id,
    )
    return _canonical_model_payload(BenchmarkProjectionSpec.model_validate(prepared))


def canonicalize_benchmark_projection_spec_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    return _canonical_model_payload(BenchmarkProjectionSpec.model_validate(payload))


def materialize_benchmark_execution_context_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = _prepare_payload(
        payload,
        id_field="benchmark_execution_context_id",
        compute_id=compute_benchmark_execution_context_id,
    )
    return _canonical_model_payload(BenchmarkExecutionContext.model_validate(prepared))


def canonicalize_benchmark_execution_context_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    return _canonical_model_payload(BenchmarkExecutionContext.model_validate(payload))


def materialize_benchmark_validation_report_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = deepcopy(payload)
    case_results: list[dict[str, Any]] = []
    for case_payload in prepared.get("validation_case_results", []):
        case_material = deepcopy(case_payload)
        case_material.setdefault(
            "match",
            case_material.get("expected_dominant_failure_family")
            == case_material.get("observed_dominant_failure_family"),
        )
        case_material.setdefault(
            "validation_case_result_id",
            compute_benchmark_validation_case_result_id(case_material),
        )
        case_results.append(
            _canonical_model_payload(
                BenchmarkValidationCaseResult.model_validate(case_material)
            )
        )
    prepared["validation_case_results"] = case_results
    prepared.setdefault(
        "all_expected_diagnostics_matched",
        all(case["match"] for case in case_results),
    )
    prepared.setdefault(
        "benchmark_validation_report_id",
        compute_benchmark_validation_report_id(prepared),
    )
    return _canonical_model_payload(BenchmarkValidationReport.model_validate(prepared))


def canonicalize_benchmark_validation_report_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    return _canonical_model_payload(BenchmarkValidationReport.model_validate(payload))


def _canonicalize_instance_material(payload: dict[str, Any]) -> dict[str, Any]:
    prepared = deepcopy(payload)
    for field_name in (
        "benchmark_projection_spec_ref",
        "benchmark_execution_context_ref",
        "instance_label",
        "repo_snapshot_ref",
    ):
        prepared[field_name] = _assert_non_empty_text(
            prepared[field_name], field_name=field_name
        )
    prepared["top_level_plan_spine"] = _ordered_unique_texts(
        list(prepared.get("top_level_plan_spine", [])),
        field_name="top_level_plan_spine",
    )
    prepared["notes"] = _sorted_unique_texts(
        list(prepared.get("notes", [])),
        field_name="notes",
    )
    step_specs = [
        ProceduralDepthStepSpec.model_validate(step_payload)
        for step_payload in prepared.get("step_specs", [])
    ]
    if not step_specs:
        raise ValueError("step_specs must not be empty")
    step_map = _procedural_step_map(step_specs)
    if len(step_map) != len(step_specs):
        raise ValueError("step_specs step_ref values must be unique")
    children_by_parent = _procedural_children_by_parent(step_specs)
    root_steps = children_by_parent.get(None, [])
    root_refs = [step.step_ref for step in root_steps]
    if prepared["top_level_plan_spine"] != root_refs:
        raise ValueError("top_level_plan_spine must match canonical ordered root step sequence")
    if prepared.get("reference_chain_key") != "hierarchical_3x3":
        raise ValueError("reference_chain_key must equal hierarchical_3x3")
    if len(root_steps) != 3 or len(prepared["top_level_plan_spine"]) != 3:
        raise ValueError("hierarchical_3x3 requires exactly three top-level steps")
    active_parents = [step for step in root_steps if step.step_role == "active_parent"]
    if len(active_parents) != 1:
        raise ValueError("hierarchical_3x3 requires exactly one active_parent root step")
    active_parent = active_parents[0]
    top_level_steps = [step for step in root_steps if step.step_role == "top_level"]
    if len(top_level_steps) != 2:
        raise ValueError("hierarchical_3x3 requires exactly two top_level root steps")
    child_steps = children_by_parent.get(active_parent.step_ref, [])
    if len(child_steps) != 3:
        raise ValueError("hierarchical_3x3 requires exactly three child steps")
    child_refs = [step.step_ref for step in child_steps]
    if active_parent.required_child_step_refs != child_refs:
        raise ValueError("active_parent required_child_step_refs must match canonical child order")
    for step in child_steps:
        if step.step_role != "child":
            raise ValueError("active_parent descendants must all carry child step_role")
        if step.parent_step_ref != active_parent.step_ref:
            raise ValueError("child parent_step_ref must equal active_parent step_ref")
        if step.return_target_step_ref != active_parent.step_ref:
            raise ValueError("child return_target_step_ref must equal active_parent step_ref")
    for step in top_level_steps:
        if step.required_child_step_refs:
            raise ValueError("top_level root steps may not declare child refs")
    other_children = {
        parent_ref: entries
        for parent_ref, entries in children_by_parent.items()
        if parent_ref not in (None, active_parent.step_ref)
    }
    if any(other_children.values()):
        raise ValueError("hierarchical_3x3 forbids deeper nested descendants")
    prepared["step_specs"] = [
        _canonical_model_payload(step_map[step_ref])
        for step_ref in _procedural_canonical_step_order(
            prepared["top_level_plan_spine"],
            children_by_parent,
        )
    ]
    return prepared


def materialize_procedural_depth_instance_payload(payload: dict[str, Any]) -> dict[str, Any]:
    prepared = _canonicalize_instance_material(payload)
    prepared.setdefault(
        "procedural_depth_instance_id",
        compute_procedural_depth_instance_id(prepared),
    )
    return _canonical_model_payload(ProceduralDepthInstance.model_validate(prepared))


def canonicalize_procedural_depth_instance_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return _canonical_model_payload(ProceduralDepthInstance.model_validate(payload))


def _canonicalize_trace_events(
    payloads: list[dict[str, Any]],
    *,
    field_name: str,
) -> list[dict[str, Any]]:
    events = [ProceduralDepthTraceEvent.model_validate(payload) for payload in payloads]
    events = _assert_contiguous_event_indexes(events, field_name=field_name)
    return [_canonical_model_payload(event) for event in events]


def materialize_procedural_depth_gold_trace_payload(payload: dict[str, Any]) -> dict[str, Any]:
    prepared = _canonicalize_procedural_depth_gold_trace_material(payload)
    prepared.setdefault(
        "procedural_depth_gold_trace_id",
        compute_procedural_depth_gold_trace_id(prepared),
    )
    return _canonical_model_payload(ProceduralDepthGoldTrace.model_validate(prepared))


def canonicalize_procedural_depth_gold_trace_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return _canonical_model_payload(ProceduralDepthGoldTrace.model_validate(payload))


def materialize_procedural_depth_run_trace_payload(payload: dict[str, Any]) -> dict[str, Any]:
    prepared = _canonicalize_procedural_depth_run_trace_material(payload)
    prepared.setdefault(
        "procedural_depth_run_trace_id",
        compute_procedural_depth_run_trace_id(prepared),
    )
    return _canonical_model_payload(ProceduralDepthRunTrace.model_validate(prepared))


def canonicalize_procedural_depth_run_trace_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return _canonical_model_payload(ProceduralDepthRunTrace.model_validate(payload))


def _canonicalize_supporting_event_refs(
    payloads: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    refs = [
        ProceduralDepthSupportingEventRef.model_validate(payload)
        for payload in payloads
    ]
    refs = sorted(
        refs,
        key=lambda entry: (
            0 if entry.trace_role == "gold" else 1,
            entry.event_index,
            entry.trace_ref,
        ),
    )
    return [_canonical_model_payload(entry) for entry in refs]


def materialize_procedural_depth_metrics_payload(payload: dict[str, Any]) -> dict[str, Any]:
    prepared = _canonicalize_procedural_depth_metrics_material(payload)
    prepared.setdefault(
        "procedural_depth_metrics_id",
        compute_procedural_depth_metrics_id(prepared),
    )
    return _canonical_model_payload(ProceduralDepthMetrics.model_validate(prepared))


def canonicalize_procedural_depth_metrics_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return _canonical_model_payload(ProceduralDepthMetrics.model_validate(payload))


def materialize_procedural_depth_diagnostic_report_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = _canonicalize_procedural_depth_diagnostic_report_material(payload)
    prepared.setdefault(
        "procedural_depth_diagnostic_report_id",
        compute_procedural_depth_diagnostic_report_id(prepared),
    )
    return _canonical_model_payload(
        ProceduralDepthDiagnosticReport.model_validate(prepared)
    )


def canonicalize_procedural_depth_diagnostic_report_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    return _canonical_model_payload(
        ProceduralDepthDiagnosticReport.model_validate(payload)
    )


def derive_benchmark_validation_report(
    *,
    benchmark_projection_spec_ref: str,
    validation_label: str,
    case_expectations: list[dict[str, Any]],
    benchmark_limitations: list[str],
) -> dict[str, Any]:
    case_results = [
        {
            "case_label": expectation["case_label"],
            "case_ref": expectation["case_ref"],
            "expected_dominant_failure_family": expectation[
                "expected_dominant_failure_family"
            ],
            "observed_dominant_failure_family": expectation[
                "observed_dominant_failure_family"
            ],
            "match": expectation["expected_dominant_failure_family"]
            == expectation["observed_dominant_failure_family"],
        }
        for expectation in case_expectations
    ]
    return materialize_benchmark_validation_report_payload(
        {
            "benchmark_projection_spec_ref": benchmark_projection_spec_ref,
            "validation_label": validation_label,
            "validation_scope": "tiny_reference_fixture_bundle",
            "scorer_determinism_posture": "deterministic_fixture_replay_confirmed",
            "validation_case_results": case_results,
            "benchmark_limitations": benchmark_limitations,
        }
    )
