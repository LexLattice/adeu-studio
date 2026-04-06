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
ADEU_PROCEDURAL_DEPTH_PERTURBATION_CASE_SCHEMA = "adeu_procedural_depth_perturbation_case@1"
ADEU_PROCEDURAL_DEPTH_FAILURE_TOPOLOGY_SCHEMA = "adeu_procedural_depth_failure_topology@1"
ADEU_PROCEDURAL_DEPTH_NON_REGRESSION_REPORT_SCHEMA = "adeu_procedural_depth_non_regression_report@1"
ADEU_PROCEDURAL_DEPTH_BENCHMARK_VALIDATION_REPORT_SCHEMA = (
    "adeu_procedural_depth_benchmark_validation_report@1"
)
ADEU_BENCHMARK_SUBJECT_RECORD_SCHEMA = "adeu_benchmark_subject_record@1"
ADEU_CROSS_SUBJECT_COMPARISON_CASE_SCHEMA = "adeu_cross_subject_comparison_case@1"
ADEU_CROSS_SUBJECT_COMPARISON_REPORT_SCHEMA = "adeu_cross_subject_comparison_report@1"
ADEU_CROSS_SUBJECT_COMPARISON_VALIDATION_REPORT_SCHEMA = (
    "adeu_cross_subject_comparison_validation_report@1"
)

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
PROCEDURAL_DEPTH_DIAGNOSTIC_EPISTEMIC_POSTURE_VOCABULARY = ["inferred_interpretively"]
PERTURBATION_KIND_VOCABULARY = [
    "branch_shift",
    "delayed_constraint",
    "paraphrase_preserving",
]
EVALUATION_CONTEXT_POSTURE_VOCABULARY = ["deterministic_fixed_context"]
EXECUTION_CONTEXT_COMPATIBILITY_FIELD_VOCABULARY = [
    "repo_snapshot_ref",
    "tool_availability",
    "context_budget_posture",
    "determinism_posture",
]
COMPARISON_SURFACE_VOCABULARY = [
    "baseline_structural_fidelity",
    "perturbation_non_regression",
    "perturbation_validation",
]
COMPARISON_STATUS_VOCABULARY = [
    "comparison_ready_clean",
    "comparison_insufficient",
    "comparison_incompatible",
]
COMPARISON_MATCH_STATUS_VOCABULARY = [
    "exact_match",
    "different_but_comparable",
    "insufficient_evidence",
]
COMPARISON_VALIDATION_STATUS_VOCABULARY = [
    "validation_ready_clean",
    "validation_insufficient",
    "validation_incompatible",
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
PerturbationKind = Literal[
    "branch_shift",
    "delayed_constraint",
    "paraphrase_preserving",
]
EvaluationContextPosture = Literal["deterministic_fixed_context"]
ExecutionContextCompatibilityField = Literal[
    "repo_snapshot_ref",
    "tool_availability",
    "context_budget_posture",
    "determinism_posture",
]
ComparisonSurface = Literal[
    "baseline_structural_fidelity",
    "perturbation_non_regression",
    "perturbation_validation",
]
ComparisonStatus = Literal[
    "comparison_ready_clean",
    "comparison_insufficient",
    "comparison_incompatible",
]
ComparisonMatchStatus = Literal[
    "exact_match",
    "different_but_comparable",
    "insufficient_evidence",
]
ComparisonValidationStatus = Literal[
    "validation_ready_clean",
    "validation_insufficient",
    "validation_incompatible",
]


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


def _ordered_unique_ints(values: list[int], *, field_name: str) -> list[int]:
    if any(not isinstance(value, int) for value in values):
        raise ValueError(f"{field_name} must contain only integers")
    if any(value < 0 for value in values):
        raise ValueError(f"{field_name} must contain only non-negative integers")
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")
    return sorted(values)


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
            "expected_dominant_failure_family": case.get("expected_dominant_failure_family"),
            "observed_dominant_failure_family": case.get("observed_dominant_failure_family"),
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
        "all_expected_diagnostics_matched": payload.get("all_expected_diagnostics_matched"),
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
        prepared[field_name] = _assert_non_empty_text(prepared[field_name], field_name=field_name)
    prepared["supporting_event_refs"] = _canonicalize_supporting_event_refs(
        list(prepared.get("supporting_event_refs", []))
    )
    prepared["limitations"] = _sorted_unique_texts(
        list(prepared.get("limitations", [])),
        field_name="limitations",
    )
    prepared.setdefault("benchmark_output_epistemic_posture", "inferred_interpretively")
    return prepared


def _canonicalize_supporting_replay_refs(
    payloads: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    refs = [ProceduralDepthSupportingReplayRef.model_validate(payload) for payload in payloads]
    refs = sorted(refs, key=lambda entry: entry.replay_index)
    return [_canonical_model_payload(entry) for entry in refs]


def _canonicalize_supporting_metric_refs(
    payloads: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    refs = [ProceduralDepthSupportingMetricRef.model_validate(payload) for payload in payloads]
    refs = sorted(refs, key=lambda entry: entry.replay_index)
    return [_canonical_model_payload(entry) for entry in refs]


def _canonicalize_validation_replay_results(
    payloads: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    refs = [ProceduralDepthValidationReplayResult.model_validate(payload) for payload in payloads]
    refs = sorted(refs, key=lambda entry: entry.replay_index)
    return [_canonical_model_payload(entry) for entry in refs]


def _canonicalize_procedural_depth_perturbation_case_material(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = deepcopy(payload)
    for field_name in ("baseline_instance_ref", "perturbation_label"):
        prepared[field_name] = _assert_non_empty_text(prepared[field_name], field_name=field_name)
    prepared["perturbation_overlay_events"] = _canonicalize_trace_events(
        list(prepared.get("perturbation_overlay_events", [])),
        field_name="perturbation_overlay_events",
    )
    if prepared.get("output_summary_override") is not None:
        prepared["output_summary_override"] = _assert_non_empty_text(
            prepared["output_summary_override"],
            field_name="output_summary_override",
        )
    prepared["notes"] = _sorted_unique_texts(
        list(prepared.get("notes", [])),
        field_name="notes",
    )
    return prepared


def _canonicalize_failure_topology_evaluated_cases(
    payloads: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    rows = [
        _canonical_model_payload(ProceduralDepthFailureTopologyCase.model_validate(payload))
        for payload in payloads
    ]
    return sorted(rows, key=lambda row: row["perturbation_case_ref"])


def _canonicalize_procedural_depth_failure_topology_material(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = deepcopy(payload)
    prepared["evaluated_cases"] = _canonicalize_failure_topology_evaluated_cases(
        list(prepared.get("evaluated_cases", []))
    )
    prepared["topology_summary"] = _assert_non_empty_text(
        prepared["topology_summary"],
        field_name="topology_summary",
    )
    prepared["notes"] = _sorted_unique_texts(
        list(prepared.get("notes", [])),
        field_name="notes",
    )
    return prepared


def _canonicalize_non_regression_evaluated_cases(
    payloads: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    rows = [
        _canonical_model_payload(ProceduralDepthNonRegressionCase.model_validate(payload))
        for payload in payloads
    ]
    return sorted(rows, key=lambda row: row["perturbation_case_ref"])


def _canonicalize_procedural_depth_non_regression_report_material(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = deepcopy(payload)
    prepared["baseline_instance_ref"] = _assert_non_empty_text(
        prepared["baseline_instance_ref"],
        field_name="baseline_instance_ref",
    )
    prepared["evaluated_cases"] = _canonicalize_non_regression_evaluated_cases(
        list(prepared.get("evaluated_cases", []))
    )
    prepared["report_summary"] = _assert_non_empty_text(
        prepared["report_summary"],
        field_name="report_summary",
    )
    prepared["notes"] = _sorted_unique_texts(
        list(prepared.get("notes", [])),
        field_name="notes",
    )
    return prepared


def _canonicalize_benchmark_validation_case_results(
    payloads: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    rows = [
        _canonical_model_payload(
            ProceduralDepthBenchmarkValidationCaseResult.model_validate(payload)
        )
        for payload in payloads
    ]
    return sorted(rows, key=lambda row: row["perturbation_case_ref"])


def _canonicalize_procedural_depth_benchmark_validation_report_material(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = deepcopy(payload)
    prepared["validation_case_results"] = _canonicalize_benchmark_validation_case_results(
        list(prepared.get("validation_case_results", []))
    )
    prepared["limitations"] = _sorted_unique_texts(
        list(prepared.get("limitations", [])),
        field_name="limitations",
    )
    return prepared


def _canonicalize_benchmark_subject_record_material(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = deepcopy(payload)
    for field_name in (
        "subject_label",
        "subject_identity_ref",
        "benchmark_family_spec_ref",
        "benchmark_projection_spec_ref",
        "benchmark_execution_context_ref",
        "perturbation_bundle_ref",
        "baseline_instance_ref",
        "baseline_run_trace_ref",
        "baseline_metric_ref",
        "baseline_diagnostic_report_ref",
        "perturbation_non_regression_report_ref",
        "perturbation_benchmark_validation_report_ref",
    ):
        prepared[field_name] = _assert_non_empty_text(
            prepared[field_name],
            field_name=field_name,
        )
    prepared["perturbation_case_refs"] = _ordered_unique_texts(
        list(prepared.get("perturbation_case_refs", [])),
        field_name="perturbation_case_refs",
    )
    prepared["notes"] = _sorted_unique_texts(
        list(prepared.get("notes", [])),
        field_name="notes",
    )
    return prepared


def _canonicalize_cross_subject_comparison_case_material(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = deepcopy(payload)
    for field_name in (
        "comparison_label",
        "left_subject_ref",
        "right_subject_ref",
        "benchmark_family_spec_ref",
        "benchmark_projection_spec_ref",
        "baseline_instance_ref",
    ):
        prepared[field_name] = _assert_non_empty_text(
            prepared[field_name],
            field_name=field_name,
        )
    prepared["required_execution_context_compatibility_fields"] = _exact_ordered_vocabulary(
        list(prepared.get("required_execution_context_compatibility_fields", [])),
        expected_order=EXECUTION_CONTEXT_COMPATIBILITY_FIELD_VOCABULARY,
        field_name="required_execution_context_compatibility_fields",
    )
    prepared["perturbation_case_refs"] = _ordered_unique_texts(
        list(prepared.get("perturbation_case_refs", [])),
        field_name="perturbation_case_refs",
    )
    prepared["required_comparison_surfaces"] = _exact_ordered_vocabulary(
        list(prepared.get("required_comparison_surfaces", [])),
        expected_order=COMPARISON_SURFACE_VOCABULARY,
        field_name="required_comparison_surfaces",
    )
    prepared["notes"] = _sorted_unique_texts(
        list(prepared.get("notes", [])),
        field_name="notes",
    )
    return prepared


def _canonicalize_subject_summaries(payloads: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows = [
        _canonical_model_payload(CrossSubjectSubjectSummary.model_validate(payload))
        for payload in payloads
    ]
    return sorted(rows, key=lambda row: row["subject_record_ref"])


def _canonicalize_field_comparisons(payloads: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows = [
        _canonical_model_payload(CrossSubjectFieldComparison.model_validate(payload))
        for payload in payloads
    ]
    return sorted(
        rows,
        key=lambda row: (
            COMPARISON_SURFACE_VOCABULARY.index(row["comparison_surface"]),
            row["left_ref"],
            row["right_ref"],
        ),
    )


def _canonicalize_cross_subject_comparison_report_material(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = deepcopy(payload)
    for field_name in (
        "comparison_case_ref",
        "comparison_summary",
    ):
        prepared[field_name] = _assert_non_empty_text(
            prepared[field_name],
            field_name=field_name,
        )
    prepared["subject_summaries"] = _canonicalize_subject_summaries(
        list(prepared.get("subject_summaries", []))
    )
    prepared["field_comparisons"] = _canonicalize_field_comparisons(
        list(prepared.get("field_comparisons", []))
    )
    prepared["supporting_artifact_refs"] = _ordered_unique_texts(
        list(prepared.get("supporting_artifact_refs", [])),
        field_name="supporting_artifact_refs",
    )
    prepared["notes"] = _sorted_unique_texts(
        list(prepared.get("notes", [])),
        field_name="notes",
    )
    return prepared


def _canonicalize_comparison_validation_results(
    payloads: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    rows = [
        _canonical_model_payload(CrossSubjectComparisonValidationResult.model_validate(payload))
        for payload in payloads
    ]
    return sorted(
        rows,
        key=lambda row: (
            COMPARISON_SURFACE_VOCABULARY.index(row["comparison_surface"]),
            row["left_ref"],
            row["right_ref"],
        ),
    )


def _canonicalize_cross_subject_comparison_validation_report_material(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = deepcopy(payload)
    prepared["comparison_case_ref"] = _assert_non_empty_text(
        prepared["comparison_case_ref"],
        field_name="comparison_case_ref",
    )
    prepared["validation_results"] = _canonicalize_comparison_validation_results(
        list(prepared.get("validation_results", []))
    )
    prepared["limitations"] = _sorted_unique_texts(
        list(prepared.get("limitations", [])),
        field_name="limitations",
    )
    return prepared


def compute_procedural_depth_instance_id(payload: dict[str, Any]) -> str:
    prepared = _canonicalize_instance_material(payload)
    material = {
        "benchmark_projection_spec_ref": prepared.get("benchmark_projection_spec_ref"),
        "benchmark_execution_context_ref": prepared.get("benchmark_execution_context_ref"),
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
        "procedural_depth_gold_trace_ref": prepared.get("procedural_depth_gold_trace_ref"),
        "plan_spine_fidelity": prepared.get("plan_spine_fidelity"),
        "active_step_compilation_fidelity": prepared.get("active_step_compilation_fidelity"),
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
        "benchmark_output_epistemic_posture": prepared.get("benchmark_output_epistemic_posture"),
        "limitations": prepared.get("limitations"),
        "diagnostic_summary": prepared.get("diagnostic_summary"),
    }
    return f"pdepthdiag_{sha256_canonical_json(material)[:32]}"


def compute_procedural_depth_perturbation_case_id(payload: dict[str, Any]) -> str:
    prepared = _canonicalize_procedural_depth_perturbation_case_material(payload)
    material = {
        "baseline_instance_ref": prepared.get("baseline_instance_ref"),
        "perturbation_kind": prepared.get("perturbation_kind"),
        "perturbation_label": prepared.get("perturbation_label"),
        "perturbation_overlay_events": prepared.get("perturbation_overlay_events"),
        "output_summary_override": prepared.get("output_summary_override"),
        "expected_dominant_failure_family": prepared.get("expected_dominant_failure_family"),
        "expected_terminal_trace_status": prepared.get("expected_terminal_trace_status"),
        "notes": prepared.get("notes"),
    }
    return f"pdepthpert_{sha256_canonical_json(material)[:32]}"


def compute_procedural_depth_failure_topology_id(payload: dict[str, Any]) -> str:
    prepared = _canonicalize_procedural_depth_failure_topology_material(payload)
    material = {
        "evaluated_cases": prepared.get("evaluated_cases"),
        "topology_summary": prepared.get("topology_summary"),
        "notes": prepared.get("notes"),
    }
    return f"pdepthtopo_{sha256_canonical_json(material)[:32]}"


def compute_procedural_depth_non_regression_report_id(payload: dict[str, Any]) -> str:
    prepared = _canonicalize_procedural_depth_non_regression_report_material(payload)
    material = {
        "baseline_instance_ref": prepared.get("baseline_instance_ref"),
        "evaluation_context_posture": prepared.get("evaluation_context_posture"),
        "replay_count": prepared.get("replay_count"),
        "regression_detected": prepared.get("regression_detected"),
        "evaluated_cases": prepared.get("evaluated_cases"),
        "report_summary": prepared.get("report_summary"),
        "notes": prepared.get("notes"),
    }
    return f"pdepthnreg_{sha256_canonical_json(material)[:32]}"


def compute_procedural_depth_benchmark_validation_report_id(
    payload: dict[str, Any],
) -> str:
    prepared = _canonicalize_procedural_depth_benchmark_validation_report_material(payload)
    material = {
        "evaluation_context_posture": prepared.get("evaluation_context_posture"),
        "replay_count": prepared.get("replay_count"),
        "deterministic_replay_confirmed": prepared.get("deterministic_replay_confirmed"),
        "validation_case_results": prepared.get("validation_case_results"),
        "limitations": prepared.get("limitations"),
    }
    return f"pdepthbval_{sha256_canonical_json(material)[:32]}"


def compute_procedural_depth_perturbation_bundle_ref(
    *,
    baseline_instance_ref: str,
    perturbation_case_refs: list[str],
) -> str:
    material = {
        "baseline_instance_ref": _assert_non_empty_text(
            baseline_instance_ref,
            field_name="baseline_instance_ref",
        ),
        "perturbation_case_refs": _ordered_unique_texts(
            list(perturbation_case_refs),
            field_name="perturbation_case_refs",
        ),
    }
    return f"pdepthbundle_{sha256_canonical_json(material)[:32]}"


def compute_benchmark_subject_record_id(payload: dict[str, Any]) -> str:
    prepared = _canonicalize_benchmark_subject_record_material(payload)
    material = {
        "subject_class": prepared.get("subject_class"),
        "subject_label": prepared.get("subject_label"),
        "subject_identity_ref": prepared.get("subject_identity_ref"),
        "benchmark_family_spec_ref": prepared.get("benchmark_family_spec_ref"),
        "benchmark_projection_spec_ref": prepared.get("benchmark_projection_spec_ref"),
        "benchmark_execution_context_ref": prepared.get("benchmark_execution_context_ref"),
        "perturbation_bundle_ref": prepared.get("perturbation_bundle_ref"),
        "perturbation_case_refs": prepared.get("perturbation_case_refs"),
        "baseline_instance_ref": prepared.get("baseline_instance_ref"),
        "baseline_run_trace_ref": prepared.get("baseline_run_trace_ref"),
        "baseline_metric_ref": prepared.get("baseline_metric_ref"),
        "baseline_diagnostic_report_ref": prepared.get("baseline_diagnostic_report_ref"),
        "perturbation_non_regression_report_ref": prepared.get(
            "perturbation_non_regression_report_ref"
        ),
        "perturbation_benchmark_validation_report_ref": prepared.get(
            "perturbation_benchmark_validation_report_ref"
        ),
        "notes": prepared.get("notes"),
    }
    return f"benchsubj_{sha256_canonical_json(material)[:32]}"


def compute_cross_subject_comparison_case_id(payload: dict[str, Any]) -> str:
    prepared = _canonicalize_cross_subject_comparison_case_material(payload)
    material = {
        "comparison_label": prepared.get("comparison_label"),
        "left_subject_ref": prepared.get("left_subject_ref"),
        "right_subject_ref": prepared.get("right_subject_ref"),
        "benchmark_family_spec_ref": prepared.get("benchmark_family_spec_ref"),
        "benchmark_projection_spec_ref": prepared.get("benchmark_projection_spec_ref"),
        "baseline_instance_ref": prepared.get("baseline_instance_ref"),
        "required_execution_context_compatibility_fields": prepared.get(
            "required_execution_context_compatibility_fields"
        ),
        "perturbation_case_refs": prepared.get("perturbation_case_refs"),
        "required_comparison_surfaces": prepared.get("required_comparison_surfaces"),
        "notes": prepared.get("notes"),
    }
    return f"xsubcase_{sha256_canonical_json(material)[:32]}"


def compute_cross_subject_comparison_report_id(payload: dict[str, Any]) -> str:
    prepared = _canonicalize_cross_subject_comparison_report_material(payload)
    material = {
        "comparison_case_ref": prepared.get("comparison_case_ref"),
        "comparison_status": prepared.get("comparison_status"),
        "subject_summaries": prepared.get("subject_summaries"),
        "field_comparisons": prepared.get("field_comparisons"),
        "supporting_artifact_refs": prepared.get("supporting_artifact_refs"),
        "comparison_summary": prepared.get("comparison_summary"),
        "notes": prepared.get("notes"),
    }
    return f"xsubreport_{sha256_canonical_json(material)[:32]}"


def compute_cross_subject_comparison_validation_report_id(
    payload: dict[str, Any],
) -> str:
    prepared = _canonicalize_cross_subject_comparison_validation_report_material(payload)
    material = {
        "comparison_case_ref": prepared.get("comparison_case_ref"),
        "deterministic_comparison_confirmed": prepared.get("deterministic_comparison_confirmed"),
        "validation_status": prepared.get("validation_status"),
        "validation_results": prepared.get("validation_results"),
        "limitations": prepared.get("limitations"),
    }
    return f"xsubvalid_{sha256_canonical_json(material)[:32]}"


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
    benchmark_output_epistemic_postures: list[BenchmarkOutputEpistemicPosture] = Field(min_length=1)
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
            raise ValueError("benchmark_family_spec_id must match canonical family spec identity")
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
        if self.explicit_reintegration_trace_required and not self.hierarchical_trace_required:
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
            self.expected_dominant_failure_family == self.observed_dominant_failure_family
        )
        if self.match != expected_match:
            raise ValueError(
                "match must equal equality of expected and observed dominant failure family"
            )
        expected_id = compute_benchmark_validation_case_result_id(_canonical_model_payload(self))
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
        expected_id = compute_benchmark_validation_report_id(_canonical_model_payload(self))
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
                raise ValueError("child step return_target_step_ref must equal parent_step_ref")
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
            raise ValueError("top_level_plan_spine must match canonical ordered root step sequence")
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
        canonical_order = _procedural_canonical_step_order(
            self.top_level_plan_spine,
            children_by_parent,
        )
        object.__setattr__(self, "step_specs", [step_map[step_ref] for step_ref in canonical_order])
        expected_id = compute_procedural_depth_instance_id(_canonical_model_payload(self))
        if self.procedural_depth_instance_id != expected_id:
            raise ValueError("procedural_depth_instance_id must match canonical instance identity")
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
            raise ValueError("procedural_depth_metrics_id must match canonical metrics identity")
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
        expected_id = compute_procedural_depth_diagnostic_report_id(_canonical_model_payload(self))
        if self.procedural_depth_diagnostic_report_id != expected_id:
            raise ValueError(
                "procedural_depth_diagnostic_report_id must match canonical diagnostic identity"
            )
        return self


class ProceduralDepthPerturbationCase(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_PROCEDURAL_DEPTH_PERTURBATION_CASE_SCHEMA] = Field(
        default=ADEU_PROCEDURAL_DEPTH_PERTURBATION_CASE_SCHEMA,
        alias="schema",
    )
    procedural_depth_perturbation_case_id: str
    baseline_instance_ref: str
    perturbation_kind: PerturbationKind
    perturbation_label: str
    perturbation_overlay_events: list[ProceduralDepthTraceEvent] = Field(min_length=1)
    output_summary_override: str | None = None
    expected_dominant_failure_family: DominantFailureFamily
    expected_terminal_trace_status: ProceduralDepthTerminalTraceStatus
    notes: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthPerturbationCase":
        for field_name in (
            "procedural_depth_perturbation_case_id",
            "baseline_instance_ref",
            "perturbation_label",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "perturbation_overlay_events",
            _assert_contiguous_event_indexes(
                self.perturbation_overlay_events,
                field_name="perturbation_overlay_events",
            ),
        )
        if self.output_summary_override is not None:
            object.__setattr__(
                self,
                "output_summary_override",
                _assert_non_empty_text(
                    self.output_summary_override,
                    field_name="output_summary_override",
                ),
            )
        if self.perturbation_kind == "paraphrase_preserving":
            if self.output_summary_override is None:
                raise ValueError(
                    "paraphrase_preserving perturbation must declare output_summary_override"
                )
        elif self.output_summary_override is not None:
            raise ValueError(
                "output_summary_override is only allowed for paraphrase_preserving perturbations"
            )
        if self.expected_dominant_failure_family == "clean_success":
            if self.expected_terminal_trace_status != "completed_clean":
                raise ValueError("clean_success perturbation cases must expect completed_clean")
        elif self.expected_terminal_trace_status != "completed_with_structural_break":
            raise ValueError(
                "starter structural-break perturbation cases must expect "
                "completed_with_structural_break"
            )
        object.__setattr__(self, "notes", _sorted_unique_texts(self.notes, field_name="notes"))
        expected_id = compute_procedural_depth_perturbation_case_id(_canonical_model_payload(self))
        if self.procedural_depth_perturbation_case_id != expected_id:
            raise ValueError(
                "procedural_depth_perturbation_case_id must match canonical perturbation identity"
            )
        return self


class ProceduralDepthSupportingReplayRef(BaseModel):
    model_config = MODEL_CONFIG

    replay_index: int = Field(ge=0)
    run_trace_ref: str

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthSupportingReplayRef":
        object.__setattr__(
            self,
            "run_trace_ref",
            _assert_non_empty_text(self.run_trace_ref, field_name="run_trace_ref"),
        )
        return self


class ProceduralDepthFailureTopologyCase(BaseModel):
    model_config = MODEL_CONFIG

    perturbation_case_ref: str
    observed_dominant_failure_family: DominantFailureFamily
    supporting_replay_refs: list[ProceduralDepthSupportingReplayRef] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthFailureTopologyCase":
        object.__setattr__(
            self,
            "perturbation_case_ref",
            _assert_non_empty_text(
                self.perturbation_case_ref,
                field_name="perturbation_case_ref",
            ),
        )
        replay_indexes = [entry.replay_index for entry in self.supporting_replay_refs]
        _ordered_unique_ints(replay_indexes, field_name="supporting_replay_refs.replay_index")
        object.__setattr__(
            self,
            "supporting_replay_refs",
            sorted(self.supporting_replay_refs, key=lambda entry: entry.replay_index),
        )
        return self


class ProceduralDepthFailureTopology(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_PROCEDURAL_DEPTH_FAILURE_TOPOLOGY_SCHEMA] = Field(
        default=ADEU_PROCEDURAL_DEPTH_FAILURE_TOPOLOGY_SCHEMA,
        alias="schema",
    )
    procedural_depth_failure_topology_id: str
    evaluated_cases: list[ProceduralDepthFailureTopologyCase] = Field(min_length=1)
    topology_summary: str
    notes: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthFailureTopology":
        for field_name in ("procedural_depth_failure_topology_id", "topology_summary"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        ordered_cases = sorted(
            self.evaluated_cases,
            key=lambda item: item.perturbation_case_ref,
        )
        case_refs = [item.perturbation_case_ref for item in ordered_cases]
        if len(case_refs) != len(set(case_refs)):
            raise ValueError("evaluated_cases perturbation_case_ref values must be unique")
        object.__setattr__(self, "evaluated_cases", ordered_cases)
        object.__setattr__(self, "notes", _sorted_unique_texts(self.notes, field_name="notes"))
        expected_id = compute_procedural_depth_failure_topology_id(_canonical_model_payload(self))
        if self.procedural_depth_failure_topology_id != expected_id:
            raise ValueError(
                "procedural_depth_failure_topology_id must match canonical topology identity"
            )
        return self


class ProceduralDepthSupportingMetricRef(BaseModel):
    model_config = MODEL_CONFIG

    replay_index: int = Field(ge=0)
    metric_ref: str

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthSupportingMetricRef":
        object.__setattr__(
            self,
            "metric_ref",
            _assert_non_empty_text(self.metric_ref, field_name="metric_ref"),
        )
        return self


class ProceduralDepthNonRegressionCase(BaseModel):
    model_config = MODEL_CONFIG

    perturbation_case_ref: str
    replay_indexes: list[int] = Field(min_length=1)
    regression_detected: bool
    supporting_metric_refs: list[ProceduralDepthSupportingMetricRef] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthNonRegressionCase":
        object.__setattr__(
            self,
            "perturbation_case_ref",
            _assert_non_empty_text(
                self.perturbation_case_ref,
                field_name="perturbation_case_ref",
            ),
        )
        ordered_indexes = _ordered_unique_ints(
            self.replay_indexes,
            field_name="replay_indexes",
        )
        metric_replay_indexes = _ordered_unique_ints(
            [entry.replay_index for entry in self.supporting_metric_refs],
            field_name="supporting_metric_refs.replay_index",
        )
        if ordered_indexes != metric_replay_indexes:
            raise ValueError(
                "supporting_metric_refs replay indexes must match replay_indexes exactly"
            )
        object.__setattr__(self, "replay_indexes", ordered_indexes)
        object.__setattr__(
            self,
            "supporting_metric_refs",
            sorted(self.supporting_metric_refs, key=lambda entry: entry.replay_index),
        )
        return self


class ProceduralDepthNonRegressionReport(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_PROCEDURAL_DEPTH_NON_REGRESSION_REPORT_SCHEMA] = Field(
        default=ADEU_PROCEDURAL_DEPTH_NON_REGRESSION_REPORT_SCHEMA,
        alias="schema",
    )
    procedural_depth_non_regression_report_id: str
    baseline_instance_ref: str
    evaluation_context_posture: EvaluationContextPosture
    replay_count: int = Field(ge=1)
    regression_detected: bool
    evaluated_cases: list[ProceduralDepthNonRegressionCase] = Field(min_length=1)
    report_summary: str
    notes: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthNonRegressionReport":
        for field_name in (
            "procedural_depth_non_regression_report_id",
            "baseline_instance_ref",
            "report_summary",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        ordered_cases = sorted(
            self.evaluated_cases,
            key=lambda item: item.perturbation_case_ref,
        )
        case_refs = [item.perturbation_case_ref for item in ordered_cases]
        if len(case_refs) != len(set(case_refs)):
            raise ValueError("evaluated_cases perturbation_case_ref values must be unique")
        if any(len(item.replay_indexes) != self.replay_count for item in ordered_cases):
            raise ValueError("replay_count must match every evaluated case replay_indexes length")
        object.__setattr__(self, "evaluated_cases", ordered_cases)
        object.__setattr__(self, "notes", _sorted_unique_texts(self.notes, field_name="notes"))
        expected_regression = any(item.regression_detected for item in self.evaluated_cases)
        if self.regression_detected != expected_regression:
            raise ValueError(
                "regression_detected must equal disjunction of evaluated case regression_detected"
            )
        expected_id = compute_procedural_depth_non_regression_report_id(
            _canonical_model_payload(self)
        )
        if self.procedural_depth_non_regression_report_id != expected_id:
            raise ValueError(
                "procedural_depth_non_regression_report_id must match canonical "
                "non-regression identity"
            )
        return self


class ProceduralDepthValidationReplayResult(BaseModel):
    model_config = MODEL_CONFIG

    replay_index: int = Field(ge=0)
    run_trace_ref: str
    metric_ref: str
    diagnostic_report_ref: str

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthValidationReplayResult":
        for field_name in ("run_trace_ref", "metric_ref", "diagnostic_report_ref"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        return self


class ProceduralDepthBenchmarkValidationCaseResult(BaseModel):
    model_config = MODEL_CONFIG

    perturbation_case_ref: str
    expected_dominant_failure_family: DominantFailureFamily
    observed_dominant_failure_family: DominantFailureFamily
    expected_terminal_trace_status: ProceduralDepthTerminalTraceStatus
    observed_terminal_trace_status: ProceduralDepthTerminalTraceStatus
    deterministic_replay_confirmed: bool
    replay_results: list[ProceduralDepthValidationReplayResult] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthBenchmarkValidationCaseResult":
        object.__setattr__(
            self,
            "perturbation_case_ref",
            _assert_non_empty_text(
                self.perturbation_case_ref,
                field_name="perturbation_case_ref",
            ),
        )
        replay_indexes = _ordered_unique_ints(
            [entry.replay_index for entry in self.replay_results],
            field_name="replay_results.replay_index",
        )
        object.__setattr__(
            self,
            "replay_results",
            sorted(self.replay_results, key=lambda entry: entry.replay_index),
        )
        first = self.replay_results[0]
        identical_replays = all(
            entry.run_trace_ref == first.run_trace_ref
            and entry.metric_ref == first.metric_ref
            and entry.diagnostic_report_ref == first.diagnostic_report_ref
            for entry in self.replay_results[1:]
        )
        if self.deterministic_replay_confirmed != identical_replays:
            raise ValueError(
                "deterministic_replay_confirmed must equal exact replay identity stability"
            )
        if replay_indexes != list(range(len(self.replay_results))):
            raise ValueError("replay_results replay_index values must be contiguous from 0")
        if self.observed_dominant_failure_family == "clean_success":
            if self.observed_terminal_trace_status != "completed_clean":
                raise ValueError(
                    "clean_success observed results must pair with completed_clean terminal status"
                )
        elif self.observed_terminal_trace_status != "completed_with_structural_break":
            raise ValueError(
                "starter structural-break observed results must pair with "
                "completed_with_structural_break"
            )
        return self


class ProceduralDepthBenchmarkValidationReport(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_PROCEDURAL_DEPTH_BENCHMARK_VALIDATION_REPORT_SCHEMA] = Field(
        default=ADEU_PROCEDURAL_DEPTH_BENCHMARK_VALIDATION_REPORT_SCHEMA,
        alias="schema",
    )
    procedural_depth_benchmark_validation_report_id: str
    evaluation_context_posture: EvaluationContextPosture
    replay_count: int = Field(ge=1)
    deterministic_replay_confirmed: bool
    validation_case_results: list[ProceduralDepthBenchmarkValidationCaseResult] = Field(
        min_length=1
    )
    limitations: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_model(self) -> "ProceduralDepthBenchmarkValidationReport":
        object.__setattr__(
            self,
            "procedural_depth_benchmark_validation_report_id",
            _assert_non_empty_text(
                self.procedural_depth_benchmark_validation_report_id,
                field_name="procedural_depth_benchmark_validation_report_id",
            ),
        )
        ordered_cases = sorted(
            self.validation_case_results,
            key=lambda item: item.perturbation_case_ref,
        )
        case_refs = [item.perturbation_case_ref for item in ordered_cases]
        if len(case_refs) != len(set(case_refs)):
            raise ValueError("validation_case_results perturbation_case_ref values must be unique")
        if any(len(item.replay_results) != self.replay_count for item in ordered_cases):
            raise ValueError("replay_count must match every validation case replay_results length")
        object.__setattr__(self, "validation_case_results", ordered_cases)
        object.__setattr__(
            self,
            "limitations",
            _sorted_unique_texts(self.limitations, field_name="limitations"),
        )
        expected_deterministic = all(
            item.deterministic_replay_confirmed
            and item.expected_dominant_failure_family == item.observed_dominant_failure_family
            and item.expected_terminal_trace_status == item.observed_terminal_trace_status
            for item in self.validation_case_results
        )
        if self.deterministic_replay_confirmed != expected_deterministic:
            raise ValueError(
                "deterministic_replay_confirmed must equal conjunction of validation "
                "case replay stability and expected/observed agreement"
            )
        expected_id = compute_procedural_depth_benchmark_validation_report_id(
            _canonical_model_payload(self)
        )
        if self.procedural_depth_benchmark_validation_report_id != expected_id:
            raise ValueError(
                "procedural_depth_benchmark_validation_report_id must match "
                "canonical validation identity"
            )
        return self


class BenchmarkSubjectRecord(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_BENCHMARK_SUBJECT_RECORD_SCHEMA] = Field(
        default=ADEU_BENCHMARK_SUBJECT_RECORD_SCHEMA,
        alias="schema",
    )
    benchmark_subject_record_id: str
    subject_class: SubjectUnderTestClass
    subject_label: str
    subject_identity_ref: str
    benchmark_family_spec_ref: str
    benchmark_projection_spec_ref: str
    benchmark_execution_context_ref: str
    perturbation_bundle_ref: str
    perturbation_case_refs: list[str] = Field(min_length=1)
    baseline_instance_ref: str
    baseline_run_trace_ref: str
    baseline_metric_ref: str
    baseline_diagnostic_report_ref: str
    perturbation_non_regression_report_ref: str
    perturbation_benchmark_validation_report_ref: str
    notes: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_model(self) -> "BenchmarkSubjectRecord":
        for field_name in (
            "benchmark_subject_record_id",
            "subject_label",
            "subject_identity_ref",
            "benchmark_family_spec_ref",
            "benchmark_projection_spec_ref",
            "benchmark_execution_context_ref",
            "perturbation_bundle_ref",
            "baseline_instance_ref",
            "baseline_run_trace_ref",
            "baseline_metric_ref",
            "baseline_diagnostic_report_ref",
            "perturbation_non_regression_report_ref",
            "perturbation_benchmark_validation_report_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "perturbation_case_refs",
            _ordered_unique_texts(
                self.perturbation_case_refs,
                field_name="perturbation_case_refs",
            ),
        )
        expected_bundle_ref = compute_procedural_depth_perturbation_bundle_ref(
            baseline_instance_ref=self.baseline_instance_ref,
            perturbation_case_refs=self.perturbation_case_refs,
        )
        if self.perturbation_bundle_ref != expected_bundle_ref:
            raise ValueError(
                "perturbation_bundle_ref must match canonical bundle identity over "
                "baseline_instance_ref and perturbation_case_refs"
            )
        object.__setattr__(self, "notes", _sorted_unique_texts(self.notes, field_name="notes"))
        expected_id = compute_benchmark_subject_record_id(_canonical_model_payload(self))
        if self.benchmark_subject_record_id != expected_id:
            raise ValueError("benchmark_subject_record_id must match canonical subject identity")
        return self


class CrossSubjectComparisonCase(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_CROSS_SUBJECT_COMPARISON_CASE_SCHEMA] = Field(
        default=ADEU_CROSS_SUBJECT_COMPARISON_CASE_SCHEMA,
        alias="schema",
    )
    cross_subject_comparison_case_id: str
    comparison_label: str
    left_subject_ref: str
    right_subject_ref: str
    benchmark_family_spec_ref: str
    benchmark_projection_spec_ref: str
    baseline_instance_ref: str
    required_execution_context_compatibility_fields: list[ExecutionContextCompatibilityField] = (
        Field(min_length=1)
    )
    perturbation_case_refs: list[str] = Field(min_length=1)
    required_comparison_surfaces: list[ComparisonSurface] = Field(min_length=1)
    notes: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_model(self) -> "CrossSubjectComparisonCase":
        for field_name in (
            "cross_subject_comparison_case_id",
            "comparison_label",
            "left_subject_ref",
            "right_subject_ref",
            "benchmark_family_spec_ref",
            "benchmark_projection_spec_ref",
            "baseline_instance_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        if self.left_subject_ref == self.right_subject_ref:
            raise ValueError("left_subject_ref and right_subject_ref must differ")
        object.__setattr__(
            self,
            "required_execution_context_compatibility_fields",
            _exact_ordered_vocabulary(
                list(self.required_execution_context_compatibility_fields),
                expected_order=EXECUTION_CONTEXT_COMPATIBILITY_FIELD_VOCABULARY,
                field_name="required_execution_context_compatibility_fields",
            ),
        )
        object.__setattr__(
            self,
            "perturbation_case_refs",
            _ordered_unique_texts(
                self.perturbation_case_refs,
                field_name="perturbation_case_refs",
            ),
        )
        object.__setattr__(
            self,
            "required_comparison_surfaces",
            _exact_ordered_vocabulary(
                list(self.required_comparison_surfaces),
                expected_order=COMPARISON_SURFACE_VOCABULARY,
                field_name="required_comparison_surfaces",
            ),
        )
        object.__setattr__(self, "notes", _sorted_unique_texts(self.notes, field_name="notes"))
        expected_id = compute_cross_subject_comparison_case_id(_canonical_model_payload(self))
        if self.cross_subject_comparison_case_id != expected_id:
            raise ValueError(
                "cross_subject_comparison_case_id must match canonical comparison-case identity"
            )
        return self


class CrossSubjectSubjectSummary(BaseModel):
    model_config = MODEL_CONFIG

    subject_record_ref: str
    baseline_metric_ref: str
    baseline_diagnostic_report_ref: str
    perturbation_non_regression_report_ref: str
    perturbation_benchmark_validation_report_ref: str

    @model_validator(mode="after")
    def _validate_model(self) -> "CrossSubjectSubjectSummary":
        for field_name in (
            "subject_record_ref",
            "baseline_metric_ref",
            "baseline_diagnostic_report_ref",
            "perturbation_non_regression_report_ref",
            "perturbation_benchmark_validation_report_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        return self


class CrossSubjectFieldComparison(BaseModel):
    model_config = MODEL_CONFIG

    comparison_surface: ComparisonSurface
    left_ref: str
    right_ref: str
    match_status: ComparisonMatchStatus
    difference_summary: str

    @model_validator(mode="after")
    def _validate_model(self) -> "CrossSubjectFieldComparison":
        for field_name in ("left_ref", "right_ref", "difference_summary"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        if self.left_ref == self.right_ref and self.match_status == "different_but_comparable":
            raise ValueError(
                "different_but_comparable requires distinct left_ref and right_ref values"
            )
        return self


class CrossSubjectComparisonReport(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_CROSS_SUBJECT_COMPARISON_REPORT_SCHEMA] = Field(
        default=ADEU_CROSS_SUBJECT_COMPARISON_REPORT_SCHEMA,
        alias="schema",
    )
    cross_subject_comparison_report_id: str
    comparison_case_ref: str
    comparison_status: ComparisonStatus
    subject_summaries: list[CrossSubjectSubjectSummary] = Field(min_length=2, max_length=2)
    field_comparisons: list[CrossSubjectFieldComparison] = Field(min_length=1)
    supporting_artifact_refs: list[str] = Field(min_length=1)
    comparison_summary: str
    notes: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_model(self) -> "CrossSubjectComparisonReport":
        for field_name in (
            "cross_subject_comparison_report_id",
            "comparison_case_ref",
            "comparison_summary",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        ordered_subject_summaries = sorted(
            self.subject_summaries,
            key=lambda item: item.subject_record_ref,
        )
        subject_refs = [item.subject_record_ref for item in ordered_subject_summaries]
        if len(subject_refs) != len(set(subject_refs)):
            raise ValueError("subject_summaries subject_record_ref values must be unique")
        object.__setattr__(self, "subject_summaries", ordered_subject_summaries)
        ordered_field_comparisons = sorted(
            self.field_comparisons,
            key=lambda item: (
                COMPARISON_SURFACE_VOCABULARY.index(item.comparison_surface),
                item.left_ref,
                item.right_ref,
            ),
        )
        surfaces = [item.comparison_surface for item in ordered_field_comparisons]
        if surfaces != COMPARISON_SURFACE_VOCABULARY:
            raise ValueError(
                "field_comparisons must cover the starter comparison surfaces exactly once"
            )
        object.__setattr__(self, "field_comparisons", ordered_field_comparisons)
        object.__setattr__(
            self,
            "supporting_artifact_refs",
            _ordered_unique_texts(
                self.supporting_artifact_refs,
                field_name="supporting_artifact_refs",
            ),
        )
        object.__setattr__(self, "notes", _sorted_unique_texts(self.notes, field_name="notes"))
        has_incompatible = self.comparison_status == "comparison_incompatible"
        has_insufficient = any(
            item.match_status == "insufficient_evidence" for item in self.field_comparisons
        )
        if has_incompatible and not has_insufficient:
            raise ValueError(
                "comparison_incompatible requires at least one "
                "insufficient_evidence field comparison"
            )
        if self.comparison_status == "comparison_ready_clean" and has_insufficient:
            raise ValueError(
                "comparison_ready_clean requires every field comparison to stay comparable"
            )
        expected_id = compute_cross_subject_comparison_report_id(_canonical_model_payload(self))
        if self.cross_subject_comparison_report_id != expected_id:
            raise ValueError(
                "cross_subject_comparison_report_id must match canonical comparison identity"
            )
        return self


class CrossSubjectComparisonValidationResult(BaseModel):
    model_config = MODEL_CONFIG

    comparison_surface: ComparisonSurface
    left_ref: str
    right_ref: str
    comparison_status: ComparisonMatchStatus
    deterministic_comparison_confirmed: bool

    @model_validator(mode="after")
    def _validate_model(self) -> "CrossSubjectComparisonValidationResult":
        for field_name in ("left_ref", "right_ref"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        if (
            self.comparison_status == "insufficient_evidence"
            and self.deterministic_comparison_confirmed
        ):
            raise ValueError(
                "insufficient_evidence validation results may not claim deterministic comparison"
            )
        return self


class CrossSubjectComparisonValidationReport(BaseModel):
    model_config = MODEL_CONFIG

    schema_id: Literal[ADEU_CROSS_SUBJECT_COMPARISON_VALIDATION_REPORT_SCHEMA] = Field(
        default=ADEU_CROSS_SUBJECT_COMPARISON_VALIDATION_REPORT_SCHEMA,
        alias="schema",
    )
    cross_subject_comparison_validation_report_id: str
    comparison_case_ref: str
    deterministic_comparison_confirmed: bool
    validation_status: ComparisonValidationStatus
    validation_results: list[CrossSubjectComparisonValidationResult] = Field(min_length=1)
    limitations: list[str] = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_model(self) -> "CrossSubjectComparisonValidationReport":
        for field_name in (
            "cross_subject_comparison_validation_report_id",
            "comparison_case_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        ordered_results = sorted(
            self.validation_results,
            key=lambda item: (
                COMPARISON_SURFACE_VOCABULARY.index(item.comparison_surface),
                item.left_ref,
                item.right_ref,
            ),
        )
        surfaces = [item.comparison_surface for item in ordered_results]
        if surfaces != COMPARISON_SURFACE_VOCABULARY:
            raise ValueError(
                "validation_results must cover the starter comparison surfaces exactly once"
            )
        object.__setattr__(self, "validation_results", ordered_results)
        object.__setattr__(
            self,
            "limitations",
            _sorted_unique_texts(self.limitations, field_name="limitations"),
        )
        expected_deterministic = all(
            item.deterministic_comparison_confirmed for item in self.validation_results
        )
        if self.deterministic_comparison_confirmed != expected_deterministic:
            raise ValueError(
                "deterministic_comparison_confirmed must equal conjunction of validation results"
            )
        has_insufficient = any(
            item.comparison_status == "insufficient_evidence" for item in self.validation_results
        )
        expected_status: ComparisonValidationStatus
        if has_insufficient:
            expected_status = "validation_incompatible"
        elif self.deterministic_comparison_confirmed:
            expected_status = "validation_ready_clean"
        else:
            expected_status = "validation_insufficient"
        if self.validation_status != expected_status:
            raise ValueError("validation_status must match the starter validation aggregation law")
        expected_id = compute_cross_subject_comparison_validation_report_id(
            _canonical_model_payload(self)
        )
        if self.cross_subject_comparison_validation_report_id != expected_id:
            raise ValueError(
                "cross_subject_comparison_validation_report_id must match canonical "
                "comparison validation identity"
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
            _canonical_model_payload(BenchmarkValidationCaseResult.model_validate(case_material))
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
        prepared[field_name] = _assert_non_empty_text(prepared[field_name], field_name=field_name)
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
    refs = [ProceduralDepthSupportingEventRef.model_validate(payload) for payload in payloads]
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
    return _canonical_model_payload(ProceduralDepthDiagnosticReport.model_validate(prepared))


def canonicalize_procedural_depth_diagnostic_report_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    return _canonical_model_payload(ProceduralDepthDiagnosticReport.model_validate(payload))


def materialize_procedural_depth_perturbation_case_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = _canonicalize_procedural_depth_perturbation_case_material(payload)
    prepared.setdefault(
        "procedural_depth_perturbation_case_id",
        compute_procedural_depth_perturbation_case_id(prepared),
    )
    return _canonical_model_payload(ProceduralDepthPerturbationCase.model_validate(prepared))


def canonicalize_procedural_depth_perturbation_case_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    return _canonical_model_payload(ProceduralDepthPerturbationCase.model_validate(payload))


def materialize_procedural_depth_failure_topology_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = _canonicalize_procedural_depth_failure_topology_material(payload)
    prepared.setdefault(
        "procedural_depth_failure_topology_id",
        compute_procedural_depth_failure_topology_id(prepared),
    )
    return _canonical_model_payload(ProceduralDepthFailureTopology.model_validate(prepared))


def canonicalize_procedural_depth_failure_topology_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    return _canonical_model_payload(ProceduralDepthFailureTopology.model_validate(payload))


def materialize_procedural_depth_non_regression_report_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = _canonicalize_procedural_depth_non_regression_report_material(payload)
    prepared.setdefault(
        "procedural_depth_non_regression_report_id",
        compute_procedural_depth_non_regression_report_id(prepared),
    )
    return _canonical_model_payload(ProceduralDepthNonRegressionReport.model_validate(prepared))


def canonicalize_procedural_depth_non_regression_report_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    return _canonical_model_payload(ProceduralDepthNonRegressionReport.model_validate(payload))


def materialize_procedural_depth_benchmark_validation_report_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = _canonicalize_procedural_depth_benchmark_validation_report_material(payload)
    prepared.setdefault(
        "procedural_depth_benchmark_validation_report_id",
        compute_procedural_depth_benchmark_validation_report_id(prepared),
    )
    return _canonical_model_payload(
        ProceduralDepthBenchmarkValidationReport.model_validate(prepared)
    )


def canonicalize_procedural_depth_benchmark_validation_report_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    return _canonical_model_payload(
        ProceduralDepthBenchmarkValidationReport.model_validate(payload)
    )


def materialize_benchmark_subject_record_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = _canonicalize_benchmark_subject_record_material(payload)
    prepared.setdefault(
        "benchmark_subject_record_id",
        compute_benchmark_subject_record_id(prepared),
    )
    return _canonical_model_payload(BenchmarkSubjectRecord.model_validate(prepared))


def canonicalize_benchmark_subject_record_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    return _canonical_model_payload(BenchmarkSubjectRecord.model_validate(payload))


def materialize_cross_subject_comparison_case_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = _canonicalize_cross_subject_comparison_case_material(payload)
    prepared.setdefault(
        "cross_subject_comparison_case_id",
        compute_cross_subject_comparison_case_id(prepared),
    )
    return _canonical_model_payload(CrossSubjectComparisonCase.model_validate(prepared))


def canonicalize_cross_subject_comparison_case_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    return _canonical_model_payload(CrossSubjectComparisonCase.model_validate(payload))


def materialize_cross_subject_comparison_report_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = _canonicalize_cross_subject_comparison_report_material(payload)
    prepared.setdefault(
        "cross_subject_comparison_report_id",
        compute_cross_subject_comparison_report_id(prepared),
    )
    return _canonical_model_payload(CrossSubjectComparisonReport.model_validate(prepared))


def canonicalize_cross_subject_comparison_report_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    return _canonical_model_payload(CrossSubjectComparisonReport.model_validate(payload))


def materialize_cross_subject_comparison_validation_report_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    prepared = _canonicalize_cross_subject_comparison_validation_report_material(payload)
    prepared.setdefault(
        "cross_subject_comparison_validation_report_id",
        compute_cross_subject_comparison_validation_report_id(prepared),
    )
    return _canonical_model_payload(CrossSubjectComparisonValidationReport.model_validate(prepared))


def canonicalize_cross_subject_comparison_validation_report_payload(
    payload: dict[str, Any],
) -> dict[str, Any]:
    return _canonical_model_payload(CrossSubjectComparisonValidationReport.model_validate(payload))


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
            "expected_dominant_failure_family": expectation["expected_dominant_failure_family"],
            "observed_dominant_failure_family": expectation["observed_dominant_failure_family"],
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
