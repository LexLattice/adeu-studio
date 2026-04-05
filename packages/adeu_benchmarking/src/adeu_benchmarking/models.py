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
