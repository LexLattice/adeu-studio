from __future__ import annotations

from copy import deepcopy
from typing import Any, Callable, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from ._hashing import sha256_canonical_json

MODEL_CONFIG = ConfigDict(extra="forbid", frozen=True, protected_namespaces=())

BENCHMARK_FAMILY_SPEC_SCHEMA = "benchmark_family_spec@1"
BENCHMARK_PROJECTION_SPEC_SCHEMA = "benchmark_projection_spec@1"
BENCHMARK_EXECUTION_CONTEXT_SCHEMA = "benchmark_execution_context@1"
BENCHMARK_VALIDATION_REPORT_SCHEMA = "benchmark_validation_report@1"

SubjectUnderTestClass = Literal[
    "base_model",
    "prompted_model",
    "routed_runtime",
    "multi_agent_system",
    "adeu_runtime_surface",
]
DeterminismPosture = Literal["deterministic_fixed_context", "stochastic_context"]
DiagnosticPosture = Literal["diagnostic_only"]
ImplementationPosture = Literal["bounded_proto_non_promotional"]
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


def compute_benchmark_family_spec_id(payload: dict[str, Any]) -> str:
    material = {
        "family_key": payload.get("family_key"),
        "family_label": payload.get("family_label"),
        "doctrinal_source_refs": sorted(set(payload.get("doctrinal_source_refs", []))),
        "capability_axes": sorted(set(payload.get("capability_axes", []))),
        "subject_under_test_classes": sorted(
            set(payload.get("subject_under_test_classes", []))
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
        "target_capability_axes": sorted(set(payload.get("target_capability_axes", []))),
        "instance_schema": payload.get("instance_schema"),
        "gold_trace_schema": payload.get("gold_trace_schema"),
        "run_trace_schema": payload.get("run_trace_schema"),
        "metrics_schema": payload.get("metrics_schema"),
        "diagnostic_report_schema": payload.get("diagnostic_report_schema"),
        "hierarchical_trace_required": payload.get("hierarchical_trace_required"),
        "explicit_reintegration_trace_required": payload.get(
            "explicit_reintegration_trace_required"
        ),
        "projection_notes": sorted(set(payload.get("projection_notes", []))),
    }
    return f"benchproj_{sha256_canonical_json(material)[:32]}"


def compute_benchmark_execution_context_id(payload: dict[str, Any]) -> str:
    material = {
        "subject_under_test_class": payload.get("subject_under_test_class"),
        "subject_label": payload.get("subject_label"),
        "subject_version": payload.get("subject_version"),
        "prompt_wrapper_ref": payload.get("prompt_wrapper_ref"),
        "tool_availability": sorted(set(payload.get("tool_availability", []))),
        "determinism_posture": payload.get("determinism_posture"),
        "repo_snapshot_ref": payload.get("repo_snapshot_ref"),
        "notes": sorted(set(payload.get("notes", []))),
    }
    return f"benchctx_{sha256_canonical_json(material)[:32]}"


def compute_benchmark_validation_case_result_id(payload: dict[str, Any]) -> str:
    material = {
        "case_label": payload.get("case_label"),
        "run_trace_ref": payload.get("run_trace_ref"),
        "expected_dominant_failure_family": payload.get(
            "expected_dominant_failure_family"
        ),
        "observed_dominant_failure_family": payload.get(
            "observed_dominant_failure_family"
        ),
        "match": payload.get("match"),
    }
    return f"benchvalcase_{sha256_canonical_json(material)[:32]}"


def compute_benchmark_validation_report_id(payload: dict[str, Any]) -> str:
    case_material = [
        {
            "case_label": entry.get("case_label"),
            "run_trace_ref": entry.get("run_trace_ref"),
            "expected": entry.get("expected_dominant_failure_family"),
            "observed": entry.get("observed_dominant_failure_family"),
            "match": entry.get("match"),
        }
        for entry in sorted(
            payload.get("validation_case_results", []),
            key=lambda entry: entry.get("case_label", ""),
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
        "benchmark_limitations": sorted(set(payload.get("benchmark_limitations", []))),
    }
    return f"benchval_{sha256_canonical_json(material)[:32]}"


class BenchmarkFamilySpec(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[BENCHMARK_FAMILY_SPEC_SCHEMA] = BENCHMARK_FAMILY_SPEC_SCHEMA
    benchmark_family_spec_id: str
    family_key: str
    family_label: str
    doctrinal_source_refs: list[str] = Field(min_length=1)
    capability_axes: list[str] = Field(min_length=1)
    subject_under_test_classes: list[SubjectUnderTestClass] = Field(min_length=1)
    diagnostic_posture: DiagnosticPosture
    implementation_posture: ImplementationPosture

    @model_validator(mode="after")
    def _validate_model(self) -> "BenchmarkFamilySpec":
        object.__setattr__(
            self,
            "benchmark_family_spec_id",
            _assert_non_empty_text(
                self.benchmark_family_spec_id,
                field_name="benchmark_family_spec_id",
            ),
        )
        object.__setattr__(
            self,
            "family_key",
            _assert_non_empty_text(self.family_key, field_name="family_key"),
        )
        object.__setattr__(
            self,
            "family_label",
            _assert_non_empty_text(self.family_label, field_name="family_label"),
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
            sorted(set(self.subject_under_test_classes)),
        )
        expected_id = compute_benchmark_family_spec_id(_canonical_model_payload(self))
        if self.benchmark_family_spec_id != expected_id:
            raise ValueError(
                "benchmark_family_spec_id must match canonical family spec identity"
            )
        return self


class BenchmarkProjectionSpec(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[BENCHMARK_PROJECTION_SPEC_SCHEMA] = BENCHMARK_PROJECTION_SPEC_SCHEMA
    benchmark_projection_spec_id: str
    benchmark_family_spec_ref: str
    projection_key: str
    projection_label: str
    target_capability_axes: list[str] = Field(min_length=1)
    instance_schema: str
    gold_trace_schema: str
    run_trace_schema: str
    metrics_schema: str
    diagnostic_report_schema: str
    hierarchical_trace_required: bool
    explicit_reintegration_trace_required: bool
    projection_notes: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_model(self) -> "BenchmarkProjectionSpec":
        for field_name in (
            "benchmark_projection_spec_id",
            "benchmark_family_spec_ref",
            "projection_key",
            "projection_label",
            "instance_schema",
            "gold_trace_schema",
            "run_trace_schema",
            "metrics_schema",
            "diagnostic_report_schema",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
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
            "projection_notes",
            _sorted_unique_texts(self.projection_notes, field_name="projection_notes"),
        )
        expected_id = compute_benchmark_projection_spec_id(_canonical_model_payload(self))
        if self.benchmark_projection_spec_id != expected_id:
            raise ValueError(
                "benchmark_projection_spec_id must match canonical projection identity"
            )
        return self


class BenchmarkExecutionContext(BaseModel):
    model_config = MODEL_CONFIG

    schema: Literal[BENCHMARK_EXECUTION_CONTEXT_SCHEMA] = BENCHMARK_EXECUTION_CONTEXT_SCHEMA
    benchmark_execution_context_id: str
    subject_under_test_class: SubjectUnderTestClass
    subject_label: str
    subject_version: str
    prompt_wrapper_ref: str | None = None
    tool_availability: list[str] = Field(min_length=1)
    determinism_posture: DeterminismPosture
    repo_snapshot_ref: str
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
    run_trace_ref: str
    expected_dominant_failure_family: DominantFailureFamily
    observed_dominant_failure_family: DominantFailureFamily
    match: bool

    @model_validator(mode="after")
    def _validate_model(self) -> "BenchmarkValidationCaseResult":
        for field_name in (
            "validation_case_result_id",
            "case_label",
            "run_trace_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
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

    schema: Literal[BENCHMARK_VALIDATION_REPORT_SCHEMA] = BENCHMARK_VALIDATION_REPORT_SCHEMA
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
        sorted_case_results = sorted(self.validation_case_results, key=lambda entry: entry.case_label)
        case_labels = [entry.case_label for entry in sorted_case_results]
        if len(case_labels) != len(set(case_labels)):
            raise ValueError("validation_case_results case_label values must be unique")
        object.__setattr__(self, "validation_case_results", sorted_case_results)
        object.__setattr__(
            self,
            "benchmark_limitations",
            _sorted_unique_texts(
                self.benchmark_limitations,
                field_name="benchmark_limitations",
            ),
        )
        expected_all_matched = all(entry.match for entry in self.validation_case_results)
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


def materialize_benchmark_family_spec_payload(payload: dict[str, Any]) -> dict[str, Any]:
    prepared = _prepare_payload(
        payload,
        id_field="benchmark_family_spec_id",
        compute_id=compute_benchmark_family_spec_id,
    )
    return _canonical_model_payload(BenchmarkFamilySpec.model_validate(prepared))


def canonicalize_benchmark_family_spec_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return _canonical_model_payload(BenchmarkFamilySpec.model_validate(payload))


def materialize_benchmark_projection_spec_payload(payload: dict[str, Any]) -> dict[str, Any]:
    prepared = _prepare_payload(
        payload,
        id_field="benchmark_projection_spec_id",
        compute_id=compute_benchmark_projection_spec_id,
    )
    return _canonical_model_payload(BenchmarkProjectionSpec.model_validate(prepared))


def canonicalize_benchmark_projection_spec_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return _canonical_model_payload(BenchmarkProjectionSpec.model_validate(payload))


def materialize_benchmark_execution_context_payload(payload: dict[str, Any]) -> dict[str, Any]:
    prepared = _prepare_payload(
        payload,
        id_field="benchmark_execution_context_id",
        compute_id=compute_benchmark_execution_context_id,
    )
    return _canonical_model_payload(BenchmarkExecutionContext.model_validate(prepared))


def canonicalize_benchmark_execution_context_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return _canonical_model_payload(BenchmarkExecutionContext.model_validate(payload))


def materialize_benchmark_validation_report_payload(payload: dict[str, Any]) -> dict[str, Any]:
    prepared = deepcopy(payload)
    case_results: list[dict[str, Any]] = []
    for case_payload in prepared.get("validation_case_results", []):
        case_material = deepcopy(case_payload)
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
        all(case_payload["match"] for case_payload in case_results),
    )
    prepared.setdefault(
        "benchmark_validation_report_id",
        compute_benchmark_validation_report_id(prepared),
    )
    return _canonical_model_payload(BenchmarkValidationReport.model_validate(prepared))


def canonicalize_benchmark_validation_report_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return _canonical_model_payload(BenchmarkValidationReport.model_validate(payload))


def derive_benchmark_validation_report(
    *,
    benchmark_projection_spec_ref: str,
    validation_label: str,
    case_expectations: list[dict[str, Any]],
    benchmark_limitations: list[str],
) -> dict[str, Any]:
    case_results = []
    for expectation in case_expectations:
        expected_family = expectation["expected_dominant_failure_family"]
        observed_family = expectation["observed_dominant_failure_family"]
        case_results.append(
            {
                "case_label": expectation["case_label"],
                "run_trace_ref": expectation["run_trace_ref"],
                "expected_dominant_failure_family": expected_family,
                "observed_dominant_failure_family": observed_family,
                "match": expected_family == observed_family,
            }
        )
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


__all__ = [
    "BENCHMARK_EXECUTION_CONTEXT_SCHEMA",
    "BENCHMARK_FAMILY_SPEC_SCHEMA",
    "BENCHMARK_PROJECTION_SPEC_SCHEMA",
    "BENCHMARK_VALIDATION_REPORT_SCHEMA",
    "BenchmarkExecutionContext",
    "BenchmarkFamilySpec",
    "BenchmarkProjectionSpec",
    "BenchmarkValidationCaseResult",
    "BenchmarkValidationReport",
    "DiagnosticPosture",
    "DominantFailureFamily",
    "ImplementationPosture",
    "ScorerDeterminismPosture",
    "SubjectUnderTestClass",
    "ValidationScope",
    "canonicalize_benchmark_execution_context_payload",
    "canonicalize_benchmark_family_spec_payload",
    "canonicalize_benchmark_projection_spec_payload",
    "canonicalize_benchmark_validation_report_payload",
    "compute_benchmark_execution_context_id",
    "compute_benchmark_family_spec_id",
    "compute_benchmark_projection_spec_id",
    "compute_benchmark_validation_case_result_id",
    "compute_benchmark_validation_report_id",
    "derive_benchmark_validation_report",
    "materialize_benchmark_execution_context_payload",
    "materialize_benchmark_family_spec_payload",
    "materialize_benchmark_projection_spec_payload",
    "materialize_benchmark_validation_report_payload",
]
