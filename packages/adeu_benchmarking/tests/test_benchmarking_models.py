from __future__ import annotations

import json
import re
from pathlib import Path

import pytest
from adeu_benchmarking import (
    ADEU_BENCHMARK_EXECUTION_CONTEXT_SCHEMA,
    ADEU_BENCHMARK_FAMILY_SPEC_SCHEMA,
    ADEU_BENCHMARK_PROJECTION_SPEC_SCHEMA,
    ADEU_BENCHMARK_VALIDATION_REPORT_SCHEMA,
    BENCHMARK_OUTPUT_EPISTEMIC_POSTURE_VOCABULARY,
    DOMINANT_FAILURE_FAMILY_VOCABULARY,
    SUBJECT_UNDER_TEST_CLASS_VOCABULARY,
    BenchmarkExecutionContext,
    BenchmarkFamilySpec,
    BenchmarkProjectionSpec,
    BenchmarkValidationReport,
    derive_benchmark_validation_report,
    materialize_benchmark_family_spec_payload,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from pydantic import ValidationError

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v46a"
_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _schema_pairs() -> list[tuple[str, Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return [
        (
            ADEU_BENCHMARK_FAMILY_SPEC_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_benchmark_family_spec.v1.json",
            root / "spec" / "adeu_benchmark_family_spec.schema.json",
        ),
        (
            ADEU_BENCHMARK_PROJECTION_SPEC_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_benchmark_projection_spec.v1.json",
            root / "spec" / "adeu_benchmark_projection_spec.schema.json",
        ),
        (
            ADEU_BENCHMARK_EXECUTION_CONTEXT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_benchmark_execution_context.v1.json",
            root / "spec" / "adeu_benchmark_execution_context.schema.json",
        ),
        (
            ADEU_BENCHMARK_VALIDATION_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_benchmark_validation_report.v1.json",
            root / "spec" / "adeu_benchmark_validation_report.schema.json",
        ),
    ]


def test_reference_fixtures_validate_and_exercise_starter_vocabularies() -> None:
    family = BenchmarkFamilySpec.model_validate(
        _load_json("reference_benchmark_family_spec.json")
    )
    projection = BenchmarkProjectionSpec.model_validate(
        _load_json("reference_benchmark_projection_spec.json")
    )
    context = BenchmarkExecutionContext.model_validate(
        _load_json("reference_benchmark_execution_context.json")
    )
    report = BenchmarkValidationReport.model_validate(
        _load_json("reference_benchmark_validation_report.json")
    )
    matrix = _load_json("reference_v46a_validation_case_matrix.json")

    assert family.subject_under_test_classes == SUBJECT_UNDER_TEST_CLASS_VOCABULARY
    assert (
        family.benchmark_output_epistemic_postures
        == BENCHMARK_OUTPUT_EPISTEMIC_POSTURE_VOCABULARY
    )
    assert projection.declared_instance_contract_id == "adeu_procedural_depth_instance@1"
    assert context.determinism_posture == "deterministic_fixed_context"
    assert report.validation_scope == "tiny_reference_fixture_bundle"
    assert {
        item.observed_dominant_failure_family for item in report.validation_case_results
    } == set(DOMINANT_FAILURE_FAMILY_VOCABULARY)
    assert [
        item["observed_dominant_failure_family"]
        for item in matrix["validation_case_results"]
    ] == [item.observed_dominant_failure_family for item in report.validation_case_results]
    assert DOMINANT_FAILURE_FAMILY_VOCABULARY == [
        "clean_success",
        "horizontal_plan_spine",
        "vertical_active_step_compilation",
        "reintegration",
        "mixed",
    ]


def test_family_spec_canonicalizes_ordered_vocabularies_before_id_check() -> None:
    payload = _load_json("reference_benchmark_family_spec.json")
    assert isinstance(payload, dict)
    reversed_payload = dict(payload)
    reversed_payload["subject_under_test_classes"] = list(
        reversed(payload["subject_under_test_classes"])
    )
    reversed_payload["benchmark_output_epistemic_postures"] = list(
        reversed(payload["benchmark_output_epistemic_postures"])
    )

    validated = BenchmarkFamilySpec.model_validate(reversed_payload)

    assert validated.subject_under_test_classes == SUBJECT_UNDER_TEST_CLASS_VOCABULARY
    assert (
        validated.benchmark_output_epistemic_postures
        == BENCHMARK_OUTPUT_EPISTEMIC_POSTURE_VOCABULARY
    )
    assert validated.benchmark_family_spec_id == payload["benchmark_family_spec_id"]


def test_materialize_family_spec_populates_canonical_id() -> None:
    payload = _load_json("reference_benchmark_family_spec.json")
    assert isinstance(payload, dict)
    payload_without_id = dict(payload)
    payload_without_id.pop("benchmark_family_spec_id")

    materialized = materialize_benchmark_family_spec_payload(payload_without_id)

    assert materialized == payload


def test_derive_validation_report_replays_reference_fixture() -> None:
    projection = _load_json("reference_benchmark_projection_spec.json")
    matrix = _load_json("reference_v46a_validation_case_matrix.json")
    expected_report = _load_json("reference_benchmark_validation_report.json")
    assert isinstance(projection, dict)
    assert isinstance(matrix, dict)

    derived = derive_benchmark_validation_report(
        benchmark_projection_spec_ref=projection["benchmark_projection_spec_id"],
        validation_label=matrix["validation_label"],
        case_expectations=matrix["validation_case_results"],
        benchmark_limitations=matrix["benchmark_limitations"],
    )

    assert derived == expected_report


@pytest.mark.parametrize(
    "fixture_name, model",
    [
        (
            "reject_benchmark_projection_spec_missing_declared_contract_ids.json",
            BenchmarkProjectionSpec,
        ),
        (
            "reject_benchmark_validation_report_unsupported_dominant_family.json",
            BenchmarkValidationReport,
        ),
    ],
)
def test_reject_fixtures_fail_closed_during_model_validation(
    fixture_name: str,
    model: type[BenchmarkProjectionSpec] | type[BenchmarkValidationReport],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_json(fixture_name))


def test_export_schema_replays_authoritative_and_mirror_outputs() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative["properties"]["schema"]["const"] == expected_schema
        assert authoritative == mirror

        serialized = json.dumps(authoritative, sort_keys=True)
        assert repo_root(anchor=Path(__file__)).as_posix() not in serialized
        assert not _WINDOWS_ABSOLUTE_PATH_RE.search(serialized)
