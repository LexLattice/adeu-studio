from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_benchmarking import (
    ADEU_BENCHMARK_CONSUMER_ADVISORY_REPORT_SCHEMA,
    ADEU_BENCHMARK_CONSUMER_CASE_SCHEMA,
    ADEU_BENCHMARK_CONSUMER_VALIDATION_REPORT_SCHEMA,
    BenchmarkConsumerCase,
    derive_benchmark_consumer_case,
    evaluate_benchmark_consumer_case,
    materialize_benchmark_consumer_advisory_report_payload,
    materialize_benchmark_consumer_validation_report_payload,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from pydantic import ValidationError

V46D_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v46d"
V46E_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v46e"


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _load_comparison_fixture(name: str) -> object:
    candidate = V46E_FIXTURE_ROOT / name
    if candidate.exists():
        return json.loads(candidate.read_text(encoding="utf-8"))
    return json.loads((V46D_FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _schema_pairs() -> list[tuple[str, Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return [
        (
            ADEU_BENCHMARK_CONSUMER_CASE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_benchmark_consumer_case.v1.json",
            root / "spec" / "adeu_benchmark_consumer_case.schema.json",
        ),
        (
            ADEU_BENCHMARK_CONSUMER_ADVISORY_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_benchmark_consumer_advisory_report.v1.json",
            root / "spec" / "adeu_benchmark_consumer_advisory_report.schema.json",
        ),
        (
            ADEU_BENCHMARK_CONSUMER_VALIDATION_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_benchmark_consumer_validation_report.v1.json",
            root / "spec" / "adeu_benchmark_consumer_validation_report.schema.json",
        ),
    ]


def test_v46e_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative == mirror
        assert authoritative["properties"]["schema"]["const"] == expected_schema


@pytest.mark.parametrize(
    (
        "comparison_report_name",
        "comparison_validation_name",
        "case_name",
        "advisory_name",
        "validation_name",
        "consumer_label",
    ),
    [
        (
            "reference_cross_subject_comparison_report.json",
            "reference_cross_subject_comparison_validation_report.json",
            "reference_benchmark_consumer_case_architecture_difference_supported.json",
            "reference_benchmark_consumer_advisory_report_architecture_difference_supported.json",
            "reference_benchmark_consumer_validation_report_architecture_difference_supported.json",
            "reference_architecture_difference_supported",
        ),
        (
            "reference_cross_subject_comparison_report_mixed_or_cautionary.json",
            "reference_cross_subject_comparison_validation_report_mixed_or_cautionary.json",
            "reference_benchmark_consumer_case_mixed_or_cautionary.json",
            "reference_benchmark_consumer_advisory_report_mixed_or_cautionary.json",
            "reference_benchmark_consumer_validation_report_mixed_or_cautionary.json",
            "reference_mixed_or_cautionary",
        ),
        (
            "reference_cross_subject_comparison_report_insufficient_evidence.json",
            "reference_cross_subject_comparison_validation_report_insufficient_evidence.json",
            "reference_benchmark_consumer_case_insufficient_evidence.json",
            "reference_benchmark_consumer_advisory_report_insufficient_evidence.json",
            "reference_benchmark_consumer_validation_report_insufficient_evidence.json",
            "reference_insufficient_evidence",
        ),
    ],
)
def test_reference_consumer_bundle_matches_committed_fixtures(
    comparison_report_name: str,
    comparison_validation_name: str,
    case_name: str,
    advisory_name: str,
    validation_name: str,
    consumer_label: str,
) -> None:
    comparison_case = _load_json(V46D_FIXTURE_ROOT, "reference_cross_subject_comparison_case.json")
    comparison_report = _load_comparison_fixture(comparison_report_name)
    comparison_validation = _load_comparison_fixture(comparison_validation_name)
    expected_case = _load_json(V46E_FIXTURE_ROOT, case_name)
    expected_advisory = _load_json(V46E_FIXTURE_ROOT, advisory_name)
    expected_validation = _load_json(V46E_FIXTURE_ROOT, validation_name)

    consumer_case = derive_benchmark_consumer_case(
        comparison_case_payload=comparison_case,
        comparison_report_payload=comparison_report,
        comparison_validation_report_payload=comparison_validation,
        consumer_label=consumer_label,
    )
    evaluation = evaluate_benchmark_consumer_case(
        consumer_case_payload=consumer_case,
        comparison_case_payload=comparison_case,
        comparison_report_payload=comparison_report,
        comparison_validation_report_payload=comparison_validation,
    )

    assert consumer_case == expected_case
    assert evaluation["advisory_report"] == expected_advisory
    assert evaluation["validation_report"] == expected_validation


def test_reject_consumer_case_unsupported_target_fixture() -> None:
    payload = _load_json(
        V46E_FIXTURE_ROOT,
        "reject_benchmark_consumer_case_unsupported_target.json",
    )

    with pytest.raises(ValidationError, match="architecture_comparison_research"):
        BenchmarkConsumerCase.model_validate(payload)


def test_reject_consumer_case_mismatched_comparison_report_ref() -> None:
    comparison_case = _load_json(V46D_FIXTURE_ROOT, "reference_cross_subject_comparison_case.json")
    comparison_report = _load_json(
        V46D_FIXTURE_ROOT,
        "reference_cross_subject_comparison_report.json",
    )
    comparison_validation = _load_json(
        V46D_FIXTURE_ROOT,
        "reference_cross_subject_comparison_validation_report.json",
    )
    payload = _load_json(
        V46E_FIXTURE_ROOT,
        "reject_benchmark_consumer_case_mismatched_comparison_report_ref.json",
    )

    with pytest.raises(ValueError, match="consumer case must bind to released comparison report"):
        evaluate_benchmark_consumer_case(
            consumer_case_payload=payload,
            comparison_case_payload=comparison_case,
            comparison_report_payload=comparison_report,
            comparison_validation_report_payload=comparison_validation,
        )


def test_reject_advisory_report_mixed_comparison_report_refs() -> None:
    payload = _load_json(
        V46E_FIXTURE_ROOT,
        "reference_benchmark_consumer_advisory_report_architecture_difference_supported.json",
    )
    mixed_report = _load_json(
        V46E_FIXTURE_ROOT,
        "reference_cross_subject_comparison_report_mixed_or_cautionary.json",
    )

    assert isinstance(payload, dict)
    assert isinstance(mixed_report, dict)
    payload["supporting_comparison_field_refs"][0]["comparison_report_ref"] = mixed_report[
        "cross_subject_comparison_report_id"
    ]
    payload.pop("benchmark_consumer_advisory_report_id", None)

    with pytest.raises(
        ValueError,
        match="supporting_comparison_field_refs must bind to exactly one comparison_report_ref",
    ):
        materialize_benchmark_consumer_advisory_report_payload(payload)


def test_reject_validation_report_mixed_validation_report_refs() -> None:
    payload = _load_json(
        V46E_FIXTURE_ROOT,
        "reference_benchmark_consumer_validation_report_architecture_difference_supported.json",
    )
    mixed_validation = _load_json(
        V46E_FIXTURE_ROOT,
        "reference_cross_subject_comparison_validation_report_mixed_or_cautionary.json",
    )

    assert isinstance(payload, dict)
    assert isinstance(mixed_validation, dict)
    payload["supporting_validation_result_refs"][0]["comparison_validation_report_ref"] = (
        mixed_validation["cross_subject_comparison_validation_report_id"]
    )
    payload.pop("benchmark_consumer_validation_report_id", None)

    with pytest.raises(
        ValueError,
        match=(
            "supporting_validation_result_refs must bind to exactly one "
            "comparison_validation_report_ref"
        ),
    ):
        materialize_benchmark_consumer_validation_report_payload(payload)
