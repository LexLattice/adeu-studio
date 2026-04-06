from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_benchmarking import (
    ADEU_PROCEDURAL_DEPTH_BENCHMARK_VALIDATION_REPORT_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_FAILURE_TOPOLOGY_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_NON_REGRESSION_REPORT_SCHEMA,
    ADEU_PROCEDURAL_DEPTH_PERTURBATION_CASE_SCHEMA,
    ProceduralDepthNonRegressionReport,
    ProceduralDepthPerturbationCase,
    evaluate_procedural_depth_perturbation_bundle,
    evaluate_procedural_depth_perturbation_case,
    materialize_procedural_depth_run_trace_from_perturbation_case,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from pydantic import ValidationError

V46A_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v46a"
V46B_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v46b"
V46C_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v46c"


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _schema_pairs() -> list[tuple[str, Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return [
        (
            ADEU_PROCEDURAL_DEPTH_PERTURBATION_CASE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_perturbation_case.v1.json",
            root / "spec" / "adeu_procedural_depth_perturbation_case.schema.json",
        ),
        (
            ADEU_PROCEDURAL_DEPTH_FAILURE_TOPOLOGY_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_failure_topology.v1.json",
            root / "spec" / "adeu_procedural_depth_failure_topology.schema.json",
        ),
        (
            ADEU_PROCEDURAL_DEPTH_NON_REGRESSION_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_non_regression_report.v1.json",
            root / "spec" / "adeu_procedural_depth_non_regression_report.schema.json",
        ),
        (
            ADEU_PROCEDURAL_DEPTH_BENCHMARK_VALIDATION_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_procedural_depth_benchmark_validation_report.v1.json",
            root
            / "spec"
            / "adeu_procedural_depth_benchmark_validation_report.schema.json",
        ),
    ]


def _reference_case_fixture_names() -> list[str]:
    return [
        "reference_procedural_depth_perturbation_case_branch_shift.json",
        "reference_procedural_depth_perturbation_case_delayed_constraint.json",
        "reference_procedural_depth_perturbation_case_paraphrase_preserving.json",
    ]


def test_v46c_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative == mirror
        assert authoritative["properties"]["schema"]["const"] == expected_schema


def test_reference_perturbation_cases_replay_released_v46b_stack() -> None:
    context = _load_json(V46A_FIXTURE_ROOT, "reference_benchmark_execution_context.json")
    instance = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    gold = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_gold_trace.json")
    case_matrix = _load_json(V46C_FIXTURE_ROOT, "reference_v46c_case_matrix.json")

    assert isinstance(context, dict)
    assert isinstance(instance, dict)
    assert isinstance(gold, dict)
    assert isinstance(case_matrix, dict)

    rows = {
        row["perturbation_kind"]: row
        for row in case_matrix["case_rows"]
    }

    for fixture_name in _reference_case_fixture_names():
        case = _load_json(V46C_FIXTURE_ROOT, fixture_name)
        assert isinstance(case, dict)

        evaluation = evaluate_procedural_depth_perturbation_case(
            benchmark_execution_context_payload=context,
            instance_payload=instance,
            gold_trace_payload=gold,
            perturbation_case_payload=case,
        )
        row = rows[case["perturbation_kind"]]
        first_replay = evaluation["replay_results"][0]

        assert evaluation["observed_dominant_failure_family"] == row[
            "observed_dominant_failure_family"
        ]
        assert evaluation["observed_terminal_trace_status"] == row[
            "observed_terminal_trace_status"
        ]
        assert first_replay["run_trace"]["procedural_depth_run_trace_id"] == row["run_trace_ref"]
        assert first_replay["metrics"]["procedural_depth_metrics_id"] == row["metric_ref"]
        assert (
            first_replay["diagnostic_report"]["procedural_depth_diagnostic_report_id"]
            == row["diagnostic_report_ref"]
        )
        assert evaluation["deterministic_replay_confirmed"] is True
        assert evaluation["regression_detected"] is False


def test_reference_drift_run_trace_fixture_replays() -> None:
    instance = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    case = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_perturbation_case_paraphrase_preserving.json",
    )
    expected = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_run_trace_paraphrase_preserving_drift.json",
    )

    assert isinstance(instance, dict)
    assert isinstance(case, dict)
    assert isinstance(expected, dict)

    drift = materialize_procedural_depth_run_trace_from_perturbation_case(
        instance_payload=instance,
        perturbation_case_payload=case,
        run_trace_override_payload={
            "observed_output_summary": "Produced a paraphrased yet structure-preserving summary."
        },
    )

    assert drift == expected


def test_reference_bundle_reports_match_committed_stable_fixtures() -> None:
    context = _load_json(V46A_FIXTURE_ROOT, "reference_benchmark_execution_context.json")
    instance = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    gold = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_gold_trace.json")
    cases = [_load_json(V46C_FIXTURE_ROOT, name) for name in _reference_case_fixture_names()]
    expected_topology = _load_json(
        V46C_FIXTURE_ROOT, "reference_procedural_depth_failure_topology.json"
    )
    expected_non_regression = _load_json(
        V46C_FIXTURE_ROOT, "reference_procedural_depth_non_regression_report_stable.json"
    )
    expected_validation = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_benchmark_validation_report_stable.json",
    )

    bundle = evaluate_procedural_depth_perturbation_bundle(
        benchmark_execution_context_payload=context,
        instance_payload=instance,
        gold_trace_payload=gold,
        perturbation_case_payloads=cases,
    )

    assert bundle["failure_topology"] == expected_topology
    assert bundle["non_regression_report"] == expected_non_regression
    assert bundle["benchmark_validation_report"] == expected_validation


def test_reference_bundle_detects_regression_from_drifted_replay() -> None:
    context = _load_json(V46A_FIXTURE_ROOT, "reference_benchmark_execution_context.json")
    instance = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    gold = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_gold_trace.json")
    branch_case = _load_json(
        V46C_FIXTURE_ROOT, "reference_procedural_depth_perturbation_case_branch_shift.json"
    )
    delayed_case = _load_json(
        V46C_FIXTURE_ROOT, "reference_procedural_depth_perturbation_case_delayed_constraint.json"
    )
    paraphrase_case = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_perturbation_case_paraphrase_preserving.json",
    )
    drift_run = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_run_trace_paraphrase_preserving_drift.json",
    )
    expected_non_regression = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_non_regression_report_regression_detected.json",
    )
    expected_validation = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_benchmark_validation_report_regression_detected.json",
    )

    assert isinstance(paraphrase_case, dict)
    stable_paraphrase = materialize_procedural_depth_run_trace_from_perturbation_case(
        instance_payload=instance,
        perturbation_case_payload=paraphrase_case,
    )
    bundle = evaluate_procedural_depth_perturbation_bundle(
        benchmark_execution_context_payload=context,
        instance_payload=instance,
        gold_trace_payload=gold,
        perturbation_case_payloads=[branch_case, delayed_case, paraphrase_case],
        replay_run_trace_payloads_by_case_ref={
            paraphrase_case["procedural_depth_perturbation_case_id"]: [
                stable_paraphrase,
                drift_run,
                stable_paraphrase,
            ]
        },
    )

    assert bundle["non_regression_report"] == expected_non_regression
    assert bundle["benchmark_validation_report"] == expected_validation


def test_reject_unknown_override_case_refs_fail_closed() -> None:
    context = _load_json(V46A_FIXTURE_ROOT, "reference_benchmark_execution_context.json")
    instance = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    gold = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_gold_trace.json")
    cases = [_load_json(V46C_FIXTURE_ROOT, name) for name in _reference_case_fixture_names()]

    with pytest.raises(ValueError, match="unknown perturbation case refs"):
        evaluate_procedural_depth_perturbation_bundle(
            benchmark_execution_context_payload=context,
            instance_payload=instance,
            gold_trace_payload=gold,
            perturbation_case_payloads=cases,
            replay_run_trace_payloads_by_case_ref={
                "fixture:v46c/unknown_case_ref": [{}, {}, {}]
            },
        )


def test_validation_report_top_level_flag_fails_when_expectation_is_deterministically_wrong(
) -> None:
    context = _load_json(V46A_FIXTURE_ROOT, "reference_benchmark_execution_context.json")
    instance = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    gold = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_gold_trace.json")
    branch_case = _load_json(
        V46C_FIXTURE_ROOT, "reference_procedural_depth_perturbation_case_branch_shift.json"
    )

    assert isinstance(branch_case, dict)
    mismatched_case = dict(branch_case)
    mismatched_case.pop("procedural_depth_perturbation_case_id", None)
    mismatched_case["expected_dominant_failure_family"] = "mixed"

    bundle = evaluate_procedural_depth_perturbation_bundle(
        benchmark_execution_context_payload=context,
        instance_payload=instance,
        gold_trace_payload=gold,
        perturbation_case_payloads=[mismatched_case],
    )

    case_result = bundle["benchmark_validation_report"]["validation_case_results"][0]
    assert case_result["deterministic_replay_confirmed"] is True
    assert case_result["expected_dominant_failure_family"] == "mixed"
    assert case_result["observed_dominant_failure_family"] == "horizontal_plan_spine"
    assert bundle["benchmark_validation_report"]["deterministic_replay_confirmed"] is False


@pytest.mark.parametrize(
    ("model", "fixture_name"),
    [
        (
            ProceduralDepthPerturbationCase,
            "reject_procedural_depth_perturbation_case_paraphrase_missing_output_summary.json",
        ),
        (
            ProceduralDepthNonRegressionReport,
            "reject_procedural_depth_non_regression_report_replay_index_mismatch.json",
        ),
    ],
)
def test_reject_v46c_fixtures_fail_closed(model: object, fixture_name: str) -> None:
    fixture = _load_json(V46C_FIXTURE_ROOT, fixture_name)

    with pytest.raises(ValidationError):
        model.model_validate(fixture)
