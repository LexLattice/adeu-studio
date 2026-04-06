from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_benchmarking import (
    ADEU_BENCHMARK_SUBJECT_RECORD_SCHEMA,
    ADEU_CROSS_SUBJECT_COMPARISON_CASE_SCHEMA,
    ADEU_CROSS_SUBJECT_COMPARISON_REPORT_SCHEMA,
    ADEU_CROSS_SUBJECT_COMPARISON_VALIDATION_REPORT_SCHEMA,
    BenchmarkSubjectRecord,
    compute_benchmark_subject_record_id,
    compute_procedural_depth_diagnostic_report_id,
    compute_procedural_depth_metrics_id,
    derive_benchmark_subject_record,
    derive_cross_subject_comparison_case,
    evaluate_cross_subject_comparison_case,
    score_procedural_depth_run,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from pydantic import ValidationError

V46A_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v46a"
V46B_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v46b"
V46C_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v46c"
V46D_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v46d"


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _schema_pairs() -> list[tuple[str, Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return [
        (
            ADEU_BENCHMARK_SUBJECT_RECORD_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_benchmark_subject_record.v1.json",
            root / "spec" / "adeu_benchmark_subject_record.schema.json",
        ),
        (
            ADEU_CROSS_SUBJECT_COMPARISON_CASE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_cross_subject_comparison_case.v1.json",
            root / "spec" / "adeu_cross_subject_comparison_case.schema.json",
        ),
        (
            ADEU_CROSS_SUBJECT_COMPARISON_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_cross_subject_comparison_report.v1.json",
            root / "spec" / "adeu_cross_subject_comparison_report.schema.json",
        ),
        (
            ADEU_CROSS_SUBJECT_COMPARISON_VALIDATION_REPORT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "adeu_cross_subject_comparison_validation_report.v1.json",
            root / "spec" / "adeu_cross_subject_comparison_validation_report.schema.json",
        ),
    ]


def test_v46d_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative == mirror
        assert authoritative["properties"]["schema"]["const"] == expected_schema


def test_reference_cross_subject_comparison_matches_committed_fixtures() -> None:
    family = _load_json(V46A_FIXTURE_ROOT, "reference_benchmark_family_spec.json")
    projection = _load_json(V46A_FIXTURE_ROOT, "reference_benchmark_projection_spec.json")
    base_context = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_execution_context_base_model.json"
    )
    prompted_context = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_execution_context_prompted_model.json"
    )
    instance = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    gold = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_gold_trace.json")
    clean_run = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_run_trace_clean_success.json"
    )
    clean_metrics = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_metrics_clean_success.json"
    )
    clean_diagnostic = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_diagnostic_report_clean_success.json"
    )
    vertical_run = _load_json(
        V46B_FIXTURE_ROOT,
        "reference_procedural_depth_run_trace_vertical_active_step_compilation.json",
    )
    stable_non_regression = _load_json(
        V46C_FIXTURE_ROOT, "reference_procedural_depth_non_regression_report_stable.json"
    )
    stable_validation = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_benchmark_validation_report_stable.json",
    )
    regression_non_regression = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_non_regression_report_regression_detected.json",
    )
    regression_validation = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_benchmark_validation_report_regression_detected.json",
    )
    expected_base_subject = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_subject_record_base_model.json"
    )
    expected_prompted_subject = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_subject_record_prompted_model.json"
    )
    expected_case = _load_json(V46D_FIXTURE_ROOT, "reference_cross_subject_comparison_case.json")
    expected_report = _load_json(
        V46D_FIXTURE_ROOT, "reference_cross_subject_comparison_report.json"
    )
    expected_validation_report = _load_json(
        V46D_FIXTURE_ROOT, "reference_cross_subject_comparison_validation_report.json"
    )

    vertical_metrics, vertical_diagnostic = score_procedural_depth_run(
        instance_payload=instance,
        gold_trace_payload=gold,
        run_trace_payload=vertical_run,
    )
    base_subject = derive_benchmark_subject_record(
        benchmark_family_spec_payload=family,
        benchmark_projection_spec_payload=projection,
        benchmark_execution_context_payload=base_context,
        baseline_instance_payload=instance,
        baseline_run_trace_payload=clean_run,
        baseline_metrics_payload=clean_metrics,
        baseline_diagnostic_report_payload=clean_diagnostic,
        perturbation_non_regression_report_payload=stable_non_regression,
        perturbation_benchmark_validation_report_payload=stable_validation,
        subject_identity_ref="subject:v46d/base_model/reference",
        notes=["starter v46d base-model reference subject"],
    )
    prompted_subject = derive_benchmark_subject_record(
        benchmark_family_spec_payload=family,
        benchmark_projection_spec_payload=projection,
        benchmark_execution_context_payload=prompted_context,
        baseline_instance_payload=instance,
        baseline_run_trace_payload=vertical_run,
        baseline_metrics_payload=vertical_metrics,
        baseline_diagnostic_report_payload=vertical_diagnostic,
        perturbation_non_regression_report_payload=regression_non_regression,
        perturbation_benchmark_validation_report_payload=regression_validation,
        subject_identity_ref="subject:v46d/prompted_model/reference",
        notes=["starter v46d prompted-model reference subject"],
    )
    comparison_case = derive_cross_subject_comparison_case(
        left_subject_record_payload=base_subject,
        right_subject_record_payload=prompted_subject,
        comparison_label="reference_procedural_depth_base_vs_prompted",
        notes=["starter v46d deterministic subject-pair comparison case"],
    )
    evaluation = evaluate_cross_subject_comparison_case(
        comparison_case_payload=comparison_case,
        left_subject_record_payload=base_subject,
        right_subject_record_payload=prompted_subject,
        left_execution_context_payload=base_context,
        right_execution_context_payload=prompted_context,
        left_baseline_run_trace_payload=clean_run,
        right_baseline_run_trace_payload=vertical_run,
        left_baseline_metrics_payload=clean_metrics,
        right_baseline_metrics_payload=vertical_metrics,
        left_baseline_diagnostic_report_payload=clean_diagnostic,
        right_baseline_diagnostic_report_payload=vertical_diagnostic,
        left_perturbation_non_regression_report_payload=stable_non_regression,
        right_perturbation_non_regression_report_payload=regression_non_regression,
        left_perturbation_benchmark_validation_report_payload=stable_validation,
        right_perturbation_benchmark_validation_report_payload=regression_validation,
    )

    assert base_subject == expected_base_subject
    assert prompted_subject == expected_prompted_subject
    assert comparison_case == expected_case
    assert evaluation["comparison_report"] == expected_report
    assert evaluation["comparison_validation_report"] == expected_validation_report


def test_reject_subject_record_unsupported_subject_class_fixture() -> None:
    family = _load_json(V46A_FIXTURE_ROOT, "reference_benchmark_family_spec.json")
    projection = _load_json(V46A_FIXTURE_ROOT, "reference_benchmark_projection_spec.json")
    payload = _load_json(
        V46D_FIXTURE_ROOT,
        "reject_benchmark_execution_context_unsupported_subject_class.json",
    )
    instance = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    clean_run = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_run_trace_clean_success.json"
    )
    clean_metrics = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_metrics_clean_success.json"
    )
    clean_diagnostic = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_diagnostic_report_clean_success.json"
    )
    stable_non_regression = _load_json(
        V46C_FIXTURE_ROOT, "reference_procedural_depth_non_regression_report_stable.json"
    )
    stable_validation = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_benchmark_validation_report_stable.json",
    )

    with pytest.raises(
        ValueError,
        match="only admits base_model and prompted_model subject classes",
    ):
        derive_benchmark_subject_record(
            benchmark_family_spec_payload=family,
            benchmark_projection_spec_payload=projection,
            benchmark_execution_context_payload=payload,
            baseline_instance_payload=instance,
            baseline_run_trace_payload=clean_run,
            baseline_metrics_payload=clean_metrics,
            baseline_diagnostic_report_payload=clean_diagnostic,
            perturbation_non_regression_report_payload=stable_non_regression,
            perturbation_benchmark_validation_report_payload=stable_validation,
            subject_identity_ref="subject:v46d/reject_unsupported_subject_class",
        )


def test_reject_subject_record_mismatched_perturbation_bundle_fixture() -> None:
    payload = _load_json(
        V46D_FIXTURE_ROOT,
        "reject_benchmark_subject_record_mismatched_perturbation_bundle.json",
    )

    with pytest.raises(
        ValidationError,
        match="perturbation_bundle_ref must match canonical bundle identity",
    ):
        BenchmarkSubjectRecord.model_validate(payload)


def test_reject_cross_subject_comparison_on_incompatible_context_repo_snapshot() -> None:
    family = _load_json(V46A_FIXTURE_ROOT, "reference_benchmark_family_spec.json")
    projection = _load_json(V46A_FIXTURE_ROOT, "reference_benchmark_projection_spec.json")
    base_subject = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_subject_record_base_model.json"
    )
    base_context = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_execution_context_base_model.json"
    )
    bad_prompted_context = _load_json(
        V46D_FIXTURE_ROOT,
        "reject_benchmark_execution_context_prompted_model_repo_snapshot_mismatch.json",
    )
    clean_run = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_run_trace_clean_success.json"
    )
    clean_metrics = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_metrics_clean_success.json"
    )
    clean_diagnostic = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_diagnostic_report_clean_success.json"
    )
    vertical_run = _load_json(
        V46B_FIXTURE_ROOT,
        "reference_procedural_depth_run_trace_vertical_active_step_compilation.json",
    )
    instance = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    gold = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_gold_trace.json")
    vertical_metrics, vertical_diagnostic = score_procedural_depth_run(
        instance_payload=instance,
        gold_trace_payload=gold,
        run_trace_payload=vertical_run,
    )
    stable_non_regression = _load_json(
        V46C_FIXTURE_ROOT, "reference_procedural_depth_non_regression_report_stable.json"
    )
    stable_validation = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_benchmark_validation_report_stable.json",
    )
    regression_non_regression = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_non_regression_report_regression_detected.json",
    )
    regression_validation = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_benchmark_validation_report_regression_detected.json",
    )
    bad_prompted_subject = derive_benchmark_subject_record(
        benchmark_family_spec_payload=family,
        benchmark_projection_spec_payload=projection,
        benchmark_execution_context_payload=bad_prompted_context,
        baseline_instance_payload=instance,
        baseline_run_trace_payload=vertical_run,
        baseline_metrics_payload=vertical_metrics,
        baseline_diagnostic_report_payload=vertical_diagnostic,
        perturbation_non_regression_report_payload=regression_non_regression,
        perturbation_benchmark_validation_report_payload=regression_validation,
        subject_identity_ref="subject:v46d/prompted_model_repo_snapshot_mismatch",
    )
    comparison_case = derive_cross_subject_comparison_case(
        left_subject_record_payload=base_subject,
        right_subject_record_payload=bad_prompted_subject,
        comparison_label="v46d_repo_snapshot_mismatch",
    )

    with pytest.raises(ValueError, match="execution contexts must match on repo_snapshot_ref"):
        evaluate_cross_subject_comparison_case(
            comparison_case_payload=comparison_case,
            left_subject_record_payload=base_subject,
            right_subject_record_payload=bad_prompted_subject,
            left_execution_context_payload=base_context,
            right_execution_context_payload=bad_prompted_context,
            left_baseline_run_trace_payload=clean_run,
            right_baseline_run_trace_payload=vertical_run,
            left_baseline_metrics_payload=clean_metrics,
            right_baseline_metrics_payload=vertical_metrics,
            left_baseline_diagnostic_report_payload=clean_diagnostic,
            right_baseline_diagnostic_report_payload=vertical_diagnostic,
            left_perturbation_non_regression_report_payload=stable_non_regression,
            right_perturbation_non_regression_report_payload=regression_non_regression,
            left_perturbation_benchmark_validation_report_payload=stable_validation,
            right_perturbation_benchmark_validation_report_payload=regression_validation,
        )


def test_reject_cross_subject_comparison_on_mismatched_projection_spec_fixture() -> None:
    base_subject = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_subject_record_base_model.json"
    )
    with pytest.raises(
        ValueError, match="starter pair must share one released benchmark projection spec"
    ):
        derive_cross_subject_comparison_case(
            left_subject_record_payload=base_subject,
            right_subject_record_payload=_load_json(
                V46D_FIXTURE_ROOT,
                "reject_benchmark_subject_record_mismatched_projection_spec_ref.json",
            ),
            comparison_label="reject_projection_mismatch",
        )


def test_reject_cross_subject_comparison_on_subject_class_context_mismatch() -> None:
    base_subject = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_subject_record_base_model.json"
    )
    prompted_subject = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_subject_record_prompted_model.json"
    )
    base_context = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_execution_context_base_model.json"
    )
    prompted_context = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_execution_context_prompted_model.json"
    )
    clean_run = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_run_trace_clean_success.json"
    )
    clean_metrics = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_metrics_clean_success.json"
    )
    clean_diagnostic = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_diagnostic_report_clean_success.json"
    )
    vertical_run = _load_json(
        V46B_FIXTURE_ROOT,
        "reference_procedural_depth_run_trace_vertical_active_step_compilation.json",
    )
    instance = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    gold = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_gold_trace.json")
    vertical_metrics, vertical_diagnostic = score_procedural_depth_run(
        instance_payload=instance,
        gold_trace_payload=gold,
        run_trace_payload=vertical_run,
    )
    stable_non_regression = _load_json(
        V46C_FIXTURE_ROOT, "reference_procedural_depth_non_regression_report_stable.json"
    )
    stable_validation = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_benchmark_validation_report_stable.json",
    )
    regression_non_regression = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_non_regression_report_regression_detected.json",
    )
    regression_validation = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_benchmark_validation_report_regression_detected.json",
    )

    mismatched_prompted_subject = dict(prompted_subject)
    mismatched_prompted_subject["subject_class"] = "base_model"
    mismatched_prompted_subject["benchmark_subject_record_id"] = (
        compute_benchmark_subject_record_id(mismatched_prompted_subject)
    )
    comparison_case = derive_cross_subject_comparison_case(
        left_subject_record_payload=base_subject,
        right_subject_record_payload=mismatched_prompted_subject,
        comparison_label="reject_subject_class_context_mismatch",
    )

    with pytest.raises(
        ValueError,
        match="right subject_class must match bound execution context subject_under_test_class",
    ):
        evaluate_cross_subject_comparison_case(
            comparison_case_payload=comparison_case,
            left_subject_record_payload=base_subject,
            right_subject_record_payload=mismatched_prompted_subject,
            left_execution_context_payload=base_context,
            right_execution_context_payload=prompted_context,
            left_baseline_run_trace_payload=clean_run,
            right_baseline_run_trace_payload=vertical_run,
            left_baseline_metrics_payload=clean_metrics,
            right_baseline_metrics_payload=vertical_metrics,
            left_baseline_diagnostic_report_payload=clean_diagnostic,
            right_baseline_diagnostic_report_payload=vertical_diagnostic,
            left_perturbation_non_regression_report_payload=stable_non_regression,
            right_perturbation_non_regression_report_payload=regression_non_regression,
            left_perturbation_benchmark_validation_report_payload=stable_validation,
            right_perturbation_benchmark_validation_report_payload=regression_validation,
        )


def test_reject_cross_subject_comparison_on_metric_run_trace_chain_mismatch() -> None:
    base_subject = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_subject_record_base_model.json"
    )
    prompted_subject = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_subject_record_prompted_model.json"
    )
    base_context = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_execution_context_base_model.json"
    )
    prompted_context = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_execution_context_prompted_model.json"
    )
    clean_run = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_run_trace_clean_success.json"
    )
    clean_metrics = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_metrics_clean_success.json"
    )
    clean_diagnostic = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_diagnostic_report_clean_success.json"
    )
    vertical_run = _load_json(
        V46B_FIXTURE_ROOT,
        "reference_procedural_depth_run_trace_vertical_active_step_compilation.json",
    )
    instance = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    gold = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_gold_trace.json")
    vertical_metrics, vertical_diagnostic = score_procedural_depth_run(
        instance_payload=instance,
        gold_trace_payload=gold,
        run_trace_payload=vertical_run,
    )
    stable_non_regression = _load_json(
        V46C_FIXTURE_ROOT, "reference_procedural_depth_non_regression_report_stable.json"
    )
    stable_validation = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_benchmark_validation_report_stable.json",
    )
    regression_non_regression = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_non_regression_report_regression_detected.json",
    )
    regression_validation = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_benchmark_validation_report_regression_detected.json",
    )

    bad_metrics = dict(clean_metrics)
    bad_metrics["procedural_depth_run_trace_ref"] = vertical_run["procedural_depth_run_trace_id"]
    bad_metrics["procedural_depth_metrics_id"] = compute_procedural_depth_metrics_id(bad_metrics)
    bad_diagnostic = dict(clean_diagnostic)
    bad_diagnostic["procedural_depth_metrics_ref"] = bad_metrics["procedural_depth_metrics_id"]
    bad_diagnostic["procedural_depth_diagnostic_report_id"] = (
        compute_procedural_depth_diagnostic_report_id(bad_diagnostic)
    )
    bad_base_subject = dict(base_subject)
    bad_base_subject["baseline_metric_ref"] = bad_metrics["procedural_depth_metrics_id"]
    bad_base_subject["baseline_diagnostic_report_ref"] = bad_diagnostic[
        "procedural_depth_diagnostic_report_id"
    ]
    bad_base_subject["benchmark_subject_record_id"] = compute_benchmark_subject_record_id(
        bad_base_subject
    )
    comparison_case = derive_cross_subject_comparison_case(
        left_subject_record_payload=bad_base_subject,
        right_subject_record_payload=prompted_subject,
        comparison_label="reject_metric_chain_mismatch",
    )

    with pytest.raises(
        ValueError,
        match="left baseline metrics must bind to left baseline run trace",
    ):
        evaluate_cross_subject_comparison_case(
            comparison_case_payload=comparison_case,
            left_subject_record_payload=bad_base_subject,
            right_subject_record_payload=prompted_subject,
            left_execution_context_payload=base_context,
            right_execution_context_payload=prompted_context,
            left_baseline_run_trace_payload=clean_run,
            right_baseline_run_trace_payload=vertical_run,
            left_baseline_metrics_payload=bad_metrics,
            right_baseline_metrics_payload=vertical_metrics,
            left_baseline_diagnostic_report_payload=bad_diagnostic,
            right_baseline_diagnostic_report_payload=vertical_diagnostic,
            left_perturbation_non_regression_report_payload=stable_non_regression,
            right_perturbation_non_regression_report_payload=regression_non_regression,
            left_perturbation_benchmark_validation_report_payload=stable_validation,
            right_perturbation_benchmark_validation_report_payload=regression_validation,
        )


def test_reject_cross_subject_comparison_on_diagnostic_chain_mismatch() -> None:
    base_subject = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_subject_record_base_model.json"
    )
    prompted_subject = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_subject_record_prompted_model.json"
    )
    base_context = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_execution_context_base_model.json"
    )
    prompted_context = _load_json(
        V46D_FIXTURE_ROOT, "reference_benchmark_execution_context_prompted_model.json"
    )
    clean_run = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_run_trace_clean_success.json"
    )
    clean_metrics = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_metrics_clean_success.json"
    )
    clean_diagnostic = _load_json(
        V46B_FIXTURE_ROOT, "reference_procedural_depth_diagnostic_report_clean_success.json"
    )
    vertical_run = _load_json(
        V46B_FIXTURE_ROOT,
        "reference_procedural_depth_run_trace_vertical_active_step_compilation.json",
    )
    instance = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_instance.json")
    gold = _load_json(V46B_FIXTURE_ROOT, "reference_procedural_depth_gold_trace.json")
    vertical_metrics, vertical_diagnostic = score_procedural_depth_run(
        instance_payload=instance,
        gold_trace_payload=gold,
        run_trace_payload=vertical_run,
    )
    stable_non_regression = _load_json(
        V46C_FIXTURE_ROOT, "reference_procedural_depth_non_regression_report_stable.json"
    )
    stable_validation = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_benchmark_validation_report_stable.json",
    )
    regression_non_regression = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_non_regression_report_regression_detected.json",
    )
    regression_validation = _load_json(
        V46C_FIXTURE_ROOT,
        "reference_procedural_depth_benchmark_validation_report_regression_detected.json",
    )

    bad_diagnostic = dict(clean_diagnostic)
    bad_diagnostic["procedural_depth_run_trace_ref"] = vertical_run[
        "procedural_depth_run_trace_id"
    ]
    bad_diagnostic["procedural_depth_diagnostic_report_id"] = (
        compute_procedural_depth_diagnostic_report_id(bad_diagnostic)
    )
    bad_base_subject = dict(base_subject)
    bad_base_subject["baseline_diagnostic_report_ref"] = bad_diagnostic[
        "procedural_depth_diagnostic_report_id"
    ]
    bad_base_subject["benchmark_subject_record_id"] = compute_benchmark_subject_record_id(
        bad_base_subject
    )
    comparison_case = derive_cross_subject_comparison_case(
        left_subject_record_payload=bad_base_subject,
        right_subject_record_payload=prompted_subject,
        comparison_label="reject_diagnostic_chain_mismatch",
    )

    with pytest.raises(
        ValueError,
        match="left baseline diagnostic must bind to left baseline run trace",
    ):
        evaluate_cross_subject_comparison_case(
            comparison_case_payload=comparison_case,
            left_subject_record_payload=bad_base_subject,
            right_subject_record_payload=prompted_subject,
            left_execution_context_payload=base_context,
            right_execution_context_payload=prompted_context,
            left_baseline_run_trace_payload=clean_run,
            right_baseline_run_trace_payload=vertical_run,
            left_baseline_metrics_payload=clean_metrics,
            right_baseline_metrics_payload=vertical_metrics,
            left_baseline_diagnostic_report_payload=bad_diagnostic,
            right_baseline_diagnostic_report_payload=vertical_diagnostic,
            left_perturbation_non_regression_report_payload=stable_non_regression,
            right_perturbation_non_regression_report_payload=regression_non_regression,
            left_perturbation_benchmark_validation_report_payload=stable_validation,
            right_perturbation_benchmark_validation_report_payload=regression_validation,
        )
