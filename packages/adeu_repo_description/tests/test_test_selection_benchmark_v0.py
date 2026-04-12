from __future__ import annotations

import pytest
from adeu_repo_description import test_selection_benchmark_v0 as benchmark


def _pytest_result(
    *, executed: tuple[str, ...], failing: tuple[str, ...]
) -> benchmark.PytestRunResult:
    return benchmark.PytestRunResult(
        command=("pytest",),
        exit_code=1 if failing else 0,
        wall_time_seconds=1.0,
        junit_xml_path=None,
        executed_node_ids=executed,
        failing_node_ids=failing,
        outcome_counts={
            "passed": len(set(executed) - set(failing)),
            "failed": len(failing),
            "error": 0,
            "skipped": 0,
        },
        stdout_tail="",
        stderr_tail="",
    )


def test_parse_delta_rejects_file_level_targets_for_directory_tree() -> None:
    with pytest.raises(ValueError, match="directory_tree"):
        benchmark._parse_delta(
            {
                "delta_id": "bad_file_scope",
                "source_kind": "git_commit_pair",
                "base_revision": "abc",
                "changed_revision": "def",
                "category": "changed_test_file",
                "blast_radius": "narrow",
                "expected_blast_radius_intuition": "bad fixture",
                "target_scope_kind": "directory_tree",
                "target_scope_note": "should fail",
                "pytest_targets": ["apps/api/tests/test_recursive_coordinate_warning_lint.py"],
            }
        )


def test_compute_metrics_row_reports_selected_nonfailing_counts() -> None:
    delta = benchmark.DeltaSpec(
        delta_id="delta",
        source_kind="git_commit_pair",
        base_revision="abc",
        changed_revision="def",
        category="narrow_package_local_python_source_change",
        blast_radius="narrow",
        expected_blast_radius_intuition="narrow",
        eligibility=("cold", "warm"),
        target_scope_kind="directory_tree",
        target_scope_note="tests tree",
        pytest_targets=("packages/adeu_edge_ledger/tests",),
        changed_paths=("packages/adeu_edge_ledger/src/adeu_edge_ledger/probe_test_intent.py",),
        notes=None,
        synthetic_replace_operations=(),
    )
    ground_truth = _pytest_result(
        executed=("a::test_one", "a::test_two", "a::test_three"),
        failing=("a::test_two",),
    )
    adeu_execution = _pytest_result(
        executed=("a::test_one", "a::test_two"),
        failing=("a::test_two",),
    )
    testmon_execution = _pytest_result(
        executed=("a::test_two",),
        failing=("a::test_two",),
    )

    row = benchmark._compute_metrics_row(
        delta=delta,
        regime="warm",
        ground_truth=ground_truth,
        adeu_selector_time_seconds=0.5,
        adeu_execution=adeu_execution,
        testmon_overhead_seconds=0.25,
        testmon_execution=testmon_execution,
    )

    assert row["false_negative_count_adeu"] == 0
    assert row["false_negative_count_testmon"] == 0
    assert row["selected_nonfailing_count_adeu"] == 1
    assert row["selected_nonfailing_count_testmon"] == 0
