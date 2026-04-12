from __future__ import annotations

import sys
from pathlib import Path

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


def _benchmark_corpus_payload(*, changed_paths: list[str] | None) -> dict[str, object]:
    delta: dict[str, object] = {
        "delta_id": "delta_cleanup_probe",
        "source_kind": "git_commit_pair",
        "base_revision": "abc123",
        "changed_revision": "def456",
        "category": "narrow_package_local_python_source_change",
        "blast_radius": "narrow",
        "expected_blast_radius_intuition": "narrow probe",
        "target_scope_kind": "directory_tree",
        "target_scope_note": "cleanup probe",
        "pytest_targets": ["packages/adeu_repo_description/tests"],
    }
    if changed_paths is not None:
        delta["changed_paths"] = changed_paths
    return {"schema": benchmark.CORPUS_SCHEMA, "deltas": [delta]}


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


def test_run_pytest_raises_when_junit_output_is_missing(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    def _fake_run_command(
        *,
        command: list[str],
        cwd: Path,
        env: dict[str, str],
    ) -> benchmark.CommandResult:
        del cwd, env
        return benchmark.CommandResult(
            command=tuple(command),
            exit_code=2,
            wall_time_seconds=0.01,
            stdout_tail="",
            stderr_tail="pytest failed before junit write",
        )

    monkeypatch.setattr(benchmark, "_run_command", _fake_run_command)
    missing_junit_xml = tmp_path / "missing.xml"

    with pytest.raises(RuntimeError, match="did not produce expected junit xml"):
        benchmark._run_pytest(
            python_executable=Path(sys.executable),
            worktree_root=tmp_path,
            targets=["packages/adeu_repo_description/tests"],
            extra_args=[],
            env={},
            junit_xml_path=missing_junit_xml,
        )


def test_parse_args_defaults_python_executable_to_running_interpreter() -> None:
    namespace = benchmark._parse_args([])
    assert namespace.python_executable == Path(sys.executable)


@pytest.mark.parametrize(
    ("keep_worktrees", "expect_temp_root_exists_after_failure"),
    [(False, False), (True, True)],
)
def test_run_benchmark_temp_root_cleanup_on_worktree_add_failure(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    keep_worktrees: bool,
    expect_temp_root_exists_after_failure: bool,
) -> None:
    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    temp_root = tmp_path / "temp_root"
    temp_root.mkdir()

    monkeypatch.setattr(benchmark, "canonical_repo_root", lambda: repo_root)
    monkeypatch.setattr(
        benchmark,
        "_load_corpus",
        lambda _path: _benchmark_corpus_payload(
            changed_paths=["packages/adeu_repo_description/src/adeu_repo_description/x.py"]
        ),
    )
    monkeypatch.setattr(benchmark.tempfile, "mkdtemp", lambda prefix: temp_root.as_posix())

    def _fake_ensure_git_success(
        *,
        command: list[str],
        cwd: Path,
        env: dict[str, str],
    ) -> None:
        del cwd, env
        if command[:3] == ["git", "worktree", "add"]:
            raise RuntimeError("simulated worktree-add failure")

    monkeypatch.setattr(benchmark, "_ensure_git_success", _fake_ensure_git_success)

    with pytest.raises(RuntimeError, match="simulated worktree-add failure"):
        benchmark.run_benchmark(
            corpus_path=tmp_path / "corpus.json",
            output_dir=tmp_path / "out",
            python_executable=Path(sys.executable),
            keep_worktrees=keep_worktrees,
        )

    assert temp_root.exists() is expect_temp_root_exists_after_failure


@pytest.mark.parametrize(("keep_worktrees", "expect_remove_call"), [(False, True), (True, False)])
def test_run_benchmark_keep_worktrees_controls_forced_worktree_remove(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    keep_worktrees: bool,
    expect_remove_call: bool,
) -> None:
    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    temp_root = tmp_path / "temp_root"
    temp_root.mkdir()
    seen_git_commands: list[tuple[str, ...]] = []

    monkeypatch.setattr(benchmark, "canonical_repo_root", lambda: repo_root)
    monkeypatch.setattr(
        benchmark,
        "_load_corpus",
        lambda _path: _benchmark_corpus_payload(changed_paths=None),
    )
    monkeypatch.setattr(benchmark.tempfile, "mkdtemp", lambda prefix: temp_root.as_posix())

    def _fake_ensure_git_success(
        *,
        command: list[str],
        cwd: Path,
        env: dict[str, str],
    ) -> None:
        del cwd, env
        seen_git_commands.append(tuple(command))

    monkeypatch.setattr(benchmark, "_ensure_git_success", _fake_ensure_git_success)

    def _raise_after_add(**kwargs: object) -> list[str]:
        del kwargs
        raise RuntimeError("stop after add")

    monkeypatch.setattr(benchmark, "_discover_changed_paths_from_pair", _raise_after_add)

    with pytest.raises(RuntimeError, match="stop after add"):
        benchmark.run_benchmark(
            corpus_path=tmp_path / "corpus.json",
            output_dir=tmp_path / "out",
            python_executable=Path(sys.executable),
            keep_worktrees=keep_worktrees,
        )

    remove_was_called = any(
        command[:4] == ("git", "worktree", "remove", "--force") for command in seen_git_commands
    )
    assert remove_was_called is expect_remove_call
    assert temp_root.exists() is keep_worktrees
