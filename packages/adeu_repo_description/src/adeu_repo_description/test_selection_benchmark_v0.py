from __future__ import annotations

import argparse
import csv
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Literal

from adeu_ir.repo import repo_root as canonical_repo_root

from .test_selection_v0 import select_python_tests_v0

CORPUS_SCHEMA = "adeu_test_selection_ab_corpus@2"
RUNS_SCHEMA = "adeu_test_selection_ab_benchmark_runs@2"
SUMMARY_SCHEMA = "adeu_test_selection_ab_benchmark_summary@2"
MAX_STDIO_TAIL_CHARS = 4000


@dataclass(frozen=True)
class SyntheticReplaceOperation:
    file_path: str
    find: str
    replace: str
    reason: str


@dataclass(frozen=True)
class DeltaSpec:
    delta_id: str
    source_kind: Literal["git_commit_pair", "synthetic_patch"]
    base_revision: str
    changed_revision: str
    category: str
    blast_radius: Literal["narrow", "broad"]
    expected_blast_radius_intuition: str
    eligibility: tuple[Literal["cold", "warm"], ...]
    target_scope_kind: Literal["directory_tree", "mixed_tree"]
    target_scope_note: str
    pytest_targets: tuple[str, ...]
    changed_paths: tuple[str, ...] | None
    notes: str | None
    synthetic_replace_operations: tuple[SyntheticReplaceOperation, ...]


@dataclass(frozen=True)
class CommandResult:
    command: tuple[str, ...]
    exit_code: int
    wall_time_seconds: float
    stdout_tail: str
    stderr_tail: str


@dataclass(frozen=True)
class PytestRunResult:
    command: tuple[str, ...]
    exit_code: int
    wall_time_seconds: float
    junit_xml_path: str | None
    executed_node_ids: tuple[str, ...]
    failing_node_ids: tuple[str, ...]
    outcome_counts: dict[str, int]
    stdout_tail: str
    stderr_tail: str


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _tail(value: str, *, max_chars: int = MAX_STDIO_TAIL_CHARS) -> str:
    if len(value) <= max_chars:
        return value
    return value[-max_chars:]


def _run_command(
    *,
    command: list[str],
    cwd: Path,
    env: dict[str, str],
) -> CommandResult:
    started = time.perf_counter()
    completed = subprocess.run(
        command,
        cwd=cwd,
        env=env,
        check=False,
        text=True,
        capture_output=True,
    )
    elapsed = time.perf_counter() - started
    return CommandResult(
        command=tuple(command),
        exit_code=completed.returncode,
        wall_time_seconds=elapsed,
        stdout_tail=_tail(completed.stdout),
        stderr_tail=_tail(completed.stderr),
    )


def _parse_junit_xml(path: Path) -> tuple[tuple[str, ...], tuple[str, ...], dict[str, int]]:
    if not path.exists():
        return (), (), {"passed": 0, "failed": 0, "error": 0, "skipped": 0}

    tree = ET.parse(path)
    root = tree.getroot()
    executed: list[str] = []
    failing: list[str] = []
    counts = {"passed": 0, "failed": 0, "error": 0, "skipped": 0}
    for node in root.iter("testcase"):
        classname = node.attrib.get("classname", "")
        name = node.attrib.get("name", "")
        node_id = f"{classname}::{name}" if classname else name
        outcome = "passed"
        if node.find("failure") is not None:
            outcome = "failed"
        elif node.find("error") is not None:
            outcome = "error"
        elif node.find("skipped") is not None:
            outcome = "skipped"
        counts[outcome] += 1
        executed.append(node_id)
        if outcome in {"failed", "error"}:
            failing.append(node_id)
    return tuple(executed), tuple(failing), counts


def _run_pytest(
    *,
    python_executable: Path,
    worktree_root: Path,
    targets: list[str],
    extra_args: list[str],
    env: dict[str, str],
    junit_xml_path: Path | None,
) -> PytestRunResult:
    command = [str(python_executable), "-m", "pytest", "-q", *extra_args, *targets]
    if junit_xml_path is not None:
        command.extend(["--junitxml", str(junit_xml_path)])
    result = _run_command(command=command, cwd=worktree_root, env=env)
    executed: tuple[str, ...] = ()
    failing: tuple[str, ...] = ()
    outcome_counts: dict[str, int] = {"passed": 0, "failed": 0, "error": 0, "skipped": 0}
    if junit_xml_path is not None:
        executed, failing, outcome_counts = _parse_junit_xml(junit_xml_path)
    return PytestRunResult(
        command=result.command,
        exit_code=result.exit_code,
        wall_time_seconds=result.wall_time_seconds,
        junit_xml_path=(junit_xml_path.as_posix() if junit_xml_path is not None else None),
        executed_node_ids=executed,
        failing_node_ids=failing,
        outcome_counts=outcome_counts,
        stdout_tail=result.stdout_tail,
        stderr_tail=result.stderr_tail,
    )


def _build_pythonpath(repo_root: Path) -> str:
    source_roots = sorted((repo_root / "packages").glob("*/src"))
    source_roots.extend(sorted((repo_root / "apps").glob("*/src")))
    normalized = [path.as_posix() for path in source_roots if path.is_dir()]
    return os.pathsep.join(normalized)


def _build_env_for_repo(*, repo_root: Path) -> dict[str, str]:
    env = dict(os.environ)
    env["PYTHONHASHSEED"] = "0"
    env["TZ"] = "UTC"
    env["LC_ALL"] = "C"
    repo_pythonpath = _build_pythonpath(repo_root)
    prior_pythonpath = env.get("PYTHONPATH")
    if prior_pythonpath:
        env["PYTHONPATH"] = os.pathsep.join([repo_pythonpath, prior_pythonpath])
    else:
        env["PYTHONPATH"] = repo_pythonpath
    env.pop("PYTEST_ADDOPTS", None)
    return env


def _remove_testmon_state(worktree_root: Path) -> None:
    for path in worktree_root.glob(".testmondata*"):
        if path.is_dir():
            shutil.rmtree(path)
        elif path.exists():
            path.unlink()


def _ensure_git_success(
    *,
    command: list[str],
    cwd: Path,
    env: dict[str, str],
) -> None:
    result = _run_command(command=command, cwd=cwd, env=env)
    if result.exit_code != 0:
        raise RuntimeError(
            "git command failed: "
            + " ".join(command)
            + "\nSTDOUT:\n"
            + result.stdout_tail
            + "\nSTDERR:\n"
            + result.stderr_tail
        )


def _checkout_revision(
    *,
    worktree_root: Path,
    revision: str,
    env: dict[str, str],
) -> None:
    _ensure_git_success(
        command=["git", "checkout", "--detach", revision],
        cwd=worktree_root,
        env=env,
    )


def _discover_changed_paths_from_pair(
    *,
    worktree_root: Path,
    base_revision: str,
    changed_revision: str,
    env: dict[str, str],
) -> list[str]:
    completed = subprocess.run(
        ["git", "diff", "--name-only", base_revision, changed_revision],
        cwd=worktree_root,
        env=env,
        check=False,
        text=True,
        capture_output=True,
    )
    if completed.returncode != 0:
        raise RuntimeError(
            "failed to discover changed paths for pair "
            f"{base_revision}..{changed_revision}: {_tail(completed.stderr)}"
        )
    return sorted({line.strip() for line in completed.stdout.splitlines() if line.strip()})


def _path_is_in_targets(path: str, targets: tuple[str, ...]) -> bool:
    for target in targets:
        normalized_target = target.rstrip("/")
        if normalized_target.endswith(".py"):
            if path == normalized_target:
                return True
        else:
            if path == normalized_target or path.startswith(f"{normalized_target}/"):
                return True
    return False


def _filter_selected_paths_to_targets(
    *,
    selected_test_paths: list[str],
    targets: tuple[str, ...],
) -> list[str]:
    return sorted(
        {
            path
            for path in selected_test_paths
            if _path_is_in_targets(path, targets)
        }
    )


def _apply_synthetic_replace_operations(
    *,
    worktree_root: Path,
    operations: tuple[SyntheticReplaceOperation, ...],
) -> list[str]:
    touched_paths: list[str] = []
    for operation in operations:
        file_path = worktree_root / operation.file_path
        original_text = file_path.read_text(encoding="utf-8")
        if operation.find not in original_text:
            raise ValueError(
                "synthetic replace operation target not found: "
                f"{operation.file_path} ({operation.reason})"
            )
        updated_text = original_text.replace(operation.find, operation.replace, 1)
        file_path.write_text(updated_text, encoding="utf-8")
        touched_paths.append(operation.file_path)
    return sorted(set(touched_paths))


def _empty_pytest_result(*, reason: str) -> PytestRunResult:
    return PytestRunResult(
        command=(),
        exit_code=0,
        wall_time_seconds=0.0,
        junit_xml_path=None,
        executed_node_ids=(),
        failing_node_ids=(),
        outcome_counts={"passed": 0, "failed": 0, "error": 0, "skipped": 0},
        stdout_tail="",
        stderr_tail=reason,
    )


def _compute_metrics_row(
    *,
    delta: DeltaSpec,
    regime: Literal["cold", "warm"],
    ground_truth: PytestRunResult,
    adeu_selector_time_seconds: float,
    adeu_execution: PytestRunResult,
    testmon_overhead_seconds: float,
    testmon_execution: PytestRunResult,
) -> dict[str, Any]:
    full_failing = set(ground_truth.failing_node_ids)
    adeu_executed = set(adeu_execution.executed_node_ids)
    testmon_executed = set(testmon_execution.executed_node_ids)

    total_full_tests = len(ground_truth.executed_node_ids)
    total_selected_tests_adeu = len(adeu_execution.executed_node_ids)
    total_selected_tests_testmon = len(testmon_execution.executed_node_ids)

    adeu_false_negatives = len(full_failing - adeu_executed)
    testmon_false_negatives = len(full_failing - testmon_executed)
    adeu_selected_nonfailing = len(adeu_executed - full_failing)
    testmon_selected_nonfailing = len(testmon_executed - full_failing)

    adeu_selected_fraction = (
        total_selected_tests_adeu / total_full_tests if total_full_tests else 0.0
    )
    testmon_selected_fraction = (
        total_selected_tests_testmon / total_full_tests if total_full_tests else 0.0
    )

    return {
        "delta_id": delta.delta_id,
        "category": delta.category,
        "blast_radius": delta.blast_radius,
        "regime": regime,
        "total_full_tests": total_full_tests,
        "total_selected_tests_adeu": total_selected_tests_adeu,
        "total_selected_tests_testmon": total_selected_tests_testmon,
        "selector_time_adeu": round(adeu_selector_time_seconds, 6),
        "selector_or_overhead_time_testmon": round(testmon_overhead_seconds, 6),
        "execution_time_selected_adeu": round(adeu_execution.wall_time_seconds, 6),
        "execution_time_selected_testmon": round(testmon_execution.wall_time_seconds, 6),
        "total_time_adeu": round(
            adeu_selector_time_seconds + adeu_execution.wall_time_seconds,
            6,
        ),
        "total_time_testmon": round(
            testmon_overhead_seconds + testmon_execution.wall_time_seconds,
            6,
        ),
        "total_time_full": round(ground_truth.wall_time_seconds, 6),
        "selected_fraction_adeu": round(adeu_selected_fraction, 6),
        "selected_fraction_testmon": round(testmon_selected_fraction, 6),
        "false_negative_count_adeu": adeu_false_negatives,
        "false_negative_count_testmon": testmon_false_negatives,
        "selected_nonfailing_count_adeu": adeu_selected_nonfailing,
        "selected_nonfailing_count_testmon": testmon_selected_nonfailing,
        "safety_pass_adeu": adeu_false_negatives == 0,
        "safety_pass_testmon": testmon_false_negatives == 0,
        "ground_truth_exit_code": ground_truth.exit_code,
        "adeu_exit_code": adeu_execution.exit_code,
        "testmon_exit_code": testmon_execution.exit_code,
    }


def _aggregate_metric_rows(rows: list[dict[str, Any]]) -> dict[str, Any]:
    if not rows:
        return {
            "row_count": 0,
            "total_full_tests": 0,
            "total_selected_tests_adeu": 0,
            "total_selected_tests_testmon": 0,
            "selector_time_adeu": 0.0,
            "selector_or_overhead_time_testmon": 0.0,
            "execution_time_selected_adeu": 0.0,
            "execution_time_selected_testmon": 0.0,
            "total_time_adeu": 0.0,
            "total_time_testmon": 0.0,
            "total_time_full": 0.0,
            "selected_fraction_adeu": 0.0,
            "selected_fraction_testmon": 0.0,
            "false_negative_count_adeu": 0,
            "false_negative_count_testmon": 0,
            "selected_nonfailing_count_adeu": 0,
            "selected_nonfailing_count_testmon": 0,
            "safety_pass_adeu": True,
            "safety_pass_testmon": True,
        }

    summed_int_fields = [
        "total_full_tests",
        "total_selected_tests_adeu",
        "total_selected_tests_testmon",
        "false_negative_count_adeu",
        "false_negative_count_testmon",
        "selected_nonfailing_count_adeu",
        "selected_nonfailing_count_testmon",
    ]
    summed_float_fields = [
        "selector_time_adeu",
        "selector_or_overhead_time_testmon",
        "execution_time_selected_adeu",
        "execution_time_selected_testmon",
        "total_time_adeu",
        "total_time_testmon",
        "total_time_full",
    ]

    aggregate: dict[str, Any] = {"row_count": len(rows)}
    for field_name in summed_int_fields:
        aggregate[field_name] = sum(int(row[field_name]) for row in rows)
    for field_name in summed_float_fields:
        aggregate[field_name] = round(sum(float(row[field_name]) for row in rows), 6)

    full_count = aggregate["total_full_tests"]
    if full_count:
        aggregate["selected_fraction_adeu"] = round(
            aggregate["total_selected_tests_adeu"] / full_count,
            6,
        )
        aggregate["selected_fraction_testmon"] = round(
            aggregate["total_selected_tests_testmon"] / full_count,
            6,
        )
    else:
        aggregate["selected_fraction_adeu"] = 0.0
        aggregate["selected_fraction_testmon"] = 0.0
    aggregate["safety_pass_adeu"] = aggregate["false_negative_count_adeu"] == 0
    aggregate["safety_pass_testmon"] = aggregate["false_negative_count_testmon"] == 0
    return aggregate


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _load_corpus(corpus_path: Path) -> dict[str, Any]:
    payload = json.loads(corpus_path.read_text(encoding="utf-8"))
    if payload.get("schema") != CORPUS_SCHEMA:
        raise ValueError(
            f"unsupported corpus schema: {payload.get('schema')!r}; expected {CORPUS_SCHEMA!r}"
        )
    return payload


def _parse_delta(raw: dict[str, Any]) -> DeltaSpec:
    replace_ops: list[SyntheticReplaceOperation] = []
    for operation in raw.get("synthetic_replace_operations", []):
        replace_ops.append(
            SyntheticReplaceOperation(
                file_path=operation["file_path"],
                find=operation["find"],
                replace=operation["replace"],
                reason=operation.get("reason", "synthetic calibration replacement"),
            )
        )
    eligibility = tuple(raw.get("eligibility", ["cold", "warm"]))
    target_scope_kind = raw.get("target_scope_kind", "directory_tree")
    pytest_targets = tuple(raw["pytest_targets"])
    if target_scope_kind == "directory_tree" and any(
        target.endswith(".py") for target in pytest_targets
    ):
        raise ValueError(
            f"delta {raw['delta_id']} declares target_scope_kind=directory_tree "
            "but includes file-level pytest targets"
        )
    if target_scope_kind not in {"directory_tree", "mixed_tree"}:
        raise ValueError(
            f"delta {raw['delta_id']} has unsupported target_scope_kind={target_scope_kind!r}"
        )
    return DeltaSpec(
        delta_id=raw["delta_id"],
        source_kind=raw["source_kind"],
        base_revision=raw["base_revision"],
        changed_revision=raw["changed_revision"],
        category=raw["category"],
        blast_radius=raw["blast_radius"],
        expected_blast_radius_intuition=raw["expected_blast_radius_intuition"],
        eligibility=eligibility,
        target_scope_kind=target_scope_kind,
        target_scope_note=raw["target_scope_note"],
        pytest_targets=pytest_targets,
        changed_paths=(
            tuple(raw["changed_paths"])
            if raw.get("changed_paths") is not None
            else None
        ),
        notes=raw.get("notes"),
        synthetic_replace_operations=tuple(replace_ops),
    )


def _write_summary_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = [
        "delta_id",
        "category",
        "blast_radius",
        "regime",
        "total_full_tests",
        "total_selected_tests_adeu",
        "total_selected_tests_testmon",
        "selector_time_adeu",
        "selector_or_overhead_time_testmon",
        "execution_time_selected_adeu",
        "execution_time_selected_testmon",
        "total_time_adeu",
        "total_time_testmon",
        "total_time_full",
        "selected_fraction_adeu",
        "selected_fraction_testmon",
        "false_negative_count_adeu",
        "false_negative_count_testmon",
        "selected_nonfailing_count_adeu",
        "selected_nonfailing_count_testmon",
        "safety_pass_adeu",
        "safety_pass_testmon",
        "ground_truth_exit_code",
        "adeu_exit_code",
        "testmon_exit_code",
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def _build_markdown_report(
    *,
    runs_payload: dict[str, Any],
    summary_payload: dict[str, Any],
) -> str:
    lines: list[str] = []
    lines.append("# ADEU Selector vs pytest-testmon Benchmark (v0)")
    lines.append("")
    lines.append(f"- generated_at_utc: `{summary_payload['generated_at_utc']}`")
    lines.append(f"- corpus_path: `{summary_payload['corpus_path']}`")
    lines.append("- adeu_selector_mode: `stateless_planner_no_warm_cache`")
    lines.append(
        "- ground_truth_rule: full pytest run over each delta's declared benchmark target scope"
    )
    lines.append(
        "- selected_nonfailing_count: selected tests that did not fail in the "
        "ground-truth run; this is not a true impact false-positive oracle"
    )
    lines.append("")

    lines.append("## Corpus")
    lines.append("")
    lines.append(
        "| delta_id | source_kind | category | blast_radius | target_scope_kind | "
        "base_revision | changed_revision |"
    )
    lines.append("|---|---|---|---|---|---|---|")
    for delta in runs_payload["delta_runs"]:
        lines.append(
            "| "
            + " | ".join(
                [
                    delta["delta_id"],
                    delta["source_kind"],
                    delta["category"],
                    delta["blast_radius"],
                    delta["target_scope_kind"],
                    delta["base_revision"][:12],
                    delta["changed_revision"][:12],
                ]
            )
            + " |"
        )
    lines.append("")

    lines.append("## Aggregate")
    lines.append("")
    overall = summary_payload["aggregate_overall"]
    lines.append(
        "| scope | rows | full_tests | adeu_selected | testmon_selected | adeu_fn | testmon_fn |"
    )
    lines.append("|---|---:|---:|---:|---:|---:|---:|")
    lines.append(
        "| overall | "
        f"{overall['row_count']} | "
        f"{overall['total_full_tests']} | "
        f"{overall['total_selected_tests_adeu']} | "
        f"{overall['total_selected_tests_testmon']} | "
        f"{overall['false_negative_count_adeu']} | "
        f"{overall['false_negative_count_testmon']} |"
    )
    for regime in ("cold", "warm"):
        aggregate = summary_payload["aggregate_by_regime"][regime]
        lines.append(
            "| regime:"
            + regime
            + " | "
            f"{aggregate['row_count']} | "
            f"{aggregate['total_full_tests']} | "
            f"{aggregate['total_selected_tests_adeu']} | "
            f"{aggregate['total_selected_tests_testmon']} | "
            f"{aggregate['false_negative_count_adeu']} | "
            f"{aggregate['false_negative_count_testmon']} |"
        )
    for blast in ("narrow", "broad"):
        aggregate = summary_payload["aggregate_by_blast_radius"][blast]
        lines.append(
            "| blast:"
            + blast
            + " | "
            f"{aggregate['row_count']} | "
            f"{aggregate['total_full_tests']} | "
            f"{aggregate['total_selected_tests_adeu']} | "
            f"{aggregate['total_selected_tests_testmon']} | "
            f"{aggregate['false_negative_count_adeu']} | "
            f"{aggregate['false_negative_count_testmon']} |"
        )
    lines.append("")

    lines.append("## Safety")
    lines.append("")
    if summary_payload["safety_failures"]:
        for failure in summary_payload["safety_failures"]:
            lines.append(
                "- "
                f"{failure['delta_id']} [{failure['regime']}]: "
                f"adeu_fn={failure['false_negative_count_adeu']}, "
                f"testmon_fn={failure['false_negative_count_testmon']}"
            )
    else:
        lines.append("- No false-negative safety failures were observed in this run set.")
    lines.append("")

    lines.append("## Per-Delta Regime Rows")
    lines.append("")
    lines.append(
        "| delta_id | regime | full | adeu_selected | testmon_selected | adeu_time | testmon_time |"
    )
    lines.append("|---|---|---:|---:|---:|---:|---:|")
    for row in summary_payload["metric_rows"]:
        lines.append(
            "| "
            + " | ".join(
                [
                    row["delta_id"],
                    row["regime"],
                    str(row["total_full_tests"]),
                    str(row["total_selected_tests_adeu"]),
                    str(row["total_selected_tests_testmon"]),
                    f"{row['total_time_adeu']:.3f}",
                    f"{row['total_time_testmon']:.3f}",
                ]
            )
            + " |"
        )
    lines.append("")
    return "\n".join(lines) + "\n"


def run_benchmark(
    *,
    corpus_path: Path,
    output_dir: Path,
    python_executable: Path,
    delta_ids: set[str] | None = None,
    keep_worktrees: bool = False,
) -> dict[str, Any]:
    repo_root = canonical_repo_root()
    resolved_output_dir = (
        output_dir if output_dir.is_absolute() else (repo_root / output_dir).resolve()
    )
    resolved_python_executable = (
        python_executable
        if python_executable.is_absolute()
        else (repo_root / python_executable)
    )
    if not resolved_python_executable.exists():
        raise FileNotFoundError(
            f"python executable not found: {resolved_python_executable.as_posix()}"
        )
    corpus_payload = _load_corpus(corpus_path)
    all_deltas = [_parse_delta(raw) for raw in corpus_payload["deltas"]]
    if delta_ids:
        deltas = [delta for delta in all_deltas if delta.delta_id in delta_ids]
    else:
        deltas = list(all_deltas)
    if not deltas:
        raise ValueError("no deltas selected for execution")

    resolved_output_dir.mkdir(parents=True, exist_ok=True)
    deltas_output_dir = resolved_output_dir / "deltas"
    deltas_output_dir.mkdir(parents=True, exist_ok=True)

    benchmark_rows: list[dict[str, Any]] = []
    delta_runs: list[dict[str, Any]] = []

    git_env = dict(os.environ)
    for delta in deltas:
        temp_root = Path(
            tempfile.mkdtemp(prefix=f"adeu_test_selection_benchmark_{delta.delta_id}_")
        )
        worktree_path = temp_root / "worktree"
        delta_output_dir = deltas_output_dir / delta.delta_id
        delta_output_dir.mkdir(parents=True, exist_ok=True)

        _ensure_git_success(
            command=[
                "git",
                "worktree",
                "add",
                "--detach",
                worktree_path.as_posix(),
                delta.base_revision,
            ],
            cwd=repo_root,
            env=git_env,
        )
        try:
            changed_paths = (
                sorted(delta.changed_paths)
                if delta.changed_paths is not None
                else _discover_changed_paths_from_pair(
                    worktree_root=worktree_path,
                    base_revision=delta.base_revision,
                    changed_revision=delta.changed_revision,
                    env=git_env,
                )
            )

            base_env = _build_env_for_repo(repo_root=worktree_path)
            _remove_testmon_state(worktree_root=worktree_path)
            warm_seed_base = _run_pytest(
                python_executable=resolved_python_executable,
                worktree_root=worktree_path,
                targets=list(delta.pytest_targets),
                extra_args=["--testmon"],
                env=base_env,
                junit_xml_path=delta_output_dir / "testmon_warm_seed_base.xml",
            )

            _checkout_revision(
                worktree_root=worktree_path,
                revision=delta.changed_revision,
                env=git_env,
            )
            changed_env = _build_env_for_repo(repo_root=worktree_path)

            synthetic_touched_paths: list[str] = []
            if delta.source_kind == "synthetic_patch":
                synthetic_touched_paths = _apply_synthetic_replace_operations(
                    worktree_root=worktree_path,
                    operations=delta.synthetic_replace_operations,
                )
                if delta.changed_paths is None:
                    changed_paths = synthetic_touched_paths

            (delta_output_dir / "changed_paths.json").write_text(
                json.dumps(changed_paths, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )

            ground_truth = _run_pytest(
                python_executable=resolved_python_executable,
                worktree_root=worktree_path,
                targets=list(delta.pytest_targets),
                extra_args=[],
                env=changed_env,
                junit_xml_path=delta_output_dir / "ground_truth_full.xml",
            )

            selector_started = time.perf_counter()
            adeu_plan = select_python_tests_v0(
                changed_paths=changed_paths,
                repo_root=worktree_path,
            )
            selector_elapsed = time.perf_counter() - selector_started
            adeu_plan_path = delta_output_dir / "adeu_selector_plan.json"
            adeu_plan_path.write_text(
                json.dumps(adeu_plan, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )

            adeu_selected_raw = list(adeu_plan["selected_test_paths"])
            adeu_selected_in_target = _filter_selected_paths_to_targets(
                selected_test_paths=adeu_selected_raw,
                targets=delta.pytest_targets,
            )
            if adeu_selected_in_target:
                adeu_execution = _run_pytest(
                    python_executable=resolved_python_executable,
                    worktree_root=worktree_path,
                    targets=adeu_selected_in_target,
                    extra_args=[],
                    env=changed_env,
                    junit_xml_path=delta_output_dir / "adeu_selected.xml",
                )
            else:
                adeu_execution = _empty_pytest_result(
                    reason="no ADEU-selected tests within benchmark target tree"
                )

            warm_collect = _run_command(
                command=[
                    str(resolved_python_executable),
                    "-m",
                    "pytest",
                    "-q",
                    "--testmon",
                    "--collect-only",
                    *delta.pytest_targets,
                ],
                cwd=worktree_path,
                env=changed_env,
            )
            testmon_warm_execution = _run_pytest(
                python_executable=resolved_python_executable,
                worktree_root=worktree_path,
                targets=list(delta.pytest_targets),
                extra_args=["--testmon"],
                env=changed_env,
                junit_xml_path=delta_output_dir / "testmon_warm_selected.xml",
            )

            _remove_testmon_state(worktree_root=worktree_path)
            cold_collect = _run_command(
                command=[
                    str(resolved_python_executable),
                    "-m",
                    "pytest",
                    "-q",
                    "--testmon",
                    "--collect-only",
                    *delta.pytest_targets,
                ],
                cwd=worktree_path,
                env=changed_env,
            )
            _remove_testmon_state(worktree_root=worktree_path)
            testmon_cold_execution = _run_pytest(
                python_executable=resolved_python_executable,
                worktree_root=worktree_path,
                targets=list(delta.pytest_targets),
                extra_args=["--testmon"],
                env=changed_env,
                junit_xml_path=delta_output_dir / "testmon_cold_selected.xml",
            )

            warm_row = _compute_metrics_row(
                delta=delta,
                regime="warm",
                ground_truth=ground_truth,
                adeu_selector_time_seconds=selector_elapsed,
                adeu_execution=adeu_execution,
                testmon_overhead_seconds=warm_collect.wall_time_seconds,
                testmon_execution=testmon_warm_execution,
            )
            cold_row = _compute_metrics_row(
                delta=delta,
                regime="cold",
                ground_truth=ground_truth,
                adeu_selector_time_seconds=selector_elapsed,
                adeu_execution=adeu_execution,
                testmon_overhead_seconds=cold_collect.wall_time_seconds,
                testmon_execution=testmon_cold_execution,
            )
            metric_rows = [
                row
                for row in (cold_row, warm_row)
                if row["regime"] in set(delta.eligibility)
            ]
            benchmark_rows.extend(metric_rows)

            delta_runs.append(
                {
                    "delta_id": delta.delta_id,
                    "source_kind": delta.source_kind,
                    "category": delta.category,
                    "blast_radius": delta.blast_radius,
                    "expected_blast_radius_intuition": delta.expected_blast_radius_intuition,
                    "base_revision": delta.base_revision,
                    "changed_revision": delta.changed_revision,
                    "changed_paths": changed_paths,
                    "target_scope_kind": delta.target_scope_kind,
                    "target_scope_note": delta.target_scope_note,
                    "pytest_targets": list(delta.pytest_targets),
                    "notes": delta.notes,
                    "synthetic_touched_paths": synthetic_touched_paths,
                    "ground_truth": {
                        "command": list(ground_truth.command),
                        "exit_code": ground_truth.exit_code,
                        "wall_time_seconds": round(ground_truth.wall_time_seconds, 6),
                        "junit_xml_path": ground_truth.junit_xml_path,
                        "executed_test_count": len(ground_truth.executed_node_ids),
                        "failing_test_count": len(ground_truth.failing_node_ids),
                        "outcome_counts": ground_truth.outcome_counts,
                        "executed_node_ids": list(ground_truth.executed_node_ids),
                        "failing_node_ids": list(ground_truth.failing_node_ids),
                        "stdout_tail": ground_truth.stdout_tail,
                        "stderr_tail": ground_truth.stderr_tail,
                    },
                    "adeu": {
                        "selector_time_seconds": round(selector_elapsed, 6),
                        "plan_artifact_path": adeu_plan_path.as_posix(),
                        "risk_posture": adeu_plan["risk_posture"],
                        "full_suite_recommended": adeu_plan["full_suite_recommended"],
                        "selected_test_paths_raw": adeu_selected_raw,
                        "selected_test_paths_in_target": adeu_selected_in_target,
                        "selected_raw_count": len(adeu_selected_raw),
                        "selected_in_target_count": len(adeu_selected_in_target),
                        "execution": {
                            "command": list(adeu_execution.command),
                            "exit_code": adeu_execution.exit_code,
                            "wall_time_seconds": round(adeu_execution.wall_time_seconds, 6),
                            "junit_xml_path": adeu_execution.junit_xml_path,
                            "executed_test_count": len(adeu_execution.executed_node_ids),
                            "failing_test_count": len(adeu_execution.failing_node_ids),
                            "outcome_counts": adeu_execution.outcome_counts,
                            "executed_node_ids": list(adeu_execution.executed_node_ids),
                            "failing_node_ids": list(adeu_execution.failing_node_ids),
                            "stdout_tail": adeu_execution.stdout_tail,
                            "stderr_tail": adeu_execution.stderr_tail,
                        },
                    },
                    "testmon": {
                        "base_seed": {
                            "command": list(warm_seed_base.command),
                            "exit_code": warm_seed_base.exit_code,
                            "wall_time_seconds": round(warm_seed_base.wall_time_seconds, 6),
                            "junit_xml_path": warm_seed_base.junit_xml_path,
                            "executed_test_count": len(warm_seed_base.executed_node_ids),
                            "failing_test_count": len(warm_seed_base.failing_node_ids),
                            "outcome_counts": warm_seed_base.outcome_counts,
                            "stdout_tail": warm_seed_base.stdout_tail,
                            "stderr_tail": warm_seed_base.stderr_tail,
                        },
                        "warm": {
                            "collect_only_command": list(warm_collect.command),
                            "collect_only_exit_code": warm_collect.exit_code,
                            "collect_only_overhead_seconds": round(
                                warm_collect.wall_time_seconds,
                                6,
                            ),
                            "collect_only_stdout_tail": warm_collect.stdout_tail,
                            "collect_only_stderr_tail": warm_collect.stderr_tail,
                            "execution": {
                                "command": list(testmon_warm_execution.command),
                                "exit_code": testmon_warm_execution.exit_code,
                                "wall_time_seconds": round(
                                    testmon_warm_execution.wall_time_seconds,
                                    6,
                                ),
                                "junit_xml_path": testmon_warm_execution.junit_xml_path,
                                "executed_test_count": len(
                                    testmon_warm_execution.executed_node_ids
                                ),
                                "failing_test_count": len(
                                    testmon_warm_execution.failing_node_ids
                                ),
                                "outcome_counts": testmon_warm_execution.outcome_counts,
                                "executed_node_ids": list(
                                    testmon_warm_execution.executed_node_ids
                                ),
                                "failing_node_ids": list(
                                    testmon_warm_execution.failing_node_ids
                                ),
                                "stdout_tail": testmon_warm_execution.stdout_tail,
                                "stderr_tail": testmon_warm_execution.stderr_tail,
                            },
                        },
                        "cold": {
                            "collect_only_command": list(cold_collect.command),
                            "collect_only_exit_code": cold_collect.exit_code,
                            "collect_only_overhead_seconds": round(
                                cold_collect.wall_time_seconds,
                                6,
                            ),
                            "collect_only_stdout_tail": cold_collect.stdout_tail,
                            "collect_only_stderr_tail": cold_collect.stderr_tail,
                            "execution": {
                                "command": list(testmon_cold_execution.command),
                                "exit_code": testmon_cold_execution.exit_code,
                                "wall_time_seconds": round(
                                    testmon_cold_execution.wall_time_seconds,
                                    6,
                                ),
                                "junit_xml_path": testmon_cold_execution.junit_xml_path,
                                "executed_test_count": len(
                                    testmon_cold_execution.executed_node_ids
                                ),
                                "failing_test_count": len(
                                    testmon_cold_execution.failing_node_ids
                                ),
                                "outcome_counts": testmon_cold_execution.outcome_counts,
                                "executed_node_ids": list(
                                    testmon_cold_execution.executed_node_ids
                                ),
                                "failing_node_ids": list(
                                    testmon_cold_execution.failing_node_ids
                                ),
                                "stdout_tail": testmon_cold_execution.stdout_tail,
                                "stderr_tail": testmon_cold_execution.stderr_tail,
                            },
                        },
                    },
                    "metric_rows": metric_rows,
                }
            )
        finally:
            try:
                _ensure_git_success(
                    command=["git", "worktree", "remove", "--force", worktree_path.as_posix()],
                    cwd=repo_root,
                    env=git_env,
                )
            finally:
                if not keep_worktrees:
                    shutil.rmtree(temp_root, ignore_errors=True)

    benchmark_rows.sort(key=lambda row: (row["delta_id"], row["regime"]))
    summary_payload = {
        "schema": SUMMARY_SCHEMA,
        "generated_at_utc": _utc_now_iso(),
        "repo_root": repo_root.as_posix(),
        "corpus_path": corpus_path.as_posix(),
        "python_executable": resolved_python_executable.as_posix(),
        "delta_count": len(delta_runs),
        "metric_row_count": len(benchmark_rows),
        "metric_rows": benchmark_rows,
        "aggregate_overall": _aggregate_metric_rows(benchmark_rows),
        "aggregate_by_regime": {
            "cold": _aggregate_metric_rows(
                [row for row in benchmark_rows if row["regime"] == "cold"]
            ),
            "warm": _aggregate_metric_rows(
                [row for row in benchmark_rows if row["regime"] == "warm"]
            ),
        },
        "aggregate_by_blast_radius": {
            "narrow": _aggregate_metric_rows(
                [row for row in benchmark_rows if row["blast_radius"] == "narrow"]
            ),
            "broad": _aggregate_metric_rows(
                [row for row in benchmark_rows if row["blast_radius"] == "broad"]
            ),
        },
        "safety_failures": [
            {
                "delta_id": row["delta_id"],
                "regime": row["regime"],
                "false_negative_count_adeu": row["false_negative_count_adeu"],
                "false_negative_count_testmon": row["false_negative_count_testmon"],
            }
            for row in benchmark_rows
            if (row["false_negative_count_adeu"] > 0 or row["false_negative_count_testmon"] > 0)
        ],
    }
    runs_payload = {
        "schema": RUNS_SCHEMA,
        "generated_at_utc": summary_payload["generated_at_utc"],
        "repo_root": repo_root.as_posix(),
        "corpus_path": corpus_path.as_posix(),
        "python_executable": resolved_python_executable.as_posix(),
        "delta_runs": delta_runs,
    }

    _write_json(resolved_output_dir / "benchmark_runs.json", runs_payload)
    _write_json(resolved_output_dir / "benchmark_summary.json", summary_payload)
    _write_summary_csv(resolved_output_dir / "benchmark_summary.csv", benchmark_rows)
    (resolved_output_dir / "benchmark_report.md").write_text(
        _build_markdown_report(runs_payload=runs_payload, summary_payload=summary_payload),
        encoding="utf-8",
    )
    return summary_payload


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run a bounded A/B benchmark comparing ADEU select_tests_v0 against pytest-testmon "
            "across a corpus of git-derived deltas."
        )
    )
    parser.add_argument(
        "--corpus",
        type=Path,
        default=Path("packages/adeu_repo_description/benchmarks/test_selection_ab_corpus_v0.json"),
        help="Path to the benchmark corpus JSON file.",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("artifacts/benchmarks/test_selection_ab_v0"),
        help=(
            "Directory where benchmark_runs.json, benchmark_summary.json, "
            "benchmark_summary.csv, and benchmark_report.md are written."
        ),
    )
    parser.add_argument(
        "--python-executable",
        type=Path,
        default=Path(".venv/bin/python"),
        help="Python interpreter used for pytest executions.",
    )
    parser.add_argument(
        "--delta-id",
        action="append",
        default=[],
        help="Optional delta_id filter. May be specified multiple times.",
    )
    parser.add_argument(
        "--keep-worktrees",
        action="store_true",
        help="Keep temporary benchmark worktrees for debugging.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    namespace = _parse_args(argv if argv is not None else sys.argv[1:])
    summary = run_benchmark(
        corpus_path=namespace.corpus,
        output_dir=namespace.output_dir,
        python_executable=namespace.python_executable,
        delta_ids=set(namespace.delta_id) or None,
        keep_worktrees=namespace.keep_worktrees,
    )
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
