from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

from adeu_repo_description.test_selection_v0 import (
    discover_changed_paths_from_git,
    select_python_tests_v0,
)

RUN_SCHEMA = "repo_selected_test_run@1"
DEFAULT_BASE_REF = "origin/main"
MANUAL_INSPECTION_EXIT_CODE = 3
FULL_FALLBACK_BASENAMES = {"Makefile", "pyproject.toml"}
FULL_FALLBACK_PREFIXES = (".github/workflows/",)
FULL_FALLBACK_SUFFIXES = (".py",)


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the selector-driven local pytest workflow, escalating back for manual "
            "inspection when the planner recommends full-suite coverage."
        )
    )
    parser.add_argument("--repo-root", type=Path, default=None)
    parser.add_argument("--base-ref", default=DEFAULT_BASE_REF)
    parser.add_argument("--no-untracked", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument(
        "--allow-full-fallback",
        action="store_true",
        help=(
            "Allow conservative full pytest execution after inspecting the escalation "
            "reason. By default, full-suite recommendations stop for manual review."
        ),
    )
    return parser.parse_args(argv)


def _full_fallback_out_of_scope_paths(changed_paths: list[str]) -> list[str]:
    fallback_paths: list[str] = []
    for changed_path in changed_paths:
        path = Path(changed_path)
        if path.name in FULL_FALLBACK_BASENAMES:
            fallback_paths.append(changed_path)
            continue
        if changed_path.startswith(FULL_FALLBACK_PREFIXES):
            fallback_paths.append(changed_path)
            continue
        if changed_path.endswith(FULL_FALLBACK_SUFFIXES):
            fallback_paths.append(changed_path)
    return sorted(set(fallback_paths))


def _discover_changed_paths(
    *,
    repo_root: Path | None,
    base_ref: str | None,
    include_untracked: bool,
) -> tuple[list[str], str | None, list[str]]:
    warnings: list[str] = []
    resolved_base_ref = base_ref
    if resolved_base_ref is not None:
        try:
            changed_paths = discover_changed_paths_from_git(
                repo_root=repo_root,
                base_ref=resolved_base_ref,
                include_untracked=include_untracked,
            )
            return changed_paths, resolved_base_ref, warnings
        except (RuntimeError, subprocess.CalledProcessError) as exc:
            warnings.append(
                f"base ref {resolved_base_ref!r} unavailable for selector diff discovery: {exc}"
            )
            resolved_base_ref = None

    changed_paths = discover_changed_paths_from_git(
        repo_root=repo_root,
        base_ref=None,
        include_untracked=include_untracked,
    )
    return changed_paths, resolved_base_ref, warnings


def _build_run_summary(
    *,
    repo_root: Path | None,
    base_ref: str | None,
    include_untracked: bool,
) -> dict[str, Any]:
    changed_paths, resolved_base_ref, warnings = _discover_changed_paths(
        repo_root=repo_root,
        base_ref=base_ref,
        include_untracked=include_untracked,
    )
    payload = select_python_tests_v0(changed_paths=changed_paths, repo_root=repo_root)
    out_of_scope_full_fallback_paths = _full_fallback_out_of_scope_paths(
        payload["out_of_scope_changed_paths"]
    )

    mode = "skip"
    full_suite_reason: str | None = None
    pytest_args: list[str] = []
    if payload["full_suite_recommended"]:
        mode = "full"
        full_suite_reason = "; ".join(payload["escalation_reasons"])
    elif out_of_scope_full_fallback_paths:
        mode = "full"
        full_suite_reason = (
            "unmatched Python/config surface changed: "
            + ", ".join(out_of_scope_full_fallback_paths)
        )
    elif payload["selected_test_paths"]:
        mode = "selected"
        pytest_args = list(payload["pytest_args"])

    return {
        "schema": RUN_SCHEMA,
        "selection_schema": payload["schema"],
        "selection_algorithm": payload["selection_algorithm"],
        "repo_root": payload["repo_root"],
        "base_ref_requested": base_ref,
        "base_ref_used": resolved_base_ref,
        "changed_paths": payload["changed_paths"],
        "selector_warnings": sorted(set(payload["warnings"]) | set(warnings)),
        "mode": mode,
        "manual_inspection_required": mode == "full",
        "full_suite_reason": full_suite_reason,
        "selected_test_paths": payload["selected_test_paths"],
        "out_of_scope_changed_paths": payload["out_of_scope_changed_paths"],
        "out_of_scope_full_fallback_paths": out_of_scope_full_fallback_paths,
        "full_suite_recommended": payload["full_suite_recommended"],
        "risk_posture": payload["risk_posture"],
        "summary": payload["summary"],
        "pytest_args": pytest_args,
    }


def main(argv: list[str] | None = None) -> int:
    namespace = _parse_args(argv)
    summary = _build_run_summary(
        repo_root=namespace.repo_root,
        base_ref=namespace.base_ref,
        include_untracked=not namespace.no_untracked,
    )

    if namespace.dry_run:
        print(json.dumps(summary, indent=2, sort_keys=True))
        return 0

    for warning in summary["selector_warnings"]:
        print(f"[selected-test-runner] {warning}", file=sys.stderr)

    if summary["mode"] == "skip":
        print(
            "[selected-test-runner] no in-scope pytest modules selected; skipping pytest",
            file=sys.stderr,
        )
        return 0

    command = [sys.executable, "-m", "pytest"]
    command_cwd = Path(summary["repo_root"])
    if summary["mode"] == "selected":
        command.extend(summary["pytest_args"])
        print(
            "[selected-test-runner] running "
            f"{len(summary['pytest_args'])} selected pytest module(s)",
            file=sys.stderr,
        )
    else:
        if not namespace.allow_full_fallback:
            print(
                "[selected-test-runner] manual inspection required before full pytest: "
                f"{summary['full_suite_reason']}",
                file=sys.stderr,
            )
            print(
                "[selected-test-runner] rerun with --allow-full-fallback, or use "
                "`make test` / `make check-full` once the escalation reason is accepted",
                file=sys.stderr,
            )
            return MANUAL_INSPECTION_EXIT_CODE
        print(
            "[selected-test-runner] falling back to full pytest suite: "
            f"{summary['full_suite_reason']}",
            file=sys.stderr,
        )

    completed = subprocess.run(command, check=False, cwd=command_cwd)
    return completed.returncode


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
