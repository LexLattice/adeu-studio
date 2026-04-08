from __future__ import annotations

import importlib.util
import json
import os
import shutil
import subprocess
import sys
import importlib.util
from pathlib import Path
from types import ModuleType


def _repo_root() -> Path:
    current = Path(__file__).resolve()
    for parent in current.parents:
        if (parent / ".git").is_dir():
            return parent
    raise FileNotFoundError("repository root not found")


def _script_path() -> Path:
    return _repo_root() / "apps" / "api" / "scripts" / "lint_semantic_compiler_closeout.py"


def _load_script_module() -> ModuleType:
    module_name = "lint_semantic_compiler_closeout_for_tests"
    spec = importlib.util.spec_from_file_location(module_name, _script_path())
    if spec is None or spec.loader is None:
        raise RuntimeError("failed to load lint_semantic_compiler_closeout module")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def _pythonpath_env() -> dict[str, str]:
    repo_root = _repo_root()
    env = os.environ.copy()
    existing = env.get("PYTHONPATH")
    paths = [
        str(repo_root / "apps" / "api" / "src"),
        str(repo_root / "packages" / "urm_runtime" / "src"),
    ]
    if existing:
        paths.append(existing)
    env["PYTHONPATH"] = os.pathsep.join(paths)
    env["TZ"] = "UTC"
    env["LC_ALL"] = "C"
    env["PYTHONHASHSEED"] = "0"
    return env


def _run_lint(*, repo_root: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(_script_path()),
            "--repo-root",
            str(repo_root),
        ],
        check=False,
        capture_output=True,
        text=True,
        env=_pythonpath_env(),
    )


def _copy_fixture_file(*, destination_root: Path, relative_path: str) -> None:
    source = _repo_root() / relative_path
    target = destination_root / relative_path
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target)


def _make_repo_fixture(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    required_files = (
        ".github/workflows/ci.yml",
        "docs/LOCKED_CONTINUATION_vNEXT_PLUS42.md",
        "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS42.md",
        "docs/generated/semantic_compiler/v41/PR_SPLITS.md",
        "artifacts/semantic_compiler/v41/surface_snapshot.json",
        "artifacts/semantic_compiler/v41/surface_diff.json",
        "artifacts/semantic_compiler/v41/evidence_manifest.json",
        "artifacts/quality_dashboard_v41_closeout.json",
        "artifacts/stop_gate/metrics_v41_closeout.json",
        "artifacts/stop_gate/metrics_v42_closeout.json",
        "artifacts/stop_gate/report_v41_closeout.md",
        "artifacts/stop_gate/report_v42_closeout.md",
    )
    for relative_path in required_files:
        _copy_fixture_file(destination_root=root, relative_path=relative_path)
    return root


def test_semantic_compiler_closeout_lint_passes_on_current_fixture(tmp_path: Path) -> None:
    repo_root = _make_repo_fixture(tmp_path)
    completed = _run_lint(repo_root=repo_root)
    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "semantic_compiler_closeout_lint@1"
    assert payload["failures"] == []
    assert payload["decision_doc"] == "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS42.md"


def test_repo_root_discovery_accepts_worktree_git_file(tmp_path: Path) -> None:
    worktree_root = tmp_path / "synthetic_worktree"
    script_path = (
        worktree_root / "apps" / "api" / "scripts" / "lint_semantic_compiler_closeout.py"
    )
    script_path.parent.mkdir(parents=True, exist_ok=True)
    script_path.write_text("# synthetic", encoding="utf-8")
    (worktree_root / ".git").write_text(
        "gitdir: /tmp/synthetic-main-repo/.git/worktrees/synthetic_worktree\n",
        encoding="utf-8",
    )

    module = _load_script_module()
    original_file = module.__file__
    try:
        module.__file__ = str(script_path)
        assert module._repo_root_from_script() == worktree_root
    finally:
        module.__file__ = original_file


def test_semantic_compiler_closeout_lint_fails_when_required_block_missing(tmp_path: Path) -> None:
    repo_root = _make_repo_fixture(tmp_path)
    decision_path = repo_root / "docs" / "DRAFT_STOP_GATE_DECISION_vNEXT_PLUS42.md"
    original_text = decision_path.read_text(encoding="utf-8")
    marker = "## CI Wiring Evidence"
    marker_index = original_text.find(marker)
    assert marker_index >= 0
    broken_text = original_text[:marker_index].rstrip() + "\n"
    decision_path.write_text(broken_text, encoding="utf-8")

    completed = _run_lint(repo_root=repo_root)
    assert completed.returncode == 1
    payload = json.loads(completed.stdout)
    failure_codes = {row["code"] for row in payload["failures"]}
    assert "REQUIRED_CLOSEOUT_BLOCK_MISSING" in failure_codes


def test_semantic_compiler_closeout_lint_fails_when_full_lane_guard_has_no_closeout_bridge(
    tmp_path: Path,
) -> None:
    repo_root = _make_repo_fixture(tmp_path)
    workflow_path = repo_root / ".github" / "workflows" / "ci.yml"
    workflow_text = workflow_path.read_text(encoding="utf-8")
    workflow_text = workflow_text.replace(
        "      - name: Run arc closeout bundle checks\n"
        "        if: steps.python_scope.outputs.scope == 'arc_closeout'\n"
        "        run: make arc-closeout-check ARC=${{ steps.python_scope.outputs.arc }}\n",
        "",
    )
    workflow_path.write_text(workflow_text, encoding="utf-8")

    completed = _run_lint(repo_root=repo_root)
    assert completed.returncode == 1
    payload = json.loads(completed.stdout)
    failure_codes = {row["code"] for row in payload["failures"]}
    assert "CI_WIRING_REQUIRED_CHECK_CONDITIONALLY_SKIPPED" in failure_codes
