from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path
from types import ModuleType


def _repo_root() -> Path:
    current = Path(__file__).resolve()
    for parent in current.parents:
        if (parent / ".git").is_dir():
            return parent
    raise FileNotFoundError("repository root not found")


def _script_path() -> Path:
    return _repo_root() / "apps" / "api" / "scripts" / "lint_v31g_persistence_release.py"


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
    return env


def _default_base_ref() -> str:
    repo_root = _repo_root()
    for candidate in ("origin/main", "HEAD"):
        completed = subprocess.run(
            ["git", "rev-parse", "--verify", "--quiet", f"{candidate}^{{commit}}"],
            cwd=repo_root,
            check=False,
            capture_output=True,
            text=True,
        )
        if completed.returncode == 0:
            return candidate
    return "HEAD"


def _run_lint(
    *,
    lock_doc: Path | None = None,
    base_ref: str | None = None,
) -> subprocess.CompletedProcess[str]:
    repo_root = _repo_root()
    lock_doc_path = lock_doc or repo_root / "docs" / "LOCKED_CONTINUATION_vNEXT_PLUS37.md"
    base_ref_value = base_ref or _default_base_ref()
    return subprocess.run(
        [
            sys.executable,
            str(_script_path()),
            "--lock-doc",
            str(lock_doc_path),
            "--base-ref",
            base_ref_value,
        ],
        cwd=repo_root,
        check=False,
        capture_output=True,
        text=True,
        env=_pythonpath_env(),
    )


def _load_script_module() -> ModuleType:
    module_name = "lint_v31g_persistence_release_for_tests"
    spec = importlib.util.spec_from_file_location(module_name, _script_path())
    if spec is None or spec.loader is None:
        raise RuntimeError("failed to load lint_v31g_persistence_release module")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def test_v31g_persistence_release_lint_passes_on_current_repo() -> None:
    completed = _run_lint()
    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert "Traceback" not in completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "v31g_persistence_release_lint@1"
    assert payload["failures"] == []


def test_v31g_persistence_release_lint_fails_closed_when_base_ref_missing() -> None:
    completed = _run_lint(base_ref="origin/__missing_v31g_ref__")
    assert completed.returncode == 5
    payload = json.loads(completed.stdout)
    failure_codes = {row["code"] for row in payload["failures"]}
    assert "BASE_REF_UNAVAILABLE" in failure_codes


def test_v31g_persistence_release_lint_fails_on_consumption_drift(tmp_path: Path) -> None:
    source_path = _repo_root() / "docs" / "LOCKED_CONTINUATION_vNEXT_PLUS37.md"
    modified = source_path.read_text(encoding="utf-8").replace(
        "\"REPLAY_CONFLICT_REGRESSION_GUARDS_GREEN\"",
        "\"REPLAY_CONFLICT_REGRESSION_GUARDS_BROKEN\"",
        1,
    )
    lock_doc_copy = tmp_path / "LOCKED_CONTINUATION_vNEXT_PLUS37.invalid.md"
    lock_doc_copy.write_text(modified, encoding="utf-8")

    completed = _run_lint(lock_doc=lock_doc_copy)
    assert completed.returncode == 2
    payload = json.loads(completed.stdout)
    failure_codes = {row["code"] for row in payload["failures"]}
    assert "CONSUMPTION_SCHEMA_INVALID" in failure_codes


def test_v31g_persistence_release_lint_exit_code_contract() -> None:
    module = _load_script_module()
    assert module.EXIT_BY_CATEGORY == {
        "schema": 2,
        "callgraph": 3,
        "determinism": 4,
        "base_ref": 5,
    }

    result = module.LintResult(lock_doc="x", base_ref="origin/main", repo_root=".")
    result.add_failure(category="determinism", code="X", details={})
    assert result.exit_code() == 4

    result.add_failure(category="callgraph", code="Y", details={})
    assert result.exit_code() == 3

    result.add_failure(category="schema", code="Z", details={})
    assert result.exit_code() == 2

    result.add_failure(category="base_ref", code="W", details={})
    assert result.exit_code() == 5


def test_v31g_persistence_release_lint_changed_files_use_merge_base_semantics() -> None:
    module = _load_script_module()
    captured_calls: list[tuple[str, ...]] = []

    def _fake_git_text(*args: str, repo_root: Path) -> str:
        captured_calls.append(args)
        if args[0] == "merge-base":
            return "abc123"
        if args[0] == "diff":
            return "apps/api/src/adeu_api/main.py\napps/api/src/adeu_api/storage.py\n"
        raise AssertionError(f"unexpected git args: {args}")

    module._git_text = _fake_git_text
    merge_base, changed_files = module._changed_files_against_base_ref(
        base_ref="origin/main",
        repo_root=_repo_root(),
    )

    assert merge_base == "abc123"
    assert changed_files == [
        "apps/api/src/adeu_api/main.py",
        "apps/api/src/adeu_api/storage.py",
    ]
    assert captured_calls[0] == ("merge-base", "origin/main", "HEAD")
    assert captured_calls[1] == (
        "diff",
        "--name-only",
        "--diff-filter=ACDMRTUXB",
        "abc123..HEAD",
    )
