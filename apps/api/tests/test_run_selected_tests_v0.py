from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path


def _repo_root() -> Path:
    current = Path(__file__).resolve()
    for parent in current.parents:
        git_marker = parent / ".git"
        if git_marker.is_dir() or git_marker.is_file():
            return parent
    raise FileNotFoundError("repository root not found")


def _script_path() -> Path:
    return _repo_root() / "apps" / "api" / "scripts" / "run_selected_tests_v0.py"


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


def _bootstrap_repo(tmp_path: Path, files: dict[str, str]) -> Path:
    base_files = {
        "pyproject.toml": '[tool.pytest.ini_options]\naddopts = "-q"\n',
        "packages/urm_runtime/pyproject.toml": (
            "[build-system]\n"
            'requires = ["hatchling"]\n'
            'build-backend = "hatchling.build"\n\n'
            "[project]\n"
            'name = "urm_runtime"\n'
            'version = "0.0.0"\n'
        ),
        "packages/urm_runtime/src/urm_runtime/__init__.py": "__all__ = []\n",
    }
    base_files.update(files)
    for relative_path, content in base_files.items():
        path = tmp_path / relative_path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
    return tmp_path


def _git(repo_root: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=repo_root,
        check=True,
        capture_output=True,
        text=True,
    )


def _init_git_repo(repo_root: Path) -> None:
    _git(repo_root, "init")
    _git(repo_root, "config", "user.email", "test@example.com")
    _git(repo_root, "config", "user.name", "Test User")
    _git(repo_root, "add", ".")
    _git(repo_root, "commit", "-m", "base")


def _run_script(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(_script_path()), *args],
        cwd=_repo_root(),
        check=False,
        capture_output=True,
        text=True,
        env=_pythonpath_env(),
    )


def test_dry_run_selects_new_untracked_test_file(tmp_path: Path) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "packages/pkg_a/pyproject.toml": (
                "[build-system]\n"
                'requires = ["hatchling"]\n'
                'build-backend = "hatchling.build"\n\n'
                "[project]\n"
                'name = "pkg_a"\n'
                'version = "0.0.0"\n\n'
                "[tool.hatch.build.targets.wheel]\n"
                'packages = ["src/pkg_a"]\n'
            ),
            "packages/pkg_a/src/pkg_a/__init__.py": "VALUE = 1\n",
        },
    )
    _init_git_repo(repo_root)
    new_test_path = repo_root / "packages" / "pkg_a" / "tests" / "test_new_case.py"
    new_test_path.parent.mkdir(parents=True, exist_ok=True)
    new_test_path.write_text("def test_new_case() -> None:\n    assert True\n", encoding="utf-8")

    completed = _run_script(
        "--repo-root",
        str(repo_root),
        "--base-ref",
        "HEAD",
        "--dry-run",
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["mode"] == "selected"
    assert payload["selected_test_paths"] == ["packages/pkg_a/tests/test_new_case.py"]
    assert payload["summary"]["selected_test_count"] == 1


def test_dry_run_falls_back_to_full_suite_for_root_makefile_change(tmp_path: Path) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "Makefile": "test:\n\tpython -m pytest\n",
            "packages/pkg_a/pyproject.toml": (
                "[build-system]\n"
                'requires = ["hatchling"]\n'
                'build-backend = "hatchling.build"\n\n'
                "[project]\n"
                'name = "pkg_a"\n'
                'version = "0.0.0"\n\n'
                "[tool.hatch.build.targets.wheel]\n"
                'packages = ["src/pkg_a"]\n'
            ),
            "packages/pkg_a/src/pkg_a/__init__.py": "VALUE = 1\n",
            "packages/pkg_a/tests/test_core.py": "def test_core() -> None:\n    assert True\n",
        },
    )
    _init_git_repo(repo_root)
    (repo_root / "Makefile").write_text("test:\n\tpython -m pytest -q\n", encoding="utf-8")

    completed = _run_script(
        "--repo-root",
        str(repo_root),
        "--base-ref",
        "HEAD",
        "--dry-run",
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["mode"] == "full"
    assert payload["manual_inspection_required"] is True
    assert payload["full_suite_recommended"] is True
    assert "Makefile" in payload["full_suite_reason"]


def test_non_dry_run_escalates_for_manual_inspection_before_full_suite(tmp_path: Path) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "Makefile": "test:\n\tpython -m pytest\n",
            "packages/pkg_a/pyproject.toml": (
                "[build-system]\n"
                'requires = ["hatchling"]\n'
                'build-backend = "hatchling.build"\n\n'
                "[project]\n"
                'name = "pkg_a"\n'
                'version = "0.0.0"\n\n'
                "[tool.hatch.build.targets.wheel]\n"
                'packages = ["src/pkg_a"]\n'
            ),
            "packages/pkg_a/src/pkg_a/__init__.py": "VALUE = 1\n",
            "packages/pkg_a/tests/test_core.py": "def test_core() -> None:\n    assert False\n",
        },
    )
    _init_git_repo(repo_root)
    (repo_root / "Makefile").write_text("test:\n\tpython -m pytest -q\n", encoding="utf-8")

    completed = _run_script(
        "--repo-root",
        str(repo_root),
        "--base-ref",
        "HEAD",
    )

    assert completed.returncode == 3
    assert completed.stdout == ""
    assert "manual inspection required before full pytest" in completed.stderr
    assert "Makefile" in completed.stderr


def test_full_suite_can_be_run_explicitly_after_manual_inspection(tmp_path: Path) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "Makefile": "test:\n\tpython -m pytest\n",
            "packages/pkg_a/pyproject.toml": (
                "[build-system]\n"
                'requires = ["hatchling"]\n'
                'build-backend = "hatchling.build"\n\n'
                "[project]\n"
                'name = "pkg_a"\n'
                'version = "0.0.0"\n\n'
                "[tool.hatch.build.targets.wheel]\n"
                'packages = ["src/pkg_a"]\n'
            ),
            "packages/pkg_a/src/pkg_a/__init__.py": "VALUE = 1\n",
            "packages/pkg_a/tests/test_core.py": "def test_core() -> None:\n    assert True\n",
        },
    )
    _init_git_repo(repo_root)
    (repo_root / "Makefile").write_text("test:\n\tpython -m pytest -q\n", encoding="utf-8")

    completed = _run_script(
        "--repo-root",
        str(repo_root),
        "--base-ref",
        "HEAD",
        "--allow-full-fallback",
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert "falling back to full pytest suite" in completed.stderr
    assert "." in completed.stdout or "passed" in completed.stdout


def test_dry_run_skips_docs_only_out_of_scope_changes(tmp_path: Path) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "packages/pkg_a/pyproject.toml": (
                "[build-system]\n"
                'requires = ["hatchling"]\n'
                'build-backend = "hatchling.build"\n\n'
                "[project]\n"
                'name = "pkg_a"\n'
                'version = "0.0.0"\n\n'
                "[tool.hatch.build.targets.wheel]\n"
                'packages = ["src/pkg_a"]\n'
            ),
            "packages/pkg_a/src/pkg_a/__init__.py": "VALUE = 1\n",
            "packages/pkg_a/tests/test_core.py": "def test_core() -> None:\n    assert True\n",
        },
    )
    _init_git_repo(repo_root)
    docs_path = repo_root / "docs" / "note.md"
    docs_path.parent.mkdir(parents=True, exist_ok=True)
    docs_path.write_text("# note\n", encoding="utf-8")

    completed = _run_script(
        "--repo-root",
        str(repo_root),
        "--base-ref",
        "HEAD",
        "--dry-run",
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["mode"] == "skip"
    assert payload["changed_paths"] == ["docs/note.md"]
    assert payload["selected_test_paths"] == []
    assert payload["out_of_scope_full_fallback_paths"] == []


def test_dry_run_falls_back_when_requested_base_ref_is_missing(tmp_path: Path) -> None:
    repo_root = _bootstrap_repo(
        tmp_path,
        {
            "packages/pkg_a/pyproject.toml": (
                "[build-system]\n"
                'requires = ["hatchling"]\n'
                'build-backend = "hatchling.build"\n\n'
                "[project]\n"
                'name = "pkg_a"\n'
                'version = "0.0.0"\n\n'
                "[tool.hatch.build.targets.wheel]\n"
                'packages = ["src/pkg_a"]\n'
            ),
            "packages/pkg_a/src/pkg_a/__init__.py": "VALUE = 1\n",
        },
    )
    _init_git_repo(repo_root)
    new_test_path = repo_root / "packages" / "pkg_a" / "tests" / "test_new_case.py"
    new_test_path.parent.mkdir(parents=True, exist_ok=True)
    new_test_path.write_text("def test_new_case() -> None:\n    assert True\n", encoding="utf-8")

    completed = _run_script(
        "--repo-root",
        str(repo_root),
        "--base-ref",
        "origin/main",
        "--dry-run",
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["mode"] == "selected"
    assert payload["base_ref_requested"] == "origin/main"
    assert payload["base_ref_used"] is None
    assert payload["selected_test_paths"] == ["packages/pkg_a/tests/test_new_case.py"]
    assert payload["selector_warnings"]
