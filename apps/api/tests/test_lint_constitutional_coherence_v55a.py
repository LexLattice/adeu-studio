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
    return _repo_root() / "apps" / "api" / "scripts" / "lint_constitutional_coherence_v55a.py"


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


def _run_lint(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(_script_path()), *args],
        cwd=_repo_root(),
        check=False,
        capture_output=True,
        text=True,
        env=_pythonpath_env(),
    )


def test_default_cli_emits_report_stdout_and_unresolved_stderr() -> None:
    completed = _run_lint()

    assert completed.returncode == 0, completed.stdout + completed.stderr
    report_payload = json.loads(completed.stdout)
    unresolved_payload = json.loads(completed.stderr)

    assert report_payload["schema"] == "constitutional_coherence_report@1"
    assert unresolved_payload["schema"] == "constitutional_unresolved_seam_register@1"
    assert unresolved_payload["entry_count"] == 7


def test_unresolved_output_path_suppresses_default_stderr(tmp_path: Path) -> None:
    unresolved_path = tmp_path / "unresolved.json"

    completed = _run_lint("--unresolved-output", str(unresolved_path))

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert completed.stderr == ""

    unresolved_payload = json.loads(unresolved_path.read_text(encoding="utf-8"))
    assert unresolved_payload["schema"] == "constitutional_unresolved_seam_register@1"
    assert unresolved_payload["entry_count"] == 7
