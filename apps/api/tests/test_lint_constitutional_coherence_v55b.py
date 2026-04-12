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
    return _repo_root() / "apps" / "api" / "scripts" / "lint_constitutional_coherence_v55b.py"


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
    assert report_payload["target_path"] == "V55-B"
    assert unresolved_payload["schema"] == "constitutional_unresolved_seam_register@1"
    assert unresolved_payload["target_path"] == "V55-B"
    assert unresolved_payload["entry_count"] == 8


def test_invalid_lane_drift_path_fails_closed(tmp_path: Path) -> None:
    bad_path = tmp_path / "bad_lane_drift.json"
    bad_path.write_text(
        json.dumps(
            {
                "schema": "constitutional_coherence_lane_drift_record@1",
                "record_id": "constitutional_lane_drift:badbadbadbadbadb",
                "target_arc": "vNext+150",
                "target_path": "V55-B",
                "prior_lane_ref": "docs/LOCKED_CONTINUATION_vNEXT_PLUS149.md",
                "entry_count": 0,
                "entries": [],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )

    completed = _run_lint("--lane-drift", str(bad_path))

    assert completed.returncode != 0
    assert "error:" in completed.stderr
    assert "required handoff posture" in completed.stderr
