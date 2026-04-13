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
    return _repo_root() / "apps" / "api" / "scripts" / "lint_constitutional_coherence_v55c.py"


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


def test_default_cli_emits_governance_stdout_and_migration_stderr() -> None:
    completed = _run_lint()

    assert completed.returncode == 0, completed.stdout + completed.stderr
    governance_payload = json.loads(completed.stdout)
    migration_payload = json.loads(completed.stderr)

    assert governance_payload["schema"] == "constitutional_governance_calibration_register@1"
    assert governance_payload["target_path"] == "V55-C"
    assert governance_payload["entry_count"] == 3
    assert migration_payload["schema"] == "constitutional_migration_decision_register@1"
    assert migration_payload["target_path"] == "V55-C"
    assert migration_payload["entry_count"] == 6


def test_invalid_v55b_drift_path_fails_closed(tmp_path: Path) -> None:
    bad_path = tmp_path / "bad_v55b_drift.json"
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

    completed = _run_lint("--v55b-drift", str(bad_path))

    assert completed.returncode != 0
    assert "error:" in completed.stderr
    assert "required handoff posture" in completed.stderr
