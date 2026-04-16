from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

from adeu_ir.repo import repo_root

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v56a",
    "packages/adeu_agentic_de/tests/fixtures/v56b",
    "packages/adeu_agentic_de/tests/fixtures/v56c",
    "packages/adeu_agentic_de/tests/fixtures/v59a",
    "packages/adeu_agentic_de/tests/fixtures/v59b",
    "packages/adeu_agentic_de/tests/fixtures/v60a",
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v60c",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v161/evidence_inputs/v59a_workspace_continuity_starter_evidence_v161.json",
    "artifacts/agent_harness/v162/evidence_inputs/v59b_workspace_continuity_restoration_evidence_v162.json",
    "artifacts/agent_harness/v164/evidence_inputs/v60a_continuation_starter_evidence_v164.json",
    "artifacts/agent_harness/v165/evidence_inputs/v60b_continuation_refresh_evidence_v165.json",
)


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _script_path() -> Path:
    return (
        _repo_root()
        / "apps"
        / "api"
        / "scripts"
        / "evaluate_agentic_de_continuation_v60c.py"
    )


def _pythonpath_env() -> dict[str, str]:
    root = _repo_root()
    env = os.environ.copy()
    existing = env.get("PYTHONPATH")
    paths = [
        str(root / "apps" / "api" / "src"),
        str(root / "packages" / "adeu_agentic_de" / "src"),
        str(root / "packages" / "urm_runtime" / "src"),
    ]
    if existing:
        paths.append(existing)
    env["PYTHONPATH"] = os.pathsep.join(paths)
    env["TZ"] = "UTC"
    env["LC_ALL"] = "C"
    return env


def _copy_v60c_input_tree(tmp_path: Path) -> tuple[Path, Path]:
    repo_root_path = _repo_root()
    for relative_dir in FIXTURE_DIRS:
        shutil.copytree(
            repo_root_path / relative_dir,
            tmp_path / relative_dir,
            dirs_exist_ok=True,
        )
    for relative_path in EVIDENCE_FILES:
        source = repo_root_path / relative_path
        target = tmp_path / relative_path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    return (
        tmp_path,
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v60c",
    )


def _run_script(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(_script_path()), *args],
        cwd=_repo_root(),
        check=False,
        capture_output=True,
        text=True,
        env=_pythonpath_env(),
    )


def test_default_cli_emits_continuation_hardening_register(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v60c_input_tree(tmp_path)

    completed = _run_script("--repo-root", str(temp_root))

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "agentic_de_continuation_hardening_register@1"
    assert payload["target_path"] == "V60-C"
    assert completed.stderr == ""


def test_cli_can_write_v60c_output(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v60c_input_tree(tmp_path / "repo")
    hardening_output_path = tmp_path / "continuation_hardening.json"

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--hardening-output",
        str(hardening_output_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert completed.stdout == ""
    assert json.loads(hardening_output_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_continuation_hardening_register@1"
    )


def test_invalid_v60c_lane_drift_returns_clean_error(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v60c_input_tree(tmp_path / "repo")
    lane_drift_path = fixture_root / "reference_agentic_de_lane_drift_record.json"
    payload = json.loads(lane_drift_path.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    lane_drift_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    completed = _run_script("--repo-root", str(temp_root))

    assert completed.returncode == 2
    assert completed.stdout == ""
    assert completed.stderr.startswith("error: ")
