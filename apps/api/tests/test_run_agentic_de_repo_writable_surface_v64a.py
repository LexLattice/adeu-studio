from __future__ import annotations

import importlib.util
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

from adeu_ir.repo import repo_root

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v59a",
    "packages/adeu_agentic_de/tests/fixtures/v60a",
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v61a",
    "packages/adeu_agentic_de/tests/fixtures/v64a",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v163/evidence_inputs/v59c_workspace_continuity_hardening_evidence_v163.json",
    "artifacts/agent_harness/v166/evidence_inputs/v60c_continuation_hardening_evidence_v166.json",
    "artifacts/agent_harness/v169/evidence_inputs/v61c_governed_communication_hardening_evidence_v169.json",
)


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _script_path() -> Path:
    return (
        _repo_root() / "apps" / "api" / "scripts" / "run_agentic_de_repo_writable_surface_v64a.py"
    )


def _pythonpath_env() -> dict[str, str]:
    root = _repo_root()
    env = os.environ.copy()
    existing = env.get("PYTHONPATH")
    paths = [
        str(root / "apps" / "api" / "src"),
        str(root / "packages" / "adeu_agentic_de" / "src"),
        str(root / "packages" / "adeu_ir" / "src"),
        str(root / "packages" / "urm_runtime" / "src"),
    ]
    if existing:
        paths.append(existing)
    env["PYTHONPATH"] = os.pathsep.join(paths)
    env["TZ"] = "UTC"
    env["LC_ALL"] = "C"
    return env


def _copy_v64a_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v64a",
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


def _load_script_module():
    spec = importlib.util.spec_from_file_location("run_v64a_script", _script_path())
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_default_cli_emits_repo_write_surface_admission(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64a_input_tree(tmp_path)

    completed = _run_script("--repo-root", str(temp_root))

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "agentic_de_repo_write_surface_admission_record@1"
    assert payload["admission_verdict"] == "admitted"
    assert completed.stderr == ""


def test_repo_write_surface_admission_output_defaults_to_none() -> None:
    module = _load_script_module()

    args = module._parse_args([])

    assert args.repo_write_surface_admission_output is None


def test_cli_can_write_all_v64a_outputs(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64a_input_tree(tmp_path / "repo")
    descriptor_path = tmp_path / "repo_writable_surface_descriptor.json"
    lease_path = tmp_path / "repo_write_lease.json"
    admission_path = tmp_path / "repo_write_surface_admission.json"

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--repo-writable-surface-descriptor-output",
        str(descriptor_path),
        "--repo-write-lease-output",
        str(lease_path),
        "--repo-write-surface-admission-output",
        str(admission_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert completed.stdout == ""
    assert json.loads(descriptor_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_repo_writable_surface_descriptor@1"
    )
    assert json.loads(lease_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_repo_write_lease_record@1"
    )
    assert json.loads(admission_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_repo_write_surface_admission_record@1"
    )


def test_invalid_v64a_lane_drift_returns_clean_error(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v64a_input_tree(tmp_path / "repo")
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
