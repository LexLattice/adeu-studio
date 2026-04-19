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
    "packages/adeu_agent_harness/tests/fixtures/v48e",
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v61a",
    "packages/adeu_agentic_de/tests/fixtures/v64a",
    "packages/adeu_agentic_de/tests/fixtures/v64c",
    "packages/adeu_agentic_de/tests/fixtures/v65a",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v116/evidence_inputs/v48e_worker_delegation_topology_evidence_v116.json",
    "artifacts/agent_harness/v178/evidence_inputs/v64c_repo_writable_surface_hardening_evidence_v178.json",
)


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _script_path() -> Path:
    return (
        _repo_root()
        / "apps"
        / "api"
        / "scripts"
        / "run_agentic_de_delegated_worker_export_v65a.py"
    )


def _pythonpath_env() -> dict[str, str]:
    root = _repo_root()
    env = os.environ.copy()
    existing = env.get("PYTHONPATH")
    paths = [
        str(root / "apps" / "api" / "src"),
        str(root / "packages" / "adeu_agent_harness" / "src"),
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


def _copy_v65a_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v65a",
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
    spec = importlib.util.spec_from_file_location("run_v65a_script", _script_path())
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_default_cli_emits_delegated_worker_export_packet(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65a_input_tree(tmp_path)

    completed = _run_script("--repo-root", str(temp_root))

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "agentic_de_delegated_worker_export_packet@1"
    assert payload["export_verdict"] == "admitted_for_export"
    assert completed.stderr == ""


def test_delegated_worker_export_output_defaults_to_none() -> None:
    module = _load_script_module()

    args = module._parse_args([])

    assert args.delegated_worker_export_output is None


def test_cli_can_write_v65a_export_output(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65a_input_tree(tmp_path / "repo")
    export_path = tmp_path / "delegated_worker_export.json"

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--delegated-worker-export-output",
        str(export_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert completed.stdout == ""
    assert json.loads(export_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_delegated_worker_export_packet@1"
    )


def test_invalid_v65a_lane_drift_returns_clean_error(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v65a_input_tree(tmp_path / "repo")
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


def test_invalid_worker_topology_returns_clean_error(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65a_input_tree(tmp_path / "repo")
    topology_path = (
        temp_root
        / "packages"
        / "adeu_agent_harness"
        / "tests"
        / "fixtures"
        / "v48e"
        / "reference_worker_delegation_topology.json"
    )
    payload = json.loads(topology_path.read_text(encoding="utf-8"))
    payload["supporting_diagnostic_families"] = ["lineage_mismatch"]
    payload["supporting_diagnostic_ids"] = ["worker_delegation_topology:lineage_mismatch"]
    payload["worker_delegation_topology_id"] = "worker_delegation_topology:mutated"
    payload["semantic_hash"] = "mutated"
    topology_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    completed = _run_script("--repo-root", str(temp_root))

    assert completed.returncode == 2
    assert completed.stdout == ""
    assert completed.stderr.startswith("error: ")


def test_worker_topology_lineage_mismatch_returns_clean_error(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v65a_input_tree(tmp_path / "repo")
    topology_path = (
        temp_root
        / "packages"
        / "adeu_agent_harness"
        / "tests"
        / "fixtures"
        / "v48e"
        / "reference_worker_delegation_topology.json"
    )
    payload = json.loads(topology_path.read_text(encoding="utf-8"))
    payload["child_worker_boundary_conformance_report_ref"] = (
        "artifacts/agent_harness/v48e/mutated_child_boundary.json"
    )
    payload["semantic_hash"] = "mutated-lineage"
    topology_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    completed = _run_script("--repo-root", str(temp_root))

    assert completed.returncode == 2
    assert completed.stdout == ""
    assert completed.stderr.startswith("error: ")
