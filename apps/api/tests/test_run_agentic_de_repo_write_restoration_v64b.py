from __future__ import annotations

import importlib.util
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

from adeu_agentic_de.workspace_continuity import DEFAULT_WORKSPACE_CONTINUITY_PAYLOAD_TEXT
from adeu_ir.repo import repo_root

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v59a",
    "packages/adeu_agentic_de/tests/fixtures/v64a",
    "packages/adeu_agentic_de/tests/fixtures/v64b",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v176/evidence_inputs/v64a_repo_writable_surface_starter_evidence_v176.json",
)


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _script_path() -> Path:
    return (
        _repo_root() / "apps" / "api" / "scripts" / "run_agentic_de_repo_write_restoration_v64b.py"
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


def _seed_prior_governed_target_state(temp_root: Path) -> None:
    observation_payload = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_agentic_de"
            / "tests"
            / "fixtures"
            / "v59a"
            / "reference_agentic_de_local_effect_observation_record.json"
        ).read_text(encoding="utf-8")
    )
    observed_entry = observation_payload["observed_write_set"][0]
    target_path = (
        temp_root
        / "artifacts"
        / "agentic_de"
        / "v59"
        / "workspace_continuity"
        / "runtime"
        / "reference_patch_candidate.diff"
    )
    target_path.parent.mkdir(parents=True, exist_ok=True)
    target_path.write_text(DEFAULT_WORKSPACE_CONTINUITY_PAYLOAD_TEXT, encoding="utf-8")
    marker_path = (
        temp_root
        / "artifacts"
        / "agentic_de"
        / "v59"
        / "workspace_continuity"
        / "_observer"
        / "reference_governed_target_lineage.json"
    )
    marker_path.parent.mkdir(parents=True, exist_ok=True)
    marker_path.write_text(
        json.dumps(
            {
                "target_relative_path": "runtime/reference_patch_candidate.diff",
                "governed_observation_ref": observation_payload["observation_id"],
                "target_content_sha256": observed_entry["content_sha256"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


def _copy_v64b_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
    _seed_prior_governed_target_state(tmp_path)
    return (
        tmp_path,
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v64b",
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
    spec = importlib.util.spec_from_file_location("run_v64b_script", _script_path())
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_default_cli_emits_repo_write_reintegration(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64b_input_tree(tmp_path)

    completed = _run_script("--repo-root", str(temp_root))

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "agentic_de_repo_write_reintegration_report@1"
    assert payload["reintegration_status"] == "reintegrated"
    assert completed.stderr == ""


def test_repo_write_reintegration_output_defaults_to_none() -> None:
    module = _load_script_module()

    args = module._parse_args([])

    assert args.repo_write_reintegration_output is None


def test_cli_can_write_all_v64b_outputs(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64b_input_tree(tmp_path / "repo")
    restoration_path = tmp_path / "repo_write_restoration.json"
    reintegration_path = tmp_path / "repo_write_reintegration.json"

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--repo-write-restoration-output",
        str(restoration_path),
        "--repo-write-reintegration-output",
        str(reintegration_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert completed.stdout == ""
    assert json.loads(restoration_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_repo_write_restoration_record@1"
    )
    assert json.loads(reintegration_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_repo_write_reintegration_report@1"
    )


def test_cli_accepts_equivalent_normalized_target_relative_path(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v64b_input_tree(tmp_path / "repo")

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--target-relative-path",
        " runtime//reference_patch_candidate.diff ",
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["reintegration_status"] == "reintegrated"


def test_invalid_v64b_lane_drift_returns_clean_error(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v64b_input_tree(tmp_path / "repo")
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
