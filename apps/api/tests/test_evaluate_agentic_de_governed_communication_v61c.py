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
    "packages/adeu_agentic_de/tests/fixtures/v60a",
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v61a",
    "packages/adeu_agentic_de/tests/fixtures/v61b",
    "packages/adeu_agentic_de/tests/fixtures/v61c",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v167/evidence_inputs/v61a_governed_communication_evidence_v167.json",
    "artifacts/agent_harness/v168/evidence_inputs/v61b_bridge_office_rewitness_evidence_v168.json",
)


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _script_path() -> Path:
    return (
        _repo_root()
        / "apps"
        / "api"
        / "scripts"
        / "evaluate_agentic_de_governed_communication_v61c.py"
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


def _copy_v61c_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v61c",
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
    spec = importlib.util.spec_from_file_location("evaluate_v61c_script", _script_path())
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_default_cli_emits_governed_communication_hardening_register(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v61c_input_tree(tmp_path)

    completed = _run_script("--repo-root", str(temp_root))

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "agentic_de_governed_communication_hardening_register@1"
    assert payload["entries"][0]["recommended_outcome"] == (
        "candidate_for_later_communication_hardening"
    )
    assert completed.stderr == ""


def test_hardening_output_defaults_to_none() -> None:
    module = _load_script_module()

    args = module._parse_args([])

    assert args.hardening_output is None


def test_cli_can_write_v61c_hardening_output(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v61c_input_tree(tmp_path / "repo")
    hardening_path = tmp_path / "governed_communication_hardening.json"

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--hardening-output",
        str(hardening_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert completed.stdout == ""
    assert json.loads(hardening_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_governed_communication_hardening_register@1"
    )


def test_invalid_v61c_lane_drift_returns_clean_error(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v61c_input_tree(tmp_path / "repo")
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


def test_repo_root_rebases_default_v61b_rewitness_fixture(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v61c_input_tree(tmp_path / "repo")
    rewitness_path = (
        fixture_root.parent / "v61b" / "reference_agentic_de_message_rewitness_gate_record.json"
    )
    payload = json.loads(rewitness_path.read_text(encoding="utf-8"))
    payload["certificate_ref_or_none"] = "certificate:local-review-note"
    payload["message_rewitness_gate_id"] = None
    rewitness_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    completed = _run_script("--repo-root", str(temp_root))

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    entry = payload["entries"][0]
    assert entry["positive_rewitness_certificate_ref_or_none"] == "certificate:local-review-note"
