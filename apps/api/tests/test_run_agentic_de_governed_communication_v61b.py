from __future__ import annotations

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
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v167/evidence_inputs/v61a_governed_communication_evidence_v167.json",
)


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _script_path() -> Path:
    return (
        _repo_root() / "apps" / "api" / "scripts" / "run_agentic_de_governed_communication_v61b.py"
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


def _copy_v61b_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v61b",
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


def test_default_cli_emits_message_rewitness_gate(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v61b_input_tree(tmp_path)

    completed = _run_script("--repo-root", str(temp_root))

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "agentic_de_message_rewitness_gate_record@1"
    assert payload["rewitness_outcome"] == "witness_candidate_promoted"
    assert completed.stderr == ""


def test_cli_can_write_both_v61b_outputs(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v61b_input_tree(tmp_path / "repo")
    bridge_path = tmp_path / "bridge_office_binding.json"
    rewitness_path = tmp_path / "message_rewitness_gate.json"

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--bridge-office-binding-output",
        str(bridge_path),
        "--message-rewitness-gate-output",
        str(rewitness_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert completed.stdout == ""
    assert json.loads(bridge_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_bridge_office_binding_record@1"
    )
    assert json.loads(rewitness_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_message_rewitness_gate_record@1"
    )


def test_invalid_v61b_lane_drift_returns_clean_error(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v61b_input_tree(tmp_path / "repo")
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


def test_repo_root_rebases_default_v61a_egress_fixture(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v61b_input_tree(tmp_path / "repo")
    egress_path = (
        fixture_root.parent / "v61a" / "reference_agentic_de_communication_egress_packet.json"
    )
    payload = json.loads(egress_path.read_text(encoding="utf-8"))
    payload["selected_egress_posture"] = "completion_report"
    payload["communication_egress_id"] = None
    egress_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    bridge_path = tmp_path / "bridge_office_binding.json"
    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--bridge-office-binding-output",
        str(bridge_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["rewitness_outcome"] == "witness_candidate_promoted"
