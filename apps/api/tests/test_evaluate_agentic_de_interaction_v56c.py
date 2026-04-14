from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

from adeu_ir.repo import repo_root


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _script_path() -> Path:
    return _repo_root() / "apps" / "api" / "scripts" / "evaluate_agentic_de_interaction_v56c.py"


def _pythonpath_env() -> dict[str, str]:
    root = _repo_root()
    env = os.environ.copy()
    existing = env.get("PYTHONPATH")
    paths = [
        str(root / "apps" / "api" / "src"),
        str(root / "packages" / "urm_runtime" / "src"),
    ]
    if existing:
        paths.append(existing)
    env["PYTHONPATH"] = os.pathsep.join(paths)
    env["TZ"] = "UTC"
    env["LC_ALL"] = "C"
    return env


def _run_script(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(_script_path()), *args],
        cwd=_repo_root(),
        check=False,
        capture_output=True,
        text=True,
        env=_pythonpath_env(),
    )


def test_default_cli_emits_runtime_harvest_record_to_stdout() -> None:
    completed = _run_script()

    assert completed.returncode == 0, completed.stdout + completed.stderr
    harvest_payload = json.loads(completed.stdout)
    assert harvest_payload["schema"] == "agentic_de_runtime_harvest_record@1"
    assert harvest_payload["target_path"] == "V56-C"
    assert completed.stderr == ""


def test_outputs_can_write_governance_and_migration_registers(tmp_path: Path) -> None:
    harvest_path = tmp_path / "harvest.json"
    governance_path = tmp_path / "governance.json"
    migration_path = tmp_path / "migration.json"

    completed = _run_script(
        "--harvest-output",
        str(harvest_path),
        "--governance-output",
        str(governance_path),
        "--migration-output",
        str(migration_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert completed.stdout == ""
    harvest_payload = json.loads(harvest_path.read_text(encoding="utf-8"))
    governance_payload = json.loads(governance_path.read_text(encoding="utf-8"))
    migration_payload = json.loads(migration_path.read_text(encoding="utf-8"))
    assert harvest_payload["schema"] == "agentic_de_runtime_harvest_record@1"
    assert governance_payload["schema"] == "agentic_de_governance_calibration_register@1"
    assert migration_payload["schema"] == "agentic_de_migration_decision_register@1"


def test_invalid_v56b_evidence_returns_clean_error(tmp_path: Path) -> None:
    evidence_fixture = (
        _repo_root()
        / "artifacts"
        / "agent_harness"
        / "v153"
        / "evidence_inputs"
        / "v56b_bounded_live_gate_starter_evidence_v153.json"
    )
    payload = json.loads(evidence_fixture.read_text(encoding="utf-8"))
    payload["selected_live_gate_action_classes_for_v56b"] = ["local_write", "stronger_execute"]
    override_path = tmp_path / "bad_v56b_evidence.json"
    override_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    completed = _run_script("--v56b-evidence", str(override_path))

    assert completed.returncode == 2
    assert completed.stdout == ""
    assert completed.stderr.startswith("error: ")
