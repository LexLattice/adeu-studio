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
    return _repo_root() / "apps" / "api" / "scripts" / "run_agentic_de_interaction_v56b.py"


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


def test_default_cli_emits_action_ticket_to_stdout() -> None:
    completed = _run_script()

    assert completed.returncode == 0, completed.stdout + completed.stderr
    ticket_payload = json.loads(completed.stdout)
    assert ticket_payload["schema"] == "agentic_de_action_ticket@1"
    assert ticket_payload["exact_action_class"] == "local_write"
    assert completed.stderr == ""


def test_outputs_can_write_runtime_state_diagnostics_and_conformance(tmp_path: Path) -> None:
    runtime_state_path = tmp_path / "runtime_state.json"
    diagnostics_path = tmp_path / "diagnostics.json"
    conformance_path = tmp_path / "conformance.json"

    completed = _run_script(
        "--runtime-state-output",
        str(runtime_state_path),
        "--diagnostics-output",
        str(diagnostics_path),
        "--conformance-output",
        str(conformance_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    runtime_payload = json.loads(runtime_state_path.read_text(encoding="utf-8"))
    diagnostics_payload = json.loads(diagnostics_path.read_text(encoding="utf-8"))
    conformance_payload = json.loads(conformance_path.read_text(encoding="utf-8"))
    assert runtime_payload["schema"] == "agentic_de_runtime_state@1"
    assert diagnostics_payload["schema"] == "agentic_de_morph_diagnostics@1"
    assert conformance_payload["schema"] == "agentic_de_conformance_report@1"
    assert "ticket_issued=true" in conformance_payload["delta_notes"]


def test_incompatible_runtime_state_emits_checkpoint_stdout_and_warn_diagnostics(
    tmp_path: Path,
) -> None:
    runtime_fixture = (
        _repo_root()
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v56b"
        / "reference_agentic_de_runtime_state.json"
    )
    payload = json.loads(runtime_fixture.read_text(encoding="utf-8"))
    payload["compatibility_status"] = "incompatible"
    payload["compatibility_note"] = "Runtime state is intentionally incompatible for this test."
    payload["state_id"] = None
    override_path = tmp_path / "runtime_state.json"
    override_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    completed = _run_script("--runtime-state", str(override_path))

    assert completed.returncode == 0, completed.stdout + completed.stderr
    checkpoint_payload = json.loads(completed.stdout)
    diagnostics_payload = json.loads(completed.stderr)
    assert checkpoint_payload["schema"] == "agentic_de_membrane_checkpoint@1"
    assert checkpoint_payload["status"] == "accepted"
    assert diagnostics_payload["findings"][-1]["code"] == "LIVE_ACTION_TICKET_WITHHELD"


def test_invalid_lane_drift_returns_clean_error(tmp_path: Path) -> None:
    fixture = (
        _repo_root()
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v56b"
        / "reference_agentic_de_lane_drift_record.json"
    )
    payload = json.loads(fixture.read_text(encoding="utf-8"))
    payload["entries"] = payload["entries"][:-1]
    payload["entry_count"] = len(payload["entries"])
    payload["record_id"] = None
    override_path = tmp_path / "lane_drift.json"
    override_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    completed = _run_script("--lane-drift", str(override_path))

    assert completed.returncode == 2
    assert completed.stdout == ""
    assert completed.stderr.startswith("error: ")
