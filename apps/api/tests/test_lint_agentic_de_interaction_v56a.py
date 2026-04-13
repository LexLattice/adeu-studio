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
    return _repo_root() / "apps" / "api" / "scripts" / "lint_agentic_de_interaction_v56a.py"


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


def test_default_cli_emits_checkpoint_stdout_only_for_reference_dry_run() -> None:
    completed = _run_lint()

    assert completed.returncode == 0, completed.stdout + completed.stderr
    checkpoint_payload = json.loads(completed.stdout)
    assert checkpoint_payload["schema"] == "agentic_de_membrane_checkpoint@1"
    assert checkpoint_payload["status"] == "accepted"
    assert completed.stderr == ""


def test_conformance_and_diagnostics_outputs_can_be_written_explicitly(tmp_path: Path) -> None:
    diagnostics_path = tmp_path / "diagnostics.json"
    conformance_path = tmp_path / "conformance.json"

    completed = _run_lint(
        "--diagnostics-output",
        str(diagnostics_path),
        "--conformance-output",
        str(conformance_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    diagnostics_payload = json.loads(diagnostics_path.read_text(encoding="utf-8"))
    conformance_payload = json.loads(conformance_path.read_text(encoding="utf-8"))
    assert diagnostics_payload["schema"] == "agentic_de_morph_diagnostics@1"
    assert conformance_payload["schema"] == "agentic_de_conformance_report@1"
    assert conformance_payload["executed_or_observed_effect"] == "no_live_effect"


def test_missing_evidence_emits_warn_diagnostics_to_stderr(tmp_path: Path) -> None:
    repo_root = _repo_root()
    proposal_path = (
        repo_root
        / "packages"
        / "adeu_agentic_de"
        / "tests"
        / "fixtures"
        / "v56a"
        / "reference_agentic_de_action_proposal.json"
    )
    payload = json.loads(proposal_path.read_text(encoding="utf-8"))
    payload["evidence_refs"] = []
    payload["proposal_id"] = None
    override_path = tmp_path / "proposal.json"
    override_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    completed = _run_lint("--action-proposal", str(override_path))

    assert completed.returncode == 0, completed.stdout + completed.stderr
    checkpoint_payload = json.loads(completed.stdout)
    diagnostics_payload = json.loads(completed.stderr)
    assert checkpoint_payload["status"] == "residualized"
    assert checkpoint_payload["reason_code"] == "insufficient_evidence"
    assert diagnostics_payload["schema"] == "agentic_de_morph_diagnostics@1"


def test_missing_input_returns_clean_error(tmp_path: Path) -> None:
    missing_path = tmp_path / "missing.json"

    completed = _run_lint("--domain-packet", str(missing_path))

    assert completed.returncode == 2
    assert completed.stdout == ""
    assert completed.stderr.startswith("error: ")
