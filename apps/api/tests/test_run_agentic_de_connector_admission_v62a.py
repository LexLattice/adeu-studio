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
    "packages/adeu_agentic_de/tests/fixtures/v62a",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v167/evidence_inputs/v61a_governed_communication_evidence_v167.json",
    "artifacts/agent_harness/v168/evidence_inputs/v61b_bridge_office_rewitness_evidence_v168.json",
    "artifacts/agent_harness/v169/evidence_inputs/v61c_governed_communication_hardening_evidence_v169.json",
)


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _script_path() -> Path:
    return (
        _repo_root() / "apps" / "api" / "scripts" / "run_agentic_de_connector_admission_v62a.py"
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


def _copy_v62a_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v62a",
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


def test_default_cli_emits_ingress_bridge_packet(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v62a_input_tree(tmp_path)

    completed = _run_script("--repo-root", str(temp_root))

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "agentic_de_external_assistant_ingress_bridge_packet@1"
    assert payload["selected_connector_principal_class"] == "external_assistant"
    assert completed.stderr == ""


def test_cli_can_write_all_v62a_outputs(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v62a_input_tree(tmp_path / "repo")
    admission_path = tmp_path / "connector_admission.json"
    ingress_bridge_path = tmp_path / "external_assistant_ingress_bridge.json"

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--connector-admission-output",
        str(admission_path),
        "--external-assistant-ingress-bridge-output",
        str(ingress_bridge_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert completed.stdout == ""
    assert json.loads(admission_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_connector_admission_record@1"
    )
    assert json.loads(ingress_bridge_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_external_assistant_ingress_bridge_packet@1"
    )


def test_stale_snapshot_returns_clean_error(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v62a_input_tree(tmp_path / "repo")

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--min-acceptable-ts",
        "2026-04-17T00:01:00+00:00",
    )

    assert completed.returncode == 2
    assert completed.stdout == ""
    assert completed.stderr.startswith("error: ")
