from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

from adeu_ir.repo import repo_root

FIXTURE_DIRS = (
    "packages/adeu_agentic_de/tests/fixtures/v59a",
    "packages/adeu_agentic_de/tests/fixtures/v59b",
    "packages/adeu_agentic_de/tests/fixtures/v60a",
    "packages/adeu_agentic_de/tests/fixtures/v60b",
    "packages/adeu_agentic_de/tests/fixtures/v60c",
    "packages/adeu_agentic_de/tests/fixtures/v61a",
)

EVIDENCE_FILES = (
    "artifacts/agent_harness/v164/evidence_inputs/v60a_continuation_starter_evidence_v164.json",
    "artifacts/agent_harness/v165/evidence_inputs/v60b_continuation_refresh_evidence_v165.json",
)


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _script_path() -> Path:
    return (
        _repo_root() / "apps" / "api" / "scripts" / "run_agentic_de_governed_communication_v61a.py"
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


def _copy_v61a_input_tree(tmp_path: Path) -> tuple[Path, Path]:
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
        tmp_path / "packages" / "adeu_agentic_de" / "tests" / "fixtures" / "v61a",
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


def test_default_cli_emits_communication_egress_packet(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v61a_input_tree(tmp_path)

    completed = _run_script("--repo-root", str(temp_root))

    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["schema"] == "agentic_de_communication_egress_packet@1"
    assert payload["selected_egress_posture"] == "status_update"
    assert completed.stderr == ""


def test_cli_can_write_all_v61a_outputs(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v61a_input_tree(tmp_path / "repo")
    ingress_path = tmp_path / "communication_ingress.json"
    descriptor_path = tmp_path / "surface_authority_descriptor.json"
    interpretation_path = tmp_path / "ingress_interpretation.json"
    egress_path = tmp_path / "communication_egress.json"

    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--communication-ingress-output",
        str(ingress_path),
        "--surface-authority-descriptor-output",
        str(descriptor_path),
        "--ingress-interpretation-output",
        str(interpretation_path),
        "--communication-egress-output",
        str(egress_path),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert completed.stdout == ""
    assert json.loads(ingress_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_communication_ingress_packet@1"
    )
    assert json.loads(descriptor_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_surface_authority_descriptor@1"
    )
    assert json.loads(interpretation_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_ingress_interpretation_record@1"
    )
    assert json.loads(egress_path.read_text(encoding="utf-8"))["schema"] == (
        "agentic_de_communication_egress_packet@1"
    )


def test_invalid_v61a_lane_drift_returns_clean_error(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v61a_input_tree(tmp_path / "repo")
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


def test_repo_root_rebases_default_v61a_send_request_fixture(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v61a_input_tree(tmp_path / "repo")
    send_request_path = fixture_root / "reference_copilot_session_send_request.json"
    payload = json.loads(send_request_path.read_text(encoding="utf-8"))
    message = payload["message"]
    assert isinstance(message, dict)
    params = message["params"]
    assert isinstance(params, dict)
    params["text"] = "Please clarify the next continuation basis?"
    send_request_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    interpretation_path = tmp_path / "ingress_interpretation.json"
    completed = _run_script(
        "--repo-root",
        str(temp_root),
        "--ingress-interpretation-output",
        str(interpretation_path),
        "--communication-egress-output",
        str(tmp_path / "communication_egress.json"),
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    interpretation_payload = json.loads(interpretation_path.read_text(encoding="utf-8"))
    assert interpretation_payload["interpretation_posture"] == "clarification_response"
