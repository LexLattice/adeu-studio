from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest
from adeu_agentic_de import (
    load_task_charter_packet,
    run_agentic_de_governed_communication_v61a,
)
from adeu_ir.repo import repo_root
from urm_runtime import CopilotSessionSendRequest

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v61a"

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


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _repo_root_path() -> Path:
    return repo_root(anchor=Path(__file__))


def _copy_v61a_input_tree(tmp_path: Path) -> tuple[Path, Path]:
    repo_root_path = _repo_root_path()
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


def _load_send_request(root: Path) -> CopilotSessionSendRequest:
    return CopilotSessionSendRequest.model_validate(
        _load_json(root, "reference_copilot_session_send_request.json")
    )


def test_reference_outputs_match_live_v61a_runner(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v61a_input_tree(tmp_path)

    ingress, descriptor, interpretation, egress = run_agentic_de_governed_communication_v61a(
        repo_root_path=temp_root,
    )

    assert ingress.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_communication_ingress_packet.json",
    )
    assert descriptor.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_surface_authority_descriptor.json",
    )
    assert interpretation.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_ingress_interpretation_record.json",
    )
    assert egress.model_dump(mode="json") == _load_json(
        FIXTURE_ROOT,
        "reference_agentic_de_communication_egress_packet.json",
    )


def test_v61a_outputs_remain_posture_only_and_exact_seam_bound(tmp_path: Path) -> None:
    temp_root, _fixture_root = _copy_v61a_input_tree(tmp_path)

    ingress, descriptor, interpretation, egress = run_agentic_de_governed_communication_v61a(
        repo_root_path=temp_root,
    )

    assert ingress.target_arc == "vNext+167"
    assert ingress.target_path == "V61-A"
    assert ingress.evidence_only is True
    assert ingress.changes_live_behavior_by_default is False
    assert ingress.source_principal_class == "human_operator"
    assert ingress.speaker_class == "resident_session_user_message"
    assert ingress.surface_class == "resident_copilot_send_api"
    assert ingress.selected_runtime_message_method == "copilot.user_message"
    assert descriptor.surface_affordance_classes == [
        "communication",
        "advisory",
        "authority_request",
    ]
    assert "not bridge office" in descriptor.bounded_authority_posture_summary
    assert interpretation.interpretation_posture == "status_request"
    assert "charter_mutation_not_selected_in_v61a" in interpretation.interpretation_reason_codes
    assert egress.selected_egress_posture == "status_update"
    assert egress.selected_egress_surface_ref == (
        "apps/api/src/adeu_api/urm_routes.py:/copilot/send"
    )


def test_charter_amendment_candidate_remains_posture_only(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v61a_input_tree(tmp_path)
    request_path = fixture_root / "reference_copilot_session_send_request.json"
    payload = _load_json(fixture_root, "reference_copilot_session_send_request.json")
    assert isinstance(payload, dict)
    message = payload["message"]
    assert isinstance(message, dict)
    params = message["params"]
    assert isinstance(params, dict)
    params["text"] = "Please change target scope in the charter for the next step."
    request_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    _ingress, _descriptor, interpretation, egress = run_agentic_de_governed_communication_v61a(
        repo_root_path=temp_root,
    )

    assert interpretation.interpretation_posture == "charter_amendment_candidate"
    assert egress.selected_egress_posture == "advisory_only_message"
    assert (
        interpretation.task_charter_ref
        == load_task_charter_packet(
            temp_root
            / "packages"
            / "adeu_agentic_de"
            / "tests"
            / "fixtures"
            / "v60a"
            / "reference_agentic_de_task_charter_packet.json"
        ).charter_id
    )


def test_invalid_send_method_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v61a_input_tree(tmp_path)
    request_path = fixture_root / "reference_copilot_session_send_request.json"
    payload = _load_json(fixture_root, "reference_copilot_session_send_request.json")
    assert isinstance(payload, dict)
    message = payload["message"]
    assert isinstance(message, dict)
    message["method"] = "copilot.tool_call"
    request_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="copilot.user_message only"):
        run_agentic_de_governed_communication_v61a(repo_root_path=temp_root)


def test_send_request_session_mismatch_fails_closed(tmp_path: Path) -> None:
    temp_root, fixture_root = _copy_v61a_input_tree(tmp_path)
    request_path = fixture_root / "reference_copilot_session_send_request.json"
    payload = _load_json(fixture_root, "reference_copilot_session_send_request.json")
    assert isinstance(payload, dict)
    payload["session_id"] = "copilot-session-mismatch"
    request_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    with pytest.raises(ValueError, match="shipped V60 resident session"):
        run_agentic_de_governed_communication_v61a(repo_root_path=temp_root)


def test_default_symlinked_repo_root_fails_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    import adeu_agentic_de.checker as checker_module

    temp_root, _fixture_root = _copy_v61a_input_tree(tmp_path / "repo")
    symlink_root = tmp_path / "repo-link"
    symlink_root.symlink_to(temp_root, target_is_directory=True)

    monkeypatch.setattr(checker_module, "repo_root", lambda anchor: symlink_root)

    with pytest.raises(
        ValueError,
        match="repository root may not be a symlink for V61-A communication",
    ):
        run_agentic_de_governed_communication_v61a()
