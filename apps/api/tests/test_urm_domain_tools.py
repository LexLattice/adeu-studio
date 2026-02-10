from __future__ import annotations

import shutil
from pathlib import Path

import pytest
from adeu_api.urm_routes import (
    _reset_manager_for_tests,
    urm_tool_call_endpoint,
    urm_worker_run_endpoint,
)
from fastapi import HTTPException
from urm_runtime.models import ToolCallRequest, WorkerRunRequest


def _prepare_fake_codex_exec(*, tmp_path: Path) -> Path:
    fixture = Path(__file__).resolve().parent / "fixtures" / "codex_exec" / "fake_codex.py"
    target = tmp_path / "fake_codex_exec.py"
    shutil.copy2(fixture, target)
    target.chmod(0o755)
    return target


def _configure_exec_fixture(
    *,
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    fixture_path = Path(__file__).resolve().parent / "fixtures" / "codex_exec" / "success.jsonl"
    monkeypatch.setenv("FAKE_CODEX_JSONL_PATH", str(fixture_path))
    monkeypatch.setenv("FAKE_CODEX_EXIT_CODE", "0")
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))


def test_urm_worker_run_endpoint_idempotent_replay(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex_exec(tmp_path=tmp_path)
    _configure_exec_fixture(monkeypatch=monkeypatch, tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    _reset_manager_for_tests()

    request = WorkerRunRequest(
        provider="codex",
        role="pipeline_worker",
        client_request_id="worker-route-1",
        prompt="domain tool worker route",
        template_id="adeu.workflow.pipeline_worker.v0",
        template_version="v0",
        schema_version="urm.workflow.v0",
        domain_pack_id="urm_domain_adeu",
        domain_pack_version="0.0.0",
    )
    first = urm_worker_run_endpoint(request)
    replay = urm_worker_run_endpoint(request)

    assert first.status == "ok"
    assert first.idempotent_replay is False
    assert replay.worker_id == first.worker_id
    assert replay.idempotent_replay is True
    _reset_manager_for_tests()


def test_urm_tool_call_list_templates_and_app_state(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex_exec(tmp_path=tmp_path)
    _configure_exec_fixture(monkeypatch=monkeypatch, tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    _reset_manager_for_tests()

    templates_response = urm_tool_call_endpoint(
        ToolCallRequest(
            provider="codex",
            role="copilot",
            tool_name="adeu.list_templates",
            arguments={},
        )
    )
    assert templates_response.warrant == "observed"
    templates = templates_response.result["templates"]
    assert templates
    assert templates[0]["template_id"] == "adeu.workflow.pipeline_worker.v0"

    state_response = urm_tool_call_endpoint(
        ToolCallRequest(
            provider="codex",
            role="copilot",
            tool_name="adeu.get_app_state",
            arguments={},
        )
    )
    assert state_response.warrant == "observed"
    assert "counts" in state_response.result
    assert "urm_evidence_record" in state_response.result["counts"]
    _reset_manager_for_tests()


def test_urm_tool_call_spawn_worker_and_read_evidence(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex_exec(tmp_path=tmp_path)
    _configure_exec_fixture(monkeypatch=monkeypatch, tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    _reset_manager_for_tests()

    spawn = urm_tool_call_endpoint(
        ToolCallRequest(
            provider="codex",
            role="copilot",
            tool_name="urm.spawn_worker",
            arguments={
                "client_request_id": "tool-spawn-1",
                "task_envelope": {
                    "role": "pipeline_worker",
                    "template_id": "adeu.workflow.pipeline_worker.v0",
                    "template_version": "v0",
                    "schema_version": "urm.workflow.v0",
                    "domain_pack_id": "urm_domain_adeu",
                    "domain_pack_version": "0.0.0",
                    "inputs": {"prompt": "tool spawn demo"},
                    "constraints": {},
                },
            },
        )
    )
    assert spawn.warrant == "checked"
    assert spawn.result["status"] == "ok"
    evidence_id = spawn.result["evidence_id"]

    evidence = urm_tool_call_endpoint(
        ToolCallRequest(
            provider="codex",
            role="copilot",
            tool_name="adeu.read_evidence",
            arguments={"evidence_id": evidence_id},
        )
    )
    assert evidence.warrant == "observed"
    assert evidence.result["evidence_id"] == evidence_id
    assert '"type":"result"' in (evidence.result["raw_jsonl"] or "")
    _reset_manager_for_tests()


def test_urm_tool_call_run_workflow(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex_exec(tmp_path=tmp_path)
    _configure_exec_fixture(monkeypatch=monkeypatch, tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    _reset_manager_for_tests()

    workflow = urm_tool_call_endpoint(
        ToolCallRequest(
            provider="codex",
            role="copilot",
            tool_name="adeu.run_workflow",
            arguments={
                "template_id": "adeu.workflow.pipeline_worker.v0",
                "inputs": {"prompt": "workflow prompt"},
                "client_request_id": "workflow-1",
            },
        )
    )
    assert workflow.warrant == "checked"
    assert workflow.result["status"] == "ok"
    assert workflow.result["template_id"] == "adeu.workflow.pipeline_worker.v0"
    _reset_manager_for_tests()


def test_urm_tool_call_denies_disallowed_role(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex_exec(tmp_path=tmp_path)
    _configure_exec_fixture(monkeypatch=monkeypatch, tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    _reset_manager_for_tests()

    with pytest.raises(HTTPException) as exc_info:
        urm_tool_call_endpoint(
            ToolCallRequest(
                provider="codex",
                role="pipeline_worker",
                tool_name="adeu.get_app_state",
                arguments={},
            )
        )
    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_POLICY_DENIED"
    _reset_manager_for_tests()


def test_urm_tool_call_spawn_worker_requires_task_envelope(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex_exec(tmp_path=tmp_path)
    _configure_exec_fixture(monkeypatch=monkeypatch, tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    _reset_manager_for_tests()

    with pytest.raises(HTTPException) as exc_info:
        urm_tool_call_endpoint(
            ToolCallRequest(
                provider="codex",
                role="copilot",
                tool_name="urm.spawn_worker",
                arguments={"client_request_id": "spawn-no-envelope"},
            )
        )
    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_POLICY_DENIED"
    _reset_manager_for_tests()
