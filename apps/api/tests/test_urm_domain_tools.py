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


def test_urm_tool_call_paper_domain_closed_world_flow(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex_exec(tmp_path=tmp_path)
    _configure_exec_fixture(monkeypatch=monkeypatch, tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    _reset_manager_for_tests()

    source_text = (
        "We introduce an evidence-first orchestration runtime for local assistants. "
        "The runtime captures replayable event streams and deterministic policy traces.\n\n"
        "The second paragraph is intentionally ignored for candidate extraction."
    )

    ingest = urm_tool_call_endpoint(
        ToolCallRequest(
            provider="codex",
            role="copilot",
            tool_name="paper.ingest_text",
            arguments={"title": "Paper A", "source_text": source_text},
        )
    )
    assert ingest.warrant == "observed"
    assert ingest.result["title"] == "Paper A"

    extract = urm_tool_call_endpoint(
        ToolCallRequest(
            provider="codex",
            role="copilot",
            tool_name="paper.extract_abstract_candidate",
            arguments={"source_text": source_text},
        )
    )
    assert extract.warrant == "derived"
    candidate = extract.result["abstract_text"]
    assert "second paragraph" not in candidate.lower()
    assert extract.result["word_count"] > 0
    assert extract.result["candidate_date_like"] is False

    check = urm_tool_call_endpoint(
        ToolCallRequest(
            provider="codex",
            role="copilot",
            tool_name="paper.check_constraints",
            arguments={"abstract_text": candidate, "min_words": 5, "max_words": 80},
        )
    )
    assert check.warrant == "checked"
    assert check.result["passes"] is True

    emit = urm_tool_call_endpoint(
        ToolCallRequest(
            provider="codex",
            role="copilot",
            tool_name="paper.emit_artifact",
            arguments={
                "title": "Paper A",
                "abstract_text": candidate,
                "checks": check.result["checks"],
            },
        )
    )
    assert emit.warrant == "checked"
    assert emit.result["status"] == "ok"
    assert emit.result["artifact"]["domain"] == "paper.abstract"
    _reset_manager_for_tests()


def test_urm_tool_call_paper_extract_prefers_abstract_section_over_date_header(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex_exec(tmp_path=tmp_path)
    _configure_exec_fixture(monkeypatch=monkeypatch, tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    _reset_manager_for_tests()

    source_text = (
        "2026-02-12\n\n"
        "Intelligent AI Delegation\n\n"
        "Abstract\n"
        "AI agents are able to tackle increasingly complex tasks. "
        "To achieve more ambitious goals, delegation should adapt to uncertainty and failure.\n\n"
        "Keywords: delegation, agents\n\n"
        "1 Introduction\n"
        "The introduction should not be selected as abstract."
    )
    extract = urm_tool_call_endpoint(
        ToolCallRequest(
            provider="codex",
            role="copilot",
            tool_name="paper.extract_abstract_candidate",
            arguments={"source_text": source_text},
        )
    )

    assert extract.warrant == "derived"
    assert extract.result["extract_strategy"] == "abstract_section_marker"
    assert extract.result["abstract_text"].startswith("AI agents are able to tackle")
    assert "2026-02-12" not in extract.result["abstract_text"]
    assert "keywords" not in extract.result["abstract_text"].lower()
    assert extract.result["sentence_count"] >= 2
    assert extract.result["candidate_date_like"] is False
    _reset_manager_for_tests()


def test_urm_tool_call_digest_domain_closed_world_flow(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex_exec(tmp_path=tmp_path)
    _configure_exec_fixture(monkeypatch=monkeypatch, tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    _reset_manager_for_tests()

    source_text = (
        "ODEU uses evidence-first runtime controls for safe orchestration. "
        "Deterministic events improve replayability and incident analysis. "
        "This final sentence should be excluded when max_sentences is two."
    )

    ingest = urm_tool_call_endpoint(
        ToolCallRequest(
            provider="codex",
            role="copilot",
            tool_name="digest.ingest_text",
            arguments={"title": "Digest A", "source_text": source_text},
        )
    )
    assert ingest.warrant == "observed"
    assert ingest.result["title"] == "Digest A"
    assert ingest.result["word_count"] > 0
    assert isinstance(ingest.result["input_hash"], str)

    extract = urm_tool_call_endpoint(
        ToolCallRequest(
            provider="codex",
            role="copilot",
            tool_name="digest.extract_digest_candidate",
            arguments={
                "source_text": source_text,
                "max_sentences": 2,
                "max_words": 30,
            },
        )
    )
    assert extract.warrant == "derived"
    digest_text = extract.result["digest_text"]
    assert "excluded" not in digest_text.lower()
    assert extract.result["sentence_count"] <= 2
    assert extract.result["word_count"] <= 30

    check = urm_tool_call_endpoint(
        ToolCallRequest(
            provider="codex",
            role="copilot",
            tool_name="digest.check_constraints",
            arguments={
                "digest_text": digest_text,
                "min_words": 5,
                "max_words": 60,
                "max_sentences": 3,
            },
        )
    )
    assert check.warrant == "checked"
    assert check.result["passes"] is True

    emit = urm_tool_call_endpoint(
        ToolCallRequest(
            provider="codex",
            role="copilot",
            tool_name="digest.emit_artifact",
            arguments={
                "title": "Digest A",
                "input_hash": ingest.result["input_hash"],
                "digest_text": digest_text,
                "policy_hash": "policy:test.v1",
                "checks": check.result["checks"],
                "evidence_refs": [
                    {"kind": "event", "ref": "event:stream#2"},
                    {"kind": "artifact", "ref": "artifact:abc"},
                ],
            },
        )
    )
    assert emit.warrant == "checked"
    assert emit.result["status"] == "ok"
    artifact = emit.result["artifact"]
    assert artifact["domain"] == "doc.digest"
    assert artifact["schema_version"] == "digest.artifact.v1"
    assert artifact["domain_pack_id"] == "urm_domain_digest"
    assert artifact["domain_pack_version"] == "0.0.0"
    assert artifact["input_hash"] == ingest.result["input_hash"]
    assert artifact["policy_hash"] == "policy:test.v1"
    assert artifact["evidence_refs"] == [
        {"kind": "artifact", "ref": "artifact:abc", "note": None},
        {"kind": "event", "ref": "event:stream#2", "note": None},
    ]
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


def test_digest_sentence_split_handles_whitespace_only() -> None:
    from urm_domain_digest.adapters import _split_sentences

    assert _split_sentences("   ") == []


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
