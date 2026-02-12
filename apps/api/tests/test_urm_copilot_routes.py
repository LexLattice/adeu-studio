from __future__ import annotations

import shutil
import sqlite3
import time
from pathlib import Path

import pytest
from adeu_api.urm_routes import (
    _get_manager,
    _reset_manager_for_tests,
    urm_agent_cancel_endpoint,
    urm_agent_spawn_endpoint,
    urm_approval_issue_endpoint,
    urm_approval_revoke_endpoint,
    urm_copilot_events_endpoint,
    urm_copilot_mode_endpoint,
    urm_copilot_send_endpoint,
    urm_copilot_start_endpoint,
    urm_copilot_steer_endpoint,
    urm_copilot_stop_endpoint,
    urm_tool_call_endpoint,
)
from fastapi import HTTPException
from fastapi.responses import StreamingResponse
from urm_runtime.config import URMRuntimeConfig
from urm_runtime.models import (
    AgentCancelRequest,
    AgentSpawnRequest,
    ApprovalIssueRequest,
    ApprovalRevokeRequest,
    CopilotModeRequest,
    CopilotSessionSendRequest,
    CopilotSessionStartRequest,
    CopilotSteerRequest,
    CopilotStopRequest,
    ToolCallRequest,
)
from urm_runtime.storage import (
    get_worker_run,
    persist_copilot_session_start,
    persist_worker_run_start,
    transaction,
    update_copilot_session_status,
)


def _prepare_fake_codex(*, tmp_path: Path) -> Path:
    fixture = Path(__file__).resolve().parent / "fixtures" / "codex_app_server" / "fake_codex.py"
    target = tmp_path / "fake_codex.py"
    shutil.copy2(fixture, target)
    target.chmod(0o755)
    return target


def test_copilot_start_send_stop_and_sse_replay(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(
            provider="codex",
            client_request_id="start-1",
            profile_id="safe_mode",
        )
    )
    session_id = start.session_id
    assert start.status == "running"
    assert start.profile_id == "safe_mode"
    assert start.profile_version == "profile.v1"
    assert start.idempotent_replay is False

    send = urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-1",
            message={"jsonrpc": "2.0", "id": "req-1", "method": "ping"},
        )
    )
    assert send.status == "running"

    stop = urm_copilot_stop_endpoint(CopilotStopRequest(provider="codex", session_id=session_id))
    assert stop.status in {"stopped", "failed"}

    stream_response = urm_copilot_events_endpoint(
        session_id=session_id,
        after_seq=0,
        provider="codex",
        max_events=10,
    )
    assert isinstance(stream_response, StreamingResponse)

    manager = _get_manager()
    events, status = manager.iter_events(session_id=session_id, after_seq=0)
    assert status in {"stopped", "failed"}
    assert events
    assert any(event.event_kind == "PROFILE_SELECTED" for event in events)
    _reset_manager_for_tests()


def test_copilot_start_rejects_unknown_profile(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    with pytest.raises(HTTPException) as exc_info:
        urm_copilot_start_endpoint(
            CopilotSessionStartRequest(
                provider="codex",
                client_request_id="start-invalid-profile-1",
                profile_id="unknown_profile",
            )
        )
    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_POLICY_PROFILE_NOT_FOUND"
    _reset_manager_for_tests()


def test_copilot_user_message_bootstraps_protocol_and_emits_agent_delta(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-user-msg-1")
    )
    session_id = start.session_id
    assert start.status == "running"

    send = urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-user-msg-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-user-msg-1",
                "method": "copilot.user_message",
                "params": {"text": "hello world"},
            },
        )
    )
    assert send.status == "running"

    manager = _get_manager()
    events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    assert any(event.event_kind == "SESSION_READY" for event in events)

    db_path = tmp_path / "adeu.sqlite3"
    with sqlite3.connect(db_path) as con:
        row = con.execute(
            """
            SELECT raw_jsonl_path
            FROM urm_copilot_session
            WHERE copilot_session_id = ?
            """,
            (session_id,),
        ).fetchone()
    assert row is not None
    raw_path = tmp_path / row[0]
    deadline = time.monotonic() + 2.0
    text = ""
    while True:
        text = raw_path.read_text(encoding="utf-8", errors="replace")
        if "agent_message_delta" in text:
            break
        if time.monotonic() >= deadline:
            break
        time.sleep(0.05)

    assert '"method":"turn/start"' in text
    assert "agent_message_delta" in text
    _reset_manager_for_tests()


def test_copilot_steer_endpoint_is_idempotent_and_rate_limited(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-steer-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-steer-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-steer-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    steer = urm_copilot_steer_endpoint(
        CopilotSteerRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="steer-1",
            text="focus on tests first",
            steer_intent_class="reprioritize",
            target_turn_id="1",
        )
    )
    assert steer.target_turn_id == "1"
    assert steer.accepted_turn_id == "1"
    assert steer.idempotent_replay is False

    replay = urm_copilot_steer_endpoint(
        CopilotSteerRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="steer-1",
            text="focus on tests first",
            steer_intent_class="reprioritize",
            target_turn_id="1",
        )
    )
    assert replay.accepted_turn_id == steer.accepted_turn_id
    assert replay.idempotent_replay is True

    for idx in range(2, 7):
        if idx < 6:
            response = urm_copilot_steer_endpoint(
                CopilotSteerRequest(
                    provider="codex",
                    session_id=session_id,
                    client_request_id=f"steer-{idx}",
                    text=f"steer-{idx}",
                    target_turn_id="1",
                )
            )
            assert response.accepted_turn_id == "1"
            continue
        with pytest.raises(HTTPException) as exc_info:
            urm_copilot_steer_endpoint(
                CopilotSteerRequest(
                    provider="codex",
                    session_id=session_id,
                    client_request_id=f"steer-{idx}",
                    text=f"steer-{idx}",
                    target_turn_id="1",
                )
            )
        assert exc_info.value.status_code == 400
        assert exc_info.value.detail["code"] == "URM_STEER_DENIED"
    _reset_manager_for_tests()


def test_agent_spawn_and_cancel_terminal_idempotent(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-child-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-child-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-child-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    spawn = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-1",
            prompt="summarize this module",
            target_turn_id="turn-bootstrap-1",
            use_last_turn=False,
            profile_id="experimental",
        )
    )
    assert spawn.parent_session_id == session_id
    assert spawn.status in {"completed", "failed"}
    assert spawn.child_id
    assert spawn.parent_stream_id == f"copilot:{session_id}"
    assert spawn.child_stream_id.startswith("child:")
    assert spawn.profile_id == "experimental"
    assert spawn.profile_version == "profile.v1"
    spawn_replay = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-1",
            prompt="summarize this module",
            target_turn_id="turn-bootstrap-1",
            use_last_turn=False,
            profile_id="experimental",
        )
    )
    assert spawn_replay.child_id == spawn.child_id
    assert spawn_replay.idempotent_replay is True

    cancel = urm_agent_cancel_endpoint(
        spawn.child_id,
        AgentCancelRequest(
            provider="codex",
            client_request_id="cancel-child-1",
        ),
    )
    assert cancel.child_id == spawn.child_id
    assert cancel.status in {"completed", "failed", "cancelled"}
    assert cancel.idempotent_replay is True
    assert cancel.error is not None
    assert cancel.error["code"] == "URM_CHILD_CANCEL_ALREADY_TERMINAL"

    cancel_replay = urm_agent_cancel_endpoint(
        spawn.child_id,
        AgentCancelRequest(
            provider="codex",
            client_request_id="cancel-child-1",
        ),
    )
    assert cancel_replay.child_id == spawn.child_id
    assert cancel_replay.idempotent_replay is True
    manager = _get_manager()
    events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    assert any(
        event.event_kind == "PROFILE_SELECTED"
        and event.payload.get("scope") == "run"
        and event.payload.get("profile_id") == "experimental"
        for event in events
    )
    with pytest.raises(HTTPException) as bad_profile_exc:
        urm_agent_spawn_endpoint(
            AgentSpawnRequest(
                provider="codex",
                session_id=session_id,
                client_request_id="spawn-child-2-bad-profile",
                prompt="summarize this module",
                target_turn_id="turn-bootstrap-1",
                use_last_turn=False,
                profile_id="unknown_profile",
            )
    )
    assert bad_profile_exc.value.status_code == 400
    assert bad_profile_exc.value.detail["code"] == "URM_POLICY_PROFILE_NOT_FOUND"
    events_after_denial, _ = manager.iter_events(session_id=session_id, after_seq=0)
    assert any(
        event.event_kind == "PROFILE_DENIED"
        and event.payload.get("profile_id") == "unknown_profile"
        for event in events_after_denial
    )
    _reset_manager_for_tests()


def test_agent_spawn_queue_mode_v2_enforces_fifo_and_queue_limit(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "0.6")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-child-v2-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-child-v2-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-child-v2-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    spawn1 = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-1",
            prompt="first child",
            target_turn_id="turn-bootstrap-1",
        )
    )
    spawn2 = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-2",
            prompt="second child",
            target_turn_id="turn-bootstrap-1",
        )
    )
    assert spawn1.status == "running"
    assert spawn2.status in {"queued", "running"}
    with pytest.raises(HTTPException) as exc_info:
        urm_agent_spawn_endpoint(
            AgentSpawnRequest(
                provider="codex",
                session_id=session_id,
                client_request_id="spawn-child-v2-3",
                prompt="third child",
                target_turn_id="turn-bootstrap-1",
            )
        )
    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_CHILD_QUEUE_LIMIT_EXCEEDED"

    manager = _get_manager()
    deadline = time.monotonic() + 5.0
    while time.monotonic() < deadline:
        child1 = manager._child_runs.get(spawn1.child_id)  # type: ignore[attr-defined]
        child2 = manager._child_runs.get(spawn2.child_id)  # type: ignore[attr-defined]
        if child1 is not None and child2 is not None and child1.status in {
            "completed",
            "failed",
            "cancelled",
        } and child2.status in {"completed", "failed", "cancelled"}:
            break
        time.sleep(0.05)
    child1 = manager._child_runs.get(spawn1.child_id)  # type: ignore[attr-defined]
    child2 = manager._child_runs.get(spawn2.child_id)  # type: ignore[attr-defined]
    assert child1 is not None and child2 is not None
    assert child1.queue_seq == 1
    assert child2.queue_seq == 2

    child2_events_path = (
        tmp_path / "evidence" / "codex" / "agent" / spawn2.child_id / "urm_events.ndjson"
    )
    child2_payload = child2_events_path.read_text(encoding="utf-8", errors="replace")
    assert '"status":"queued"' in child2_payload
    assert '"status":"running"' in child2_payload
    _reset_manager_for_tests()


def test_manager_marks_stale_running_child_runs_on_startup(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    config = URMRuntimeConfig.from_env()
    child_id = "stale-child-run-1"
    parent_session_id = "stale-parent-1"
    raw_rel_path = f"evidence/codex/agent/{child_id}/codex_raw.ndjson"
    events_rel_path = f"evidence/codex/agent/{child_id}/urm_events.ndjson"
    raw_path = config.var_root / raw_rel_path
    events_path = config.var_root / events_rel_path
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    events_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text("", encoding="utf-8")
    events_path.write_text("", encoding="utf-8")

    with transaction(db_path=config.db_path) as con:
        persist_worker_run_start(
            con=con,
            worker_id=child_id,
            role="copilot_child",
            provider="codex",
            template_id="urm.agent.spawn",
            template_version="v2",
            schema_version="urm.child-run.v1",
            domain_pack_id="urm_domain_adeu",
            domain_pack_version="v0",
            raw_jsonl_path=raw_rel_path,
            status="running",
            result_json={
                "parent_session_id": parent_session_id,
                "parent_stream_id": f"copilot:{parent_session_id}",
                "child_stream_id": f"child:{child_id}",
                "parent_turn_id": "turn-stale-1",
                "profile_id": "default",
                "profile_version": "profile.v1",
                "budget_snapshot": {
                    "budget_version": "budget.v1",
                    "max_solver_calls": 10,
                    "max_token_budget": 20_000,
                    "max_duration_secs": 300,
                },
                "inherited_policy_hash": "policy-hash-stale-1",
                "capabilities_allowed": ["urm.agent.spawn"],
                "queue_seq": 1,
                "raw_jsonl_path": raw_rel_path,
                "urm_events_path": events_rel_path,
            },
        )

    _get_manager()

    with transaction(db_path=config.db_path) as con:
        row = get_worker_run(con=con, worker_id=child_id)
    assert row is not None
    assert row.status == "failed"
    assert row.error_code == "URM_CHILD_TERMINATED_ON_RESTART"

    child_events_payload = events_path.read_text(encoding="utf-8", errors="replace")
    assert "WORKER_FAIL" in child_events_payload
    assert "URM_CHILD_TERMINATED_ON_RESTART" in child_events_payload

    audit_path = config.evidence_root / "audit" / parent_session_id / "urm_events.ndjson"
    assert audit_path.is_file()
    audit_payload = audit_path.read_text(encoding="utf-8", errors="replace")
    assert "WORKER_FAIL" in audit_payload
    assert "URM_CHILD_TERMINATED_ON_RESTART" in audit_payload
    _reset_manager_for_tests()


def test_copilot_start_idempotency_conflict_and_replay(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    first = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-idem")
    )
    replay = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-idem")
    )
    assert replay.session_id == first.session_id
    assert replay.idempotent_replay is True

    with pytest.raises(HTTPException) as exc_info:
        urm_copilot_start_endpoint(
            CopilotSessionStartRequest(
                provider="codex",
                client_request_id="start-idem",
                cwd="/tmp",
            )
        )
    detail = exc_info.value.detail
    assert exc_info.value.status_code == 409
    assert detail["code"] == "URM_IDEMPOTENCY_KEY_CONFLICT"
    _reset_manager_for_tests()


def test_copilot_start_worker_only_mode_when_app_server_unavailable(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("FAKE_APP_SERVER_DISABLE_READY", "1")
    _reset_manager_for_tests()

    with pytest.raises(HTTPException) as exc_info:
        urm_copilot_start_endpoint(
            CopilotSessionStartRequest(provider="codex", client_request_id="start-disabled")
        )
    detail = exc_info.value.detail
    assert exc_info.value.status_code == 400
    assert detail["code"] == "URM_CODEX_APP_SERVER_UNAVAILABLE"
    _reset_manager_for_tests()


def test_copilot_start_accepts_silent_app_server(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("FAKE_APP_SERVER_SILENT_READY", "1")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-silent-ready")
    )
    assert start.status == "running"
    assert start.app_server_unavailable is False
    _reset_manager_for_tests()


def test_copilot_mode_enable_requires_approval_and_consumes_single_use(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="mode-start-1")
    )
    session_id = start.session_id

    with pytest.raises(HTTPException) as exc_info:
        urm_copilot_mode_endpoint(
            CopilotModeRequest(
                provider="codex",
                session_id=session_id,
                writes_allowed=True,
            )
        )
    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_APPROVAL_REQUIRED"

    issued = urm_approval_issue_endpoint(
        ApprovalIssueRequest(
            provider="codex",
            session_id=session_id,
            action_kind="urm.set_mode.enable_writes",
            action_payload={"writes_allowed": True},
        )
    )
    enabled = urm_copilot_mode_endpoint(
        CopilotModeRequest(
            provider="codex",
            session_id=session_id,
            writes_allowed=True,
            approval_id=issued.approval_id,
        )
    )
    assert enabled.status == "running"

    with pytest.raises(HTTPException) as reuse_exc:
        urm_copilot_mode_endpoint(
            CopilotModeRequest(
                provider="codex",
                session_id=session_id,
                writes_allowed=True,
                approval_id=issued.approval_id,
            )
        )
    assert reuse_exc.value.status_code == 400
    assert reuse_exc.value.detail["code"] == "URM_APPROVAL_INVALID"

    disabled = urm_copilot_mode_endpoint(
        CopilotModeRequest(
            provider="codex",
            session_id=session_id,
            writes_allowed=False,
        )
    )
    assert disabled.status == "running"
    _reset_manager_for_tests()


def test_approval_revoke_is_idempotent(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="revoke-start-1")
    )
    issued = urm_approval_issue_endpoint(
        ApprovalIssueRequest(
            provider="codex",
            session_id=start.session_id,
            action_kind="urm.set_mode.enable_writes",
            action_payload={"writes_allowed": True},
        )
    )

    first = urm_approval_revoke_endpoint(
        ApprovalRevokeRequest(provider="codex", approval_id=issued.approval_id)
    )
    second = urm_approval_revoke_endpoint(
        ApprovalRevokeRequest(provider="codex", approval_id=issued.approval_id)
    )

    assert first.revoked is True
    assert first.idempotent_replay is False
    assert second.revoked is True
    assert second.idempotent_replay is True
    _reset_manager_for_tests()


def test_manager_marks_stale_running_sessions_on_startup(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    config = URMRuntimeConfig.from_env()
    with transaction(db_path=config.db_path) as con:
        persist_copilot_session_start(
            con=con,
            copilot_session_id="stale-session-1",
            role="copilot",
            status="running",
            codex_version="codex-fake",
            capability_probe_id=None,
            pid=1234,
            bin_path=str(codex_bin),
            raw_jsonl_path="evidence/codex/copilot/stale-session-1.jsonl",
            profile_id="default",
            profile_version="profile.v1",
            profile_policy_hash=None,
        )
        update_copilot_session_status(
            con=con,
            copilot_session_id="stale-session-1",
            status="running",
        )

    _get_manager()

    with sqlite3.connect(db_path) as con:
        row = con.execute(
            """
            SELECT status, error_code
            FROM urm_copilot_session
            WHERE copilot_session_id = ?
            """,
            ("stale-session-1",),
        ).fetchone()
    assert row is not None
    assert row[0] == "stopped"
    assert row[1] == "URM_CODEX_SESSION_TERMINATED"
    _reset_manager_for_tests()


def test_tool_call_emits_policy_eval_events_on_allow(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class _FakeManager:
        def __init__(self) -> None:
            self.events: list[tuple[str, dict[str, object]]] = []

        def record_policy_eval_event(
            self,
            *,
            session_id: str | None,
            event_kind: str,
            detail: dict[str, object],
        ) -> None:
            self.events.append((event_kind, detail))

    class _FakeRegistry:
        def call_tool(
            self,
            *,
            tool_name: str,
            arguments: dict[str, object],
        ) -> tuple[dict[str, object], str]:
            assert tool_name == "adeu.get_app_state"
            assert arguments == {}
            return ({"ok": True}, "observed")

    fake_manager = _FakeManager()
    monkeypatch.setattr("adeu_api.urm_routes._get_manager", lambda: fake_manager)
    monkeypatch.setattr("adeu_api.urm_routes._get_domain_registry", lambda: _FakeRegistry())
    monkeypatch.setattr(
        "adeu_api.urm_routes._load_session_access_state",
        lambda _sid: (False, False),
    )

    response = urm_tool_call_endpoint(
        ToolCallRequest(
            provider="codex",
            role="copilot",
            session_id="session-1",
            tool_name="adeu.get_app_state",
            arguments={},
        )
    )
    assert response.tool_name == "adeu.get_app_state"
    assert response.result == {"ok": True}
    assert response.policy_trace is not None
    assert any(
        ref.get("kind") == "proof" for ref in response.policy_trace.get("evidence_refs", [])
    )
    assert [event for event, _detail in fake_manager.events] == [
        "POLICY_EVAL_START",
        "POLICY_EVAL_PASS",
    ]


def test_tool_call_emits_policy_denied_event_on_instruction_deny(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    class _FakeManager:
        def __init__(self) -> None:
            self.events: list[tuple[str, dict[str, object]]] = []

        def record_policy_eval_event(
            self,
            *,
            session_id: str | None,
            event_kind: str,
            detail: dict[str, object],
        ) -> None:
            self.events.append((event_kind, detail))

    class _FakeRegistry:
        def call_tool(
            self,
            *,
            tool_name: str,
            arguments: dict[str, object],
        ) -> tuple[dict[str, object], str]:
            return ({}, "observed")

    deny_policy_path = tmp_path / "deny.instructions.json"
    deny_policy_path.write_text(
        """
{
  "schema":"odeu.instructions.v1",
  "rules":[
    {
      "rule_id":"deny_copilot",
      "rule_version":1,
      "priority":1,
      "kind":"deny",
      "when":{"atom":"role_is","args":["copilot"]},
      "then":{"effect":"deny_action","params":{}},
      "message":"deny copilot in route test",
      "code":"DENY_COPILOT_ROUTE_TEST"
    }
  ]
}
""".strip(),
        encoding="utf-8",
    )
    fake_manager = _FakeManager()
    monkeypatch.setenv("URM_INSTRUCTION_POLICY_PATH", str(deny_policy_path))
    monkeypatch.setattr("adeu_api.urm_routes._get_manager", lambda: fake_manager)
    monkeypatch.setattr("adeu_api.urm_routes._get_domain_registry", lambda: _FakeRegistry())
    monkeypatch.setattr(
        "adeu_api.urm_routes._load_session_access_state",
        lambda _sid: (False, False),
    )

    with pytest.raises(HTTPException) as exc_info:
        urm_tool_call_endpoint(
            ToolCallRequest(
                provider="codex",
                role="copilot",
                session_id="session-1",
                tool_name="adeu.get_app_state",
                arguments={},
            )
        )
    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "DENY_COPILOT_ROUTE_TEST"
    assert any(
        ref.get("kind") == "proof"
        for ref in exc_info.value.detail.get("context", {}).get("evidence_refs", [])
    )
    assert [event for event, _detail in fake_manager.events] == [
        "POLICY_EVAL_START",
        "POLICY_DENIED",
    ]
