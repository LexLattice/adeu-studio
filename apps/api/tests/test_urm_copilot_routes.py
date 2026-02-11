from __future__ import annotations

import shutil
import sqlite3
import time
from pathlib import Path

import pytest
from adeu_api.urm_routes import (
    _get_manager,
    _reset_manager_for_tests,
    urm_approval_issue_endpoint,
    urm_approval_revoke_endpoint,
    urm_copilot_events_endpoint,
    urm_copilot_mode_endpoint,
    urm_copilot_send_endpoint,
    urm_copilot_start_endpoint,
    urm_copilot_stop_endpoint,
)
from fastapi import HTTPException
from fastapi.responses import StreamingResponse
from urm_runtime.config import URMRuntimeConfig
from urm_runtime.models import (
    ApprovalIssueRequest,
    ApprovalRevokeRequest,
    CopilotModeRequest,
    CopilotSessionSendRequest,
    CopilotSessionStartRequest,
    CopilotStopRequest,
)
from urm_runtime.storage import (
    persist_copilot_session_start,
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
        CopilotSessionStartRequest(provider="codex", client_request_id="start-1")
    )
    session_id = start.session_id
    assert start.status == "running"
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
