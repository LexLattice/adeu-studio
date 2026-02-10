from __future__ import annotations

import shutil
from pathlib import Path

import pytest
from adeu_api.urm_routes import (
    _get_manager,
    _reset_manager_for_tests,
    urm_copilot_events_endpoint,
    urm_copilot_send_endpoint,
    urm_copilot_start_endpoint,
    urm_copilot_stop_endpoint,
)
from fastapi import HTTPException
from fastapi.responses import StreamingResponse
from urm_runtime.models import (
    CopilotSessionSendRequest,
    CopilotSessionStartRequest,
    CopilotStopRequest,
)


def _prepare_fake_codex(*, tmp_path: Path) -> Path:
    fixture = (
        Path(__file__).resolve().parent / "fixtures" / "codex_app_server" / "fake_codex.py"
    )
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

    stop = urm_copilot_stop_endpoint(
        CopilotStopRequest(provider="codex", session_id=session_id)
    )
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
