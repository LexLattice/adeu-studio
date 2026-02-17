from __future__ import annotations

import json
import shutil
import sqlite3
import time
from collections.abc import Callable
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest
from adeu_api.urm_routes import (
    _get_manager,
    _reset_manager_for_tests,
    urm_agent_cancel_endpoint,
    urm_agent_spawn_endpoint,
    urm_approval_issue_endpoint,
    urm_approval_revoke_endpoint,
    urm_connector_snapshot_create_endpoint,
    urm_connector_snapshot_get_endpoint,
    urm_copilot_events_endpoint,
    urm_copilot_mode_endpoint,
    urm_copilot_send_endpoint,
    urm_copilot_start_endpoint,
    urm_copilot_steer_endpoint,
    urm_copilot_stop_endpoint,
    urm_policy_active_endpoint,
    urm_policy_profile_current_endpoint,
    urm_policy_profile_list_endpoint,
    urm_policy_profile_select_endpoint,
    urm_policy_rollback_endpoint,
    urm_policy_rollout_endpoint,
    urm_tool_call_endpoint,
)
from fastapi import HTTPException
from fastapi.responses import StreamingResponse
from jsonschema import Draft202012Validator
from urm_runtime.config import URMRuntimeConfig
from urm_runtime.errors import URMError
from urm_runtime.instruction_policy import (
    compute_policy_hash,
    load_instruction_policy,
    policy_semantic_form,
)
from urm_runtime.models import (
    AgentCancelRequest,
    AgentSpawnRequest,
    ApprovalIssueRequest,
    ApprovalRevokeRequest,
    ConnectorSnapshotCreateRequest,
    CopilotModeRequest,
    CopilotSessionSendRequest,
    CopilotSessionStartRequest,
    CopilotSteerRequest,
    CopilotStopRequest,
    PolicyProfileSelectRequest,
    PolicyRollbackRequest,
    PolicyRolloutRequest,
    ToolCallRequest,
)
from urm_runtime.policy_governance import materialize_policy
from urm_runtime.storage import (
    get_dispatch_token_for_child,
    get_parent_budget_total,
    get_worker_run,
    lease_dispatch_token,
    persist_copilot_session_start,
    persist_worker_run_start,
    set_dispatch_token_phase,
    transaction,
    update_copilot_session_status,
    upsert_dispatch_token_queued,
)


def _prepare_fake_codex(*, tmp_path: Path) -> Path:
    fixture = Path(__file__).resolve().parent / "fixtures" / "codex_app_server" / "fake_codex.py"
    target = tmp_path / "fake_codex.py"
    shutil.copy2(fixture, target)
    target.chmod(0o755)
    return target


def _write_profile_registry(
    *,
    path: Path,
    default_policy_hash: str,
    allowed_policy_hashes: list[str],
) -> None:
    payload = {
        "schema": "policy.profiles.v1",
        "profiles": [
            {
                "profile_id": "default",
                "profile_version": "profile.v1",
                "default_policy_hash": default_policy_hash,
                "allowed_policy_hashes": sorted(allowed_policy_hashes),
                "policy_ref": "policy/odeu.instructions.v1.json",
            }
        ],
    }
    path.write_text(json.dumps(payload, sort_keys=True, indent=2), encoding="utf-8")


def _materialize_policy_file(
    *,
    config: URMRuntimeConfig,
    policy_path: Path,
    materialized_at: str,
) -> str:
    policy = load_instruction_policy(policy_path=policy_path, strict=True)
    policy_hash = compute_policy_hash(policy)
    materialize_policy(
        config=config,
        policy_hash=policy_hash,
        schema_id=policy.schema_id,
        policy_schema_version="odeu.instructions.schema.v1",
        policy_ir_version="odeu.instructions.v1",
        semantic_policy_json=policy_semantic_form(policy),
        source_policy_ref=str(policy_path),
        materialized_at=materialized_at,
    )
    return policy_hash


def _wait_for(
    predicate: Callable[[], bool],
    *,
    timeout_secs: float,
    interval_secs: float = 0.02,
) -> bool:
    deadline = time.monotonic() + timeout_secs
    while time.monotonic() < deadline:
        if predicate():
            return True
        time.sleep(interval_secs)
    return bool(predicate())


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("repository root not found")


def _budget_snapshot_v1(
    *,
    max_solver_calls: int,
    max_duration_secs: int,
    max_token_budget: int,
    remaining_parent_duration_secs: int,
    accounting_model: str = "running_total_v1",
    token_usage_unobserved: bool = True,
) -> dict[str, object]:
    return {
        "budget_version": "budget.v1",
        "accounting_model": accounting_model,
        "max_solver_calls": max_solver_calls,
        "max_duration_secs": max_duration_secs,
        "max_token_budget": max_token_budget,
        "remaining_parent_duration_secs": remaining_parent_duration_secs,
        "token_usage_unobserved": token_usage_unobserved,
    }


def test_materialize_policy_rejects_conflicting_payload_for_existing_hash(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    config = URMRuntimeConfig.from_env()
    base_policy_path = Path(__file__).resolve().parents[3] / "policy" / "odeu.instructions.v1.json"

    policy = load_instruction_policy(policy_path=base_policy_path, strict=True)
    policy_hash = compute_policy_hash(policy)
    semantic = policy_semantic_form(policy)
    materialize_policy(
        config=config,
        policy_hash=policy_hash,
        schema_id=policy.schema_id,
        policy_schema_version="odeu.instructions.schema.v1",
        policy_ir_version="odeu.instructions.v1",
        semantic_policy_json=semantic,
        source_policy_ref=str(base_policy_path),
        materialized_at="2026-02-13T10:00:00Z",
    )

    conflicting_semantic = dict(semantic)
    conflicting_semantic["rules"] = []
    with pytest.raises(URMError) as exc_info:
        materialize_policy(
            config=config,
            policy_hash=policy_hash,
            schema_id=policy.schema_id,
            policy_schema_version="odeu.instructions.schema.v1",
            policy_ir_version="odeu.instructions.v1",
            semantic_policy_json=conflicting_semantic,
            source_policy_ref=str(tmp_path / "conflicting.policy.json"),
            materialized_at="2026-02-13T10:01:00Z",
        )

    assert exc_info.value.status_code == 409
    assert exc_info.value.detail.code == "URM_POLICY_DENIED"


def test_runtime_config_defaults_child_queue_mode_v2(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.delenv("URM_CHILD_QUEUE_MODE", raising=False)
    config = URMRuntimeConfig.from_env()
    assert config.child_queue_mode == "v2"


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


def test_policy_profile_list_current_select_surfaces(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-profile-surface-1")
    )
    session_id = start.session_id
    assert start.profile_id == "default"

    listing = urm_policy_profile_list_endpoint(provider="codex")
    listed_profile_ids = [profile.profile_id for profile in listing.profiles]
    assert listed_profile_ids == sorted(listed_profile_ids)
    assert listed_profile_ids == ["default", "experimental", "safe_mode"]

    current = urm_policy_profile_current_endpoint(session_id=session_id, provider="codex")
    assert current.profile_id == "default"
    assert current.profile_version == "profile.v1"
    assert len(current.policy_hash) == 64

    selected = urm_policy_profile_select_endpoint(
        PolicyProfileSelectRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="profile-select-1",
            profile_id="safe_mode",
        )
    )
    assert selected.idempotent_replay is False
    assert selected.profile_id == "safe_mode"
    assert selected.profile_version == "profile.v1"
    assert len(selected.policy_hash) == 64

    selected_replay = urm_policy_profile_select_endpoint(
        PolicyProfileSelectRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="profile-select-1",
            profile_id="safe_mode",
        )
    )
    assert selected_replay.profile_id == "safe_mode"
    assert selected_replay.idempotent_replay is True

    current_after = urm_policy_profile_current_endpoint(session_id=session_id, provider="codex")
    assert current_after.profile_id == "safe_mode"

    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-profile-surface-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-profile-surface-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )
    spawned = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-profile-surface-1",
            prompt="profile check",
            target_turn_id="turn-profile-surface-1",
            use_last_turn=False,
        )
    )
    assert spawned.profile_id == "safe_mode"

    manager = _get_manager()
    events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    assert any(
        event.event_kind == "PROFILE_SELECTED"
        and event.payload.get("scope") == "session"
        and event.payload.get("profile_id") == "safe_mode"
        for event in events
    )
    _reset_manager_for_tests()


def test_policy_profile_select_rejects_unknown_profile_and_emits_denial(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-profile-denied-1")
    )
    session_id = start.session_id

    with pytest.raises(HTTPException) as exc_info:
        urm_policy_profile_select_endpoint(
            PolicyProfileSelectRequest(
                provider="codex",
                session_id=session_id,
                client_request_id="profile-select-denied-1",
                profile_id="unknown_profile",
            )
        )
    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_POLICY_PROFILE_NOT_FOUND"

    manager = _get_manager()
    events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    assert any(
        event.event_kind == "PROFILE_DENIED"
        and event.payload.get("scope") == "session"
        and event.payload.get("profile_id") == "unknown_profile"
        for event in events
    )
    _reset_manager_for_tests()


def test_policy_rollout_rollback_active_and_session_snapshot_behavior(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)

    base_policy_path = Path(__file__).resolve().parents[3] / "policy" / "odeu.instructions.v1.json"
    alt_policy_path = tmp_path / "odeu.instructions.alt.v1.json"
    disallowed_policy_path = tmp_path / "odeu.instructions.disallowed.v1.json"
    base_payload = json.loads(base_policy_path.read_text(encoding="utf-8"))
    assert isinstance(base_payload, dict)
    rules = base_payload.get("rules")
    assert isinstance(rules, list) and rules
    first_rule = rules[0]
    assert isinstance(first_rule, dict)
    first_rule["code"] = "ALLOW_HARD_GATED_ACTION_ALT"
    alt_policy_path.write_text(json.dumps(base_payload, sort_keys=True), encoding="utf-8")
    first_rule["code"] = "ALLOW_HARD_GATED_ACTION_DISALLOWED"
    disallowed_policy_path.write_text(json.dumps(base_payload, sort_keys=True), encoding="utf-8")

    config = URMRuntimeConfig.from_env()
    default_hash = _materialize_policy_file(
        config=config,
        policy_path=base_policy_path,
        materialized_at="2026-02-13T10:00:00Z",
    )
    alt_hash = _materialize_policy_file(
        config=config,
        policy_path=alt_policy_path,
        materialized_at="2026-02-13T10:05:00Z",
    )
    disallowed_hash = _materialize_policy_file(
        config=config,
        policy_path=disallowed_policy_path,
        materialized_at="2026-02-13T10:06:00Z",
    )

    registry_path = tmp_path / "profiles.v1.json"
    _write_profile_registry(
        path=registry_path,
        default_policy_hash=default_hash,
        allowed_policy_hashes=[default_hash, alt_hash],
    )
    monkeypatch.setenv("URM_POLICY_PROFILES_PATH", str(registry_path))
    _reset_manager_for_tests()

    active_before = urm_policy_active_endpoint(profile_id="default", provider="codex")
    assert active_before.policy_hash == default_hash
    assert active_before.source == "profile_default"

    with pytest.raises(HTTPException) as disallowed_exc:
        urm_policy_rollout_endpoint(
            PolicyRolloutRequest(
                provider="codex",
                client_request_id="rollout-disallowed-1",
                profile_id="default",
                target_policy_hash=disallowed_hash,
                activation_ts="2026-02-13T10:09:00Z",
            )
        )
    assert disallowed_exc.value.status_code == 400
    assert disallowed_exc.value.detail["code"] == "URM_POLICY_ROLLOUT_HASH_NOT_ALLOWED"

    first_rollout = urm_policy_rollout_endpoint(
        PolicyRolloutRequest(
            provider="codex",
            client_request_id="rollout-seed-default-1",
            profile_id="default",
            target_policy_hash=default_hash,
            activation_ts="2026-02-13T10:10:00Z",
        )
    )
    assert first_rollout.idempotent_replay is False
    assert first_rollout.target_policy_hash == default_hash

    first_rollout_replay = urm_policy_rollout_endpoint(
        PolicyRolloutRequest(
            provider="codex",
            client_request_id="rollout-seed-default-1",
            profile_id="default",
            target_policy_hash=default_hash,
            activation_ts="2026-02-13T10:11:00Z",
        )
    )
    assert first_rollout_replay.idempotent_replay is True
    assert first_rollout_replay.activation_seq == first_rollout.activation_seq
    assert first_rollout_replay.activation_ts == first_rollout.activation_ts

    rollout_alt = urm_policy_rollout_endpoint(
        PolicyRolloutRequest(
            provider="codex",
            client_request_id="rollout-alt-1",
            profile_id="default",
            target_policy_hash=alt_hash,
            activation_ts="2026-02-13T10:12:00Z",
        )
    )
    assert rollout_alt.target_policy_hash == alt_hash

    start_after_rollout = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-after-rollout-a4-1")
    )
    session_id = start_after_rollout.session_id
    current_after_rollout = urm_policy_profile_current_endpoint(
        session_id=session_id,
        provider="codex",
    )
    assert current_after_rollout.policy_hash == alt_hash

    with pytest.raises(HTTPException) as conflict_exc:
        urm_policy_rollout_endpoint(
            PolicyRolloutRequest(
                provider="codex",
                client_request_id="rollout-alt-conflict-1",
                profile_id="default",
                target_policy_hash=alt_hash,
                activation_ts="2026-02-13T10:13:00Z",
            )
        )
    assert conflict_exc.value.status_code == 409
    assert conflict_exc.value.detail["code"] == "URM_POLICY_ROLLOUT_CONFLICT"

    with pytest.raises(HTTPException) as rollback_missing_exc:
        urm_policy_rollback_endpoint(
            PolicyRollbackRequest(
                provider="codex",
                client_request_id="rollback-missing-1",
                profile_id="default",
                target_policy_hash="f" * 64,
                activation_ts="2026-02-13T10:14:00Z",
            )
        )
    assert rollback_missing_exc.value.status_code == 400
    assert rollback_missing_exc.value.detail["code"] == "URM_POLICY_ROLLBACK_TARGET_NOT_FOUND"

    rollback_default = urm_policy_rollback_endpoint(
        PolicyRollbackRequest(
            provider="codex",
            client_request_id="rollback-default-1",
            profile_id="default",
            target_policy_hash=default_hash,
            activation_ts="2026-02-13T10:15:00Z",
        )
    )
    assert rollback_default.action == "rollback"
    assert rollback_default.target_policy_hash == default_hash

    active_after_rollback = urm_policy_active_endpoint(profile_id="default", provider="codex")
    assert active_after_rollback.policy_hash == default_hash
    assert active_after_rollback.source == "activation_log"
    assert active_after_rollback.action == "rollback"

    current_existing_session = urm_policy_profile_current_endpoint(
        session_id=session_id,
        provider="codex",
    )
    assert current_existing_session.policy_hash == alt_hash

    with pytest.raises(HTTPException) as idem_conflict_exc:
        urm_policy_rollout_endpoint(
            PolicyRolloutRequest(
                provider="codex",
                client_request_id="rollout-alt-1",
                profile_id="default",
                target_policy_hash=default_hash,
                activation_ts="2026-02-13T10:16:00Z",
            )
        )
    assert idem_conflict_exc.value.status_code == 409
    assert idem_conflict_exc.value.detail["code"] == "URM_POLICY_IDEMPOTENCY_CONFLICT"

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
    manager = _get_manager()
    assert _wait_for(
        lambda: (
            (runtime := manager._sessions.get(session_id)) is not None
            and isinstance(runtime.last_turn_id, str)
            and bool(runtime.last_turn_id)
        ),
        timeout_secs=2.0,
        interval_secs=0.02,
    )
    runtime = manager._sessions.get(session_id)  # type: ignore[attr-defined]
    assert runtime is not None
    target_turn_id = runtime.last_turn_id
    assert isinstance(target_turn_id, str) and target_turn_id

    steer = urm_copilot_steer_endpoint(
        CopilotSteerRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="steer-1",
            text="focus on tests first",
            steer_intent_class="reprioritize",
            target_turn_id=target_turn_id,
        )
    )
    assert steer.target_turn_id == target_turn_id
    assert steer.accepted_turn_id == target_turn_id
    assert steer.resolved_against_seq >= 0
    assert steer.idempotent_replay is False

    replay = urm_copilot_steer_endpoint(
        CopilotSteerRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="steer-1",
            text="focus on tests first",
            steer_intent_class="reprioritize",
            target_turn_id=target_turn_id,
        )
    )
    assert replay.accepted_turn_id == steer.accepted_turn_id
    assert replay.resolved_against_seq == steer.resolved_against_seq
    assert replay.idempotent_replay is True

    for idx in range(2, 7):
        if idx < 6:
            response = urm_copilot_steer_endpoint(
                CopilotSteerRequest(
                    provider="codex",
                    session_id=session_id,
                    client_request_id=f"steer-{idx}",
                    text=f"steer-{idx}",
                    target_turn_id=target_turn_id,
                )
            )
            assert response.accepted_turn_id == target_turn_id
            continue
        with pytest.raises(HTTPException) as exc_info:
            urm_copilot_steer_endpoint(
                CopilotSteerRequest(
                    provider="codex",
                    session_id=session_id,
                    client_request_id=f"steer-{idx}",
                    text=f"steer-{idx}",
                    target_turn_id=target_turn_id,
                )
            )
        assert exc_info.value.status_code == 400
        assert exc_info.value.detail["code"] == "URM_STEER_DENIED"
    events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    assert any(
        event.event_kind == "STEER_APPLIED"
        and event.payload.get("accepted_turn_id") == target_turn_id
        and isinstance(event.payload.get("resolved_against_seq"), int)
        for event in events
    )
    assert any(
        event.event_kind == "STEER_DENIED"
        and event.payload.get("error_code") == "URM_STEER_DENIED"
        and event.payload.get("target_turn_id") == target_turn_id
        for event in events
    )
    _reset_manager_for_tests()


def test_copilot_steer_last_turn_after_seq_unresolved_emits_denied_event(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-steer-after-seq-1")
    )
    session_id = start.session_id

    with pytest.raises(HTTPException) as exc_info:
        urm_copilot_steer_endpoint(
            CopilotSteerRequest(
                provider="codex",
                session_id=session_id,
                client_request_id="steer-after-seq-unresolved-1",
                text="reprioritize work",
                steer_intent_class="reprioritize",
                use_last_turn=True,
                after_seq=0,
            )
        )
    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "URM_STEER_TARGET_UNRESOLVED"
    manager = _get_manager()
    events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    denied = [event for event in events if event.event_kind == "STEER_DENIED"]
    assert denied
    latest_denied = denied[-1]
    assert latest_denied.payload.get("error_code") == "URM_STEER_TARGET_UNRESOLVED"
    assert latest_denied.payload.get("resolved_against_seq") == 0
    assert latest_denied.payload.get("target_turn_id") is None
    _reset_manager_for_tests()


def test_agent_spawn_and_cancel_terminal_idempotent(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v1")
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
    assert spawn.queue_seq == 0
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
    assert spawn_replay.queue_seq == spawn.queue_seq
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
    assert cancel.idempotent_replay is False
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
    assert not any(
        event.event_kind == "WORKER_CANCEL"
        and isinstance(event.payload, dict)
        and event.payload.get("worker_id") == spawn.child_id
        for event in events
    )
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


def test_connector_snapshot_create_get_and_idempotency(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv(
        "FAKE_APP_SERVER_APPS_JSON",
        '[{"id":"zeta","name":"Zeta"},{"id":"alpha","name":"Alpha"}]',
    )
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-connector-1")
    )
    session_id = start.session_id
    first = urm_connector_snapshot_create_endpoint(
        ConnectorSnapshotCreateRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="connector-snapshot-1",
        )
    )
    assert first.snapshot_id
    assert first.session_id == session_id
    assert len(first.connector_snapshot_hash) == 64
    assert [item.get("id") for item in first.connectors] == ["alpha", "zeta"]
    assert [item.get("id") for item in first.exposed_connectors] == ["alpha", "zeta"]
    assert [item.connector_id for item in first.connector_exposure] == ["alpha", "zeta"]
    assert all(item.exposed for item in first.connector_exposure)
    assert all(item.deny_reason_code is None for item in first.connector_exposure)

    replay = urm_connector_snapshot_create_endpoint(
        ConnectorSnapshotCreateRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="connector-snapshot-1",
        )
    )
    assert replay.snapshot_id == first.snapshot_id
    assert replay.idempotent_replay is True
    assert replay.exposed_connectors == first.exposed_connectors
    assert replay.connector_exposure == first.connector_exposure

    fetched = urm_connector_snapshot_get_endpoint(
        first.snapshot_id,
        session_id=session_id,
        provider="codex",
    )
    assert fetched.snapshot_id == first.snapshot_id
    assert fetched.connector_snapshot_hash == first.connector_snapshot_hash
    assert fetched.connectors == first.connectors
    assert fetched.exposed_connectors == first.exposed_connectors
    assert fetched.connector_exposure == first.connector_exposure
    snapshot_artifact = tmp_path / "evidence" / "codex" / "connectors" / f"{first.snapshot_id}.json"
    artifact_payload = json.loads(snapshot_artifact.read_text(encoding="utf-8"))
    schema_payload = json.loads(
        (_repo_root() / "spec" / "connector_snapshot.schema.json").read_text(encoding="utf-8")
    )
    schema_errors = sorted(
        Draft202012Validator(schema_payload).iter_errors(artifact_payload),
        key=lambda err: str(err.path),
    )
    assert schema_errors == []
    _reset_manager_for_tests()


def test_connector_snapshot_get_stale_and_not_found(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-connector-2")
    )
    session_id = start.session_id
    created = urm_connector_snapshot_create_endpoint(
        ConnectorSnapshotCreateRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="connector-snapshot-2",
        )
    )

    with pytest.raises(HTTPException) as stale_cap_exc:
        urm_connector_snapshot_get_endpoint(
            created.snapshot_id,
            session_id=session_id,
            provider="codex",
            requested_capability_snapshot_id="different-capability-snapshot-id",
        )
    assert stale_cap_exc.value.status_code == 400
    assert stale_cap_exc.value.detail["code"] == "URM_CONNECTOR_SNAPSHOT_STALE"

    with pytest.raises(HTTPException) as stale_ts_exc:
        urm_connector_snapshot_get_endpoint(
            created.snapshot_id,
            session_id=session_id,
            provider="codex",
            min_acceptable_ts=datetime.now(tz=timezone.utc) + timedelta(minutes=1),
        )
    assert stale_ts_exc.value.status_code == 400
    assert stale_ts_exc.value.detail["code"] == "URM_CONNECTOR_SNAPSHOT_STALE"

    with pytest.raises(HTTPException) as missing_exc:
        urm_connector_snapshot_get_endpoint(
            "missing-snapshot-id",
            session_id=session_id,
            provider="codex",
        )
    assert missing_exc.value.status_code == 404
    assert missing_exc.value.detail["code"] == "URM_CONNECTOR_SNAPSHOT_NOT_FOUND"
    manager = _get_manager()
    events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    connector_fail_codes = [
        event.payload.get("error_code")
        for event in events
        if event.event_kind == "TOOL_CALL_FAIL"
        and isinstance(event.payload, dict)
        and event.payload.get("tool_name") == "urm.connectors.snapshot.get"
    ]
    assert connector_fail_codes[-3:] == [
        "URM_CONNECTOR_SNAPSHOT_STALE",
        "URM_CONNECTOR_SNAPSHOT_STALE",
        "URM_CONNECTOR_SNAPSHOT_NOT_FOUND",
    ]
    replay_fetch = urm_connector_snapshot_get_endpoint(
        created.snapshot_id,
        session_id=session_id,
        provider="codex",
        execution_mode="replay",
        requested_capability_snapshot_id="different-capability-snapshot-id",
        min_acceptable_ts=datetime.now(tz=timezone.utc) + timedelta(minutes=1),
    )
    assert replay_fetch.snapshot_id == created.snapshot_id
    assert replay_fetch.connectors == created.connectors
    assert replay_fetch.exposed_connectors == created.exposed_connectors
    assert replay_fetch.connector_exposure == created.connector_exposure
    assert [item.connector_id for item in replay_fetch.connector_exposure] == [
        item.connector_id for item in created.connector_exposure
    ]
    _reset_manager_for_tests()


def test_connector_snapshot_create_replay_mode_blocks_live_discovery(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-connector-3")
    )
    session_id = start.session_id
    with pytest.raises(HTTPException) as replay_exc:
        urm_connector_snapshot_create_endpoint(
            ConnectorSnapshotCreateRequest(
                provider="codex",
                session_id=session_id,
                client_request_id="connector-snapshot-replay-1",
                execution_mode="replay",
            )
        )
    assert replay_exc.value.status_code == 400
    assert replay_exc.value.detail["code"] == "URM_CONNECTOR_REPLAY_LIVE_READ_BLOCKED"
    manager = _get_manager()
    events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    fail_events = [
        event
        for event in events
        if event.event_kind == "TOOL_CALL_FAIL"
        and isinstance(event.payload, dict)
        and event.payload.get("tool_name") == "urm.connectors.snapshot.create"
    ]
    assert fail_events
    detail = fail_events[-1].payload
    assert detail.get("error_code") == "URM_CONNECTOR_REPLAY_LIVE_READ_BLOCKED"
    assert detail.get("execution_mode") == "replay"
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
    assert spawn1.queue_seq == 1
    assert spawn2.queue_seq == 2
    spawn2_replay = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-2",
            prompt="second child",
            target_turn_id="turn-bootstrap-1",
        )
    )
    assert spawn2_replay.child_id == spawn2.child_id
    assert spawn2_replay.queue_seq == spawn2.queue_seq
    assert spawn2_replay.idempotent_replay is True
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
    _wait_for(
        lambda: (
            (child1 := manager._child_runs.get(spawn1.child_id)) is not None
            and (child2 := manager._child_runs.get(spawn2.child_id)) is not None
            and child1.status in {"completed", "failed", "cancelled"}
            and child2.status in {"completed", "failed", "cancelled"}
        ),
        timeout_secs=5.0,
        interval_secs=0.05,
    )
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


def test_agent_spawn_queue_mode_v2_persists_dispatch_tokens_and_worker_start_anchors(
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
        CopilotSessionStartRequest(provider="codex", client_request_id="start-child-v2-r1-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-child-v2-r1-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-child-v2-r1-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    spawn1 = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-r1-1",
            prompt="first child",
            target_turn_id="turn-bootstrap-r1-1",
        )
    )
    spawn2 = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-r1-2",
            prompt="second child",
            target_turn_id="turn-bootstrap-r1-1",
        )
    )
    assert spawn1.queue_seq == 1
    assert spawn2.queue_seq == 2

    manager = _get_manager()
    _wait_for(
        lambda: (
            (child1 := manager._child_runs.get(spawn1.child_id)) is not None
            and (child2 := manager._child_runs.get(spawn2.child_id)) is not None
            and child1.dispatch_seq is not None
            and child2.dispatch_seq is not None
        ),
        timeout_secs=5.0,
        interval_secs=0.05,
    )
    child1 = manager._child_runs.get(spawn1.child_id)  # type: ignore[attr-defined]
    child2 = manager._child_runs.get(spawn2.child_id)  # type: ignore[attr-defined]
    assert child1 is not None and child2 is not None
    assert child1.lease_id == spawn1.child_id
    assert child2.lease_id == spawn2.child_id
    assert child1.dispatch_seq is not None and child2.dispatch_seq is not None
    assert sorted([child1.dispatch_seq, child2.dispatch_seq]) == [1, 2]

    config = URMRuntimeConfig.from_env()
    with transaction(db_path=config.db_path) as con:
        token1 = get_dispatch_token_for_child(con=con, child_id=spawn1.child_id)
        token2 = get_dispatch_token_for_child(con=con, child_id=spawn2.child_id)
    assert token1 is not None and token2 is not None
    assert token1.parent_session_id == session_id
    assert token2.parent_session_id == session_id
    assert token1.queue_seq == 1
    assert token2.queue_seq == 2
    assert token1.worker_run_id == spawn1.child_id
    assert token2.worker_run_id == spawn2.child_id
    assert token1.dispatch_seq is not None
    assert token2.dispatch_seq is not None
    assert sorted([token1.dispatch_seq, token2.dispatch_seq]) == [1, 2]
    assert token1.phase in {"started", "terminal"}
    assert token2.phase in {"started", "terminal"}

    child1_events = (
        tmp_path / "evidence" / "codex" / "agent" / spawn1.child_id / "urm_events.ndjson"
    ).read_text(encoding="utf-8", errors="replace")
    child2_events = (
        tmp_path / "evidence" / "codex" / "agent" / spawn2.child_id / "urm_events.ndjson"
    ).read_text(encoding="utf-8", errors="replace")
    child1_records = [json.loads(line) for line in child1_events.splitlines() if line.strip()]
    child2_records = [json.loads(line) for line in child2_events.splitlines() if line.strip()]
    child1_running = [
        event
        for event in child1_records
        if event.get("event") == "WORKER_START"
        and isinstance(event.get("detail"), dict)
        and event["detail"].get("status") == "running"
    ]
    child2_running = [
        event
        for event in child2_records
        if event.get("event") == "WORKER_START"
        and isinstance(event.get("detail"), dict)
        and event["detail"].get("status") == "running"
    ]
    assert child1_running and child2_running
    child1_detail = child1_running[-1]["detail"]
    child2_detail = child2_running[-1]["detail"]
    assert child1_detail.get("dispatch_seq") == token1.dispatch_seq
    assert child2_detail.get("dispatch_seq") == token2.dispatch_seq
    assert child1_detail.get("lease_id") == token1.worker_run_id
    assert child2_detail.get("lease_id") == token2.worker_run_id
    assert child1_detail.get("parent_stream_id") == f"copilot:{session_id}"
    assert child2_detail.get("parent_stream_id") == f"copilot:{session_id}"
    assert child1_detail.get("child_id") == spawn1.child_id
    assert child2_detail.get("child_id") == spawn2.child_id
    _reset_manager_for_tests()


def test_agent_spawn_queue_mode_v2_cancel_running_is_deterministic(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "0.8")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-child-v2-cancel-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-child-v2-cancel-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-child-v2-cancel-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    spawn1 = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-cancel-1",
            prompt="first child",
            target_turn_id="turn-bootstrap-cancel-1",
        )
    )
    spawn2 = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-cancel-2",
            prompt="second child",
            target_turn_id="turn-bootstrap-cancel-1",
        )
    )
    assert spawn1.queue_seq == 1
    assert spawn2.queue_seq == 2

    manager = _get_manager()
    _wait_for(
        lambda: (
            (child2 := manager._child_runs.get(spawn2.child_id)) is not None
            and child2.status in {"queued", "running"}
        ),
        timeout_secs=3.0,
    )
    child2 = manager._child_runs.get(spawn2.child_id)  # type: ignore[attr-defined]
    assert child2 is not None
    child2_status_before_cancel = child2.status
    assert child2_status_before_cancel in {"queued", "running"}

    cancel = urm_agent_cancel_endpoint(
        spawn1.child_id,
        AgentCancelRequest(
            provider="codex",
            client_request_id="cancel-child-v2-cancel-1",
        ),
    )
    assert cancel.status == "cancelled"
    assert cancel.idempotent_replay is False

    _wait_for(
        lambda: (
            (child2 := manager._child_runs.get(spawn2.child_id)) is not None
            and child2.status in {"running", "completed", "failed", "cancelled"}
        ),
        timeout_secs=5.0,
    )
    child2 = manager._child_runs.get(spawn2.child_id)  # type: ignore[attr-defined]
    assert child2 is not None
    assert child2.status != "queued"

    child1_events = (
        tmp_path / "evidence" / "codex" / "agent" / spawn1.child_id / "urm_events.ndjson"
    ).read_text(encoding="utf-8", errors="replace")
    child2_events = (
        tmp_path / "evidence" / "codex" / "agent" / spawn2.child_id / "urm_events.ndjson"
    ).read_text(encoding="utf-8", errors="replace")
    child1_records = [json.loads(line) for line in child1_events.splitlines() if line.strip()]
    child2_records = [json.loads(line) for line in child2_events.splitlines() if line.strip()]
    cancel_events = [event for event in child1_records if event.get("event") == "WORKER_CANCEL"]
    running_events = [
        event
        for event in child2_records
        if event.get("event") == "WORKER_START"
        and isinstance(event.get("detail"), dict)
        and event["detail"].get("status") == "running"
    ]
    assert cancel_events
    cancel_detail = cancel_events[-1].get("detail", {})
    assert isinstance(cancel_detail, dict)
    assert cancel_detail.get("cancel_request_id") == "cancel-child-v2-cancel-1"
    assert running_events
    parent_events, _ = manager.iter_events(session_id=session_id, after_seq=0)
    parent_cancel_events = [
        event
        for event in parent_events
        if event.event_kind == "WORKER_CANCEL"
        and isinstance(event.payload, dict)
        and event.payload.get("worker_id") == spawn1.child_id
    ]
    assert parent_cancel_events
    assert parent_cancel_events[-1].payload.get("cancel_request_id") == "cancel-child-v2-cancel-1"
    if child2_status_before_cancel == "queued":
        cancel_ts = datetime.fromisoformat(str(cancel_events[0]["ts"]))
        running_ts = datetime.fromisoformat(str(running_events[0]["ts"]))
        assert cancel_ts <= running_ts
    _reset_manager_for_tests()


def test_agent_spawn_queue_mode_v2_idempotency_conflict_includes_payload_hashes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-child-v2-idem-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-child-v2-idem-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-child-v2-idem-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    first = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-idem-1",
            prompt="first payload",
            target_turn_id="turn-bootstrap-idem-1",
        )
    )
    replay = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-child-v2-idem-1",
            prompt="first payload",
            target_turn_id="turn-bootstrap-idem-1",
        )
    )
    assert replay.child_id == first.child_id
    assert replay.queue_seq == first.queue_seq
    assert replay.idempotent_replay is True

    with pytest.raises(HTTPException) as exc_info:
        urm_agent_spawn_endpoint(
            AgentSpawnRequest(
                provider="codex",
                session_id=session_id,
                client_request_id="spawn-child-v2-idem-1",
                prompt="different payload",
                target_turn_id="turn-bootstrap-idem-1",
            )
        )
    detail = exc_info.value.detail
    assert exc_info.value.status_code == 409
    assert detail["code"] == "URM_IDEMPOTENCY_KEY_CONFLICT"
    assert detail["context"]["client_request_id"] == "spawn-child-v2-idem-1"
    assert detail["context"]["stored_payload_hash"] != detail["context"]["incoming_payload_hash"]
    _reset_manager_for_tests()


def test_agent_spawn_budget_snapshot_v1_immutable_after_profile_switch(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "0.8")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-b2-immut-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-b2-immut-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-b2-immut-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )

    spawn = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-b2-immut-1",
            prompt="budget snapshot immutability",
            target_turn_id="turn-b2-immut-1",
        )
    )
    manager = _get_manager()
    child = manager._child_runs.get(spawn.child_id)  # type: ignore[attr-defined]
    assert child is not None
    snapshot_before = dict(child.budget_snapshot)
    assert snapshot_before["budget_version"] == "budget.v1"
    assert snapshot_before["max_solver_calls"] == 40
    assert snapshot_before["max_duration_secs"] <= 300
    assert snapshot_before["max_token_budget"] == 20_000
    assert snapshot_before["token_usage_unobserved"] is True

    selected = urm_policy_profile_select_endpoint(
        PolicyProfileSelectRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="profile-select-b2-immut-1",
            profile_id="safe_mode",
        )
    )
    assert selected.profile_id == "safe_mode"

    child_after = manager._child_runs.get(spawn.child_id)  # type: ignore[attr-defined]
    assert child_after is not None
    assert child_after.budget_snapshot == snapshot_before
    _reset_manager_for_tests()


def test_agent_spawn_budget_breach_solver_calls_is_deterministic(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "0.1")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()
    manager = _get_manager()

    def _tight_budget_snapshot(self: object, *, runtime: object) -> dict[str, object]:
        del self, runtime
        return _budget_snapshot_v1(
            max_solver_calls=1,
            max_duration_secs=300,
            max_token_budget=20_000,
            remaining_parent_duration_secs=300,
            token_usage_unobserved=True,
        )

    monkeypatch.setattr(type(manager), "_child_budget_snapshot", _tight_budget_snapshot)

    failure_signatures: list[tuple[str, int, int, bool]] = []
    for run_idx in range(2):
        start = urm_copilot_start_endpoint(
            CopilotSessionStartRequest(
                provider="codex",
                client_request_id=f"start-b2-budget-{run_idx}",
            )
        )
        session_id = start.session_id
        urm_copilot_send_endpoint(
            CopilotSessionSendRequest(
                provider="codex",
                session_id=session_id,
                client_request_id=f"send-b2-budget-bootstrap-{run_idx}",
                message={
                    "jsonrpc": "2.0",
                    "id": f"req-b2-budget-bootstrap-{run_idx}",
                    "method": "copilot.user_message",
                    "params": {"text": "bootstrap turn"},
                },
            )
        )
        spawn = urm_agent_spawn_endpoint(
            AgentSpawnRequest(
                provider="codex",
                session_id=session_id,
                client_request_id=f"spawn-b2-budget-{run_idx}",
                prompt="trigger solver-call budget breach",
                target_turn_id=f"turn-b2-budget-{run_idx}",
            )
        )
        assert _wait_for(
            lambda: (
                (child := manager._child_runs.get(spawn.child_id)) is not None
                and child.status in {"completed", "failed", "cancelled"}
                and child.persisted
            ),
            timeout_secs=5.0,
        )
        child = manager._child_runs.get(spawn.child_id)  # type: ignore[attr-defined]
        assert child is not None
        assert child.status == "failed"
        assert child.error_code == "URM_CHILD_BUDGET_EXCEEDED"
        assert child.token_usage_unobserved is True

        child_events_path = (
            tmp_path / "evidence" / "codex" / "agent" / spawn.child_id / "urm_events.ndjson"
        )
        events = [
            json.loads(line)
            for line in child_events_path.read_text(encoding="utf-8", errors="replace").splitlines()
            if line.strip()
        ]
        fail_events = [
            event
            for event in events
            if event.get("event") == "WORKER_FAIL"
            and isinstance(event.get("detail"), dict)
            and event["detail"].get("error_code") == "URM_CHILD_BUDGET_EXCEEDED"
        ]
        assert fail_events
        fail_detail = fail_events[-1]["detail"]
        signature = (
            str(fail_detail.get("budget_dimension")),
            int(fail_detail.get("budget_limit")),
            int(fail_detail.get("budget_observed")),
            bool(fail_detail.get("token_usage_unobserved")),
        )
        failure_signatures.append(signature)
        assert signature == ("solver_calls", 1, 1, True)

        with transaction(db_path=URMRuntimeConfig.from_env().db_path) as con:
            row = get_worker_run(con=con, worker_id=spawn.child_id)
        assert row is not None
        assert row.error_code == "URM_CHILD_BUDGET_EXCEEDED"
        assert isinstance(row.result_json, dict)
        budget_runtime = row.result_json.get("budget_runtime")
        assert isinstance(budget_runtime, dict)
        assert budget_runtime.get("solver_calls_observed") == 1

        urm_copilot_stop_endpoint(
            CopilotStopRequest(provider="codex", session_id=session_id)
        )

    assert failure_signatures[0] == failure_signatures[1]
    _reset_manager_for_tests()


def test_agent_spawn_budget_invalid_accounting_mode_fails_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "0.1")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()
    manager = _get_manager()

    def _invalid_budget_snapshot(self: object, *, runtime: object) -> dict[str, object]:
        del self, runtime
        return _budget_snapshot_v1(
            max_solver_calls=40,
            max_duration_secs=300,
            max_token_budget=20_000,
            remaining_parent_duration_secs=300,
            accounting_model="reservation_v0",
            token_usage_unobserved=True,
        )

    monkeypatch.setattr(type(manager), "_child_budget_snapshot", _invalid_budget_snapshot)

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-b2-accounting-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-b2-accounting-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-b2-accounting-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )
    spawn = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-b2-accounting-1",
            prompt="trigger invalid accounting model",
            target_turn_id="turn-b2-accounting-1",
        )
    )
    assert _wait_for(
        lambda: (
            (child := manager._child_runs.get(spawn.child_id)) is not None
            and child.status in {"completed", "failed", "cancelled"}
            and child.persisted
        ),
        timeout_secs=5.0,
    )
    child = manager._child_runs.get(spawn.child_id)  # type: ignore[attr-defined]
    assert child is not None
    assert child.status == "failed"
    assert child.error_code == "URM_DISPATCH_ACCOUNTING_MODE_INVALID"

    events_path = tmp_path / "evidence" / "codex" / "agent" / spawn.child_id / "urm_events.ndjson"
    events = [
        json.loads(line)
        for line in events_path.read_text(encoding="utf-8", errors="replace").splitlines()
        if line.strip()
    ]
    fail_events = [
        event
        for event in events
        if event.get("event") == "WORKER_FAIL"
        and isinstance(event.get("detail"), dict)
        and event["detail"].get("error_code") == "URM_DISPATCH_ACCOUNTING_MODE_INVALID"
    ]
    assert fail_events
    _reset_manager_for_tests()


def test_agent_spawn_budget_running_total_shared_parent_lane_is_deterministic(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    codex_bin = _prepare_fake_codex(tmp_path=tmp_path)
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))
    monkeypatch.setenv("ADEU_CODEX_BIN", str(codex_bin))
    monkeypatch.setenv("URM_CHILD_QUEUE_MODE", "v2")
    monkeypatch.setenv("FAKE_APP_SERVER_WAIT_SECS", "0.2")
    monkeypatch.delenv("FAKE_APP_SERVER_DISABLE_READY", raising=False)
    _reset_manager_for_tests()
    manager = _get_manager()

    def _shared_budget_snapshot(self: object, *, runtime: object) -> dict[str, object]:
        del self, runtime
        return _budget_snapshot_v1(
            max_solver_calls=2,
            max_duration_secs=300,
            max_token_budget=20_000,
            remaining_parent_duration_secs=300,
            accounting_model="running_total_v1",
            token_usage_unobserved=True,
        )

    monkeypatch.setattr(type(manager), "_child_budget_snapshot", _shared_budget_snapshot)

    start = urm_copilot_start_endpoint(
        CopilotSessionStartRequest(provider="codex", client_request_id="start-b2-running-total-1")
    )
    session_id = start.session_id
    urm_copilot_send_endpoint(
        CopilotSessionSendRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="send-b2-running-total-bootstrap-1",
            message={
                "jsonrpc": "2.0",
                "id": "req-b2-running-total-bootstrap-1",
                "method": "copilot.user_message",
                "params": {"text": "bootstrap turn"},
            },
        )
    )
    spawn1 = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-b2-running-total-1",
            prompt="first child",
            target_turn_id="turn-b2-running-total-1",
        )
    )
    spawn2 = urm_agent_spawn_endpoint(
        AgentSpawnRequest(
            provider="codex",
            session_id=session_id,
            client_request_id="spawn-b2-running-total-2",
            prompt="second child",
            target_turn_id="turn-b2-running-total-1",
        )
    )
    assert _wait_for(
        lambda: (
            (child1 := manager._child_runs.get(spawn1.child_id)) is not None
            and (child2 := manager._child_runs.get(spawn2.child_id)) is not None
            and child1.status in {"completed", "failed", "cancelled"}
            and child2.status in {"completed", "failed", "cancelled"}
            and child1.persisted
            and child2.persisted
        ),
        timeout_secs=8.0,
        interval_secs=0.05,
    )
    child1 = manager._child_runs.get(spawn1.child_id)  # type: ignore[attr-defined]
    child2 = manager._child_runs.get(spawn2.child_id)  # type: ignore[attr-defined]
    assert child1 is not None and child2 is not None
    assert any(
        child.error_code == "URM_CHILD_BUDGET_EXCEEDED" for child in (child1, child2)
    )

    with transaction(db_path=URMRuntimeConfig.from_env().db_path) as con:
        solver_total = get_parent_budget_total(
            con=con,
            parent_session_id=session_id,
            budget_lane="solver_calls",
        )
    assert solver_total is not None
    assert solver_total.max_total == 2
    # With >= enforcement and shared running totals, only the first debit is accepted.
    assert solver_total.current_total == 1
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
                "dispatch_seq": 1,
                "lease_id": child_id,
                "phase": "started",
                "parent_seq": 7,
                "raw_jsonl_path": raw_rel_path,
                "urm_events_path": events_rel_path,
            },
        )
        upsert_dispatch_token_queued(
            con=con,
            child_id=child_id,
            parent_session_id=parent_session_id,
            parent_stream_id=f"copilot:{parent_session_id}",
            parent_seq=7,
            worker_run_id=child_id,
        )
        lease_dispatch_token(con=con, child_id=child_id)
        set_dispatch_token_phase(con=con, child_id=child_id, phase="started")

    _get_manager()

    with transaction(db_path=config.db_path) as con:
        row = get_worker_run(con=con, worker_id=child_id)
    assert row is not None
    assert row.status == "failed"
    assert row.error_code == "URM_CHILD_TERMINATED_ON_RESTART"

    child_events_payload = events_path.read_text(encoding="utf-8", errors="replace")
    assert "WORKER_FAIL" in child_events_payload
    assert "URM_CHILD_TERMINATED_ON_RESTART" in child_events_payload
    assert '"dispatch_seq":1' in child_events_payload
    assert '"lease_id":"stale-child-run-1"' in child_events_payload

    audit_path = config.evidence_root / "audit" / parent_session_id / "urm_events.ndjson"
    assert audit_path.is_file()
    audit_payload = audit_path.read_text(encoding="utf-8", errors="replace")
    assert "WORKER_FAIL" in audit_payload
    assert "URM_CHILD_TERMINATED_ON_RESTART" in audit_payload
    assert '"dispatch_seq":1' in audit_payload
    _reset_manager_for_tests()


def test_manager_marks_orphaned_dispatch_tokens_on_startup(
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
    child_id = "stale-child-orphan-1"
    parent_session_id = "stale-parent-orphan-1"
    raw_rel_path = f"evidence/codex/agent/{child_id}/codex_raw.ndjson"
    events_rel_path = f"evidence/codex/agent/{child_id}/urm_events.ndjson"
    raw_path = config.var_root / raw_rel_path
    events_path = config.var_root / events_rel_path
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    events_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text("", encoding="utf-8")
    # Simulate crash-truncated NDJSON.
    events_path.write_text("{\"schema\":\"urm-events@1\"", encoding="utf-8")

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
                "parent_turn_id": "turn-stale-orphan-1",
                "profile_id": "default",
                "profile_version": "profile.v1",
                "budget_snapshot": {
                    "budget_version": "budget.v1",
                    "max_solver_calls": 10,
                    "max_token_budget": 20_000,
                    "max_duration_secs": 300,
                },
                "inherited_policy_hash": "policy-hash-stale-orphan-1",
                "capabilities_allowed": ["urm.agent.spawn"],
                "queue_seq": 1,
                "raw_jsonl_path": raw_rel_path,
                "urm_events_path": events_rel_path,
            },
        )
        upsert_dispatch_token_queued(
            con=con,
            child_id=child_id,
            parent_session_id=parent_session_id,
            parent_stream_id=f"copilot:{parent_session_id}",
            parent_seq=11,
            worker_run_id=child_id,
        )
        lease_dispatch_token(con=con, child_id=child_id)

    _get_manager()

    with transaction(db_path=config.db_path) as con:
        row = get_worker_run(con=con, worker_id=child_id)
        token = get_dispatch_token_for_child(con=con, child_id=child_id)
    assert row is not None
    assert row.status == "failed"
    assert row.error_code == "URM_SCHEDULER_LEASE_ORPHANED"
    assert token is not None
    assert token.phase == "terminal"

    child_records = [
        json.loads(line)
        for line in events_path.read_text(encoding="utf-8", errors="replace").splitlines()
        if line.strip()
    ]
    fail_events = [
        event
        for event in child_records
        if event.get("event") == "WORKER_FAIL" and isinstance(event.get("detail"), dict)
    ]
    assert fail_events
    fail_detail = fail_events[-1]["detail"]
    assert fail_detail.get("error_code") == "URM_SCHEDULER_LEASE_ORPHANED"
    assert fail_detail.get("reason") == "lease_orphaned"
    assert fail_detail.get("lease_id") == child_id
    assert fail_detail.get("dispatch_seq") == 1
    assert fail_detail.get("parent_stream_id") == f"copilot:{parent_session_id}"
    assert fail_detail.get("parent_seq") == 11

    audit_path = config.evidence_root / "audit" / parent_session_id / "urm_events.ndjson"
    assert audit_path.is_file()
    audit_payload = audit_path.read_text(encoding="utf-8", errors="replace")
    assert "URM_SCHEDULER_LEASE_ORPHANED" in audit_payload
    assert "lease_orphaned" in audit_payload
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
        "PROOF_RUN_PASS",
        "PROOF_RUN_PASS",
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
        "PROOF_RUN_PASS",
        "PROOF_RUN_PASS",
        "POLICY_DENIED",
    ]
