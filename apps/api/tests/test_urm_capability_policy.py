from __future__ import annotations

import json
from pathlib import Path

import pytest
import urm_runtime.capability_policy as capability_policy
from urm_runtime.capability_policy import (
    authorize_action,
    load_capability_policy,
    reset_capability_policy_cache,
)
from urm_runtime.errors import URMError


@pytest.fixture(autouse=True)
def _reset_policy_cache() -> None:
    reset_capability_policy_cache()


@pytest.mark.parametrize(
    ("action", "writes_allowed", "approval_provided"),
    [
        ("adeu.get_app_state", False, False),
        ("adeu.list_templates", False, False),
        ("adeu.read_evidence", False, False),
        ("adeu.run_workflow", False, False),
        ("urm.spawn_worker", False, False),
        ("urm.set_mode.disable_writes", False, False),
        ("urm.set_mode.enable_writes", False, True),
        ("adeu.apply_patch", True, True),
    ],
)
def test_policy_allows_expected_copilot_actions(
    action: str,
    writes_allowed: bool,
    approval_provided: bool,
) -> None:
    authorize_action(
        role="copilot",
        action=action,
        writes_allowed=writes_allowed,
        approval_provided=approval_provided,
    )


@pytest.mark.parametrize("role", ["pipeline_worker", "auditor", "unknown-role"])
def test_policy_denies_action_when_role_capability_is_not_allowed(role: str) -> None:
    with pytest.raises(URMError) as exc_info:
        authorize_action(
            role=role,
            action="adeu.get_app_state",
            writes_allowed=False,
            approval_provided=False,
        )
    assert exc_info.value.detail.code == "URM_POLICY_DENIED"


def test_policy_denies_unknown_action_before_allow_checks() -> None:
    with pytest.raises(URMError) as exc_info:
        authorize_action(
            role="copilot",
            action="does.not.exist",
            writes_allowed=False,
            approval_provided=False,
        )
    assert exc_info.value.detail.code == "URM_POLICY_DENIED"
    assert exc_info.value.detail.message == "action is not defined in capability lattice"


def test_policy_enforces_runtime_mode_before_approval() -> None:
    with pytest.raises(URMError) as exc_info:
        authorize_action(
            role="copilot",
            action="adeu.apply_patch",
            writes_allowed=False,
            approval_provided=False,
        )
    assert exc_info.value.detail.code == "URM_POLICY_DENIED"
    assert exc_info.value.detail.message == "runtime mode does not permit action"


def test_policy_requires_approval_when_action_demands_it() -> None:
    with pytest.raises(URMError) as exc_info:
        authorize_action(
            role="copilot",
            action="adeu.apply_patch",
            writes_allowed=True,
            approval_provided=False,
        )
    assert exc_info.value.detail.code == "URM_APPROVAL_REQUIRED"


def test_policy_loads_packaged_fallback_when_env_and_repo_are_unavailable(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("URM_POLICY_ROOT", "/tmp/does-not-exist-urm-policy")
    monkeypatch.setattr(capability_policy, "_discover_repo_root", lambda anchor: None)
    policy = load_capability_policy()
    assert policy.policy_root == "package:urm_runtime.policy"
    assert "read_state" in policy.capabilities


def test_authorize_action_returns_policy_decision_trace_for_allow() -> None:
    decision = authorize_action(
        role="copilot",
        action="adeu.get_app_state",
        writes_allowed=False,
        approval_provided=False,
        session_active=True,
    )
    assert decision.policy_decision.decision == "allow"
    assert decision.policy_decision.decision_code == "ALLOW_HARD_GATED_ACTION"
    assert decision.policy_decision.trace_version == "odeu.instruction-trace.v1"


def test_authorize_action_emits_policy_eval_events_for_allow() -> None:
    captured: list[tuple[str, dict[str, object]]] = []

    decision = authorize_action(
        role="copilot",
        action="adeu.get_app_state",
        writes_allowed=False,
        approval_provided=False,
        session_active=True,
        emit_policy_event=lambda event, detail: captured.append((event, detail)),
    )
    assert decision.policy_decision.decision == "allow"
    assert [item[0] for item in captured] == ["POLICY_EVAL_START", "POLICY_EVAL_PASS"]
    assert captured[0][1]["decision_code"] == "PENDING"
    assert isinstance(captured[1][1]["matched_rule_ids"], list)


def test_authorize_action_emits_policy_denied_for_instruction_rule(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    policy_path = tmp_path / "policy.deny.json"
    policy_path.write_text(
        json.dumps(
            {
                "schema": "odeu.instructions.v1",
                "rules": [
                    {
                        "rule_id": "deny_copilot",
                        "rule_version": 1,
                        "priority": 1,
                        "kind": "deny",
                        "when": {"atom": "role_is", "args": ["copilot"]},
                        "then": {"effect": "deny_action", "params": {}},
                        "message": "deny copilot for test",
                        "code": "DENY_COPILOT_TEST",
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setenv("URM_INSTRUCTION_POLICY_PATH", str(policy_path))
    captured: list[tuple[str, dict[str, object]]] = []
    with pytest.raises(URMError) as exc_info:
        authorize_action(
            role="copilot",
            action="adeu.get_app_state",
            writes_allowed=False,
            approval_provided=False,
            session_active=True,
            emit_policy_event=lambda event, detail: captured.append((event, detail)),
        )
    assert exc_info.value.detail.code == "DENY_COPILOT_TEST"
    assert [item[0] for item in captured] == ["POLICY_EVAL_START", "POLICY_DENIED"]
