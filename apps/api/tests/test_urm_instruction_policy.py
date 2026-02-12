from __future__ import annotations

import pytest
from pydantic import ValidationError
from urm_runtime.errors import URMError
from urm_runtime.instruction_policy import (
    PolicyContext,
    compute_policy_hash,
    evaluate_instruction_policy,
    validate_instruction_policy_document,
)


def _make_rule(
    *,
    rule_id: str,
    priority: int,
    kind: str,
    effect: str,
    when: dict[str, object],
    code: str,
    message: str = "policy rule",
) -> dict[str, object]:
    return {
        "rule_id": rule_id,
        "rule_version": 1,
        "priority": priority,
        "kind": kind,
        "when": when,
        "then": {"effect": effect, "params": {}},
        "message": message,
        "code": code,
    }


def _context(**overrides: object) -> PolicyContext:
    payload: dict[str, object] = {
        "role": "copilot",
        "mode": "strict",
        "action_kind": "adeu.apply_patch",
        "action_hash": "hash-1",
        "session_active": True,
        "capabilities_present": ["mutate_apply_patch", "read_state"],
        "capabilities_allowed": ["mutate_apply_patch", "read_state"],
        "approval_present": False,
        "approval_valid": False,
        "approval_unexpired": False,
        "approval_unused": False,
        "evidence_kinds": ["event"],
        "warrant": "observed",
        "evaluation_ts": "2026-02-12T09:10:00Z",
    }
    payload.update(overrides)
    return PolicyContext.model_validate(payload)


def test_policy_hash_is_stable_under_rule_reordering_and_message_changes() -> None:
    rule_a = _make_rule(
        rule_id="allow_read",
        priority=20,
        kind="allow",
        effect="allow_action",
        when={"atom": "role_is", "args": ["copilot"]},
        code="ALLOW_READ",
        message="allow read",
    )
    rule_b = _make_rule(
        rule_id="require_approval",
        priority=10,
        kind="require",
        effect="require_approval",
        when={"atom": "action_kind_is", "args": ["adeu.apply_patch"]},
        code="REQUIRE_APPROVAL",
        message="require approval",
    )
    policy_one = validate_instruction_policy_document(
        {"schema": "odeu.instructions.v1", "rules": [rule_a, rule_b]},
        strict=True,
    )
    policy_two = validate_instruction_policy_document(
        {
            "schema": "odeu.instructions.v1",
            "rules": [
                {**rule_b, "message": "changed text"},
                {**rule_a, "message": "another changed text"},
            ],
        },
        strict=True,
    )
    assert compute_policy_hash(policy_one) == compute_policy_hash(policy_two)


def test_rule_driven_deny_takes_precedence_and_uses_rule_code() -> None:
    policy = validate_instruction_policy_document(
        {
            "schema": "odeu.instructions.v1",
            "rules": [
                _make_rule(
                    rule_id="allow_all_copilot",
                    priority=20,
                    kind="allow",
                    effect="allow_action",
                    when={"atom": "role_is", "args": ["copilot"]},
                    code="ALLOW_COPILOT",
                ),
                _make_rule(
                    rule_id="deny_strict_mode",
                    priority=10,
                    kind="deny",
                    effect="deny_action",
                    when={"atom": "mode_is", "args": ["strict"]},
                    code="DENY_STRICT",
                ),
            ],
        }
    )
    decision = evaluate_instruction_policy(policy=policy, context=_context())
    assert decision.decision == "deny"
    assert decision.decision_code == "DENY_STRICT"
    assert decision.matched_rule_ids == ["deny_strict_mode", "allow_all_copilot"]


def test_fallback_deny_uses_default_policy_code() -> None:
    policy = validate_instruction_policy_document({"schema": "odeu.instructions.v1", "rules": []})
    decision = evaluate_instruction_policy(policy=policy, context=_context())
    assert decision.decision == "deny"
    assert decision.decision_code == "URM_POLICY_DENIED"


def test_require_approval_denies_without_valid_approval_and_allows_with_valid_approval() -> None:
    policy = validate_instruction_policy_document(
        {
            "schema": "odeu.instructions.v1",
            "rules": [
                _make_rule(
                    rule_id="require_patch_approval",
                    priority=10,
                    kind="require",
                    effect="require_approval",
                    when={"atom": "action_kind_is", "args": ["adeu.apply_patch"]},
                    code="REQUIRE_APPROVAL",
                ),
                _make_rule(
                    rule_id="allow_patch",
                    priority=20,
                    kind="allow",
                    effect="allow_action",
                    when={"atom": "action_kind_is", "args": ["adeu.apply_patch"]},
                    code="ALLOW_PATCH",
                ),
            ],
        }
    )

    denied = evaluate_instruction_policy(policy=policy, context=_context())
    assert denied.decision == "deny"
    assert denied.decision_code == "URM_APPROVAL_REQUIRED"
    assert denied.required_approval is True

    approved_ctx = _context(
        approval_present=True,
        approval_valid=True,
        approval_unexpired=True,
        approval_unused=True,
    )
    allowed = evaluate_instruction_policy(policy=policy, context=approved_ctx)
    assert allowed.decision == "allow"
    assert allowed.decision_code == "ALLOW_PATCH"
    assert allowed.required_approval is True


def test_matched_rule_ids_include_derive_rules_and_advisories_are_kept_on_deny() -> None:
    policy = validate_instruction_policy_document(
        {
            "schema": "odeu.instructions.v1",
            "rules": [
                _make_rule(
                    rule_id="derive_warn",
                    priority=5,
                    kind="derive",
                    effect="emit_advisory",
                    when={"atom": "role_is", "args": ["copilot"]},
                    code="ADVISORY_RULE",
                ),
                _make_rule(
                    rule_id="deny_strict",
                    priority=10,
                    kind="deny",
                    effect="deny_action",
                    when={"atom": "mode_is", "args": ["strict"]},
                    code="DENY_STRICT",
                ),
            ],
        }
    )
    decision = evaluate_instruction_policy(policy=policy, context=_context())
    assert decision.decision == "deny"
    assert decision.matched_rule_ids == ["derive_warn", "deny_strict"]
    assert decision.advisories and decision.advisories[0]["rule_id"] == "derive_warn"


def test_validate_instruction_policy_document_rejects_rule_cap_exceeded() -> None:
    rules = [
        _make_rule(
            rule_id=f"allow_{idx}",
            priority=idx,
            kind="allow",
            effect="allow_action",
            when={"atom": "session_active", "args": []},
            code=f"ALLOW_{idx}",
        )
        for idx in range(0, 501)
    ]
    with pytest.raises(URMError) as exc_info:
        validate_instruction_policy_document({"schema": "odeu.instructions.v1", "rules": rules})
    assert exc_info.value.detail.code == "URM_POLICY_CAP_EXCEEDED"


def test_validate_instruction_policy_document_rejects_derive_firewall_atoms() -> None:
    with pytest.raises(URMError) as exc_info:
        validate_instruction_policy_document(
            {
                "schema": "odeu.instructions.v1",
                "rules": [
                    _make_rule(
                        rule_id="allow_with_derived_atom",
                        priority=1,
                        kind="allow",
                        effect="allow_action",
                        when={"atom": "derived_output", "args": []},
                        code="ALLOW_DERIVED",
                    )
                ],
            },
            strict=True,
        )
    assert exc_info.value.detail.code == "URM_POLICY_DERIVE_FIREWALL_VIOLATION"


def test_policy_context_requires_utc_z_timestamp() -> None:
    with pytest.raises(ValidationError):
        _context(evaluation_ts="2026-02-12T09:10:00+00:00")
