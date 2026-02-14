from __future__ import annotations

import pytest
from pydantic import ValidationError
from urm_runtime.errors import URMError
from urm_runtime.instruction_policy import (
    PolicyContext,
    compute_policy_hash,
    evaluate_instruction_policy,
    load_instruction_policy,
    load_instruction_policy_schema,
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


def _lemma_pack(
    *,
    pack_id: str,
    family: str,
    local_id: str,
    action_kind: str,
    pack_version: int = 1,
    local_priority: int = 0,
) -> dict[str, object]:
    return {
        "pack_id": pack_id,
        "pack_version": pack_version,
        "family": family,
        "items": [
            {
                "local_id": local_id,
                "action_kind": action_kind,
                "local_priority": local_priority,
            }
        ],
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


def test_lemma_packs_compile_deterministically_and_use_frozen_identity_conventions() -> None:
    base_doc = {
        "schema": "odeu.instructions.v1",
        "rules": [
            _make_rule(
                rule_id="allow_default",
                priority=900,
                kind="allow",
                effect="allow_action",
                when={"atom": "mode_is", "args": ["strict"]},
                code="ALLOW_DEFAULT",
            )
        ],
        "lemma_packs": [
            _lemma_pack(
                pack_id="guardrails",
                family="deny_action_kind",
                local_id="block_delete",
                action_kind="adeu.delete_state",
                local_priority=2,
            ),
            _lemma_pack(
                pack_id="approvals",
                family="require_approval_action_kind",
                local_id="patch_needs_approval",
                action_kind="adeu.apply_patch",
                local_priority=1,
            ),
        ],
    }
    reordered_doc = {
        "schema": "odeu.instructions.v1",
        "rules": list(base_doc["rules"]),
        "lemma_packs": list(reversed(list(base_doc["lemma_packs"]))),
    }

    policy_one = validate_instruction_policy_document(base_doc, strict=True)
    policy_two = validate_instruction_policy_document(reordered_doc, strict=True)
    assert compute_policy_hash(policy_one) == compute_policy_hash(policy_two)
    assert any(
        rule.rule_id == "lemma:guardrails@1:deny_action_kind:block_delete"
        and rule.code == "LEMMA_GUARDRAILS_DENY_ACTION_KIND_BLOCK_DELETE_DENY_ACTION"
        and rule.priority == 102
        for rule in policy_one.rules
    )
    assert any(
        rule.rule_id == "lemma:approvals@1:require_approval_action_kind:patch_needs_approval"
        and rule.code
        == "LEMMA_APPROVALS_REQUIRE_APPROVAL_ACTION_KIND_PATCH_NEEDS_APPROVAL_REQUIRE_APPROVAL"
        and rule.priority == 201
        for rule in policy_one.rules
    )


def test_validate_instruction_policy_document_rejects_lemma_family_count_mismatch() -> None:
    with pytest.raises(URMError) as exc_info:
        validate_instruction_policy_document(
            {
                "schema": "odeu.instructions.v1",
                "rules": [],
                "lemma_packs": [
                    _lemma_pack(
                        pack_id="guardrails",
                        family="deny_action_kind",
                        local_id="block_delete",
                        action_kind="adeu.delete_state",
                    )
                ],
            },
            strict=True,
        )
    assert exc_info.value.detail.code == "URM_POLICY_INVALID_SCHEMA"
    assert "lemma_packs must include exactly one pack" in exc_info.value.detail.message


def test_validate_instruction_policy_document_rejects_duplicate_compiled_rule_ids() -> None:
    with pytest.raises(URMError) as exc_info:
        validate_instruction_policy_document(
            {
                "schema": "odeu.instructions.v1",
                "rules": [
                    _make_rule(
                        rule_id="lemma:guardrails@1:deny_action_kind:block_delete",
                        priority=100,
                        kind="deny",
                        effect="deny_action",
                        when={"atom": "action_kind_is", "args": ["adeu.delete_state"]},
                        code="DENY_DUPLICATE",
                    )
                ],
                "lemma_packs": [
                    _lemma_pack(
                        pack_id="guardrails",
                        family="deny_action_kind",
                        local_id="block_delete",
                        action_kind="adeu.delete_state",
                    ),
                    _lemma_pack(
                        pack_id="approvals",
                        family="require_approval_action_kind",
                        local_id="patch_needs_approval",
                        action_kind="adeu.apply_patch",
                    ),
                ],
            },
            strict=True,
        )
    assert exc_info.value.detail.code == "URM_POLICY_INVALID_SCHEMA"
    assert "duplicate rule_id" in exc_info.value.detail.message


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


def test_derive_firewall_only_checks_rule_when_expression() -> None:
    validate_instruction_policy_document(
        {
            "schema": "odeu.instructions.v1",
            "rules": [
                {
                    **_make_rule(
                        rule_id="derive_meta_payload_ok",
                        priority=1,
                        kind="derive",
                        effect="emit_advisory",
                        when={"atom": "session_active", "args": []},
                        code="META_OK",
                    ),
                    "then": {
                        "effect": "emit_advisory",
                        "params": {"atom": "derived_output_payload"},
                    },
                }
            ],
        },
        strict=True,
    )


def test_load_instruction_policy_schema_falls_back_to_packaged(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.delenv("URM_INSTRUCTION_POLICY_SCHEMA_PATH", raising=False)
    monkeypatch.setattr(
        "urm_runtime.instruction_policy._repo_relative_path",
        lambda *_parts: None,
    )
    schema = load_instruction_policy_schema()
    assert schema["$id"] == "https://lexlattice.local/spec/instruction_policy.schema.json"


def test_load_instruction_policy_falls_back_to_packaged(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delenv("URM_INSTRUCTION_POLICY_SCHEMA_PATH", raising=False)
    monkeypatch.delenv("URM_INSTRUCTION_POLICY_PATH", raising=False)
    monkeypatch.setattr(
        "urm_runtime.instruction_policy._repo_relative_path",
        lambda *_parts: None,
    )
    policy = load_instruction_policy()
    assert policy.schema_id == "odeu.instructions.v1"
    assert len(policy.rules) == 1
    assert policy.rules[0].rule_id == "default_allow_after_hard_gates"


def test_policy_context_requires_utc_z_timestamp() -> None:
    with pytest.raises(ValidationError):
        _context(evaluation_ts="2026-02-12T09:10:00+00:00")
