from __future__ import annotations

import json
from pathlib import Path

import pytest
from urm_runtime.policy_tools import diff_policy, eval_policy, main, validate_policy


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("Repository root not found")


def _example_eval_path(*parts: str) -> Path:
    return _repo_root() / "examples" / "eval" / Path(*parts)


def _write_json(path: Path, payload: dict[str, object]) -> None:
    path.write_text(json.dumps(payload), encoding="utf-8")


def test_validate_policy_passes_for_repo_policy() -> None:
    policy_path = _repo_root() / "policy" / "odeu.instructions.v1.json"
    report = validate_policy(policy_path, strict=True)
    assert report["schema"] == "instruction-policy-validate@1"
    assert report["valid"] is True
    assert isinstance(report["policy_hash"], str) and len(report["policy_hash"]) == 64
    assert report["rule_count"] > 0
    assert report["issues"] == []


def test_validate_policy_strict_rejects_derive_firewall_violation(tmp_path: Path) -> None:
    policy_path = tmp_path / "policy.derive-firewall.json"
    policy_path.write_text(
        json.dumps(
            {
                "schema": "odeu.instructions.v1",
                "rules": [
                    {
                        "rule_id": "deny_with_derived_atom",
                        "rule_version": 1,
                        "priority": 1,
                        "kind": "deny",
                        "when": {"atom": "derived.some_fact", "args": []},
                        "then": {"effect": "deny_action", "params": {}},
                        "message": "deny for test",
                        "code": "DENY_DERIVED_TEST",
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    strict_report = validate_policy(policy_path, strict=True)
    assert strict_report["valid"] is False
    assert strict_report["issues"][0]["code"] == "URM_POLICY_DERIVE_FIREWALL_VIOLATION"

    lax_report = validate_policy(policy_path, strict=False)
    assert lax_report["valid"] is False
    assert lax_report["issues"][0]["code"] == "URM_POLICY_INVALID_SCHEMA"


def test_policy_cli_validate_returns_expected_exit_codes(
    capsys: pytest.CaptureFixture[str], tmp_path: Path
) -> None:
    valid_policy = _repo_root() / "policy" / "odeu.instructions.v1.json"
    assert main(["validate", "--in", str(valid_policy), "--strict"]) == 0
    out = capsys.readouterr().out.strip()
    out_payload = json.loads(out)
    assert out_payload["valid"] is True

    invalid_policy = tmp_path / "policy.invalid.json"
    invalid_policy.write_text(
        json.dumps({"schema": "odeu.instructions.v1", "rules": [{"not": "a rule"}]}),
        encoding="utf-8",
    )
    assert main(["validate", "--in", str(invalid_policy), "--strict"]) == 1
    out = capsys.readouterr().out.strip()
    out_payload = json.loads(out)
    assert out_payload["valid"] is False
    assert out_payload["issues"][0]["code"] == "URM_POLICY_INVALID_SCHEMA"


def test_eval_policy_is_deterministic_with_default_timestamp(tmp_path: Path) -> None:
    policy_path = _repo_root() / "policy" / "odeu.instructions.v1.json"
    context_path = tmp_path / "context.json"
    _write_json(
        context_path,
        {
            "role": "copilot",
            "mode": "read_only",
            "action_kind": "adeu.get_app_state",
            "action_hash": "test_hash",
        },
    )
    first = eval_policy(
        policy_path=policy_path,
        context_path=context_path,
        strict=True,
    )
    second = eval_policy(
        policy_path=policy_path,
        context_path=context_path,
        strict=True,
    )
    assert first == second
    assert first["schema"] == "instruction-policy-eval@1"
    assert first["valid"] is True
    assert first["evaluation_ts"] == "1970-01-01T00:00:00Z"
    assert first["decision"] == "allow"


def test_eval_policy_supports_examples_fixture_context() -> None:
    policy_path = _repo_root() / "policy" / "odeu.instructions.v1.json"
    report = eval_policy(
        policy_path=policy_path,
        context_path=_example_eval_path("policy_eval", "basic_context.json"),
        strict=True,
    )
    assert report["valid"] is True
    assert report["schema"] == "instruction-policy-eval@1"


def test_eval_policy_rejects_conflicting_timestamp_flags(tmp_path: Path) -> None:
    policy_path = _repo_root() / "policy" / "odeu.instructions.v1.json"
    context_path = tmp_path / "context.json"
    _write_json(
        context_path,
        {
            "role": "copilot",
            "mode": "read_only",
            "action_kind": "adeu.get_app_state",
            "action_hash": "test_hash",
        },
    )
    report = eval_policy(
        policy_path=policy_path,
        context_path=context_path,
        strict=True,
        evaluation_ts="2026-02-12T00:00:00Z",
        use_now=True,
    )
    assert report["schema"] == "instruction-policy-eval@1"
    assert report["valid"] is False
    assert report["issues"][0]["code"] == "URM_POLICY_INVALID_SCHEMA"


def test_diff_policy_ignores_message_and_rule_order_changes(tmp_path: Path) -> None:
    old_path = tmp_path / "old.policy.json"
    new_path = tmp_path / "new.policy.json"
    _write_json(
        old_path,
        {
            "schema": "odeu.instructions.v1",
            "rules": [
                {
                    "rule_id": "allow_read",
                    "rule_version": 1,
                    "priority": 20,
                    "kind": "allow",
                    "when": {"atom": "mode_is", "args": ["read_only"]},
                    "then": {"effect": "allow_action", "params": {}},
                    "message": "original message",
                    "code": "ALLOW_READ",
                },
                {
                    "rule_id": "require_write_approval",
                    "rule_version": 1,
                    "priority": 10,
                    "kind": "require",
                    "when": {"atom": "mode_is", "args": ["writes_allowed"]},
                    "then": {"effect": "require_approval", "params": {}},
                    "message": "require approval",
                    "code": "REQUIRE_WRITE_APPROVAL",
                },
            ],
        },
    )
    _write_json(
        new_path,
        {
            "schema": "odeu.instructions.v1",
            "rules": [
                {
                    "rule_id": "require_write_approval",
                    "rule_version": 1,
                    "priority": 10,
                    "kind": "require",
                    "when": {"atom": "mode_is", "args": ["writes_allowed"]},
                    "then": {"effect": "require_approval", "params": {}},
                    "message": "updated wording only",
                    "code": "REQUIRE_WRITE_APPROVAL",
                },
                {
                    "rule_id": "allow_read",
                    "rule_version": 1,
                    "priority": 20,
                    "kind": "allow",
                    "when": {"atom": "mode_is", "args": ["read_only"]},
                    "then": {"effect": "allow_action", "params": {}},
                    "message": "updated wording only",
                    "code": "ALLOW_READ",
                },
            ],
        },
    )
    report = diff_policy(
        old_policy_path=old_path,
        new_policy_path=new_path,
        strict=True,
    )
    assert report["schema"] == "instruction-policy-diff@1"
    assert report["valid"] is True
    assert report["semantic_equal"] is True
    assert report["added_rules"] == []
    assert report["removed_rules"] == []
    assert report["modified_rules"] == []


def test_diff_policy_reports_semantic_changes_with_field_deltas(tmp_path: Path) -> None:
    old_path = tmp_path / "old.policy.json"
    new_path = tmp_path / "new.policy.json"
    _write_json(
        old_path,
        {
            "schema": "odeu.instructions.v1",
            "rules": [
                {
                    "rule_id": "allow_read",
                    "rule_version": 1,
                    "priority": 20,
                    "kind": "allow",
                    "when": {"atom": "mode_is", "args": ["read_only"]},
                    "then": {"effect": "allow_action", "params": {}},
                    "message": "m",
                    "code": "ALLOW_READ",
                }
            ],
        },
    )
    _write_json(
        new_path,
        {
            "schema": "odeu.instructions.v1",
            "rules": [
                {
                    "rule_id": "allow_read",
                    "rule_version": 1,
                    "priority": 5,
                    "kind": "allow",
                    "when": {"atom": "mode_is", "args": ["read_only"]},
                    "then": {"effect": "allow_action", "params": {}},
                    "message": "m2",
                    "code": "ALLOW_READ_V2",
                }
            ],
        },
    )
    report = diff_policy(
        old_policy_path=old_path,
        new_policy_path=new_path,
        strict=True,
    )
    assert report["valid"] is True
    assert report["semantic_equal"] is False
    assert report["added_rules"] == []
    assert report["removed_rules"] == []
    assert report["modified_rules"] == [
        {
            "rule_id": "allow_read",
            "changed_fields": ["code", "priority"],
            "changes": {
                "code": {"old": "ALLOW_READ", "new": "ALLOW_READ_V2"},
                "priority": {"old": 20, "new": 5},
            },
        }
    ]


def test_policy_cli_eval_and_diff_support_out_files(
    capsys: pytest.CaptureFixture[str], tmp_path: Path
) -> None:
    policy_path = _repo_root() / "policy" / "odeu.instructions.v1.json"
    context_path = tmp_path / "context.json"
    _write_json(
        context_path,
        {
            "role": "copilot",
            "mode": "read_only",
            "action_kind": "adeu.get_app_state",
            "action_hash": "test_hash",
        },
    )
    eval_out = tmp_path / "eval_report.json"
    assert (
        main(
            [
                "eval",
                "--policy",
                str(policy_path),
                "--context",
                str(context_path),
                "--out",
                str(eval_out),
            ]
        )
        == 0
    )
    eval_payload = json.loads(eval_out.read_text(encoding="utf-8"))
    assert eval_payload["valid"] is True
    assert eval_payload["schema"] == "instruction-policy-eval@1"

    old_policy = tmp_path / "old.policy.json"
    new_policy = tmp_path / "new.policy.json"
    _write_json(
        old_policy,
        {
            "schema": "odeu.instructions.v1",
            "rules": [],
        },
    )
    _write_json(
        new_policy,
        {
            "schema": "odeu.instructions.v1",
            "rules": [
                {
                    "rule_id": "allow_read",
                    "rule_version": 1,
                    "priority": 1,
                    "kind": "allow",
                    "when": {"atom": "mode_is", "args": ["read_only"]},
                    "then": {"effect": "allow_action", "params": {}},
                    "message": "m",
                    "code": "ALLOW_READ",
                }
            ],
        },
    )
    diff_out = tmp_path / "diff_report.json"
    assert (
        main(
            [
                "diff",
                "--old",
                str(old_policy),
                "--new",
                str(new_policy),
                "--out",
                str(diff_out),
            ]
        )
        == 0
    )
    diff_payload = json.loads(diff_out.read_text(encoding="utf-8"))
    assert diff_payload["schema"] == "instruction-policy-diff@1"
    assert diff_payload["added_rules"] == ["allow_read"]
    # Ensure no stdout fallback when --out is used.
    assert capsys.readouterr().out == ""


def test_policy_diff_fixtures_match_expected_semantic_behavior() -> None:
    report_message_only = diff_policy(
        old_policy_path=_example_eval_path("policy_diff", "message_only_old.json"),
        new_policy_path=_example_eval_path("policy_diff", "message_only_new.json"),
        strict=True,
    )
    assert report_message_only["valid"] is True
    assert report_message_only["semantic_equal"] is True
    assert report_message_only["modified_rules"] == []

    report_semantic_change = diff_policy(
        old_policy_path=_example_eval_path("policy_diff", "semantic_change_old.json"),
        new_policy_path=_example_eval_path("policy_diff", "semantic_change_new.json"),
        strict=True,
    )
    assert report_semantic_change["valid"] is True
    assert report_semantic_change["semantic_equal"] is False
    assert report_semantic_change["modified_rules"] != []
