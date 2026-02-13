from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator
from urm_runtime.policy_tools import (
    diff_policy,
    eval_policy,
    explain_policy,
    explain_policy_from_decision,
    incident_packet,
    main,
    policy_explain_markdown,
    validate_policy,
)


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("Repository root not found")


def _example_eval_path(*parts: str) -> Path:
    return _repo_root() / "examples" / "eval" / Path(*parts)


def _load_policy_explain_schema() -> dict[str, object]:
    schema_path = _repo_root() / "spec" / "policy_explain.schema.json"
    return json.loads(schema_path.read_text(encoding="utf-8"))


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


def test_explain_policy_is_deterministic_with_default_timestamp(tmp_path: Path) -> None:
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
    first = explain_policy(
        policy_path=policy_path,
        context_path=context_path,
        strict=True,
    )
    second = explain_policy(
        policy_path=policy_path,
        context_path=context_path,
        strict=True,
    )
    assert first == second
    assert first["schema"] == "policy_explain@1"
    assert first["valid"] is True
    assert first["evaluation_ts"] == "1970-01-01T00:00:00Z"
    assert first["decision"] == "allow"
    assert first["matched_rule_ids"] == ["default_allow_after_hard_gates"]
    assert first["matched_rules"] == [
        {
            "rule_id": "default_allow_after_hard_gates",
            "rule_version": 1,
            "priority": 1000,
            "kind": "allow",
            "code": "ALLOW_HARD_GATED_ACTION",
            "effect": "allow_action",
            "message": "Allow actions that pass capability/mode/approval hard gates.",
        }
    ]


def test_explain_policy_rejects_conflicting_timestamp_flags(tmp_path: Path) -> None:
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
    report = explain_policy(
        policy_path=policy_path,
        context_path=context_path,
        strict=True,
        evaluation_ts="2026-02-12T00:00:00Z",
        use_now=True,
    )
    assert report["schema"] == "policy_explain@1"
    assert report["valid"] is False
    assert report["issues"][0]["code"] == "URM_POLICY_EXPLAIN_INVALID_INPUT"


def test_explain_policy_adds_input_manifest_and_matches_schema(tmp_path: Path) -> None:
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

    report = explain_policy(
        policy_path=policy_path,
        context_path=context_path,
        strict=True,
    )

    validator = Draft202012Validator(_load_policy_explain_schema())
    errors = sorted(validator.iter_errors(report), key=lambda err: str(err.path))
    assert errors == []
    assert report["input_manifest"]["policy_hash"] == report["policy_hash"]
    assert report["input_manifest"]["input_context_hash"] == report["input_context_hash"]
    assert report["input_manifest"]["evaluation_ts"] == report["evaluation_ts"]
    assert isinstance(report["input_manifest"]["decision_trace_hash"], str)
    assert len(report["input_manifest"]["decision_trace_hash"]) == 64


def test_policy_explain_markdown_is_deterministic_for_identical_payload() -> None:
    explain_payload = {
        "schema": "policy_explain@1",
        "valid": True,
        "deterministic_mode": True,
        "strict": True,
        "evaluation_ts": "2026-02-13T10:00:00Z",
        "policy_hash": "1" * 64,
        "input_context_hash": "2" * 64,
        "decision": "allow",
        "decision_code": "ALLOW_TEST",
        "matched_rule_ids": ["allow_rule"],
        "matched_rules": [],
        "required_approval": False,
        "evaluator_version": "odeu.instruction-evaluator.v1",
        "trace_version": "odeu.instruction-trace.v1",
        "policy_schema_version": "odeu.instructions.schema.v1",
        "policy_ir_version": "odeu.instructions.v1",
        "advisories": [],
        "warrant_invalid": False,
        "evidence_refs": [{"kind": "artifact", "ref": "artifact:artifact-a"}],
        "input_manifest": {
            "policy_hash": "1" * 64,
            "input_context_hash": "2" * 64,
            "evaluation_ts": "2026-02-13T10:00:00Z",
            "evidence_refs": [{"kind": "artifact", "ref": "artifact:artifact-a"}],
            "decision_trace_hash": "3" * 64,
        },
        "issues": [],
    }
    markdown_first = policy_explain_markdown(explain_payload)
    canonical_payload = json.loads(json.dumps(explain_payload, sort_keys=True))
    markdown_second = policy_explain_markdown(canonical_payload)
    assert markdown_first == markdown_second
    assert hashlib.sha256(markdown_first.encode("utf-8")).hexdigest() == hashlib.sha256(
        markdown_second.encode("utf-8")
    ).hexdigest()


def test_explain_from_decision_uses_persisted_decision_trace(tmp_path: Path) -> None:
    decision_path = tmp_path / "eval.json"
    _write_json(
        decision_path,
        {
            "schema": "instruction-policy-eval@1",
            "input_policy": "policy/fixture.json",
            "input_context": "context/fixture.json",
            "strict": True,
            "deterministic_mode": True,
            "valid": True,
            "evaluation_ts": "2026-02-13T10:00:00Z",
            "policy_hash": "a" * 64,
            "input_context_hash": "b" * 64,
            "decision": "deny",
            "decision_code": "DENY_TEST",
            "matched_rule_ids": ["deny_rule"],
            "required_approval": False,
            "evaluator_version": "odeu.instruction-evaluator.v1",
            "trace_version": "odeu.instruction-trace.v1",
            "policy_schema_version": "odeu.instructions.schema.v1",
            "policy_ir_version": "odeu.instructions.v1",
            "evidence_refs": [
                {"kind": "proof", "ref": "proof:z"},
                {"kind": "artifact", "ref": "artifact:a"},
            ],
            "issues": [],
        },
    )

    report = explain_policy_from_decision(decision_path=decision_path)
    assert report["valid"] is True
    assert report["schema"] == "policy_explain@1"
    assert report["input_decision"] == str(decision_path)
    assert report["decision"] == "deny"
    assert report["decision_code"] == "DENY_TEST"
    assert report["matched_rule_ids"] == ["deny_rule"]
    assert report["matched_rules"] == []
    assert report["input_manifest"]["policy_hash"] == "a" * 64
    assert report["input_manifest"]["input_context_hash"] == "b" * 64
    assert report["input_manifest"]["evaluation_ts"] == "2026-02-13T10:00:00Z"
    assert report["evidence_refs"] == [
        {"kind": "artifact", "ref": "artifact:a", "note": None},
        {"kind": "proof", "ref": "proof:z", "note": None},
    ]


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

    explain_out = tmp_path / "explain_report.json"
    assert (
        main(
            [
                "explain",
                "--policy",
                str(policy_path),
                "--context",
                str(context_path),
                "--out",
                str(explain_out),
            ]
        )
        == 0
    )
    explain_payload = json.loads(explain_out.read_text(encoding="utf-8"))
    assert explain_payload["valid"] is True
    assert explain_payload["schema"] == "policy_explain@1"

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


def test_incident_packet_is_deterministic_and_sorted(tmp_path: Path) -> None:
    decision_path = tmp_path / "decision.json"
    _write_json(
        decision_path,
        {
            "schema": "policy_explain@1",
            "valid": True,
            "policy_hash": "a" * 64,
            "input_context_hash": "b" * 64,
            "decision_code": "ALLOW_HARD_GATED_ACTION",
            "matched_rule_ids": ["default_allow_after_hard_gates"],
            "evidence_refs": [
                {"kind": "proof", "ref": "proof:proof-a", "note": "n1"},
                {"kind": "artifact", "ref": "artifact:artifact-z"},
            ],
            "debug_secret": {"api_key": "secret-value"},
        },
    )
    stream_a = tmp_path / "parent.ndjson"
    stream_a.write_text(
        "\n".join(
            [
                json.dumps(
                    {
                        "schema": "urm-events@1",
                        "event": "POLICY_EVAL_START",
                        "stream_id": "copilot:session-a",
                        "seq": 2,
                        "ts": "2026-02-12T10:00:02Z",
                        "source": {
                            "component": "urm_copilot_manager",
                            "version": "0.1.0",
                            "provider": "codex",
                        },
                        "context": {
                            "session_id": "session-a",
                            "run_id": None,
                            "role": "copilot",
                            "endpoint": "urm.tools.call",
                            "ir_hash": None,
                        },
                        "detail": {
                            "policy_hash": "a" * 64,
                            "decision_code": "PENDING",
                            "matched_rule_ids": [],
                        },
                    }
                ),
                json.dumps(
                    {
                        "schema": "urm-events@1",
                        "event": "POLICY_EVAL_PASS",
                        "stream_id": "copilot:session-a",
                        "seq": 7,
                        "ts": "2026-02-12T10:00:07Z",
                        "source": {
                            "component": "urm_copilot_manager",
                            "version": "0.1.0",
                            "provider": "codex",
                        },
                        "context": {
                            "session_id": "session-a",
                            "run_id": None,
                            "role": "copilot",
                            "endpoint": "urm.tools.call",
                            "ir_hash": None,
                        },
                        "detail": {
                            "policy_hash": "a" * 64,
                            "decision_code": "ALLOW_HARD_GATED_ACTION",
                            "matched_rule_ids": ["default_allow_after_hard_gates"],
                        },
                    }
                ),
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    stream_b = tmp_path / "child.ndjson"
    stream_b.write_text(
        json.dumps(
            {
                "schema": "urm-events@1",
                "event": "WORKER_PASS",
                "stream_id": "child:child-a",
                "seq": 3,
                "ts": "2026-02-12T10:01:03Z",
                "source": {
                    "component": "urm_copilot_manager",
                    "version": "0.1.0",
                    "provider": "codex",
                },
                "context": {
                    "session_id": "session-a",
                    "run_id": None,
                    "role": "copilot",
                    "endpoint": "urm.agent.spawn",
                    "ir_hash": None,
                },
                "detail": {"worker_id": "child-a", "status": "completed"},
            }
        )
        + "\n",
        encoding="utf-8",
    )

    first = incident_packet(
        decision_path=decision_path,
        stream_specs=[
            f"child:child-a={stream_b}",
            f"copilot:session-a={stream_a}",
        ],
        artifact_refs=["validator:validator-1"],
    )
    second = incident_packet(
        decision_path=decision_path,
        stream_specs=[
            f"child:child-a={stream_b}",
            f"copilot:session-a={stream_a}",
        ],
        artifact_refs=["validator:validator-1"],
    )

    assert first == second
    assert first["schema"] == "incident_packet@1"
    assert first["valid"] is True
    assert first["streams"] == [
        {"stream_id": "child:child-a", "seq_range": {"start_seq": 3, "end_seq": 3}},
        {"stream_id": "copilot:session-a", "seq_range": {"start_seq": 2, "end_seq": 7}},
    ]
    assert first["artifact_refs"] == [
        {"kind": "artifact", "ref": "artifact:artifact-z"},
        {"kind": "event", "ref": "event:child:child-a#3"},
        {"kind": "event", "ref": "event:copilot:session-a#2"},
        {"kind": "event", "ref": "event:copilot:session-a#7"},
        {"kind": "proof", "ref": "proof:proof-a"},
        {"kind": "validator", "ref": "validator:validator-1"},
    ]
    assert first["redaction_markers"] == [
        {"path": "debug_secret", "replacement": "[REDACTED]"}
    ]


def test_incident_packet_invalid_inputs_surface_error_code(tmp_path: Path) -> None:
    decision_path = tmp_path / "decision.json"
    _write_json(decision_path, {"schema": "unknown", "valid": True})
    stream_path = tmp_path / "stream.ndjson"
    stream_path.write_text("", encoding="utf-8")

    report = incident_packet(
        decision_path=decision_path,
        stream_specs=[f"copilot:session-a={stream_path}"],
    )
    assert report["schema"] == "incident_packet@1"
    assert report["valid"] is False
    assert report["issues"][0]["code"] == "URM_INCIDENT_PACKET_BUILD_FAILED"


def test_policy_cli_incident_supports_out_file(
    capsys: pytest.CaptureFixture[str], tmp_path: Path
) -> None:
    decision_path = tmp_path / "decision.json"
    _write_json(
        decision_path,
        {
            "schema": "policy_explain@1",
            "valid": True,
            "policy_hash": "c" * 64,
            "input_context_hash": "d" * 64,
            "decision_code": "ALLOW_HARD_GATED_ACTION",
            "matched_rule_ids": ["default_allow_after_hard_gates"],
            "evidence_refs": [],
        },
    )
    stream_path = tmp_path / "stream.ndjson"
    stream_path.write_text(
        json.dumps(
            {
                "schema": "urm-events@1",
                "event": "POLICY_EVAL_PASS",
                "stream_id": "copilot:session-b",
                "seq": 1,
                "ts": "2026-02-12T10:00:01Z",
                "source": {
                    "component": "urm_copilot_manager",
                    "version": "0.1.0",
                    "provider": "codex",
                },
                "context": {
                    "session_id": "session-b",
                    "run_id": None,
                    "role": "copilot",
                    "endpoint": "urm.tools.call",
                    "ir_hash": None,
                },
                "detail": {
                    "policy_hash": "c" * 64,
                    "decision_code": "ALLOW_HARD_GATED_ACTION",
                    "matched_rule_ids": ["default_allow_after_hard_gates"],
                },
            }
        )
        + "\n",
        encoding="utf-8",
    )
    out_path = tmp_path / "incident.json"
    assert (
        main(
            [
                "incident",
                "--decision",
                str(decision_path),
                "--stream",
                f"copilot:session-b={stream_path}",
                "--out",
                str(out_path),
            ]
        )
        == 0
    )
    payload = json.loads(out_path.read_text(encoding="utf-8"))
    assert payload["schema"] == "incident_packet@1"
    assert payload["valid"] is True
    assert capsys.readouterr().out == ""


def test_policy_cli_explain_from_decision_supports_markdown_output(tmp_path: Path) -> None:
    decision_path = tmp_path / "decision.json"
    _write_json(
        decision_path,
        {
            "schema": "instruction-policy-eval@1",
            "input_policy": "policy/fixture.json",
            "input_context": "context/fixture.json",
            "strict": True,
            "deterministic_mode": True,
            "valid": True,
            "evaluation_ts": "2026-02-13T10:00:00Z",
            "policy_hash": "c" * 64,
            "input_context_hash": "d" * 64,
            "decision": "allow",
            "decision_code": "ALLOW_TEST",
            "matched_rule_ids": ["allow_rule"],
            "required_approval": False,
            "evaluator_version": "odeu.instruction-evaluator.v1",
            "trace_version": "odeu.instruction-trace.v1",
            "policy_schema_version": "odeu.instructions.schema.v1",
            "policy_ir_version": "odeu.instructions.v1",
            "issues": [],
        },
    )
    out_json = tmp_path / "explain-from-decision.json"
    out_md = tmp_path / "explain-from-decision.md"
    exit_code = main(
        [
            "explain-from-decision",
            "--decision",
            str(decision_path),
            "--out",
            str(out_json),
            "--out-md",
            str(out_md),
        ]
    )
    assert exit_code == 0
    payload = json.loads(out_json.read_text(encoding="utf-8"))
    assert payload["schema"] == "policy_explain@1"
    assert payload["valid"] is True
    markdown = out_md.read_text(encoding="utf-8")
    assert "Policy Explain Report" in markdown
    assert "`ALLOW_TEST`" in markdown
