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


def _load_incident_packet_schema() -> dict[str, object]:
    schema_path = _repo_root() / "spec" / "incident_packet.schema.json"
    return json.loads(schema_path.read_text(encoding="utf-8"))


def _load_incident_redaction_allowlist_schema() -> dict[str, object]:
    schema_path = _repo_root() / "spec" / "policy_incident_redaction_allowlist.v1.schema.json"
    return json.loads(schema_path.read_text(encoding="utf-8"))


def _load_policy_registry_schema() -> dict[str, object]:
    schema_path = _repo_root() / "spec" / "policy_registry.schema.json"
    return json.loads(schema_path.read_text(encoding="utf-8"))


def _load_policy_activation_schema() -> dict[str, object]:
    schema_path = _repo_root() / "spec" / "policy_activation_log.schema.json"
    return json.loads(schema_path.read_text(encoding="utf-8"))


def _load_policy_lineage_schema() -> dict[str, object]:
    schema_path = _repo_root() / "spec" / "policy_lineage.schema.json"
    return json.loads(schema_path.read_text(encoding="utf-8"))


def _read_ndjson(path: Path) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        payload = json.loads(line)
        if isinstance(payload, dict):
            rows.append(payload)
    return rows


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
            "advisories": [{"api_key": "secret-value"}],
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
        {"path": "advisories.0.api_key", "replacement": "[REDACTED]"}
    ]
    incident_schema = _load_incident_packet_schema()
    schema_errors = sorted(
        Draft202012Validator(incident_schema).iter_errors(first),
        key=lambda err: str(err.path),
    )
    assert schema_errors == []


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


def test_incident_packet_unknown_fields_fail_closed(tmp_path: Path) -> None:
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
            "evidence_refs": [],
            "debug_secret": {"api_key": "secret-value"},
        },
    )
    stream_path = tmp_path / "stream.ndjson"
    stream_path.write_text(
        json.dumps(
            {
                "schema": "urm-events@1",
                "event": "POLICY_EVAL_PASS",
                "stream_id": "copilot:session-a",
                "seq": 1,
                "ts": "2026-02-12T10:00:01Z",
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
        )
        + "\n",
        encoding="utf-8",
    )
    payload = incident_packet(
        decision_path=decision_path,
        stream_specs=[f"copilot:session-a={stream_path}"],
    )
    assert payload["valid"] is False
    assert payload["issues"][0]["code"] == "URM_INCIDENT_PACKET_BUILD_FAILED"
    assert payload["issues"][0]["context"]["unknown_fields"] == ["debug_secret"]


def test_incident_packet_invalid_artifact_ref_uses_invalid_ref_code(tmp_path: Path) -> None:
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
            "evidence_refs": [],
        },
    )
    stream_path = tmp_path / "stream.ndjson"
    stream_path.write_text(
        json.dumps(
            {
                "schema": "urm-events@1",
                "event": "POLICY_EVAL_PASS",
                "stream_id": "copilot:session-a",
                "seq": 1,
                "ts": "2026-02-12T10:00:01Z",
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
        )
        + "\n",
        encoding="utf-8",
    )
    payload = incident_packet(
        decision_path=decision_path,
        stream_specs=[f"copilot:session-a={stream_path}"],
        artifact_refs=["not-a-canonical-ref"],
    )
    assert payload["valid"] is False
    assert payload["issues"][0]["code"] == "URM_INCIDENT_PACKET_INVALID_REF"


def test_incident_packet_schema_and_allowlist_files_match_spec() -> None:
    incident_schema = _load_incident_packet_schema()
    allowlist_schema = _load_incident_redaction_allowlist_schema()

    incident_fixture_path = (
        _repo_root() / "examples" / "eval" / "stop_gate" / "incident_packet_case_a_1.json"
    )
    incident_payload = json.loads(
        incident_fixture_path.read_text(encoding="utf-8")
    )
    allowlist_payload = json.loads(
        (_repo_root() / "policy" / "incident_redaction_allowlist.v1.json").read_text(
            encoding="utf-8"
        )
    )

    incident_errors = sorted(
        Draft202012Validator(incident_schema).iter_errors(incident_payload),
        key=lambda err: str(err.path),
    )
    allowlist_errors = sorted(
        Draft202012Validator(allowlist_schema).iter_errors(allowlist_payload),
        key=lambda err: str(err.path),
    )
    assert incident_errors == []
    assert allowlist_errors == []


def test_incident_redaction_allowlist_packaged_copy_matches_repo_source() -> None:
    repo_payload = json.loads(
        (_repo_root() / "policy" / "incident_redaction_allowlist.v1.json").read_text(
            encoding="utf-8"
        )
    )
    packaged_payload = json.loads(
        (
            _repo_root()
            / "packages"
            / "urm_runtime"
            / "src"
            / "urm_runtime"
            / "policy"
            / "incident_redaction_allowlist.v1.json"
        ).read_text(encoding="utf-8")
    )
    assert repo_payload == packaged_payload


def test_incident_packet_secret_like_output_fails_closed(tmp_path: Path) -> None:
    decision_path = tmp_path / "decision.json"
    _write_json(
        decision_path,
        {
            "schema": "policy_explain@1",
            "valid": True,
            "policy_hash": "a" * 64,
            "input_context_hash": "b" * 64,
            "decision_code": "ALLOW_HARD_GATED_ACTION",
            "matched_rule_ids": ["Bearer sk_live_example_secret"],
            "evidence_refs": [],
        },
    )
    stream_path = tmp_path / "stream.ndjson"
    stream_path.write_text(
        json.dumps(
            {
                "schema": "urm-events@1",
                "event": "POLICY_EVAL_PASS",
                "stream_id": "copilot:session-a",
                "seq": 1,
                "ts": "2026-02-12T10:00:01Z",
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
        )
        + "\n",
        encoding="utf-8",
    )
    payload = incident_packet(
        decision_path=decision_path,
        stream_specs=[f"copilot:session-a={stream_path}"],
    )
    assert payload["valid"] is False
    assert payload["issues"][0]["code"] == "URM_INCIDENT_PACKET_BUILD_FAILED"


def test_incident_packet_secret_key_detection_uses_allowlist_tokens(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    custom_allowlist = tmp_path / "incident_redaction_allowlist.v1.json"
    _write_json(
        custom_allowlist,
        {
            "schema": "policy.incident_redaction_allowlist.v1",
            "redaction_eligible_top_level_fields": [
                "schema",
                "valid",
                "policy_hash",
                "input_context_hash",
                "decision_code",
                "matched_rule_ids",
                "evidence_refs",
            ],
            "sensitive_key_tokens": ["credential"],
        },
    )
    monkeypatch.setenv("URM_INCIDENT_REDACTION_ALLOWLIST_PATH", str(custom_allowlist))

    decision_path = tmp_path / "decision.json"
    _write_json(
        decision_path,
        {
            "schema": "policy_explain@1",
            "valid": True,
            "policy_hash": "a" * 64,
            "input_context_hash": "b" * 64,
            "decision_code": "ALLOW_HARD_GATED_ACTION",
            "matched_rule_ids": ["credential=my-noncanonical-secret"],
            "evidence_refs": [],
        },
    )
    stream_path = tmp_path / "stream.ndjson"
    stream_path.write_text(
        json.dumps(
            {
                "schema": "urm-events@1",
                "event": "POLICY_EVAL_PASS",
                "stream_id": "copilot:session-a",
                "seq": 1,
                "ts": "2026-02-12T10:00:01Z",
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
        )
        + "\n",
        encoding="utf-8",
    )
    payload = incident_packet(
        decision_path=decision_path,
        stream_specs=[f"copilot:session-a={stream_path}"],
    )
    assert payload["valid"] is False
    assert payload["issues"][0]["code"] == "URM_INCIDENT_PACKET_BUILD_FAILED"


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


def test_policy_cli_materialize_rollout_rollback_and_active(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))

    base_policy = _repo_root() / "policy" / "odeu.instructions.v1.json"
    alt_policy = tmp_path / "odeu.instructions.alt.v1.json"
    payload = json.loads(base_policy.read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    rules = payload.get("rules")
    assert isinstance(rules, list) and rules
    first_rule = rules[0]
    assert isinstance(first_rule, dict)
    first_rule["code"] = "ALLOW_HARD_GATED_ACTION_ALT"
    alt_policy.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")

    base_hash = str(validate_policy(base_policy, strict=True)["policy_hash"])
    alt_hash = str(validate_policy(alt_policy, strict=True)["policy_hash"])
    assert base_hash != alt_hash

    profile_registry = tmp_path / "profiles.v1.json"
    _write_json(
        profile_registry,
        {
            "schema": "policy.profiles.v1",
            "profiles": [
                {
                    "profile_id": "default",
                    "profile_version": "profile.v1",
                    "default_policy_hash": base_hash,
                    "allowed_policy_hashes": [base_hash, alt_hash],
                    "policy_ref": str(base_policy),
                }
            ],
        },
    )
    monkeypatch.setenv("URM_POLICY_PROFILES_PATH", str(profile_registry))

    materialize_base_out = tmp_path / "materialize.base.json"
    materialize_alt_out = tmp_path / "materialize.alt.json"
    assert (
        main(
            [
                "materialize",
                "--policy",
                str(base_policy),
                "--materialize-ts",
                "2026-02-13T10:00:00Z",
                "--out",
                str(materialize_base_out),
            ]
        )
        == 0
    )
    assert (
        main(
            [
                "materialize",
                "--policy",
                str(alt_policy),
                "--materialize-ts",
                "2026-02-13T10:05:00Z",
                "--out",
                str(materialize_alt_out),
            ]
        )
        == 0
    )

    base_materialized = json.loads(materialize_base_out.read_text(encoding="utf-8"))
    materialized_subset = {
        "schema": "policy_registry@1",
        "policy_hash": base_materialized["policy_hash"],
        "schema_id": base_materialized["schema_id"],
        "policy_schema_version": base_materialized["policy_schema_version"],
        "policy_ir_version": base_materialized["policy_ir_version"],
        "semantic_policy_json": base_materialized["semantic_policy_json"],
        "source_policy_ref": base_materialized["source_policy_ref"],
        "materialized_at": base_materialized["materialized_at"],
    }
    registry_validator = Draft202012Validator(_load_policy_registry_schema())
    registry_errors = sorted(
        registry_validator.iter_errors(materialized_subset), key=lambda err: str(err.path)
    )
    assert registry_errors == []

    rollout_base_out = tmp_path / "rollout.base.json"
    rollout_alt_out = tmp_path / "rollout.alt.json"
    rollback_base_out = tmp_path / "rollback.base.json"
    active_out = tmp_path / "active.json"
    active_after_rollback_out = tmp_path / "active.after.rollback.json"
    assert (
        main(
            [
                "rollout",
                "--profile-id",
                "default",
                "--target-policy-hash",
                base_hash,
                "--client-request-id",
                "rollout-base-1",
                "--activation-ts",
                "2026-02-13T10:10:00Z",
                "--out",
                str(rollout_base_out),
            ]
        )
        == 0
    )
    assert (
        main(
            [
                "rollout",
                "--profile-id",
                "default",
                "--target-policy-hash",
                alt_hash,
                "--client-request-id",
                "rollout-alt-1",
                "--activation-ts",
                "2026-02-13T10:11:00Z",
                "--out",
                str(rollout_alt_out),
            ]
        )
        == 0
    )
    assert (
        main(
            [
                "active",
                "--profile-id",
                "default",
                "--out",
                str(active_out),
            ]
        )
        == 0
    )
    assert (
        main(
            [
                "rollback",
                "--profile-id",
                "default",
                "--target-policy-hash",
                base_hash,
                "--client-request-id",
                "rollback-base-1",
                "--activation-ts",
                "2026-02-13T10:12:00Z",
                "--out",
                str(rollback_base_out),
            ]
        )
        == 0
    )
    assert (
        main(
            [
                "active",
                "--profile-id",
                "default",
                "--out",
                str(active_after_rollback_out),
            ]
        )
        == 0
    )

    rollout_payload = json.loads(rollout_alt_out.read_text(encoding="utf-8"))
    activation_subset = {
        "schema": "policy_activation_log@1",
        "activation_seq": rollout_payload["activation_seq"],
        "client_request_id": rollout_payload["client_request_id"],
        "request_payload_hash": rollout_payload["request_payload_hash"],
        "profile_id": rollout_payload["profile_id"],
        "action": rollout_payload["action"],
        "target_policy_hash": rollout_payload["target_policy_hash"],
        "prev_policy_hash": rollout_payload["prev_policy_hash"],
        "activation_ts": rollout_payload["activation_ts"],
    }
    activation_validator = Draft202012Validator(_load_policy_activation_schema())
    activation_errors = sorted(
        activation_validator.iter_errors(activation_subset), key=lambda err: str(err.path)
    )
    assert activation_errors == []
    lineage_subset = dict(rollout_payload["policy_lineage"])
    lineage_validator = Draft202012Validator(_load_policy_lineage_schema())
    lineage_errors = sorted(
        lineage_validator.iter_errors(lineage_subset), key=lambda err: str(err.path)
    )
    assert lineage_errors == []
    assert (
        lineage_subset["activation_ref"]
        == f"event:urm_policy:default#{rollout_payload['activation_seq']}"
    )

    active_payload = json.loads(active_out.read_text(encoding="utf-8"))
    assert active_payload["schema"] == "policy_active@1"
    assert active_payload["valid"] is True
    assert active_payload["policy_hash"] == alt_hash
    assert active_payload["source"] == "activation_log"

    active_after_rollback_payload = json.loads(
        active_after_rollback_out.read_text(encoding="utf-8")
    )
    assert active_after_rollback_payload["schema"] == "policy_active@1"
    assert active_after_rollback_payload["valid"] is True
    assert active_after_rollback_payload["policy_hash"] == base_hash


def test_policy_cli_materialize_is_stable_for_reordered_lemma_packs(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))

    policy_one = tmp_path / "policy.lemma.one.json"
    policy_two = tmp_path / "policy.lemma.two.json"
    base_rules = [
        {
            "rule_id": "allow_default",
            "rule_version": 1,
            "priority": 900,
            "kind": "allow",
            "when": {"atom": "mode_is", "args": ["strict"]},
            "then": {"effect": "allow_action", "params": {}},
            "message": "allow default",
            "code": "ALLOW_DEFAULT",
        }
    ]
    deny_pack = {
        "pack_id": "guardrails",
        "pack_version": 1,
        "family": "deny_action_kind",
        "items": [
            {"local_id": "block_delete", "action_kind": "adeu.delete_state", "local_priority": 2}
        ],
    }
    require_pack = {
        "pack_id": "approvals",
        "pack_version": 1,
        "family": "require_approval_action_kind",
        "items": [
            {
                "local_id": "patch_needs_approval",
                "action_kind": "adeu.apply_patch",
                "local_priority": 1,
            }
        ],
    }
    _write_json(
        policy_one,
        {
            "schema": "odeu.instructions.v1",
            "rules": base_rules,
            "lemma_packs": [deny_pack, require_pack],
        },
    )
    _write_json(
        policy_two,
        {
            "schema": "odeu.instructions.v1",
            "rules": base_rules,
            "lemma_packs": [require_pack, deny_pack],
        },
    )

    out_one = tmp_path / "materialize.one.json"
    out_two = tmp_path / "materialize.two.json"
    assert (
        main(
            [
                "materialize",
                "--policy",
                str(policy_one),
                "--materialize-ts",
                "2026-02-15T10:00:00Z",
                "--out",
                str(out_one),
            ]
        )
        == 0
    )
    first_payload = json.loads(out_one.read_text(encoding="utf-8"))
    assert (
        main(
            [
                "materialize",
                "--policy",
                str(policy_two),
                "--claimed-policy-hash",
                str(first_payload["policy_hash"]),
                "--materialize-ts",
                "2026-02-15T10:01:00Z",
                "--out",
                str(out_two),
            ]
        )
        == 0
    )
    second_payload = json.loads(out_two.read_text(encoding="utf-8"))
    assert first_payload["policy_hash"] == second_payload["policy_hash"]
    assert first_payload["semantic_policy_json"] == second_payload["semantic_policy_json"]
    assert second_payload["source_policy_ref"] == str(policy_two)


def test_policy_cli_rollout_idempotency_conflict(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("ADEU_API_DB_PATH", str(tmp_path / "adeu.sqlite3"))

    base_policy = _repo_root() / "policy" / "odeu.instructions.v1.json"
    alt_policy = tmp_path / "odeu.instructions.alt.v1.json"
    payload = json.loads(base_policy.read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    rules = payload.get("rules")
    assert isinstance(rules, list) and rules
    first_rule = rules[0]
    assert isinstance(first_rule, dict)
    first_rule["code"] = "ALLOW_HARD_GATED_ACTION_ALT_IDEM"
    alt_policy.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")

    base_hash = str(validate_policy(base_policy, strict=True)["policy_hash"])
    alt_hash = str(validate_policy(alt_policy, strict=True)["policy_hash"])

    profile_registry = tmp_path / "profiles.v1.json"
    _write_json(
        profile_registry,
        {
            "schema": "policy.profiles.v1",
            "profiles": [
                {
                    "profile_id": "default",
                    "profile_version": "profile.v1",
                    "default_policy_hash": base_hash,
                    "allowed_policy_hashes": [base_hash, alt_hash],
                    "policy_ref": str(base_policy),
                }
            ],
        },
    )
    monkeypatch.setenv("URM_POLICY_PROFILES_PATH", str(profile_registry))

    assert (
        main(
            [
                "materialize",
                "--policy",
                str(base_policy),
                "--materialize-ts",
                "2026-02-13T10:20:00Z",
            ]
        )
        == 0
    )
    assert (
        main(
            [
                "materialize",
                "--policy",
                str(alt_policy),
                "--materialize-ts",
                "2026-02-13T10:21:00Z",
            ]
        )
        == 0
    )
    first_out = tmp_path / "rollout.first.json"
    second_out = tmp_path / "rollout.second.json"
    assert (
        main(
            [
                "rollout",
                "--profile-id",
                "default",
                "--target-policy-hash",
                base_hash,
                "--client-request-id",
                "rollout-idem-conflict-1",
                "--activation-ts",
                "2026-02-13T10:22:00Z",
                "--out",
                str(first_out),
            ]
        )
        == 0
    )
    assert (
        main(
            [
                "rollout",
                "--profile-id",
                "default",
                "--target-policy-hash",
                alt_hash,
                "--client-request-id",
                "rollout-idem-conflict-1",
                "--activation-ts",
                "2026-02-13T10:23:00Z",
                "--out",
                str(second_out),
            ]
        )
        == 1
    )
    conflict_payload = json.loads(second_out.read_text(encoding="utf-8"))
    assert conflict_payload["schema"] == "policy_activation_log@1"
    assert conflict_payload["valid"] is False
    assert conflict_payload["issues"][0]["code"] == "URM_POLICY_IDEMPOTENCY_CONFLICT"


def test_policy_cli_rollout_maps_profile_registry_invalid_to_lint_code_and_event(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    broken_registry = tmp_path / "broken.profiles.v1.json"
    broken_registry.write_text("{not_json", encoding="utf-8")
    monkeypatch.setenv("URM_POLICY_PROFILES_PATH", str(broken_registry))
    out_path = tmp_path / "rollout.invalid.registry.json"

    assert (
        main(
            [
                "rollout",
                "--profile-id",
                "default",
                "--target-policy-hash",
                "a" * 64,
                "--client-request-id",
                "lint-invalid-registry-1",
                "--activation-ts",
                "2026-02-16T10:00:00Z",
                "--out",
                str(out_path),
            ]
        )
        == 1
    )
    payload = json.loads(out_path.read_text(encoding="utf-8"))
    assert payload["valid"] is False
    issue = payload["issues"][0]
    assert issue["code"] == "URM_POLICY_PROFILE_REGISTRY_INVALID"
    assert issue["context"]["source_code"] == "URM_POLICY_PROFILE_MAPPING_INVALID"
    assert issue["context"]["lint_rule_id"] == "profile_registry_valid"

    events_path = (
        db_path.parent
        / "evidence"
        / "codex"
        / "governance"
        / "policy"
        / "default"
        / "urm_events.ndjson"
    )
    assert events_path.exists()
    events = _read_ndjson(events_path)
    lint_events = [event for event in events if event.get("event") == "POLICY_LINT_FAILED"]
    assert lint_events
    detail = lint_events[-1]["detail"]
    assert isinstance(detail, dict)
    assert detail["lint_rule_id"] == "profile_registry_valid"
    assert detail["lint_code"] == "URM_POLICY_PROFILE_REGISTRY_INVALID"
    assert detail["policy_hash"] == "a" * 64
    assert detail["profile_id"] == "default"
    assert detail["activation_ref"] == "event:urm_policy:default#0"
