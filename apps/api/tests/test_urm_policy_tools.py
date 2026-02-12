from __future__ import annotations

import json
from pathlib import Path

import pytest
from urm_runtime.policy_tools import main, validate_policy


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("Repository root not found")


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
