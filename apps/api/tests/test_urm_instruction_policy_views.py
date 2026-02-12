from __future__ import annotations

from pathlib import Path

import pytest
from urm_runtime.instruction_policy import validate_instruction_policy_document
from urm_runtime.instruction_policy_views import (
    render_instruction_policy_views,
    write_instruction_policy_views,
)


def _sample_policy() -> dict[str, object]:
    return {
        "schema": "odeu.instructions.v1",
        "rules": [
            {
                "rule_id": "z_allow",
                "rule_version": 1,
                "priority": 10,
                "kind": "allow",
                "when": {"atom": "mode_is", "args": ["read_only"]},
                "then": {"effect": "allow_action", "params": {}},
                "message": "allow read-only mode",
                "code": "ALLOW_READ_ONLY",
            },
            {
                "rule_id": "a_deny",
                "rule_version": 1,
                "priority": 1,
                "kind": "deny",
                "when": {"atom": "role_is", "args": ["blocked"]},
                "then": {"effect": "deny_action", "params": {}},
                "message": "deny blocked role",
                "code": "DENY_BLOCKED",
            },
        ],
    }


def test_render_instruction_policy_views_is_deterministic_and_normalized() -> None:
    policy = validate_instruction_policy_document(_sample_policy())
    rendered = render_instruction_policy_views(
        policy=policy,
        source_label="policy/test.json",
    )
    rendered_again = render_instruction_policy_views(
        policy=policy,
        source_label="policy/test.json",
    )

    assert rendered == rendered_again
    assert "\r" not in rendered.agents_markdown
    assert "\r" not in rendered.skills_markdown
    assert rendered.agents_markdown.index("`a_deny`") < rendered.agents_markdown.index("`z_allow`")


def test_write_instruction_policy_views_check_mode_detects_drift(tmp_path: Path) -> None:
    policy = validate_instruction_policy_document(_sample_policy())
    agents_out = tmp_path / "AGENTS_POLICY_VIEW.md"
    skills_out = tmp_path / "SKILLS_POLICY_VIEW.md"

    write_instruction_policy_views(
        policy=policy,
        agents_out=agents_out,
        skills_out=skills_out,
        source_label="policy/test.json",
        check=False,
    )
    write_instruction_policy_views(
        policy=policy,
        agents_out=agents_out,
        skills_out=skills_out,
        source_label="policy/test.json",
        check=True,
    )

    agents_out.write_text("stale\n", encoding="utf-8")
    with pytest.raises(RuntimeError, match="out of date"):
        write_instruction_policy_views(
            policy=policy,
            agents_out=agents_out,
            skills_out=skills_out,
            source_label="policy/test.json",
            check=True,
        )


def test_write_instruction_policy_views_check_mode_tolerates_crlf(tmp_path: Path) -> None:
    policy = validate_instruction_policy_document(_sample_policy())
    agents_out = tmp_path / "AGENTS_POLICY_VIEW.md"
    skills_out = tmp_path / "SKILLS_POLICY_VIEW.md"

    write_instruction_policy_views(
        policy=policy,
        agents_out=agents_out,
        skills_out=skills_out,
        source_label="policy/test.json",
        check=False,
    )

    agents_crlf = agents_out.read_text(encoding="utf-8").replace("\n", "\r\n")
    skills_crlf = skills_out.read_text(encoding="utf-8").replace("\n", "\r\n")
    agents_out.write_text(agents_crlf, encoding="utf-8")
    skills_out.write_text(skills_crlf, encoding="utf-8")

    write_instruction_policy_views(
        policy=policy,
        agents_out=agents_out,
        skills_out=skills_out,
        source_label="policy/test.json",
        check=True,
    )
