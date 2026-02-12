from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .instruction_policy import (
    InstructionPolicy,
    PolicyRule,
    compute_policy_hash,
    load_instruction_policy,
)

DEFAULT_AGENTS_VIEW_PATH = Path("docs/generated/AGENTS_POLICY_VIEW.md")
DEFAULT_SKILLS_VIEW_PATH = Path("docs/generated/SKILLS_POLICY_VIEW.md")
DEFAULT_SOURCE_LABEL = "policy/odeu.instructions.v1.json"
RULE_KINDS: tuple[str, ...] = ("deny", "require", "allow", "derive")


@dataclass(frozen=True)
class GeneratedPolicyViews:
    agents_markdown: str
    skills_markdown: str


def _sorted_rules(policy: InstructionPolicy) -> list[PolicyRule]:
    return sorted(policy.rules, key=lambda rule: (rule.priority, rule.rule_id, rule.rule_version))


def _pretty_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True)


def _collect_atoms(expr: dict[str, Any], out: set[str]) -> None:
    atom = expr.get("atom")
    if isinstance(atom, str):
        out.add(atom)
        return
    op = expr.get("op")
    if op == "not":
        child = expr.get("arg")
        if isinstance(child, dict):
            _collect_atoms(child, out)
        return
    if op in {"and", "or"}:
        args = expr.get("args")
        if isinstance(args, list):
            for child in args:
                if isinstance(child, dict):
                    _collect_atoms(child, out)


def _normalize_newlines(text: str) -> str:
    normalized = text.replace("\r\n", "\n").replace("\r", "\n")
    if not normalized.endswith("\n"):
        normalized += "\n"
    return normalized


def render_instruction_policy_views(
    *,
    policy: InstructionPolicy,
    source_label: str = DEFAULT_SOURCE_LABEL,
) -> GeneratedPolicyViews:
    rules = _sorted_rules(policy)
    policy_hash = compute_policy_hash(policy)
    atoms: set[str] = set()
    effects: set[str] = set()

    for rule in rules:
        _collect_atoms(rule.when, atoms)
        effects.add(rule.then.effect)

    agents_lines: list[str] = [
        "# AGENTS Policy View (Generated)",
        "",
        "This file is generated. Do not edit manually.",
        "",
        f"- Source: `{source_label}`",
        f"- Policy schema: `{policy.schema_id}`",
        f"- Policy hash: `{policy_hash}`",
        f"- Rule count: `{len(rules)}`",
        "",
        "## Rule Summary",
        "",
        "| Priority | Kind | Rule ID | Rule Version | Code | Effect |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for rule in rules:
        agents_lines.append(
            f"| `{rule.priority}` | `{rule.kind}` | `{rule.rule_id}` | "
            f"`{rule.rule_version}` | `{rule.code}` | `{rule.then.effect}` |"
        )
    agents_lines.extend(
        [
            "",
            "## Rule Details",
            "",
        ]
    )
    for rule in rules:
        agents_lines.extend(
            [
                f"### `{rule.rule_id}`",
                "",
                f"- Kind: `{rule.kind}`",
                f"- Priority: `{rule.priority}`",
                f"- Rule version: `{rule.rule_version}`",
                f"- Code: `{rule.code}`",
                f"- Effect: `{rule.then.effect}`",
                f"- Message: {rule.message}",
                "- `when` expression:",
                "```json",
                _pretty_json(rule.when),
                "```",
                "- `then` payload:",
                "```json",
                _pretty_json(rule.then.model_dump(mode="json")),
                "```",
                "",
            ]
        )

    skills_lines: list[str] = [
        "# SKILLS Policy View (Generated)",
        "",
        "This file is generated. Do not edit manually.",
        "",
        f"- Source: `{source_label}`",
        f"- Policy schema: `{policy.schema_id}`",
        f"- Policy hash: `{policy_hash}`",
        f"- Rule count: `{len(rules)}`",
        "",
        "## Predicate Atoms In Use",
        "",
    ]
    for atom in sorted(atoms):
        skills_lines.append(f"- `{atom}`")
    if not atoms:
        skills_lines.append("- _(none)_")

    skills_lines.extend(
        [
            "",
            "## Effects In Use",
            "",
        ]
    )
    for effect in sorted(effects):
        skills_lines.append(f"- `{effect}`")
    if not effects:
        skills_lines.append("- _(none)_")

    skills_lines.extend(
        [
            "",
            "## Rules By Kind",
            "",
        ]
    )
    for kind in RULE_KINDS:
        matches = [rule for rule in rules if rule.kind == kind]
        skills_lines.append(f"### `{kind}`")
        if not matches:
            skills_lines.append("- _(none)_")
            skills_lines.append("")
            continue
        for rule in matches:
            skills_lines.append(
                f"- `{rule.rule_id}` (priority `{rule.priority}`, code `{rule.code}`, "
                f"effect `{rule.then.effect}`)"
            )
        skills_lines.append("")

    return GeneratedPolicyViews(
        agents_markdown=_normalize_newlines("\n".join(agents_lines)),
        skills_markdown=_normalize_newlines("\n".join(skills_lines)),
    )


def write_instruction_policy_views(
    *,
    policy: InstructionPolicy,
    agents_out: Path = DEFAULT_AGENTS_VIEW_PATH,
    skills_out: Path = DEFAULT_SKILLS_VIEW_PATH,
    source_label: str = DEFAULT_SOURCE_LABEL,
    check: bool = False,
) -> GeneratedPolicyViews:
    views = render_instruction_policy_views(policy=policy, source_label=source_label)
    expected = {
        agents_out: views.agents_markdown,
        skills_out: views.skills_markdown,
    }

    drifted: list[str] = []
    for out_path, rendered in expected.items():
        if check:
            current_text = (
                _normalize_newlines(out_path.read_text(encoding="utf-8"))
                if out_path.exists()
                else None
            )
            if current_text != rendered:
                drifted.append(str(out_path))
            continue
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(rendered, encoding="utf-8")

    if drifted:
        joined = ", ".join(sorted(drifted))
        raise RuntimeError(
            "generated instruction-policy views are out of date; "
            f"regenerate: {joined}"
        )
    return views


def generate_instruction_policy_views(
    *,
    policy_path: Path | None = None,
    agents_out: Path = DEFAULT_AGENTS_VIEW_PATH,
    skills_out: Path = DEFAULT_SKILLS_VIEW_PATH,
    check: bool = False,
) -> GeneratedPolicyViews:
    policy = load_instruction_policy(policy_path=policy_path)
    source_label = str(policy_path) if policy_path is not None else DEFAULT_SOURCE_LABEL
    return write_instruction_policy_views(
        policy=policy,
        agents_out=agents_out,
        skills_out=skills_out,
        source_label=source_label,
        check=check,
    )
