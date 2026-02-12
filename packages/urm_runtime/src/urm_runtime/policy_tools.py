from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from .errors import URMError
from .hashing import canonical_json
from .instruction_policy import (
    InstructionPolicy,
    PolicyContext,
    PolicyDecision,
    compute_policy_hash,
    evaluate_instruction_policy,
    load_instruction_policy,
    policy_semantic_form,
)

POLICY_VALIDATE_SCHEMA = "instruction-policy-validate@1"
POLICY_EVAL_SCHEMA = "instruction-policy-eval@1"
POLICY_DIFF_SCHEMA = "instruction-policy-diff@1"
POLICY_EXPLAIN_SCHEMA = "policy_explain@1"
DEFAULT_EVALUATION_TS = "1970-01-01T00:00:00Z"


def _load_json_from_path(path: Path, *, description: str) -> dict[str, Any]:
    try:
        raw = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message=f"{description} file is not readable",
            context={"path": str(path), "error": str(exc)},
        ) from exc
    try:
        payload = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message=f"{description} is invalid JSON",
            context={"path": str(path), "error": str(exc)},
        ) from exc
    if not isinstance(payload, dict):
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message=f"{description} must be a JSON object",
            context={"path": str(path)},
        )
    return payload


def _error_issue(exc: URMError) -> dict[str, Any]:
    return {
        "code": exc.detail.code,
        "message": exc.detail.message,
        "context": exc.detail.context,
    }


def _now_utc_z() -> str:
    return datetime.now(tz=timezone.utc).replace(microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")


def validate_policy(
    path: Path,
    *,
    strict: bool,
    schema_path: Path | None = None,
) -> dict[str, Any]:
    try:
        policy = load_instruction_policy(policy_path=path, schema_path=schema_path, strict=strict)
    except URMError as exc:
        return {
            "schema": POLICY_VALIDATE_SCHEMA,
            "input": str(path),
            "strict": strict,
            "valid": False,
            "issues": [_error_issue(exc)],
        }

    return {
        "schema": POLICY_VALIDATE_SCHEMA,
        "input": str(path),
        "strict": strict,
        "valid": True,
        "policy_hash": compute_policy_hash(policy),
        "rule_count": len(policy.rules),
        "issues": [],
    }


def eval_policy(
    *,
    policy_path: Path,
    context_path: Path,
    strict: bool,
    schema_path: Path | None = None,
    evaluation_ts: str | None = None,
    use_now: bool = False,
) -> dict[str, Any]:
    try:
        if use_now and evaluation_ts is not None:
            raise URMError(
                code="URM_POLICY_INVALID_SCHEMA",
                message="cannot combine --use-now with --evaluation-ts",
            )
        policy = load_instruction_policy(
            policy_path=policy_path,
            schema_path=schema_path,
            strict=strict,
        )
        context_doc = _load_json_from_path(context_path, description="policy context")
        if use_now:
            resolved_evaluation_ts = _now_utc_z()
        elif evaluation_ts is not None:
            resolved_evaluation_ts = evaluation_ts
        elif "evaluation_ts" in context_doc:
            resolved_evaluation_ts = str(context_doc["evaluation_ts"])
        else:
            resolved_evaluation_ts = DEFAULT_EVALUATION_TS
        context_doc["evaluation_ts"] = resolved_evaluation_ts
        context = PolicyContext.model_validate(context_doc)
        decision = evaluate_instruction_policy(policy=policy, context=context)
    except URMError as exc:
        return {
            "schema": POLICY_EVAL_SCHEMA,
            "input_policy": str(policy_path),
            "input_context": str(context_path),
            "strict": strict,
            "deterministic_mode": not use_now,
            "valid": False,
            "issues": [_error_issue(exc)],
        }

    return {
        "schema": POLICY_EVAL_SCHEMA,
        "input_policy": str(policy_path),
        "input_context": str(context_path),
        "strict": strict,
        "deterministic_mode": not use_now,
        "valid": True,
        "evaluation_ts": context.evaluation_ts,
        "policy_hash": decision.policy_hash,
        "input_context_hash": decision.input_context_hash,
        "decision": decision.decision,
        "decision_code": decision.decision_code,
        "matched_rule_ids": list(decision.matched_rule_ids),
        "required_approval": decision.required_approval,
        "evaluator_version": decision.evaluator_version,
        "trace_version": decision.trace_version,
        "policy_schema_version": decision.policy_schema_version,
        "policy_ir_version": decision.policy_ir_version,
        "issues": [],
    }


def _semantic_rule_map(policy: InstructionPolicy) -> dict[str, dict[str, Any]]:
    semantic_rules = policy_semantic_form(policy)["rules"]
    return {str(rule["rule_id"]): rule for rule in semantic_rules}


def _rule_index(policy: InstructionPolicy) -> dict[str, Any]:
    return {rule.rule_id: rule for rule in policy.rules}


def _matched_rule_summaries(
    *,
    policy: InstructionPolicy,
    decision: PolicyDecision,
) -> list[dict[str, Any]]:
    by_id = _rule_index(policy)
    summaries: list[dict[str, Any]] = []
    for rule_id in decision.matched_rule_ids:
        rule = by_id.get(rule_id)
        if rule is None:
            continue
        summaries.append(
            {
                "rule_id": rule.rule_id,
                "rule_version": rule.rule_version,
                "priority": rule.priority,
                "kind": rule.kind,
                "code": rule.code,
                "effect": rule.then.effect,
                "message": rule.message,
            }
        )
    return summaries


def explain_policy(
    *,
    policy_path: Path,
    context_path: Path,
    strict: bool,
    schema_path: Path | None = None,
    evaluation_ts: str | None = None,
    use_now: bool = False,
) -> dict[str, Any]:
    try:
        if use_now and evaluation_ts is not None:
            raise URMError(
                code="URM_POLICY_EXPLAIN_INVALID_INPUT",
                message="cannot combine --use-now with --evaluation-ts",
            )
        policy = load_instruction_policy(
            policy_path=policy_path,
            schema_path=schema_path,
            strict=strict,
        )
        context_doc = _load_json_from_path(context_path, description="policy context")
        if use_now:
            resolved_evaluation_ts = _now_utc_z()
        elif evaluation_ts is not None:
            resolved_evaluation_ts = evaluation_ts
        elif "evaluation_ts" in context_doc:
            resolved_evaluation_ts = str(context_doc["evaluation_ts"])
        else:
            resolved_evaluation_ts = DEFAULT_EVALUATION_TS
        context_doc["evaluation_ts"] = resolved_evaluation_ts
        context = PolicyContext.model_validate(context_doc)
        decision = evaluate_instruction_policy(policy=policy, context=context)
    except URMError as exc:
        return {
            "schema": POLICY_EXPLAIN_SCHEMA,
            "input_policy": str(policy_path),
            "input_context": str(context_path),
            "strict": strict,
            "deterministic_mode": not use_now,
            "valid": False,
            "issues": [_error_issue(exc)],
        }

    return {
        "schema": POLICY_EXPLAIN_SCHEMA,
        "input_policy": str(policy_path),
        "input_context": str(context_path),
        "strict": strict,
        "deterministic_mode": not use_now,
        "valid": True,
        "evaluation_ts": context.evaluation_ts,
        "policy_hash": decision.policy_hash,
        "input_context_hash": decision.input_context_hash,
        "decision": decision.decision,
        "decision_code": decision.decision_code,
        "matched_rule_ids": list(decision.matched_rule_ids),
        "matched_rules": _matched_rule_summaries(policy=policy, decision=decision),
        "required_approval": decision.required_approval,
        "evaluator_version": decision.evaluator_version,
        "trace_version": decision.trace_version,
        "policy_schema_version": decision.policy_schema_version,
        "policy_ir_version": decision.policy_ir_version,
        "advisories": list(decision.advisories),
        "warrant_invalid": decision.warrant_invalid,
        "evidence_refs": [ref.model_dump(mode="json") for ref in decision.evidence_refs],
        "issues": [],
    }


def diff_policy(
    *,
    old_policy_path: Path,
    new_policy_path: Path,
    strict: bool,
    schema_path: Path | None = None,
) -> dict[str, Any]:
    try:
        old_policy = load_instruction_policy(
            policy_path=old_policy_path,
            schema_path=schema_path,
            strict=strict,
        )
        new_policy = load_instruction_policy(
            policy_path=new_policy_path,
            schema_path=schema_path,
            strict=strict,
        )
        old_by_id = _semantic_rule_map(old_policy)
        new_by_id = _semantic_rule_map(new_policy)
    except URMError as exc:
        return {
            "schema": POLICY_DIFF_SCHEMA,
            "input_old": str(old_policy_path),
            "input_new": str(new_policy_path),
            "strict": strict,
            "valid": False,
            "issues": [_error_issue(exc)],
        }

    old_ids = set(old_by_id)
    new_ids = set(new_by_id)
    added_rules = sorted(new_ids - old_ids)
    removed_rules = sorted(old_ids - new_ids)

    modified_rules: list[dict[str, Any]] = []
    changed_fields = ("priority", "when", "then", "code", "kind", "rule_version")
    for rule_id in sorted(old_ids & new_ids):
        old_rule = old_by_id[rule_id]
        new_rule = new_by_id[rule_id]
        changes: dict[str, dict[str, Any]] = {}
        for field in changed_fields:
            if old_rule.get(field) != new_rule.get(field):
                changes[field] = {"old": old_rule.get(field), "new": new_rule.get(field)}
        if changes:
            modified_rules.append(
                {
                    "rule_id": rule_id,
                    "changed_fields": sorted(changes),
                    "changes": changes,
                }
            )

    semantic_equal = not added_rules and not removed_rules and not modified_rules
    return {
        "schema": POLICY_DIFF_SCHEMA,
        "input_old": str(old_policy_path),
        "input_new": str(new_policy_path),
        "strict": strict,
        "valid": True,
        "old_policy_hash": compute_policy_hash(old_policy),
        "new_policy_hash": compute_policy_hash(new_policy),
        "semantic_equal": semantic_equal,
        "added_rules": added_rules,
        "removed_rules": removed_rules,
        "modified_rules": modified_rules,
        "issues": [],
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="policy",
        description=(
            "Instruction policy tooling: validate, eval, explain, and diff policy IR documents."
        ),
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    validate_parser = subparsers.add_parser(
        "validate",
        help="Validate an ODEU instruction policy document.",
    )
    validate_parser.add_argument("--in", dest="input_path", type=Path, required=True)
    validate_parser.add_argument("--schema", dest="schema_path", type=Path, required=False)
    validate_parser.add_argument("--strict", action="store_true")

    eval_parser = subparsers.add_parser(
        "eval",
        help="Evaluate a policy decision for a provided context document.",
    )
    eval_parser.add_argument("--policy", dest="policy_path", type=Path, required=True)
    eval_parser.add_argument("--context", dest="context_path", type=Path, required=True)
    eval_parser.add_argument("--schema", dest="schema_path", type=Path, required=False)
    eval_parser.add_argument("--evaluation-ts", dest="evaluation_ts", type=str, required=False)
    eval_parser.add_argument("--use-now", dest="use_now", action="store_true")
    eval_parser.add_argument("--out", dest="out_path", type=Path, required=False)
    eval_parser.add_argument("--lax", dest="strict", action="store_false")
    eval_parser.set_defaults(strict=True)

    explain_parser = subparsers.add_parser(
        "explain",
        help="Render deterministic explanation view from policy decision output.",
    )
    explain_parser.add_argument("--policy", dest="policy_path", type=Path, required=True)
    explain_parser.add_argument("--context", dest="context_path", type=Path, required=True)
    explain_parser.add_argument("--schema", dest="schema_path", type=Path, required=False)
    explain_parser.add_argument("--evaluation-ts", dest="evaluation_ts", type=str, required=False)
    explain_parser.add_argument("--use-now", dest="use_now", action="store_true")
    explain_parser.add_argument("--out", dest="out_path", type=Path, required=False)
    explain_parser.add_argument("--lax", dest="strict", action="store_false")
    explain_parser.set_defaults(strict=True)

    diff_parser = subparsers.add_parser(
        "diff",
        help="Compute semantic diff between two policy documents.",
    )
    diff_parser.add_argument("--old", dest="old_policy_path", type=Path, required=True)
    diff_parser.add_argument("--new", dest="new_policy_path", type=Path, required=True)
    diff_parser.add_argument("--schema", dest="schema_path", type=Path, required=False)
    diff_parser.add_argument("--out", dest="out_path", type=Path, required=False)
    diff_parser.add_argument("--lax", dest="strict", action="store_false")
    diff_parser.set_defaults(strict=True)

    return parser.parse_args(argv)


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    if args.command == "validate":
        report = validate_policy(
            args.input_path,
            strict=bool(args.strict),
            schema_path=args.schema_path,
        )
        out_text = canonical_json(report)
        print(out_text)
        return 0 if report["valid"] else 1
    if args.command == "eval":
        report = eval_policy(
            policy_path=args.policy_path,
            context_path=args.context_path,
            strict=bool(args.strict),
            schema_path=args.schema_path,
            evaluation_ts=args.evaluation_ts,
            use_now=bool(args.use_now),
        )
        out_text = canonical_json(report)
        if args.out_path is not None:
            _write_text(args.out_path, out_text + "\n")
        else:
            print(out_text)
        return 0 if report["valid"] else 1
    if args.command == "explain":
        report = explain_policy(
            policy_path=args.policy_path,
            context_path=args.context_path,
            strict=bool(args.strict),
            schema_path=args.schema_path,
            evaluation_ts=args.evaluation_ts,
            use_now=bool(args.use_now),
        )
        out_text = canonical_json(report)
        if args.out_path is not None:
            _write_text(args.out_path, out_text + "\n")
        else:
            print(out_text)
        return 0 if report["valid"] else 1
    if args.command == "diff":
        report = diff_policy(
            old_policy_path=args.old_policy_path,
            new_policy_path=args.new_policy_path,
            strict=bool(args.strict),
            schema_path=args.schema_path,
        )
        out_text = canonical_json(report)
        if args.out_path is not None:
            _write_text(args.out_path, out_text + "\n")
        else:
            print(out_text)
        return 0 if report["valid"] else 1
    return 1  # pragma: no cover


if __name__ == "__main__":
    raise SystemExit(main())
