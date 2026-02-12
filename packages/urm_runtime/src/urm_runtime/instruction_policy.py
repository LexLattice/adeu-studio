from __future__ import annotations

import importlib.resources as resources
import json
import os
import re
from collections.abc import Callable
from pathlib import Path
from typing import Any, Literal

from jsonschema import Draft202012Validator
from jsonschema import ValidationError as JsonSchemaValidationError
from pydantic import BaseModel, ConfigDict, Field, ValidationError, field_validator, model_validator

from .errors import URMError
from .hashing import sha256_canonical_json

INSTRUCTION_POLICY_SCHEMA = "odeu.instructions.v1"
INSTRUCTION_POLICY_SCHEMA_VERSION = "odeu.instructions.schema.v1"
INSTRUCTION_TRACE_VERSION = "odeu.instruction-trace.v1"
INSTRUCTION_POLICY_IR_VERSION = "odeu.instructions.v1"
INSTRUCTION_EVALUATOR_VERSION = "odeu.instruction-evaluator.v1"

INSTRUCTION_POLICY_FILE = "odeu.instructions.v1.json"
INSTRUCTION_POLICY_SCHEMA_FILE = "instruction_policy.schema.json"

MAX_RULES = 500
MAX_EXPR_DEPTH = 16
MAX_EXPR_NODES = 2_000

UTC_Z_RE = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")

AtomHandler = Callable[["PolicyContext", list[Any]], bool]


class RuleEffect(BaseModel):
    model_config = ConfigDict(extra="forbid")

    effect: Literal[
        "deny_action",
        "allow_action",
        "require_approval",
        "set_warrant_invalid",
        "emit_advisory",
    ]
    params: dict[str, Any] = Field(default_factory=dict)


class PolicyRule(BaseModel):
    model_config = ConfigDict(extra="forbid")

    rule_id: str = Field(min_length=1)
    rule_version: int = Field(ge=1)
    priority: int
    kind: Literal["deny", "allow", "require", "derive"]
    when: dict[str, Any]
    then: RuleEffect
    message: str
    code: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_kind_effect_alignment(self) -> "PolicyRule":
        if self.kind == "deny" and self.then.effect != "deny_action":
            raise ValueError("deny rules must use then.effect=deny_action")
        if self.kind == "allow" and self.then.effect != "allow_action":
            raise ValueError("allow rules must use then.effect=allow_action")
        if self.kind == "require" and self.then.effect != "require_approval":
            raise ValueError("require rules must use then.effect=require_approval")
        if self.kind == "derive" and self.then.effect not in {
            "emit_advisory",
            "set_warrant_invalid",
        }:
            raise ValueError("derive rules may only use emit_advisory or set_warrant_invalid")
        return self


class InstructionPolicy(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: Literal[INSTRUCTION_POLICY_SCHEMA] = Field(
        alias="schema",
        serialization_alias="schema",
    )
    rules: list[PolicyRule] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_unique_rule_ids(self) -> "InstructionPolicy":
        seen: set[str] = set()
        duplicates: list[str] = []
        for rule in self.rules:
            if rule.rule_id in seen:
                duplicates.append(rule.rule_id)
            seen.add(rule.rule_id)
        if duplicates:
            raise ValueError(f"duplicate rule_id values: {sorted(set(duplicates))}")
        return self


class PolicyContext(BaseModel):
    model_config = ConfigDict(extra="forbid")

    role: str = Field(min_length=1)
    mode: str = Field(min_length=1)
    action_kind: str = Field(min_length=1)
    action_hash: str = Field(min_length=1)
    session_active: bool = False

    capabilities_present: list[str] = Field(default_factory=list)
    capabilities_allowed: list[str] = Field(default_factory=list)

    approval_present: bool = False
    approval_valid: bool = False
    approval_unexpired: bool = False
    approval_unused: bool = False

    evidence_kinds: list[str] = Field(default_factory=list)
    warrant: str | None = None
    evaluation_ts: str = Field(min_length=1)

    @field_validator(
        "capabilities_present",
        "capabilities_allowed",
        "evidence_kinds",
        mode="after",
    )
    @classmethod
    def _normalize_sorted_lists(cls, value: list[str]) -> list[str]:
        normalized = sorted({item.strip() for item in value if item and item.strip()})
        return normalized

    @field_validator("evaluation_ts")
    @classmethod
    def _validate_utc_z_timestamp(cls, value: str) -> str:
        if not UTC_Z_RE.match(value):
            raise ValueError("evaluation_ts must be RFC3339 UTC with Z suffix")
        return value


class PolicyDecision(BaseModel):
    model_config = ConfigDict(extra="forbid")

    decision: Literal["allow", "deny"]
    decision_code: str
    policy_hash: str
    input_context_hash: str
    matched_rule_ids: list[str]
    required_approval: bool
    trace_version: Literal[INSTRUCTION_TRACE_VERSION] = INSTRUCTION_TRACE_VERSION
    policy_schema_version: Literal[INSTRUCTION_POLICY_SCHEMA_VERSION] = (
        INSTRUCTION_POLICY_SCHEMA_VERSION
    )
    policy_ir_version: Literal[INSTRUCTION_POLICY_IR_VERSION] = INSTRUCTION_POLICY_IR_VERSION
    evaluator_version: Literal[INSTRUCTION_EVALUATOR_VERSION] = INSTRUCTION_EVALUATOR_VERSION
    advisories: list[dict[str, Any]] = Field(default_factory=list)
    warrant_invalid: bool = False


def _eval_role_is(context: PolicyContext, args: list[Any]) -> bool:
    return context.role == str(args[0])


def _eval_mode_is(context: PolicyContext, args: list[Any]) -> bool:
    return context.mode == str(args[0])


def _eval_session_active(context: PolicyContext, args: list[Any]) -> bool:
    del args
    return context.session_active


def _eval_capability_present(context: PolicyContext, args: list[Any]) -> bool:
    return str(args[0]) in context.capabilities_present


def _eval_capability_allowed(context: PolicyContext, args: list[Any]) -> bool:
    return str(args[0]) in context.capabilities_allowed


def _eval_action_kind_is(context: PolicyContext, args: list[Any]) -> bool:
    return context.action_kind == str(args[0])


def _eval_action_hash_matches(context: PolicyContext, args: list[Any]) -> bool:
    return context.action_hash == str(args[0])


def _eval_approval_present(context: PolicyContext, args: list[Any]) -> bool:
    del args
    return context.approval_present


def _eval_approval_valid(context: PolicyContext, args: list[Any]) -> bool:
    del args
    return context.approval_valid


def _eval_approval_unexpired(context: PolicyContext, args: list[Any]) -> bool:
    del args
    return context.approval_unexpired


def _eval_approval_unused(context: PolicyContext, args: list[Any]) -> bool:
    del args
    return context.approval_unused


def _eval_has_evidence_kind(context: PolicyContext, args: list[Any]) -> bool:
    return str(args[0]) in context.evidence_kinds


def _eval_warrant_is(context: PolicyContext, args: list[Any]) -> bool:
    return context.warrant == str(args[0])


ATOM_HANDLERS: dict[str, tuple[int, AtomHandler]] = {
    "role_is": (1, _eval_role_is),
    "mode_is": (1, _eval_mode_is),
    "session_active": (0, _eval_session_active),
    "capability_present": (1, _eval_capability_present),
    "capability_allowed": (1, _eval_capability_allowed),
    "action_kind_is": (1, _eval_action_kind_is),
    "action_hash_matches": (1, _eval_action_hash_matches),
    "approval_present": (0, _eval_approval_present),
    "approval_valid": (0, _eval_approval_valid),
    "approval_unexpired": (0, _eval_approval_unexpired),
    "approval_unused": (0, _eval_approval_unused),
    "has_evidence_kind": (1, _eval_has_evidence_kind),
    "warrant_is": (1, _eval_warrant_is),
}


BASE_ATOMS: frozenset[str] = frozenset(ATOM_HANDLERS)


def _discover_repo_root(anchor: Path) -> Path | None:
    for parent in anchor.parents:
        if (parent / ".git").exists():
            return parent
    return None


def _repo_relative_path(*parts: str) -> Path | None:
    repo_root = _discover_repo_root(Path(__file__).resolve())
    if repo_root is None:
        return None
    return (repo_root.joinpath(*parts)).resolve()


def _load_json_from_path(path: Path, *, description: str) -> dict[str, Any]:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message=f"{description} file not found",
            context={"path": str(path)},
        ) from exc
    except json.JSONDecodeError as exc:
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message=f"{description} is not valid JSON",
            context={"path": str(path), "error": str(exc)},
        ) from exc
    except OSError as exc:
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message=f"failed reading {description}",
            context={"path": str(path), "error": str(exc)},
        ) from exc


def _load_packaged_policy() -> dict[str, Any]:
    resource = resources.files("urm_runtime.policy").joinpath(INSTRUCTION_POLICY_FILE)
    try:
        return json.loads(resource.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message="packaged instruction policy is missing",
            context={"resource": INSTRUCTION_POLICY_FILE},
        ) from exc
    except json.JSONDecodeError as exc:
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message="packaged instruction policy is invalid JSON",
            context={"resource": INSTRUCTION_POLICY_FILE, "error": str(exc)},
        ) from exc


def _load_packaged_schema() -> dict[str, Any]:
    resource = resources.files("urm_runtime.policy").joinpath(INSTRUCTION_POLICY_SCHEMA_FILE)
    try:
        return json.loads(resource.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message="packaged instruction policy schema is missing",
            context={"resource": INSTRUCTION_POLICY_SCHEMA_FILE},
        ) from exc
    except json.JSONDecodeError as exc:
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message="packaged instruction policy schema is invalid JSON",
            context={"resource": INSTRUCTION_POLICY_SCHEMA_FILE, "error": str(exc)},
        ) from exc


def _scan_expr_for_derive_firewall_violation(
    value: Any,
    *,
    path: tuple[str, ...],
) -> tuple[str, ...] | None:
    if isinstance(value, dict):
        atom = value.get("atom")
        if isinstance(atom, str) and (atom.startswith("derived_") or atom.startswith("derived.")):
            return path + ("atom",)
        for key in sorted(value):
            match = _scan_expr_for_derive_firewall_violation(
                value[key],
                path=path + (str(key),),
            )
            if match is not None:
                return match
        return None
    if isinstance(value, list):
        for idx, item in enumerate(value):
            match = _scan_expr_for_derive_firewall_violation(
                item,
                path=path + (str(idx),),
            )
            if match is not None:
                return match
    return None


def _scan_rule_whens_for_derive_firewall_violation(
    document: dict[str, Any],
) -> tuple[str, ...] | None:
    rules = document.get("rules")
    if not isinstance(rules, list):
        return None
    for idx, candidate_rule in enumerate(rules):
        if not isinstance(candidate_rule, dict):
            continue
        when_expr = candidate_rule.get("when")
        if not isinstance(when_expr, dict):
            continue
        match = _scan_expr_for_derive_firewall_violation(
            when_expr,
            path=("rules", str(idx), "when"),
        )
        if match is not None:
            return match
    return None


def _expr_depth_and_nodes(expr: dict[str, Any]) -> tuple[int, int]:
    if "atom" in expr:
        return (1, 1)
    op = expr.get("op")
    if op == "not":
        child = expr.get("arg")
        if not isinstance(child, dict):
            raise URMError(
                code="URM_POLICY_INVALID_SCHEMA",
                message="invalid not-expression node",
                context={"expr": expr},
            )
        depth, nodes = _expr_depth_and_nodes(child)
        return (depth + 1, nodes + 1)
    if op in {"and", "or"}:
        args = expr.get("args")
        if not isinstance(args, list) or not args:
            raise URMError(
                code="URM_POLICY_INVALID_SCHEMA",
                message="invalid boolean expression args",
                context={"expr": expr},
            )
        child_depths: list[int] = []
        child_nodes: list[int] = []
        for child in args:
            if not isinstance(child, dict):
                raise URMError(
                    code="URM_POLICY_INVALID_SCHEMA",
                    message="invalid expression child node",
                    context={"expr": expr},
                )
            depth, nodes = _expr_depth_and_nodes(child)
            child_depths.append(depth)
            child_nodes.append(nodes)
        return (1 + max(child_depths), 1 + sum(child_nodes))
    raise URMError(
        code="URM_POLICY_INVALID_SCHEMA",
        message="unknown expression operator",
        context={"expr": expr},
    )


def _enforce_resource_caps(policy: InstructionPolicy) -> None:
    if len(policy.rules) > MAX_RULES:
        raise URMError(
            code="URM_POLICY_CAP_EXCEEDED",
            message="instruction policy exceeds max_rules",
            context={"max_rules": MAX_RULES, "rule_count": len(policy.rules)},
        )
    total_nodes = 0
    max_depth_seen = 0
    for rule in policy.rules:
        depth, nodes = _expr_depth_and_nodes(rule.when)
        total_nodes += nodes
        max_depth_seen = max(max_depth_seen, depth)
    if max_depth_seen > MAX_EXPR_DEPTH:
        raise URMError(
            code="URM_POLICY_CAP_EXCEEDED",
            message="instruction policy exceeds max_expr_depth",
            context={"max_expr_depth": MAX_EXPR_DEPTH, "max_expr_depth_seen": max_depth_seen},
        )
    if total_nodes > MAX_EXPR_NODES:
        raise URMError(
            code="URM_POLICY_CAP_EXCEEDED",
            message="instruction policy exceeds max_expr_nodes",
            context={"max_expr_nodes": MAX_EXPR_NODES, "total_expr_nodes": total_nodes},
        )


def _validate_with_schema(document: dict[str, Any], schema: dict[str, Any]) -> None:
    try:
        validator = Draft202012Validator(schema)
        errors = sorted(validator.iter_errors(document), key=lambda e: (list(e.path), e.message))
    except JsonSchemaValidationError as exc:
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message="instruction policy schema validation failed",
            context={"error": str(exc)},
        ) from exc
    if not errors:
        return
    first = errors[0]
    path = "/" + "/".join(str(part) for part in first.path)
    raise URMError(
        code="URM_POLICY_INVALID_SCHEMA",
        message="instruction policy schema validation failed",
        context={"path": path, "error": first.message},
    )


def load_instruction_policy_schema(*, schema_path: Path | None = None) -> dict[str, Any]:
    if schema_path is not None:
        return _load_json_from_path(schema_path, description="instruction policy schema")

    env_path = os.environ.get("URM_INSTRUCTION_POLICY_SCHEMA_PATH", "").strip()
    if env_path:
        resolved_env = Path(env_path).expanduser().resolve()
        return _load_json_from_path(resolved_env, description="instruction policy schema")

    repo_schema_path = _repo_relative_path("spec", INSTRUCTION_POLICY_SCHEMA_FILE)
    if repo_schema_path is not None and repo_schema_path.exists():
        return _load_json_from_path(repo_schema_path, description="instruction policy schema")

    return _load_packaged_schema()


def validate_instruction_policy_document(
    document: dict[str, Any],
    *,
    strict: bool = True,
    schema: dict[str, Any] | None = None,
) -> InstructionPolicy:
    rules_candidate = document.get("rules")
    if isinstance(rules_candidate, list) and len(rules_candidate) > MAX_RULES:
        raise URMError(
            code="URM_POLICY_CAP_EXCEEDED",
            message="instruction policy exceeds max_rules",
            context={"max_rules": MAX_RULES, "rule_count": len(rules_candidate)},
        )
    if strict:
        violation_path = _scan_rule_whens_for_derive_firewall_violation(document)
        if violation_path is not None:
            pointer = "/" + "/".join(violation_path)
            raise URMError(
                code="URM_POLICY_DERIVE_FIREWALL_VIOLATION",
                message="derive-only atoms are forbidden in when expressions",
                context={"path": pointer},
            )
    resolved_schema = schema or load_instruction_policy_schema()
    _validate_with_schema(document, resolved_schema)
    try:
        policy = InstructionPolicy.model_validate(document)
    except ValidationError as exc:
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message="instruction policy model validation failed",
            context={"error": str(exc)},
        ) from exc
    _enforce_resource_caps(policy)
    return policy


def load_instruction_policy(
    *,
    policy_path: Path | None = None,
    schema_path: Path | None = None,
    strict: bool = True,
) -> InstructionPolicy:
    schema = load_instruction_policy_schema(schema_path=schema_path)
    if policy_path is not None:
        doc = _load_json_from_path(policy_path, description="instruction policy")
        return validate_instruction_policy_document(doc, strict=strict, schema=schema)

    env_path = os.environ.get("URM_INSTRUCTION_POLICY_PATH", "").strip()
    if env_path:
        resolved_env = Path(env_path).expanduser().resolve()
        doc = _load_json_from_path(resolved_env, description="instruction policy")
        return validate_instruction_policy_document(doc, strict=strict, schema=schema)

    repo_policy_path = _repo_relative_path("policy", INSTRUCTION_POLICY_FILE)
    if repo_policy_path is not None and repo_policy_path.exists():
        doc = _load_json_from_path(repo_policy_path, description="instruction policy")
        return validate_instruction_policy_document(doc, strict=strict, schema=schema)

    packaged = _load_packaged_policy()
    return validate_instruction_policy_document(packaged, strict=strict, schema=schema)


def _sort_rule_key(rule: PolicyRule) -> tuple[int, str, int]:
    return (rule.priority, rule.rule_id, rule.rule_version)


def _semantic_expr(expr: dict[str, Any]) -> dict[str, Any]:
    if "atom" in expr:
        atom = str(expr["atom"])
        args = expr.get("args", [])
        if not isinstance(args, list):
            raise URMError(
                code="URM_POLICY_INVALID_SCHEMA",
                message="atom args must be a list",
                context={"expr": expr},
            )
        return {"atom": atom, "args": args}
    op = expr.get("op")
    if op == "not":
        arg = expr.get("arg")
        if not isinstance(arg, dict):
            raise URMError(
                code="URM_POLICY_INVALID_SCHEMA",
                message="not arg must be an expression object",
                context={"expr": expr},
            )
        return {"op": "not", "arg": _semantic_expr(arg)}
    if op in {"and", "or"}:
        args = expr.get("args")
        if not isinstance(args, list):
            raise URMError(
                code="URM_POLICY_INVALID_SCHEMA",
                message="boolean args must be a list",
                context={"expr": expr},
            )
        return {"op": op, "args": [_semantic_expr(item) for item in args]}
    raise URMError(
        code="URM_POLICY_INVALID_SCHEMA",
        message="unknown expression operator",
        context={"expr": expr},
    )


def policy_semantic_form(policy: InstructionPolicy) -> dict[str, Any]:
    rules = sorted(policy.rules, key=_sort_rule_key)
    return {
        "schema": policy.schema_id,
        "rules": [
            {
                "rule_id": rule.rule_id,
                "rule_version": rule.rule_version,
                "priority": rule.priority,
                "kind": rule.kind,
                "when": _semantic_expr(rule.when),
                "then": {"effect": rule.then.effect, "params": rule.then.params},
                "code": rule.code,
            }
            for rule in rules
        ],
    }


def compute_policy_hash(policy: InstructionPolicy) -> str:
    return sha256_canonical_json(policy_semantic_form(policy))


def policy_context_semantic_form(context: PolicyContext) -> dict[str, Any]:
    return {
        "role": context.role,
        "mode": context.mode,
        "action_kind": context.action_kind,
        "action_hash": context.action_hash,
        "session_active": context.session_active,
        "capabilities_present": sorted(context.capabilities_present),
        "capabilities_allowed": sorted(context.capabilities_allowed),
        "approval_present": context.approval_present,
        "approval_valid": context.approval_valid,
        "approval_unexpired": context.approval_unexpired,
        "approval_unused": context.approval_unused,
        "evidence_kinds": sorted(context.evidence_kinds),
        "warrant": context.warrant,
        "evaluation_ts": context.evaluation_ts,
    }


def compute_input_context_hash(context: PolicyContext) -> str:
    return sha256_canonical_json(policy_context_semantic_form(context))


def _ensure_arg_count(*, atom: str, args: list[Any], expected: int) -> None:
    if len(args) != expected:
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message=f"{atom} expects {expected} argument(s)",
            context={"atom": atom, "args": args},
        )


def _evaluate_atom(*, atom: str, args: list[Any], context: PolicyContext) -> bool:
    handler_spec = ATOM_HANDLERS.get(atom)
    if handler_spec is None:
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message="unknown predicate atom",
            context={"atom": atom},
        )
    expected_args, handler = handler_spec
    _ensure_arg_count(atom=atom, args=args, expected=expected_args)
    return handler(context, args)


def _evaluate_expr(expr: dict[str, Any], context: PolicyContext) -> bool:
    if "atom" in expr:
        atom = str(expr["atom"])
        args = expr.get("args", [])
        if not isinstance(args, list):
            raise URMError(
                code="URM_POLICY_INVALID_SCHEMA",
                message="atom args must be a list",
                context={"expr": expr},
            )
        return _evaluate_atom(atom=atom, args=args, context=context)

    op = expr.get("op")
    if op == "not":
        arg = expr.get("arg")
        if not isinstance(arg, dict):
            raise URMError(
                code="URM_POLICY_INVALID_SCHEMA",
                message="not arg must be expression object",
                context={"expr": expr},
            )
        return not _evaluate_expr(arg, context)
    if op == "and":
        args = expr.get("args")
        if not isinstance(args, list):
            raise URMError(
                code="URM_POLICY_INVALID_SCHEMA",
                message="and args must be a list",
                context={"expr": expr},
            )
        return all(_evaluate_expr(cast_expr(item), context) for item in args)
    if op == "or":
        args = expr.get("args")
        if not isinstance(args, list):
            raise URMError(
                code="URM_POLICY_INVALID_SCHEMA",
                message="or args must be a list",
                context={"expr": expr},
            )
        return any(_evaluate_expr(cast_expr(item), context) for item in args)

    raise URMError(
        code="URM_POLICY_INVALID_SCHEMA",
        message="unknown predicate op",
        context={"expr": expr},
    )


def cast_expr(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise URMError(
            code="URM_POLICY_INVALID_SCHEMA",
            message="expression node must be an object",
            context={"expr": value},
        )
    return value


def _valid_approval_available(context: PolicyContext) -> bool:
    return (
        context.approval_present
        and context.approval_valid
        and context.approval_unexpired
        and context.approval_unused
    )


def evaluate_instruction_policy(
    *,
    policy: InstructionPolicy,
    context: PolicyContext,
) -> PolicyDecision:
    matching_rules = [rule for rule in policy.rules if _evaluate_expr(rule.when, context)]
    matching_rules_sorted = sorted(matching_rules, key=lambda rule: (rule.priority, rule.rule_id))
    matched_rule_ids = [rule.rule_id for rule in matching_rules_sorted]

    required_approval = any(
        rule.then.effect == "require_approval" for rule in matching_rules_sorted
    )
    advisories = [
        {
            "rule_id": rule.rule_id,
            "code": rule.code,
            "params": rule.then.params,
        }
        for rule in matching_rules_sorted
        if rule.then.effect == "emit_advisory"
    ]
    warrant_invalid = any(
        rule.then.effect == "set_warrant_invalid" for rule in matching_rules_sorted
    )

    deny_rule = next(
        (rule for rule in matching_rules_sorted if rule.then.effect == "deny_action"),
        None,
    )
    allow_rule = next(
        (rule for rule in matching_rules_sorted if rule.then.effect == "allow_action"),
        None,
    )

    if deny_rule is not None:
        decision = "deny"
        decision_code = deny_rule.code
    elif required_approval and not _valid_approval_available(context):
        decision = "deny"
        decision_code = "URM_APPROVAL_REQUIRED"
    elif allow_rule is not None:
        decision = "allow"
        decision_code = allow_rule.code
    else:
        decision = "deny"
        decision_code = "URM_POLICY_DENIED"

    return PolicyDecision(
        decision=decision,
        decision_code=decision_code,
        policy_hash=compute_policy_hash(policy),
        input_context_hash=compute_input_context_hash(context),
        matched_rule_ids=matched_rule_ids,
        required_approval=required_approval,
        advisories=advisories,
        warrant_invalid=warrant_invalid,
    )
