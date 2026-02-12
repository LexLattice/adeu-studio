from __future__ import annotations

import importlib.resources as resources
import json
import os
from collections.abc import Callable
from dataclasses import dataclass
from datetime import datetime, timezone
from functools import lru_cache
from pathlib import Path
from typing import Any, Literal, NoReturn

from adeu_ir import ProofArtifact, ProofInput
from adeu_kernel.proof import build_proof_backend, build_trivial_theorem_source

from .errors import URMError
from .hashing import action_hash as compute_action_hash
from .hashing import sha256_text
from .instruction_policy import (
    EvidenceRef,
    PolicyContext,
    PolicyDecision,
    evaluate_instruction_policy,
    load_instruction_policy,
)

CAPABILITY_LATTICE_SCHEMA = "urm.capability.lattice.v1"
ALLOW_POLICY_SCHEMA = "urm.allow.v1"
CAPABILITY_LATTICE_FILE = "urm.capability.lattice.v1.json"
ALLOW_POLICY_FILE = "urm.allow.v1.json"
HARD_GATE_TRACE_VERSION = "urm.hard-gate.v1"
PolicyEvalEventName = Literal["POLICY_EVAL_START", "POLICY_EVAL_PASS", "POLICY_DENIED"]
PolicyEvalEventCallback = Callable[[PolicyEvalEventName, dict[str, Any]], None]
InstructionProofBackend = Literal["lean", "mock"]
INSTRUCTION_KERNEL_PROOF_THEOREM_IDS: tuple[str, ...] = (
    "no_write_without_mode_and_approval",
    "approval_single_use_atomicity",
)


@dataclass(frozen=True)
class ActionPolicy:
    capability: str
    requires_writes_allowed: bool
    requires_approval: bool


@dataclass(frozen=True)
class CapabilityPolicy:
    capabilities: frozenset[str]
    role_capabilities: dict[str, frozenset[str]]
    actions: dict[str, ActionPolicy]
    policy_root: str


@dataclass(frozen=True)
class AuthorizationDecision:
    action: str
    hard_gate_trace_version: str
    policy_decision: PolicyDecision


def _discover_repo_root(anchor: Path) -> Path | None:
    for parent in anchor.parents:
        if (parent / ".git").exists():
            return parent
    return None


def _load_json(path: Path) -> dict[str, Any]:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise RuntimeError(f"failed reading policy file: {path}") from exc
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"failed parsing policy file: {path}") from exc


def _coerce_bool(*, value: Any, field_name: str, action_name: str) -> bool:
    if isinstance(value, bool):
        return value
    raise RuntimeError(
        f"invalid action policy for '{action_name}': '{field_name}' must be a boolean"
    )


def _load_json_from_package(*, filename: str) -> dict[str, Any]:
    resource = resources.files("urm_runtime.policy").joinpath(filename)
    try:
        text = resource.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise RuntimeError(f"missing packaged policy file: {filename}") from exc
    except OSError as exc:
        raise RuntimeError(f"failed reading packaged policy file: {filename}") from exc
    try:
        return json.loads(text)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"failed parsing packaged policy file: {filename}") from exc


def _load_policy_json_pair() -> tuple[dict[str, Any], dict[str, Any], str]:
    errors: list[str] = []
    env = os.environ.get("URM_POLICY_ROOT", "").strip()
    if env:
        policy_root = Path(env).expanduser().resolve()
        try:
            lattice = _load_json(policy_root / CAPABILITY_LATTICE_FILE)
            allow = _load_json(policy_root / ALLOW_POLICY_FILE)
            return lattice, allow, str(policy_root)
        except RuntimeError as exc:
            errors.append(f"env:{policy_root} -> {exc}")

    repo_root = _discover_repo_root(Path(__file__).resolve())
    if repo_root is not None:
        policy_root = repo_root / "policy"
        try:
            lattice = _load_json(policy_root / CAPABILITY_LATTICE_FILE)
            allow = _load_json(policy_root / ALLOW_POLICY_FILE)
            return lattice, allow, str(policy_root)
        except RuntimeError as exc:
            errors.append(f"repo:{policy_root} -> {exc}")

    try:
        lattice = _load_json_from_package(filename=CAPABILITY_LATTICE_FILE)
        allow = _load_json_from_package(filename=ALLOW_POLICY_FILE)
        return lattice, allow, "package:urm_runtime.policy"
    except RuntimeError as exc:
        errors.append(f"package:urm_runtime.policy -> {exc}")

    reasons = "; ".join(errors) if errors else "no policy sources available"
    raise RuntimeError(f"unable to load capability policies ({reasons})")


def _parse_action_policy(*, action_name: str, payload: Any) -> ActionPolicy:
    if not isinstance(payload, dict):
        raise RuntimeError(f"invalid action policy for '{action_name}': expected object")

    capability = payload.get("capability")
    if not isinstance(capability, str) or not capability.strip():
        raise RuntimeError(
            f"invalid action policy for '{action_name}': capability must be a non-empty string"
        )

    requires_writes_allowed = _coerce_bool(
        value=payload.get("requires_writes_allowed", False),
        field_name="requires_writes_allowed",
        action_name=action_name,
    )
    requires_approval = _coerce_bool(
        value=payload.get("requires_approval", False),
        field_name="requires_approval",
        action_name=action_name,
    )
    return ActionPolicy(
        capability=capability.strip(),
        requires_writes_allowed=requires_writes_allowed,
        requires_approval=requires_approval,
    )


def _load_policy() -> CapabilityPolicy:
    lattice, allow, policy_root = _load_policy_json_pair()

    lattice_schema = lattice.get("schema")
    if lattice_schema != CAPABILITY_LATTICE_SCHEMA:
        raise RuntimeError(
            "invalid lattice schema: "
            f"expected '{CAPABILITY_LATTICE_SCHEMA}', got '{lattice_schema}'"
        )
    allow_schema = allow.get("schema")
    if allow_schema != ALLOW_POLICY_SCHEMA:
        raise RuntimeError(
            f"invalid allow schema: expected '{ALLOW_POLICY_SCHEMA}', got '{allow_schema}'"
        )

    capabilities_raw = lattice.get("capabilities")
    if not isinstance(capabilities_raw, list):
        raise RuntimeError("invalid capability lattice: capabilities must be a list")
    capabilities: set[str] = set()
    for item in capabilities_raw:
        if not isinstance(item, str) or not item.strip():
            raise RuntimeError(
                "invalid capability lattice: "
                "capability names must be non-empty strings"
            )
        capabilities.add(item.strip())

    actions_raw = lattice.get("actions")
    if not isinstance(actions_raw, dict):
        raise RuntimeError("invalid capability lattice: actions must be an object")
    actions: dict[str, ActionPolicy] = {}
    for action_name in sorted(actions_raw):
        if not isinstance(action_name, str) or not action_name.strip():
            raise RuntimeError("invalid capability lattice: action names must be non-empty strings")
        parsed = _parse_action_policy(action_name=action_name, payload=actions_raw[action_name])
        if parsed.capability not in capabilities:
            raise RuntimeError(
                f"invalid action policy for '{action_name}': "
                f"unknown capability '{parsed.capability}'"
            )
        actions[action_name] = parsed

    roles_raw = allow.get("roles")
    if not isinstance(roles_raw, dict):
        raise RuntimeError("invalid allow policy: roles must be an object")

    role_capabilities: dict[str, frozenset[str]] = {}
    for role_name in sorted(roles_raw):
        values = roles_raw[role_name]
        if not isinstance(role_name, str) or not role_name.strip():
            raise RuntimeError("invalid allow policy: role names must be non-empty strings")
        if not isinstance(values, list):
            raise RuntimeError(f"invalid allow policy for role '{role_name}': expected list")
        role_caps: set[str] = set()
        for capability in values:
            if not isinstance(capability, str) or not capability.strip():
                raise RuntimeError(
                    f"invalid allow policy for role '{role_name}': "
                    "capabilities must be non-empty strings"
                )
            cap = capability.strip()
            if cap not in capabilities:
                raise RuntimeError(
                    f"invalid allow policy for role '{role_name}': unknown capability '{cap}'"
                )
            role_caps.add(cap)
        role_capabilities[role_name] = frozenset(role_caps)

    return CapabilityPolicy(
        capabilities=frozenset(capabilities),
        role_capabilities=role_capabilities,
        actions=actions,
        policy_root=str(policy_root),
    )


@lru_cache(maxsize=1)
def load_capability_policy() -> CapabilityPolicy:
    return _load_policy()


def reset_capability_policy_cache() -> None:
    load_capability_policy.cache_clear()


def _now_utc_z() -> str:
    return datetime.now(tz=timezone.utc).replace(microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")


def _raise_policy_denied(
    *,
    action: str,
    role: str,
    message: str,
    context: dict[str, Any],
) -> NoReturn:
    raise URMError(
        code="URM_POLICY_DENIED",
        message=message,
        context={"role": role, "action": action, **context},
    )


def _emit_policy_event(
    *,
    callback: PolicyEvalEventCallback | None,
    event_name: PolicyEvalEventName,
    detail: dict[str, Any],
) -> None:
    if callback is None:
        return
    callback(event_name, detail)


def _selected_instruction_proof_backend() -> InstructionProofBackend:
    selected = os.environ.get("ADEU_PROOF_BACKEND", "mock").strip().lower()
    return "lean" if selected == "lean" else "mock"


def _build_instruction_proof_inputs(*, action: str, action_hash: str) -> list[ProofInput]:
    return [
        ProofInput(object_id=action, json_path="/action_kind", formula_hash=action_hash),
        ProofInput(object_id="policy_context", json_path="/action_hash", formula_hash=action_hash),
    ]


def _build_failed_instruction_proof_artifact(
    *,
    theorem_id: str,
    theorem_src: str,
    inputs: list[ProofInput],
    backend: InstructionProofBackend,
    policy_hash: str,
    action: str,
    role: str,
    error: str,
) -> ProofArtifact:
    stable_id = sha256_text(f"instruction-kernel:{theorem_id}:{backend}")[:16]
    return ProofArtifact(
        proof_id=f"proof_{stable_id}",
        backend=backend,
        theorem_id=theorem_id,
        status="failed",
        proof_hash=sha256_text(theorem_src),
        inputs=inputs,
        details={
            "scope": "instruction-kernel",
            "invariant_id": theorem_id,
            "policy_hash": policy_hash,
            "action_kind": action,
            "role": role,
            "error": error,
        },
    )


def _sorted_unique_proof_evidence_refs(refs: list[EvidenceRef]) -> list[EvidenceRef]:
    unique: dict[tuple[str, str, str], EvidenceRef] = {}
    for ref in refs:
        key = (ref.kind, ref.ref, ref.note or "")
        unique[key] = ref
    ordered = sorted(unique, key=lambda key: (key[0], key[1], key[2]))
    return [unique[key] for key in ordered]


def _attach_instruction_policy_proofs(
    *,
    policy_decision: PolicyDecision,
    action: str,
    action_hash: str,
    role: str,
) -> PolicyDecision:
    inputs = _build_instruction_proof_inputs(action=action, action_hash=action_hash)
    backend_name = _selected_instruction_proof_backend()
    proof_artifacts: list[ProofArtifact] = []
    backend_error: str | None = None
    backend = None
    try:
        backend = build_proof_backend(kind=backend_name)
    except Exception as exc:  # pragma: no cover - environment-specific fallback
        backend_error = str(exc)

    for theorem_id in INSTRUCTION_KERNEL_PROOF_THEOREM_IDS:
        theorem_src = build_trivial_theorem_source(theorem_id=theorem_id)
        if backend is None:
            proof_artifacts.append(
                _build_failed_instruction_proof_artifact(
                    theorem_id=theorem_id,
                    theorem_src=theorem_src,
                    inputs=inputs,
                    backend=backend_name,
                    policy_hash=policy_decision.policy_hash,
                    action=action,
                    role=role,
                    error=backend_error or "proof backend unavailable",
                )
            )
            continue
        try:
            proof = backend.check(theorem_id=theorem_id, theorem_src=theorem_src, inputs=inputs)
        except Exception as exc:  # pragma: no cover - backend runtime fallback
            proof = _build_failed_instruction_proof_artifact(
                theorem_id=theorem_id,
                theorem_src=theorem_src,
                inputs=inputs,
                backend=backend_name,
                policy_hash=policy_decision.policy_hash,
                action=action,
                role=role,
                error=str(exc),
            )
        else:
            details = dict(proof.details)
            details.setdefault("scope", "instruction-kernel")
            details.setdefault("invariant_id", theorem_id)
            details.setdefault("policy_hash", policy_decision.policy_hash)
            details.setdefault("action_kind", action)
            details.setdefault("role", role)
            proof = proof.model_copy(update={"details": details})
        proof_artifacts.append(proof)

    ordered_proofs = sorted(
        proof_artifacts,
        key=lambda artifact: (artifact.theorem_id, artifact.proof_id),
    )
    evidence_refs = list(policy_decision.evidence_refs)
    evidence_refs.extend(
        EvidenceRef(kind="proof", ref=f"proof:{artifact.proof_id}", note=artifact.theorem_id)
        for artifact in ordered_proofs
    )
    return policy_decision.model_copy(
        update={
            "proof_artifacts": ordered_proofs,
            "evidence_refs": _sorted_unique_proof_evidence_refs(evidence_refs),
        }
    )


def authorize_action(
    *,
    role: str,
    action: str,
    writes_allowed: bool,
    approval_provided: bool,
    action_payload: dict[str, Any] | None = None,
    approval_valid: bool | None = None,
    approval_unexpired: bool | None = None,
    approval_unused: bool | None = None,
    session_active: bool = False,
    evidence_kinds: list[str] | None = None,
    warrant: str | None = None,
    evaluation_ts: str | None = None,
    emit_policy_event: PolicyEvalEventCallback | None = None,
) -> AuthorizationDecision:
    try:
        policy = load_capability_policy()
    except RuntimeError as exc:
        _raise_policy_denied(
            action=action,
            role=role,
            message="capability policy unavailable",
            context={"reason": str(exc)},
        )

    action_policy = policy.actions.get(action)
    if action_policy is None:
        _raise_policy_denied(
            action=action,
            role=role,
            message="action is not defined in capability lattice",
            context={"policy_root": str(policy.policy_root)},
        )

    role_caps = policy.role_capabilities.get(role)
    if role_caps is None:
        _raise_policy_denied(
            action=action,
            role=role,
            message="unknown role",
            context={},
        )
    if action_policy.capability not in role_caps:
        _raise_policy_denied(
            action=action,
            role=role,
            message="capability not allowed for role",
            context={"required_capability": action_policy.capability},
        )
    if action_policy.requires_writes_allowed and not writes_allowed:
        _raise_policy_denied(
            action=action,
            role=role,
            message="runtime mode does not permit action",
            context={"writes_allowed": writes_allowed},
        )
    action_payload_resolved = action_payload or {}
    action_hash = compute_action_hash(action_kind=action, action_payload=action_payload_resolved)
    approval_valid_resolved = approval_valid if approval_valid is not None else approval_provided
    approval_unexpired_resolved = (
        approval_unexpired if approval_unexpired is not None else approval_provided
    )
    approval_unused_resolved = approval_unused if approval_unused is not None else approval_provided
    approval_is_valid = (
        approval_provided
        and approval_valid_resolved
        and approval_unexpired_resolved
        and approval_unused_resolved
    )
    if action_policy.requires_approval and not approval_provided:
        raise URMError(
            code="URM_APPROVAL_REQUIRED",
            message="approval is required for this action",
            context={"role": role, "action": action},
        )
    if action_policy.requires_approval and not approval_is_valid:
        if not approval_unexpired_resolved:
            raise URMError(
                code="URM_APPROVAL_EXPIRED",
                message="approval expired",
                context={"role": role, "action": action},
            )
        raise URMError(
            code="URM_APPROVAL_INVALID",
            message="approval invalid",
            context={"role": role, "action": action},
        )

    instruction_policy = load_instruction_policy()
    policy_decision = evaluate_instruction_policy(
        policy=instruction_policy,
        context=PolicyContext.model_validate(
            {
                "role": role,
                "mode": "writes_allowed" if writes_allowed else "read_only",
                "action_kind": action,
                "action_hash": action_hash,
                "session_active": session_active,
                "capabilities_present": sorted(policy.capabilities),
                "capabilities_allowed": sorted(role_caps),
                "approval_present": approval_provided,
                "approval_valid": approval_valid_resolved,
                "approval_unexpired": approval_unexpired_resolved,
                "approval_unused": approval_unused_resolved,
                "evidence_kinds": sorted(evidence_kinds or []),
                "warrant": warrant,
                "evaluation_ts": evaluation_ts or _now_utc_z(),
            }
        ),
    )
    policy_decision = _attach_instruction_policy_proofs(
        policy_decision=policy_decision,
        action=action,
        action_hash=action_hash,
        role=role,
    )
    start_detail = {
        "policy_hash": policy_decision.policy_hash,
        "decision_code": "PENDING",
        "matched_rule_ids": [],
        "action": action,
        "trace_version": policy_decision.trace_version,
        "hard_gate_trace_version": HARD_GATE_TRACE_VERSION,
    }
    _emit_policy_event(
        callback=emit_policy_event,
        event_name="POLICY_EVAL_START",
        detail=start_detail,
    )

    decision_detail = {
        "policy_hash": policy_decision.policy_hash,
        "decision_code": policy_decision.decision_code,
        "matched_rule_ids": policy_decision.matched_rule_ids,
        "action": action,
        "trace_version": policy_decision.trace_version,
        "hard_gate_trace_version": HARD_GATE_TRACE_VERSION,
    }
    if policy_decision.decision == "deny":
        _emit_policy_event(
            callback=emit_policy_event,
            event_name="POLICY_DENIED",
            detail=decision_detail,
        )
        denial_message = (
            "approval is required for this action"
            if policy_decision.decision_code == "URM_APPROVAL_REQUIRED"
            else "instruction policy denied action"
        )
        raise URMError(
            code=policy_decision.decision_code,
            message=denial_message,
            context={
                "role": role,
                "action": action,
                "policy_hash": policy_decision.policy_hash,
                "matched_rule_ids": policy_decision.matched_rule_ids,
                "trace_version": policy_decision.trace_version,
                "input_context_hash": policy_decision.input_context_hash,
                "evidence_refs": [
                    ref.model_dump(mode="json") for ref in policy_decision.evidence_refs
                ],
            },
        )

    _emit_policy_event(
        callback=emit_policy_event,
        event_name="POLICY_EVAL_PASS",
        detail=decision_detail,
    )
    return AuthorizationDecision(
        action=action,
        hard_gate_trace_version=HARD_GATE_TRACE_VERSION,
        policy_decision=policy_decision,
    )
