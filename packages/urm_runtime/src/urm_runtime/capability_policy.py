from __future__ import annotations

import importlib.resources as resources
import json
import os
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any

from .errors import URMError

CAPABILITY_LATTICE_SCHEMA = "urm.capability.lattice.v1"
ALLOW_POLICY_SCHEMA = "urm.allow.v1"
CAPABILITY_LATTICE_FILE = "urm.capability.lattice.v1.json"
ALLOW_POLICY_FILE = "urm.allow.v1.json"


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


def authorize_action(
    *,
    role: str,
    action: str,
    writes_allowed: bool,
    approval_provided: bool,
) -> None:
    try:
        policy = load_capability_policy()
    except RuntimeError as exc:
        raise URMError(
            code="URM_POLICY_DENIED",
            message="capability policy unavailable",
            context={"action": action, "reason": str(exc)},
        ) from exc

    action_policy = policy.actions.get(action)
    if action_policy is None:
        raise URMError(
            code="URM_POLICY_DENIED",
            message="action is not defined in capability lattice",
            context={"action": action, "policy_root": str(policy.policy_root)},
        )

    role_caps = policy.role_capabilities.get(role)
    if role_caps is None:
        raise URMError(
            code="URM_POLICY_DENIED",
            message="unknown role",
            context={"role": role, "action": action},
        )
    if action_policy.capability not in role_caps:
        raise URMError(
            code="URM_POLICY_DENIED",
            message="capability not allowed for role",
            context={
                "role": role,
                "action": action,
                "required_capability": action_policy.capability,
            },
        )
    if action_policy.requires_writes_allowed and not writes_allowed:
        raise URMError(
            code="URM_POLICY_DENIED",
            message="runtime mode does not permit action",
            context={"role": role, "action": action, "writes_allowed": writes_allowed},
        )
    if action_policy.requires_approval and not approval_provided:
        raise URMError(
            code="URM_APPROVAL_REQUIRED",
            message="approval is required for this action",
            context={"role": role, "action": action},
        )
