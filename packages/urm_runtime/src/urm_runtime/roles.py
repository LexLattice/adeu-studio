from __future__ import annotations

from dataclasses import dataclass
from typing import Literal


@dataclass(frozen=True)
class RolePolicy:
    role: str
    transport: Literal["app_server", "exec"]
    writes_allowed_default: bool
    sandbox: Literal["read-only", "workspace-write", "danger-full-access"] | None
    allowed_tools: tuple[str, ...]


ROLE_REGISTRY: dict[str, RolePolicy] = {
    "copilot": RolePolicy(
        role="copilot",
        transport="app_server",
        writes_allowed_default=False,
        sandbox=None,
        allowed_tools=(
            "adeu.get_app_state",
            "adeu.list_templates",
            "adeu.run_workflow",
            "adeu.read_evidence",
            "urm.spawn_worker",
            "urm.set_mode",
        ),
    ),
    "pipeline_worker": RolePolicy(
        role="pipeline_worker",
        transport="exec",
        writes_allowed_default=False,
        sandbox="read-only",
        allowed_tools=(),
    ),
    "auditor": RolePolicy(
        role="auditor",
        transport="exec",
        writes_allowed_default=False,
        sandbox="read-only",
        allowed_tools=(),
    ),
}


def get_role_policy(role: str) -> RolePolicy:
    try:
        return ROLE_REGISTRY[role]
    except KeyError as exc:
        raise KeyError(f"unknown role: {role}") from exc
