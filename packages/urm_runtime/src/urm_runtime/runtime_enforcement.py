from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from .errors import URMError
from .orchestration_state import SCOPE_GRANULARITY_ENUM
from .roles import CHILD_DELEGATION_ROLES

RuntimeEnforcementBoundary = Literal[
    "spawn_request_boundary",
    "orchestration_state_materialization_boundary",
    "worker_visibility_materialization_boundary",
    "topology_duty_map_materialization_boundary",
]
REQUIRED_ENFORCEMENT_SURFACES: tuple[RuntimeEnforcementBoundary, ...] = (
    "spawn_request_boundary",
    "orchestration_state_materialization_boundary",
    "worker_visibility_materialization_boundary",
    "topology_duty_map_materialization_boundary",
)
MATERIALIZATION_ENFORCEMENT_SURFACES: tuple[RuntimeEnforcementBoundary, ...] = (
    "orchestration_state_materialization_boundary",
    "worker_visibility_materialization_boundary",
    "topology_duty_map_materialization_boundary",
)

ROLE_TASK_KIND_BY_ROLE: dict[str, str] = {
    "builder_worker": "write_task",
    "explorer": "analysis_task",
    "validator": "validation_task",
    "docs_helper": "docs_task",
}
ACTIVE_DELEGATION_STATUSES = frozenset({"queued", "running"})
BUILDER_REQUIRED_ARTIFACT_SURFACES = frozenset({"implementation"})
SUPPORT_PROXY_FORBIDDEN_ARTIFACT_SURFACES = frozenset({"implementation", "governance", "mixed"})

INVALID_ROLE_TASK_COMBINATION_CODE = "URM_RUNTIME_ENFORCEMENT_INVALID_ROLE_TASK_COMBINATION"
SINGLE_BUILDER_DEFAULT_VIOLATION_CODE = (
    "URM_RUNTIME_ENFORCEMENT_SINGLE_BUILDER_DEFAULT_VIOLATION"
)
SUPPORT_PROXY_AUTHORITY_CODE = "URM_RUNTIME_ENFORCEMENT_SUPPORT_PROXY_AUTHORITY"
SCOPE_KIND_INVALID_CODE = "URM_RUNTIME_ENFORCEMENT_SCOPE_KIND_INVALID"
CLAIMED_WORK_HANDOFF_INVALID_CODE = "URM_RUNTIME_ENFORCEMENT_CLAIMED_WORK_HANDOFF_INVALID"
DETERMINISTIC_DENIAL_CODES: tuple[str, ...] = (
    INVALID_ROLE_TASK_COMBINATION_CODE,
    SINGLE_BUILDER_DEFAULT_VIOLATION_CODE,
    SUPPORT_PROXY_AUTHORITY_CODE,
    SCOPE_KIND_INVALID_CODE,
    CLAIMED_WORK_HANDOFF_INVALID_CODE,
)


@dataclass(frozen=True)
class RuntimeEnforcementCandidate:
    subject_id: str
    requested_role: str
    granted_role: str
    delegation_task_kind: str
    delegated_scope_kind: str
    delegated_scope_artifact_surfaces: tuple[str, ...]
    authoritative_write_lease_granted: bool
    status: str | None = None


def validate_runtime_enforcement_candidate(
    *,
    boundary: RuntimeEnforcementBoundary,
    candidate: RuntimeEnforcementCandidate,
    parent_writes_allowed: bool | None = None,
) -> None:
    if candidate.requested_role not in CHILD_DELEGATION_ROLES:
        _raise_runtime_enforcement_error(
            code=INVALID_ROLE_TASK_COMBINATION_CODE,
            message="requested_role is not part of the released child delegation surface",
            boundary=boundary,
            subject_id=candidate.subject_id,
            context={"requested_role": candidate.requested_role},
        )
    if candidate.granted_role not in CHILD_DELEGATION_ROLES:
        _raise_runtime_enforcement_error(
            code=INVALID_ROLE_TASK_COMBINATION_CODE,
            message="granted_role is not part of the released child delegation surface",
            boundary=boundary,
            subject_id=candidate.subject_id,
            context={"granted_role": candidate.granted_role},
        )
    if candidate.granted_role != candidate.requested_role:
        _raise_runtime_enforcement_error(
            code=INVALID_ROLE_TASK_COMBINATION_CODE,
            message="granted_role must equal requested_role for released child delegation",
            boundary=boundary,
            subject_id=candidate.subject_id,
            context={
                "requested_role": candidate.requested_role,
                "granted_role": candidate.granted_role,
            },
        )
    expected_task_kind = ROLE_TASK_KIND_BY_ROLE.get(candidate.granted_role)
    if expected_task_kind is None or candidate.delegation_task_kind != expected_task_kind:
        _raise_runtime_enforcement_error(
            code=INVALID_ROLE_TASK_COMBINATION_CODE,
            message="delegation task kind is incompatible with the requested/granted role",
            boundary=boundary,
            subject_id=candidate.subject_id,
            context={
                "requested_role": candidate.requested_role,
                "granted_role": candidate.granted_role,
                "delegation_task_kind": candidate.delegation_task_kind,
                "expected_task_kind": expected_task_kind,
            },
        )
    if candidate.delegated_scope_kind not in SCOPE_GRANULARITY_ENUM:
        _raise_runtime_enforcement_error(
            code=SCOPE_KIND_INVALID_CODE,
            message="delegated scope kind is missing or invalid",
            boundary=boundary,
            subject_id=candidate.subject_id,
            context={"delegated_scope_kind": candidate.delegated_scope_kind},
        )

    artifact_surfaces = frozenset(candidate.delegated_scope_artifact_surfaces)
    if candidate.granted_role == "builder_worker":
        if not candidate.authoritative_write_lease_granted:
            _raise_runtime_enforcement_error(
                code=INVALID_ROLE_TASK_COMBINATION_CODE,
                message="builder write_task must carry an authoritative write lease grant",
                boundary=boundary,
                subject_id=candidate.subject_id,
                context={
                    "granted_role": candidate.granted_role,
                    "delegation_task_kind": candidate.delegation_task_kind,
                    "authoritative_write_lease_granted": (
                        candidate.authoritative_write_lease_granted
                    ),
                },
            )
        if parent_writes_allowed is False:
            _raise_runtime_enforcement_error(
                code=INVALID_ROLE_TASK_COMBINATION_CODE,
                message="builder write_task requires parent writes_allowed=true",
                boundary=boundary,
                subject_id=candidate.subject_id,
                context={"parent_writes_allowed": parent_writes_allowed},
            )
        if candidate.delegated_scope_kind == "artifact_surface_only":
            _raise_runtime_enforcement_error(
                code=INVALID_ROLE_TASK_COMBINATION_CODE,
                message="builder write_task requires a writable delegated scope",
                boundary=boundary,
                subject_id=candidate.subject_id,
                context={"delegated_scope_kind": candidate.delegated_scope_kind},
            )
        if artifact_surfaces != BUILDER_REQUIRED_ARTIFACT_SURFACES:
            _raise_runtime_enforcement_error(
                code=INVALID_ROLE_TASK_COMBINATION_CODE,
                message="builder write_task must target the implementation artifact surface only",
                boundary=boundary,
                subject_id=candidate.subject_id,
                context={
                    "delegated_scope_artifact_surfaces": list(
                        candidate.delegated_scope_artifact_surfaces
                    ),
                },
            )
        return

    if candidate.authoritative_write_lease_granted:
        _raise_runtime_enforcement_error(
            code=SUPPORT_PROXY_AUTHORITY_CODE,
            message="support roles may not receive authoritative write lease access",
            boundary=boundary,
            subject_id=candidate.subject_id,
            context={
                "granted_role": candidate.granted_role,
                "authoritative_write_lease_granted": candidate.authoritative_write_lease_granted,
            },
        )
    forbidden_surfaces = sorted(artifact_surfaces & SUPPORT_PROXY_FORBIDDEN_ARTIFACT_SURFACES)
    if forbidden_surfaces:
        _raise_runtime_enforcement_error(
            code=SUPPORT_PROXY_AUTHORITY_CODE,
            message="support role scope may not imply implementation or governance authority",
            boundary=boundary,
            subject_id=candidate.subject_id,
            context={
                "granted_role": candidate.granted_role,
                "delegated_scope_artifact_surfaces": forbidden_surfaces,
            },
        )


def validate_single_builder_default(
    *,
    boundary: RuntimeEnforcementBoundary,
    candidates: list[RuntimeEnforcementCandidate],
) -> None:
    active_builders = [
        candidate.subject_id
        for candidate in candidates
        if candidate.granted_role == "builder_worker"
        and candidate.authoritative_write_lease_granted
        and (candidate.status is None or candidate.status in ACTIVE_DELEGATION_STATUSES)
    ]
    if len(active_builders) > 1:
        raise URMError(
            code=SINGLE_BUILDER_DEFAULT_VIOLATION_CODE,
            message="single-builder default violated by concurrent authoritative builders",
            context={
                "boundary": boundary,
                "active_builder_ids": active_builders,
            },
        )


def validate_claimed_work_handoff_field(
    *,
    boundary: RuntimeEnforcementBoundary,
    subject_id: str,
    field_name: str,
    value: object,
    claimed_work_present: bool,
    context: dict[str, object] | None = None,
) -> str:
    if isinstance(value, str) and value.strip():
        return value
    error_context = {"field_name": field_name}
    if context is not None:
        error_context.update(context)
    if claimed_work_present:
        _raise_runtime_enforcement_error(
            code=CLAIMED_WORK_HANDOFF_INVALID_CODE,
            message=f"completed child claims outputs but is missing {field_name}",
            boundary=boundary,
            subject_id=subject_id,
            context=error_context,
        )
    _raise_runtime_enforcement_error(
        code=INVALID_ROLE_TASK_COMBINATION_CODE,
        message=f"persisted child is missing {field_name}",
        boundary=boundary,
        subject_id=subject_id,
        context=error_context,
    )


def _raise_runtime_enforcement_error(
    *,
    code: str,
    message: str,
    boundary: RuntimeEnforcementBoundary,
    subject_id: str,
    context: dict[str, object],
) -> None:
    raise URMError(
        code=code,
        message=message,
        context={
            "boundary": boundary,
            "subject_id": subject_id,
            **context,
        },
    )
