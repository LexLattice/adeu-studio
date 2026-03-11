from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, field_validator

from .hashing import canonical_json, sha256_canonical_json
from .models import NormalizedEvent

ORCHESTRATION_STATE_CONTRACT_SOURCE = "docs/LOCKED_CONTINUATION_vNEXT_PLUS56.md"
ORCHESTRATION_FOUNDATION_PACKAGE = "packages/urm_runtime"
CONTROL_PLANE_OWNER = "main_orchestrator"
SCOPE_GRANULARITY_ENUM: tuple[str, ...] = (
    "repo_wide",
    "subtree",
    "module_set",
    "file_set",
    "artifact_surface_only",
)
HANDOFF_REQUIRED_FIELDS: tuple[str, ...] = (
    "role",
    "authority_level",
    "authority_domain",
    "artifact_class",
    "artifact_surface",
    "repo_root",
    "branch_or_head",
    "scope_owned",
    "scope_remaining",
    "files_changed",
    "commands_run",
    "artifacts_produced",
    "evidence_refs",
    "status",
    "blocking_state",
    "blockers",
    "open_risks",
    "escalation_reason",
    "recommended_next_action",
)
HANDOFF_EMPTY_VALUE_POLICIES: dict[str, str] = {
    "escalation_reason": "required_field_uses_null_when_no_escalation_exists",
    "blockers": "required_field_uses_empty_array_when_none_exist",
    "files_changed": "required_field_uses_empty_array_when_none_exist",
    "commands_run": "required_field_uses_empty_array_when_none_exist",
    "artifacts_produced": "required_field_uses_empty_array_when_none_exist",
    "evidence_refs": "required_field_uses_empty_array_when_none_exist",
    "open_risks": "required_field_uses_empty_array_when_none_exist",
}
RUNTIME_EVENT_TRUTH_POLICY = (
    "runtime_events_are_source_surfaces_only_not_accepted_truth_without_"
    "canonical_reconciliation_or_explicit_governance_acceptance"
)
SUPPORT_WORKER_SURFACE_POLICY = "advisory_or_scratch_only_by_default_unless_explicitly_re_roled"
LEASE_TRANSFER_POLICY = "explicit_main_orchestrator_only"
EXECUTION_TOPOLOGY_STATE_POLICY = "reconciliation_and_state_artifact_only_not_rendered_ux_graph"
ROLE_TRANSITION_ZERO_OCCURRENCE_POLICY = (
    "deterministic_empty_artifact_required_when_no_transition_occurs"
)
ROLE_HANDOFF_ZERO_OCCURRENCE_POLICY = "deterministic_empty_artifact_required_when_no_handoff_occurs"
HANDOFF_TRUST_MODEL = "self_report_non_authoritative_until_reconciled"
RECONCILIATION_MINIMUM_CHECKS: tuple[str, ...] = (
    "recompute_effective_files_changed_from_observed_repo_state",
    "compare_claimed_scope_owned_to_observed_mutation_surface",
    "verify_evidence_refs_resolve_to_actual_outputs",
    "reject_lease_scope_sufficiency_claims_based_on_self_report_alone",
)

ScopeGranularity = Literal[
    "repo_wide",
    "subtree",
    "module_set",
    "file_set",
    "artifact_surface_only",
]
AuthorityDomain = Literal["implementation", "governance", "advisory"]
ArtifactClass = Literal["authoritative", "advisory", "scratch"]
ArtifactSurface = Literal["implementation", "governance", "mixed", "none"]
BlockingState = Literal["blocking", "non_blocking"]


class OrchestrationStateError(ValueError):
    pass


@dataclass(frozen=True)
class SessionStateInput:
    session_id: str
    status: str
    started_at: str
    ended_at: str | None
    writes_allowed: bool
    profile_id: str
    profile_version: str
    profile_policy_hash: str | None
    raw_jsonl_path: str | None
    urm_events_path: str | None
    runtime_thread_id: str | None
    active_turn_id: str | None
    last_turn_id: str | None


@dataclass(frozen=True)
class ChildStateInput:
    child_id: str
    parent_session_id: str
    status: str
    started_at: str
    ended_at: str | None
    runtime_role: str
    parent_turn_id: str | None
    parent_stream_id: str
    child_stream_id: str
    child_thread_id: str | None
    queue_seq: int
    dispatch_seq: int | None
    lease_id: str | None
    dispatch_phase: str | None
    profile_id: str | None
    profile_version: str | None
    inherited_policy_hash: str | None
    capabilities_allowed: tuple[str, ...]
    raw_jsonl_path: str | None
    urm_events_path: str | None
    error_code: str | None
    error_message: str | None


@dataclass(frozen=True)
class EventStreamHeadInput:
    stream_id: str
    path: str
    event_count: int
    last_seq: int
    last_event: str | None
    last_event_ref: str | None
    last_ts: str | None


class ScopeDescriptor(BaseModel):
    model_config = ConfigDict(extra="forbid")

    kind: ScopeGranularity
    values: list[str] = Field(default_factory=list)
    artifact_surfaces: list[ArtifactSurface] = Field(default_factory=list)
    rationale: str | None = None


class EventStreamCursor(BaseModel):
    model_config = ConfigDict(extra="forbid")

    stream_id: str = Field(min_length=1)
    path: str = Field(min_length=1)
    event_count: int = Field(ge=0)
    last_seq: int = Field(ge=0)
    last_event: str | None = None
    last_event_ref: str | None = None
    last_ts: str | None = None


class EventCursor(BaseModel):
    model_config = ConfigDict(extra="forbid")

    streams: list[EventStreamCursor] = Field(default_factory=list)


class ContinuationBridgeRef(BaseModel):
    model_config = ConfigDict(extra="forbid")

    bridge_kind: Literal["audit_stream_bridge"] = "audit_stream_bridge"
    bridge_ref: str = Field(min_length=1)
    source_stream_id: str = Field(min_length=1)
    target_stream_id: str = Field(min_length=1)
    bridge_path: str = Field(min_length=1)
    reason: Literal["recovery_audit_events_present"] = "recovery_audit_events_present"


class ActorState(BaseModel):
    model_config = ConfigDict(extra="forbid")

    actor_id: str = Field(min_length=1)
    role: str = Field(min_length=1)
    runtime_role: str = Field(min_length=1)
    authority_level: str = Field(min_length=1)
    authority_domain: AuthorityDomain
    status: str = Field(min_length=1)
    user_facing_boundary: bool
    authoritative_write_access: bool
    session_id: str = Field(min_length=1)
    parent_session_id: str | None = None
    stream_id: str = Field(min_length=1)
    worker_session_id: str | None = None
    scope_owned: ScopeDescriptor


class CompactionSeam(BaseModel):
    model_config = ConfigDict(extra="forbid")

    seam_kind: Literal["audit_stream_bridge"] = "audit_stream_bridge"
    source_stream_id: str = Field(min_length=1)
    target_stream_id: str = Field(min_length=1)
    bridge_ref: str = Field(min_length=1)
    bridge_path: str = Field(min_length=1)


class TopologyEdge(BaseModel):
    model_config = ConfigDict(extra="forbid")

    edge_kind: Literal["delegates_to"] = "delegates_to"
    source_actor_id: str = Field(min_length=1)
    target_actor_id: str = Field(min_length=1)
    parent_session_id: str = Field(min_length=1)
    queue_seq: int = Field(ge=0)
    dispatch_seq: int | None = Field(default=None, ge=1)
    lease_id: str | None = None
    authoritative_write_access: bool = False


class LeaseHolderState(BaseModel):
    model_config = ConfigDict(extra="forbid")

    actor_id: str = Field(min_length=1)
    role: str = Field(min_length=1)
    runtime_role: str = Field(min_length=1)
    authority_level: str = Field(min_length=1)
    authority_domain: AuthorityDomain
    lease_kind: Literal["exclusive"] = "exclusive"
    scope_owned: ScopeDescriptor


class DispatchLeaseObservation(BaseModel):
    model_config = ConfigDict(extra="forbid")

    child_id: str = Field(min_length=1)
    parent_session_id: str = Field(min_length=1)
    parent_stream_id: str = Field(min_length=1)
    child_stream_id: str = Field(min_length=1)
    worker_session_id: str | None = None
    status: str = Field(min_length=1)
    queue_seq: int = Field(ge=0)
    dispatch_seq: int | None = Field(default=None, ge=1)
    lease_id: str | None = None
    phase: str | None = None
    authoritative_write_access: bool = False
    scope_owned: ScopeDescriptor


class RoleTransitionEntry(BaseModel):
    model_config = ConfigDict(extra="forbid")

    from_role: str = Field(min_length=1)
    to_role: str = Field(min_length=1)
    authority_level_before: str = Field(min_length=1)
    authority_level_after: str = Field(min_length=1)
    scope_owned: list[ScopeDescriptor]
    reason: str = Field(min_length=1)
    effective_time: str = Field(min_length=1)
    granted_by: str = Field(min_length=1)

    @field_validator("scope_owned")
    @classmethod
    def _validate_scope_owned(cls, value: list[ScopeDescriptor]) -> list[ScopeDescriptor]:
        if not value:
            raise ValueError("scope_owned must contain at least one scope descriptor")
        return value


class RoleHandoffEntry(BaseModel):
    model_config = ConfigDict(extra="forbid")

    role: str = Field(min_length=1)
    authority_level: str = Field(min_length=1)
    authority_domain: AuthorityDomain
    artifact_class: ArtifactClass
    artifact_surface: ArtifactSurface
    repo_root: str = Field(min_length=1)
    branch_or_head: str = Field(min_length=1)
    scope_owned: list[ScopeDescriptor]
    scope_remaining: list[ScopeDescriptor]
    files_changed: list[str]
    commands_run: list[str]
    artifacts_produced: list[str]
    evidence_refs: list[str]
    status: str = Field(min_length=1)
    blocking_state: BlockingState
    blockers: list[str]
    open_risks: list[str]
    escalation_reason: str | None = None
    recommended_next_action: str = Field(min_length=1)

    @field_validator("escalation_reason")
    @classmethod
    def _validate_escalation_reason(cls, value: str | None) -> str | None:
        if value is None:
            return None
        normalized = value.strip()
        if not normalized:
            raise ValueError("escalation_reason must be null or a non-empty string")
        return normalized


class OrchestrationStateSnapshot(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: Literal["orchestration_state_snapshot@1"] = Field(
        default="orchestration_state_snapshot@1",
        alias="schema",
    )
    contract_source: str = ORCHESTRATION_STATE_CONTRACT_SOURCE
    orchestration_foundation_package: str = ORCHESTRATION_FOUNDATION_PACKAGE
    control_plane_owner: Literal["main_orchestrator"] = CONTROL_PLANE_OWNER
    single_writer_default_required: bool = True
    single_writer_default_enforced: bool
    worker_direct_user_boundary_forbidden: bool = True
    support_worker_surface_policy: str = SUPPORT_WORKER_SURFACE_POLICY
    runtime_event_truth_policy: str = RUNTIME_EVENT_TRUTH_POLICY
    scope_granularity_enum: list[ScopeGranularity] = Field(
        default_factory=lambda: list(SCOPE_GRANULARITY_ENUM)
    )
    orchestrator_session_id: str = Field(min_length=1)
    worker_session_id: str | None = None
    parent_session_id: str | None = None
    event_cursor: EventCursor
    last_reconciled_event: str | None = None
    continuation_bridge_ref: ContinuationBridgeRef | None = None
    session_status: str = Field(min_length=1)
    writes_allowed: bool
    profile_id: str = Field(min_length=1)
    profile_version: str = Field(min_length=1)
    profile_policy_hash: str | None = None
    current_authoritative_holder_actor_id: str | None = None
    current_roles: list[ActorState] = Field(default_factory=list)


class ExecutionTopologyState(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: Literal["execution_topology_state@1"] = Field(
        default="execution_topology_state@1",
        alias="schema",
    )
    contract_source: str = ORCHESTRATION_STATE_CONTRACT_SOURCE
    orchestration_foundation_package: str = ORCHESTRATION_FOUNDATION_PACKAGE
    execution_topology_state_policy: str = EXECUTION_TOPOLOGY_STATE_POLICY
    state_origin: Literal["urm_runtime"] = "urm_runtime"
    reconciliation_status: Literal["reconciled_from_runtime_state"] = (
        "reconciled_from_runtime_state"
    )
    last_reconciled_event: str | None = None
    continuation_bridge_ref: ContinuationBridgeRef | None = None
    nodes: list[ActorState] = Field(default_factory=list)
    edges: list[TopologyEdge] = Field(default_factory=list)
    compaction_seams: list[CompactionSeam] = Field(default_factory=list)


class WriteLeaseState(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: Literal["write_lease_state@1"] = Field(
        default="write_lease_state@1",
        alias="schema",
    )
    contract_source: str = ORCHESTRATION_STATE_CONTRACT_SOURCE
    orchestration_foundation_package: str = ORCHESTRATION_FOUNDATION_PACKAGE
    control_plane_owner: Literal["main_orchestrator"] = CONTROL_PLANE_OWNER
    single_writer_default_required: bool = True
    single_writer_default_enforced: bool
    lease_transfer_policy: str = LEASE_TRANSFER_POLICY
    support_worker_surface_policy: str = SUPPORT_WORKER_SURFACE_POLICY
    active_authoritative_writer_count: int = Field(ge=0)
    current_authoritative_holder: LeaseHolderState | None = None
    dispatch_lease_observations: list[DispatchLeaseObservation] = Field(default_factory=list)
    lease_scope_sufficiency_self_report_accepted: bool = False


class RoleTransitionRecord(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: Literal["role_transition_record@1"] = Field(
        default="role_transition_record@1",
        alias="schema",
    )
    contract_source: str = ORCHESTRATION_STATE_CONTRACT_SOURCE
    required_transition_fields: list[str] = Field(
        default_factory=lambda: [
            "from_role",
            "to_role",
            "authority_level_before",
            "authority_level_after",
            "scope_owned",
            "reason",
            "effective_time",
            "granted_by",
        ]
    )
    zero_occurrence_policy: str = ROLE_TRANSITION_ZERO_OCCURRENCE_POLICY
    entries: list[RoleTransitionEntry] = Field(default_factory=list)


class RoleHandoffEnvelope(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: Literal["role_handoff_envelope@1"] = Field(
        default="role_handoff_envelope@1",
        alias="schema",
    )
    contract_source: str = ORCHESTRATION_STATE_CONTRACT_SOURCE
    trust_model: str = HANDOFF_TRUST_MODEL
    reconciliation_required: bool = True
    required_fields: list[str] = Field(default_factory=lambda: list(HANDOFF_REQUIRED_FIELDS))
    empty_value_policies: dict[str, str] = Field(
        default_factory=lambda: dict(HANDOFF_EMPTY_VALUE_POLICIES)
    )
    reconciliation_minimum_checks: list[str] = Field(
        default_factory=lambda: list(RECONCILIATION_MINIMUM_CHECKS)
    )
    zero_occurrence_policy: str = ROLE_HANDOFF_ZERO_OCCURRENCE_POLICY
    entries: list[RoleHandoffEntry] = Field(default_factory=list)


@dataclass(frozen=True)
class MaterializedArtifact:
    path: str
    hash: str
    payload: dict[str, Any]


@dataclass(frozen=True)
class MaterializedOrchestrationArtifacts:
    session_id: str
    output_root: str
    orchestration_state_snapshot: MaterializedArtifact
    execution_topology_state: MaterializedArtifact
    write_lease_state: MaterializedArtifact
    role_transition_record: MaterializedArtifact
    role_handoff_envelope: MaterializedArtifact


def read_event_stream_head(*, path: Path, relative_path: str) -> EventStreamHeadInput | None:
    if not path.exists():
        return None
    stream_id: str | None = None
    event_count = 0
    last_event: str | None = None
    last_seq = 0
    last_ref: str | None = None
    last_ts: str | None = None
    with path.open("r", encoding="utf-8", errors="replace") as handle:
        for lineno, line in enumerate(handle, start=1):
            stripped = line.strip()
            if not stripped:
                continue
            try:
                payload = json.loads(stripped)
            except json.JSONDecodeError as exc:
                raise OrchestrationStateError(
                    f"invalid event JSON in {relative_path}:{lineno}"
                ) from exc
            try:
                event = NormalizedEvent.model_validate(payload)
            except Exception as exc:  # pragma: no cover - pydantic error surface
                raise OrchestrationStateError(
                    f"invalid normalized event in {relative_path}:{lineno}"
                ) from exc
            stream_id = event.stream_id
            event_count += 1
            last_event = event.event
            last_seq = event.seq
            last_ref = f"event:{event.stream_id}#{event.seq}"
            last_ts = event.ts.isoformat()
    if stream_id is None:
        return None
    return EventStreamHeadInput(
        stream_id=stream_id,
        path=relative_path,
        event_count=event_count,
        last_seq=last_seq,
        last_event=last_event,
        last_event_ref=last_ref,
        last_ts=last_ts,
    )


def build_orchestration_artifacts(
    *,
    session: SessionStateInput,
    children: list[ChildStateInput],
    event_streams: list[EventStreamHeadInput],
    repo_root: str,
    branch_or_head: str,
    prior_transition_entries: list[dict[str, Any]] | None = None,
) -> tuple[
    OrchestrationStateSnapshot,
    ExecutionTopologyState,
    WriteLeaseState,
    RoleTransitionRecord,
    RoleHandoffEnvelope,
]:
    del branch_or_head  # reserved for future handoff materialization.
    event_cursor = _build_event_cursor(event_streams=event_streams)
    last_reconciled_event, effective_time = _resolve_last_reconciled_event(
        event_streams=event_streams,
        fallback_ts=session.ended_at or session.started_at,
    )
    continuation_bridge_ref = _build_continuation_bridge_ref(
        session_id=session.session_id,
        event_streams=event_streams,
    )
    current_worker = _select_current_worker(children=children)
    current_worker_session_id = (
        current_worker.child_thread_id if current_worker is not None else None
    )
    current_authoritative_holder = _build_current_authoritative_holder(
        session=session,
        repo_root=repo_root,
    )
    active_authoritative_writer_count = 1 if current_authoritative_holder is not None else 0
    if active_authoritative_writer_count > 1:
        raise OrchestrationStateError("multiple authoritative writers active by default")
    if any(child.parent_session_id != session.session_id for child in children):
        raise OrchestrationStateError("child state parent_session_id drift detected")
    actor_states = _build_actor_states(
        session=session,
        children=children,
        repo_root=repo_root,
        writes_allowed=session.writes_allowed,
    )
    write_lease_state = WriteLeaseState(
        single_writer_default_enforced=active_authoritative_writer_count <= 1,
        active_authoritative_writer_count=active_authoritative_writer_count,
        current_authoritative_holder=current_authoritative_holder,
        dispatch_lease_observations=[
            DispatchLeaseObservation(
                child_id=child.child_id,
                parent_session_id=child.parent_session_id,
                parent_stream_id=child.parent_stream_id,
                child_stream_id=child.child_stream_id,
                worker_session_id=child.child_thread_id,
                status=child.status,
                queue_seq=child.queue_seq,
                dispatch_seq=child.dispatch_seq,
                lease_id=child.lease_id,
                phase=child.dispatch_phase,
                authoritative_write_access=False,
                scope_owned=_support_worker_scope(),
            )
            for child in sorted(children, key=_child_order_key)
        ],
    )
    transition_record = _build_role_transition_record(
        current_write_lease_state=write_lease_state,
        effective_time=effective_time,
        prior_entries=prior_transition_entries or [],
    )
    handoff_envelope = RoleHandoffEnvelope(entries=[])
    snapshot = OrchestrationStateSnapshot(
        single_writer_default_enforced=write_lease_state.single_writer_default_enforced,
        orchestrator_session_id=session.session_id,
        worker_session_id=current_worker_session_id,
        parent_session_id=session.session_id,
        event_cursor=event_cursor,
        last_reconciled_event=last_reconciled_event,
        continuation_bridge_ref=continuation_bridge_ref,
        session_status=session.status,
        writes_allowed=session.writes_allowed,
        profile_id=session.profile_id,
        profile_version=session.profile_version,
        profile_policy_hash=session.profile_policy_hash,
        current_authoritative_holder_actor_id=(
            current_authoritative_holder.actor_id
            if current_authoritative_holder is not None
            else None
        ),
        current_roles=actor_states,
    )
    topology = ExecutionTopologyState(
        last_reconciled_event=last_reconciled_event,
        continuation_bridge_ref=continuation_bridge_ref,
        nodes=actor_states,
        edges=[
            TopologyEdge(
                source_actor_id=session.session_id,
                target_actor_id=child.child_id,
                parent_session_id=session.session_id,
                queue_seq=child.queue_seq,
                dispatch_seq=child.dispatch_seq,
                lease_id=child.lease_id,
                authoritative_write_access=False,
            )
            for child in sorted(children, key=_child_order_key)
        ],
        compaction_seams=(
            [
                CompactionSeam(
                    source_stream_id=continuation_bridge_ref.source_stream_id,
                    target_stream_id=continuation_bridge_ref.target_stream_id,
                    bridge_ref=continuation_bridge_ref.bridge_ref,
                    bridge_path=continuation_bridge_ref.bridge_path,
                )
            ]
            if continuation_bridge_ref is not None
            else []
        ),
    )
    return snapshot, topology, write_lease_state, transition_record, handoff_envelope


def materialize_orchestration_artifacts(
    *,
    output_root: Path,
    output_root_relative: str,
    session: SessionStateInput,
    children: list[ChildStateInput],
    event_streams: list[EventStreamHeadInput],
    repo_root: str,
    branch_or_head: str,
) -> MaterializedOrchestrationArtifacts:
    previous_transition_record_path = output_root / "role_transition_record.json"
    prior_transition_entries = _load_prior_transition_entries(path=previous_transition_record_path)
    (
        orchestration_state_snapshot,
        execution_topology_state,
        write_lease_state,
        role_transition_record,
        role_handoff_envelope,
    ) = build_orchestration_artifacts(
        session=session,
        children=children,
        event_streams=event_streams,
        repo_root=repo_root,
        branch_or_head=branch_or_head,
        prior_transition_entries=prior_transition_entries,
    )
    output_root.mkdir(parents=True, exist_ok=True)
    snapshot_artifact = _write_artifact(
        output_root=output_root,
        output_root_relative=output_root_relative,
        filename="orchestration_state_snapshot.json",
        model=orchestration_state_snapshot,
    )
    topology_artifact = _write_artifact(
        output_root=output_root,
        output_root_relative=output_root_relative,
        filename="execution_topology_state.json",
        model=execution_topology_state,
    )
    write_lease_artifact = _write_artifact(
        output_root=output_root,
        output_root_relative=output_root_relative,
        filename="write_lease_state.json",
        model=write_lease_state,
    )
    transition_artifact = _write_artifact(
        output_root=output_root,
        output_root_relative=output_root_relative,
        filename="role_transition_record.json",
        model=role_transition_record,
    )
    handoff_artifact = _write_artifact(
        output_root=output_root,
        output_root_relative=output_root_relative,
        filename="role_handoff_envelope.json",
        model=role_handoff_envelope,
    )
    return MaterializedOrchestrationArtifacts(
        session_id=session.session_id,
        output_root=output_root_relative,
        orchestration_state_snapshot=snapshot_artifact,
        execution_topology_state=topology_artifact,
        write_lease_state=write_lease_artifact,
        role_transition_record=transition_artifact,
        role_handoff_envelope=handoff_artifact,
    )


def _write_artifact(
    *,
    output_root: Path,
    output_root_relative: str,
    filename: str,
    model: BaseModel,
) -> MaterializedArtifact:
    payload = model.model_dump(mode="json", by_alias=True)
    encoded = canonical_json(payload)
    path = output_root / filename
    path.write_text(encoded, encoding="utf-8")
    return MaterializedArtifact(
        path=f"{output_root_relative}/{filename}",
        hash=sha256_canonical_json(payload),
        payload=payload,
    )


def _build_event_cursor(*, event_streams: list[EventStreamHeadInput]) -> EventCursor:
    cursors = [
        EventStreamCursor(
            stream_id=stream.stream_id,
            path=stream.path,
            event_count=stream.event_count,
            last_seq=stream.last_seq,
            last_event=stream.last_event,
            last_event_ref=stream.last_event_ref,
            last_ts=stream.last_ts,
        )
        for stream in sorted(event_streams, key=lambda item: item.stream_id)
    ]
    return EventCursor(streams=cursors)


def _resolve_last_reconciled_event(
    *,
    event_streams: list[EventStreamHeadInput],
    fallback_ts: str,
) -> tuple[str | None, str]:
    ordered = sorted(
        (
            stream
            for stream in event_streams
            if stream.last_event_ref is not None and stream.last_ts is not None
        ),
        key=lambda item: (item.last_ts or "", item.last_seq, item.stream_id),
    )
    if not ordered:
        return None, fallback_ts
    last = ordered[-1]
    return last.last_event_ref, last.last_ts or fallback_ts


def _build_continuation_bridge_ref(
    *,
    session_id: str,
    event_streams: list[EventStreamHeadInput],
) -> ContinuationBridgeRef | None:
    audit_stream_id = f"urm_audit:{session_id}"
    for stream in event_streams:
        if stream.stream_id != audit_stream_id or stream.last_event_ref is None:
            continue
        return ContinuationBridgeRef(
            bridge_ref=stream.last_event_ref,
            source_stream_id=f"copilot:{session_id}",
            target_stream_id=stream.stream_id,
            bridge_path=stream.path,
        )
    return None


def _build_current_authoritative_holder(
    *,
    session: SessionStateInput,
    repo_root: str,
) -> LeaseHolderState | None:
    if not session.writes_allowed:
        return None
    return LeaseHolderState(
        actor_id=session.session_id,
        role="main_orchestrator",
        runtime_role="copilot",
        authority_level="governance_authority",
        authority_domain="governance",
        scope_owned=_orchestrator_scope(repo_root=repo_root, writes_allowed=True),
    )


def _build_actor_states(
    *,
    session: SessionStateInput,
    children: list[ChildStateInput],
    repo_root: str,
    writes_allowed: bool,
) -> list[ActorState]:
    actors = [
        ActorState(
            actor_id=session.session_id,
            role="main_orchestrator",
            runtime_role="copilot",
            authority_level="governance_authority",
            authority_domain="governance",
            status=session.status,
            user_facing_boundary=True,
            authoritative_write_access=writes_allowed,
            session_id=session.session_id,
            parent_session_id=None,
            stream_id=f"copilot:{session.session_id}",
            worker_session_id=session.runtime_thread_id,
            scope_owned=_orchestrator_scope(repo_root=repo_root, writes_allowed=writes_allowed),
        )
    ]
    for child in sorted(children, key=_child_order_key):
        actors.append(
            ActorState(
                actor_id=child.child_id,
                role="support_worker",
                runtime_role=child.runtime_role,
                authority_level="advisory_information_only",
                authority_domain="advisory",
                status=child.status,
                user_facing_boundary=False,
                authoritative_write_access=False,
                session_id=child.parent_session_id,
                parent_session_id=child.parent_session_id,
                stream_id=child.child_stream_id,
                worker_session_id=child.child_thread_id,
                scope_owned=_support_worker_scope(),
            )
        )
    return actors


def _orchestrator_scope(*, repo_root: str, writes_allowed: bool) -> ScopeDescriptor:
    if writes_allowed:
        return ScopeDescriptor(
            kind="repo_wide",
            values=[repo_root],
            artifact_surfaces=["implementation"],
            rationale=(
                "orchestrator session writes are enabled; "
                "no narrower runtime write lease exists"
            ),
        )
    return ScopeDescriptor(
        kind="artifact_surface_only",
        values=[],
        artifact_surfaces=["governance"],
        rationale=(
            "orchestrator remains the sole user-facing governance surface "
            "with writes disabled"
        ),
    )


def _support_worker_scope() -> ScopeDescriptor:
    return ScopeDescriptor(
        kind="artifact_surface_only",
        values=[],
        artifact_surfaces=["none"],
        rationale=(
            "support workers remain advisory_or_scratch_only_by_default "
            "unless explicitly re-roled"
        ),
    )


def _select_current_worker(*, children: list[ChildStateInput]) -> ChildStateInput | None:
    ordered = sorted(children, key=_current_worker_order_key)
    if not ordered:
        return None
    return ordered[0]


def _current_worker_order_key(child: ChildStateInput) -> tuple[int, int, int, str, str]:
    if child.status == "running":
        status_rank = 0
    elif child.status == "queued":
        status_rank = 1
    elif child.status == "completed":
        status_rank = 2
    else:
        status_rank = 3
    dispatch_rank = child.dispatch_seq if child.dispatch_seq is not None else 2**30
    return (status_rank, dispatch_rank, child.queue_seq, child.started_at, child.child_id)


def _child_order_key(child: ChildStateInput) -> tuple[int, int, str]:
    dispatch_rank = child.dispatch_seq if child.dispatch_seq is not None else 2**30
    return (dispatch_rank, child.queue_seq, child.child_id)


def _load_prior_transition_entries(*, path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise OrchestrationStateError("invalid prior role_transition_record artifact") from exc
    record = RoleTransitionRecord.model_validate(payload)
    return [entry.model_dump(mode="json") for entry in record.entries]


def _build_role_transition_record(
    *,
    current_write_lease_state: WriteLeaseState,
    effective_time: str,
    prior_entries: list[dict[str, Any]],
) -> RoleTransitionRecord:
    entries = [RoleTransitionEntry.model_validate(entry) for entry in prior_entries]
    previous = entries[-1] if entries else None
    previous_role = previous.to_role if previous is not None else "main_orchestrator"
    previous_authority = (
        previous.authority_level_after
        if previous is not None
        else "governance_authority_without_write_lease"
    )
    current_holder = current_write_lease_state.current_authoritative_holder
    current_role = current_holder.role if current_holder is not None else "main_orchestrator"
    current_authority = (
        current_holder.authority_level
        if current_holder is not None
        else "governance_authority_without_write_lease"
    )
    authority_changed = (previous is None and current_holder is not None) or (
        previous is not None and previous.authority_level_after != current_authority
    )
    if previous is None and current_holder is None:
        authority_changed = False
    if authority_changed:
        scope_owned = (
            [current_holder.scope_owned]
            if current_holder is not None
            else [
                ScopeDescriptor(
                    kind="artifact_surface_only",
                    values=[],
                    artifact_surfaces=["governance"],
                    rationale="authoritative write lease absent",
                )
            ]
        )
        entries.append(
            RoleTransitionEntry(
                from_role=previous_role,
                to_role=current_role,
                authority_level_before=previous_authority,
                authority_level_after=current_authority,
                scope_owned=scope_owned,
                reason="authoritative_write_access_changed",
                effective_time=effective_time,
                granted_by=CONTROL_PLANE_OWNER,
            )
        )
    return RoleTransitionRecord(entries=entries)
