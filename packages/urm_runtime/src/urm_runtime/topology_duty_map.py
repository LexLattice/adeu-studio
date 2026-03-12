from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field

from .hashing import canonical_json, sha256_canonical_json
from .orchestration_state import (
    ActorState,
    AuthorityDomain,
    BlockingState,
    CompactionSeam,
    ContinuationBridgeRef,
    EventStreamHeadInput,
    ExecutionTopologyState,
    MaterializedArtifact,
    RoleHandoffEntry,
    RoleHandoffEnvelope,
    ScopeDescriptor,
    TopologyEdge,
    WriteLeaseState,
)
from .worker_visibility import VisibilityLaneState, WorkerVisibilityEntry, WorkerVisibilityState

TOPOLOGY_DUTY_MAP_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS59.md#v35d_topology_duty_map_contract@1"
)
TOPOLOGY_DUTY_MAP_FOUNDATION_PACKAGE = "packages/urm_runtime"
TOPOLOGY_DUTY_MAP_SCHEMA = "topology_duty_map_state@1"
TOPOLOGY_SURFACE_AUTHORITY_POLICY = (
    "derived_from_canonical_execution_state_only_non_authoritative_visualization"
)
EVENT_STREAM_DRILLDOWN_POLICY = (
    "event_streams_are_provenance_targets_only_not_topology_projection_truth_inputs"
)
TOPOLOGY_DUTY_MAP_STATE_ORIGIN = (
    "derived_from_execution_topology_state_write_lease_state_worker_visibility_state_"
    "and_role_handoff_envelope"
)


class TopologyDutyMapStateError(ValueError):
    pass


@dataclass(frozen=True)
class TopologyDutyMapSourceArtifacts:
    execution_topology_state_path: str
    write_lease_state_path: str
    worker_visibility_state_path: str
    role_handoff_envelope_path: str


class TopologyProvenanceRef(BaseModel):
    model_config = ConfigDict(extra="forbid")

    ref_kind: Literal["artifact", "event_stream"]
    path: str = Field(min_length=1)
    source_schema: str | None = None
    stream_id: str | None = None
    event_ref: str | None = None


class TopologyDutyMapNode(BaseModel):
    model_config = ConfigDict(extra="forbid")

    actor_id: str = Field(min_length=1)
    role: str = Field(min_length=1)
    authority_domain: AuthorityDomain
    authority_level: str = Field(min_length=1)
    current_duty: str = Field(min_length=1)
    scope_owned: ScopeDescriptor
    blocking_state: BlockingState
    state_origin: str = Field(min_length=1)
    reconciliation_status: str = Field(min_length=1)
    last_updated_at: str | None = None
    last_reconciled_at: str | None = None
    provenance_refs: list[TopologyProvenanceRef] = Field(default_factory=list)
    user_facing_boundary: bool
    authoritative_write_access: bool = False
    status: str = Field(min_length=1)
    blockers: list[str] = Field(default_factory=list)


class TopologyDutyMapEdge(BaseModel):
    model_config = ConfigDict(extra="forbid")

    source_actor_id: str = Field(min_length=1)
    target_actor_id: str = Field(min_length=1)
    edge_kind: str = Field(min_length=1)
    blocking_state: BlockingState
    state_origin: str = Field(min_length=1)
    reconciliation_status: str = Field(min_length=1)
    last_updated_at: str | None = None
    last_reconciled_at: str | None = None
    provenance_refs: list[TopologyProvenanceRef] = Field(default_factory=list)
    authoritative_write_access: bool = False
    requested_role: str | None = None
    granted_role: str | None = None
    delegation_task_kind: str | None = None
    blockers: list[str] = Field(default_factory=list)


class TopologyDutyMapState(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: Literal["topology_duty_map_state@1"] = Field(
        default=TOPOLOGY_DUTY_MAP_SCHEMA,
        alias="schema",
    )
    contract_source: str = TOPOLOGY_DUTY_MAP_CONTRACT_SOURCE
    topology_duty_map_foundation_package: str = TOPOLOGY_DUTY_MAP_FOUNDATION_PACKAGE
    read_only_topology_required: bool = True
    topology_surface_authority_policy: str = TOPOLOGY_SURFACE_AUTHORITY_POLICY
    event_stream_drilldown_policy: str = EVENT_STREAM_DRILLDOWN_POLICY
    orchestrator_session_id: str = Field(min_length=1)
    parent_session_id: str = Field(min_length=1)
    current_authoritative_holder_actor_id: str | None = None
    last_reconciled_event: str | None = None
    continuation_bridge_ref: ContinuationBridgeRef | None = None
    compaction_seams: list[CompactionSeam] = Field(default_factory=list)
    nodes: list[TopologyDutyMapNode] = Field(default_factory=list)
    edges: list[TopologyDutyMapEdge] = Field(default_factory=list)


@dataclass(frozen=True)
class MaterializedTopologyDutyMapArtifacts:
    session_id: str
    output_root: str
    topology_duty_map_state: MaterializedArtifact


def materialize_topology_duty_map_artifacts(
    *,
    output_root: Path,
    output_root_relative: str,
    execution_topology_state: ExecutionTopologyState,
    write_lease_state: WriteLeaseState,
    worker_visibility_state: WorkerVisibilityState,
    role_handoff_envelope: RoleHandoffEnvelope,
    source_artifacts: TopologyDutyMapSourceArtifacts,
    event_streams: list[EventStreamHeadInput] | None = None,
) -> MaterializedTopologyDutyMapArtifacts:
    topology_duty_map_state = build_topology_duty_map_state(
        execution_topology_state=execution_topology_state,
        write_lease_state=write_lease_state,
        worker_visibility_state=worker_visibility_state,
        role_handoff_envelope=role_handoff_envelope,
        source_artifacts=source_artifacts,
        event_streams=event_streams or [],
    )
    output_root.mkdir(parents=True, exist_ok=True)
    artifact = _write_artifact(
        output_root=output_root,
        output_root_relative=output_root_relative,
        filename="topology_duty_map_state.json",
        model=topology_duty_map_state,
    )
    return MaterializedTopologyDutyMapArtifacts(
        session_id=worker_visibility_state.parent_session_id,
        output_root=output_root_relative,
        topology_duty_map_state=artifact,
    )


def build_topology_duty_map_state(
    *,
    execution_topology_state: ExecutionTopologyState,
    write_lease_state: WriteLeaseState,
    worker_visibility_state: WorkerVisibilityState,
    role_handoff_envelope: RoleHandoffEnvelope,
    source_artifacts: TopologyDutyMapSourceArtifacts,
    event_streams: list[EventStreamHeadInput] | None = None,
) -> TopologyDutyMapState:
    event_streams = event_streams or []
    orchestrator = _resolve_orchestrator_node(nodes=execution_topology_state.nodes)
    if worker_visibility_state.orchestrator_session_id != orchestrator.actor_id:
        raise TopologyDutyMapStateError("visibility orchestrator_session_id drift detected")
    if worker_visibility_state.parent_session_id != orchestrator.actor_id:
        raise TopologyDutyMapStateError("visibility parent_session_id drift detected")

    child_nodes = [
        node for node in execution_topology_state.nodes if node.actor_id != orchestrator.actor_id
    ]
    visibility_by_worker = {worker.worker_id: worker for worker in worker_visibility_state.workers}
    topology_child_ids = {node.actor_id for node in child_nodes}
    visibility_child_ids = set(visibility_by_worker)
    if topology_child_ids != visibility_child_ids:
        raise TopologyDutyMapStateError("visibility workers do not match topology child nodes")
    if any(node.user_facing_boundary for node in child_nodes):
        raise TopologyDutyMapStateError("worker direct user boundary drift detected")
    if any(worker.direct_user_boundary_established for worker in worker_visibility_state.workers):
        raise TopologyDutyMapStateError("worker visibility direct user boundary drift detected")

    _validate_edges(
        edges=execution_topology_state.edges,
        orchestrator_actor_id=orchestrator.actor_id,
        expected_child_ids=topology_child_ids,
    )
    current_holder_actor_id = (
        write_lease_state.current_authoritative_holder.actor_id
        if write_lease_state.current_authoritative_holder is not None
        else None
    )
    _validate_current_holder_alignment(
        nodes=execution_topology_state.nodes,
        current_holder_actor_id=current_holder_actor_id,
    )
    event_heads_by_stream = {stream.stream_id: stream for stream in event_streams}
    last_reconciled_at = _resolve_last_reconciled_at(
        last_reconciled_event=execution_topology_state.last_reconciled_event,
        event_streams=event_streams,
    )
    handoff_by_worker = _match_handoff_entries(
        workers=worker_visibility_state.workers,
        handoff_entries=role_handoff_envelope.entries,
    )
    nodes = [
        _build_orchestrator_node(
            orchestrator=orchestrator,
            current_holder_actor_id=current_holder_actor_id,
            execution_topology_state_path=source_artifacts.execution_topology_state_path,
            write_lease_state_path=source_artifacts.write_lease_state_path,
            worker_visibility_state_path=source_artifacts.worker_visibility_state_path,
            event_head=event_heads_by_stream.get(orchestrator.stream_id),
            last_reconciled_at=last_reconciled_at,
            reconciliation_status=execution_topology_state.reconciliation_status,
        )
    ]
    for child_node in child_nodes:
        worker_visibility = visibility_by_worker[child_node.actor_id]
        nodes.append(
            _build_child_node(
                node=child_node,
                worker_visibility=worker_visibility,
                matched_handoff=handoff_by_worker.get(child_node.actor_id),
                current_holder_actor_id=current_holder_actor_id,
                source_artifacts=source_artifacts,
                event_head=event_heads_by_stream.get(child_node.stream_id),
                last_reconciled_at=last_reconciled_at,
            )
        )
    edges = [
        _build_edge(
            edge=edge,
            worker_visibility=visibility_by_worker[edge.target_actor_id],
            matched_handoff=handoff_by_worker.get(edge.target_actor_id),
            source_artifacts=source_artifacts,
            event_head=event_heads_by_stream.get(
                _target_stream_id(
                    child_nodes=child_nodes,
                    target_id=edge.target_actor_id,
                )
            ),
            last_reconciled_at=last_reconciled_at,
        )
        for edge in execution_topology_state.edges
    ]
    return TopologyDutyMapState(
        orchestrator_session_id=orchestrator.actor_id,
        parent_session_id=worker_visibility_state.parent_session_id,
        current_authoritative_holder_actor_id=current_holder_actor_id,
        last_reconciled_event=execution_topology_state.last_reconciled_event,
        continuation_bridge_ref=execution_topology_state.continuation_bridge_ref,
        compaction_seams=execution_topology_state.compaction_seams,
        nodes=nodes,
        edges=edges,
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


def _resolve_orchestrator_node(*, nodes: list[ActorState]) -> ActorState:
    orchestrators = [node for node in nodes if node.role == "main_orchestrator"]
    if len(orchestrators) != 1:
        raise TopologyDutyMapStateError("topology must contain exactly one orchestrator node")
    return orchestrators[0]


def _validate_edges(
    *,
    edges: list[TopologyEdge],
    orchestrator_actor_id: str,
    expected_child_ids: set[str],
) -> dict[str, TopologyEdge]:
    edge_by_target: dict[str, TopologyEdge] = {}
    for edge in edges:
        if edge.source_actor_id != orchestrator_actor_id:
            raise TopologyDutyMapStateError("topology edge source drift detected")
        if edge.target_actor_id in edge_by_target:
            raise TopologyDutyMapStateError("duplicate topology edge target detected")
        edge_by_target[edge.target_actor_id] = edge
    if set(edge_by_target) != expected_child_ids:
        raise TopologyDutyMapStateError("topology edges do not match topology child nodes")
    return edge_by_target


def _validate_current_holder_alignment(
    *,
    nodes: list[ActorState],
    current_holder_actor_id: str | None,
) -> None:
    holder_nodes = [node.actor_id for node in nodes if node.authoritative_write_access]
    if current_holder_actor_id is None:
        if holder_nodes:
            raise TopologyDutyMapStateError("topology reports write access with no lease holder")
        return
    if current_holder_actor_id not in {node.actor_id for node in nodes}:
        raise TopologyDutyMapStateError("write lease holder not present in topology nodes")
    if holder_nodes != [current_holder_actor_id]:
        raise TopologyDutyMapStateError("topology authoritative write holder drift detected")


def _resolve_last_reconciled_at(
    *,
    last_reconciled_event: str | None,
    event_streams: list[EventStreamHeadInput],
) -> str | None:
    if last_reconciled_event is None:
        return None
    for stream in event_streams:
        if stream.last_event_ref == last_reconciled_event:
            return stream.last_ts
    return None


def _match_handoff_entries(
    *,
    workers: list[WorkerVisibilityEntry],
    handoff_entries: list[RoleHandoffEntry],
) -> dict[str, RoleHandoffEntry]:
    matched: dict[str, RoleHandoffEntry] = {}
    consumed: set[int] = set()
    for worker in sorted(workers, key=lambda item: item.worker_id):
        raw_source_path = _lane_source_path(worker=worker, lane="raw_transcript")
        if raw_source_path is None:
            continue
        for index, entry in enumerate(handoff_entries):
            if index in consumed:
                continue
            if raw_source_path in entry.artifacts_produced:
                matched[worker.worker_id] = entry
                consumed.add(index)
                break
    if len(consumed) != len(handoff_entries):
        raise TopologyDutyMapStateError("role handoff entries do not match visible workers")
    return matched


def _lane_source_path(*, worker: WorkerVisibilityEntry, lane: str) -> str | None:
    lane_state = _lane_state(worker=worker, lane=lane)
    if lane_state is None:
        return None
    return lane_state.source_path


def _lane_state(*, worker: WorkerVisibilityEntry, lane: str) -> VisibilityLaneState | None:
    for lane_state in worker.epistemic_lanes:
        if lane_state.lane == lane:
            return lane_state
    return None


def _target_stream_id(*, child_nodes: list[ActorState], target_id: str) -> str | None:
    for node in child_nodes:
        if node.actor_id == target_id:
            return node.stream_id
    return None


def _build_orchestrator_node(
    *,
    orchestrator: ActorState,
    current_holder_actor_id: str | None,
    execution_topology_state_path: str,
    write_lease_state_path: str,
    worker_visibility_state_path: str,
    event_head: EventStreamHeadInput | None,
    last_reconciled_at: str | None,
    reconciliation_status: str,
) -> TopologyDutyMapNode:
    current_duty = (
        "governing_with_active_write_lease"
        if current_holder_actor_id == orchestrator.actor_id
        else "governing_and_reconciling_delegated_work"
    )
    provenance_refs = [
        _artifact_ref(
            path=execution_topology_state_path,
            source_schema="execution_topology_state@1",
        ),
        _artifact_ref(
            path=write_lease_state_path,
            source_schema="write_lease_state@1",
        ),
        _artifact_ref(
            path=worker_visibility_state_path,
            source_schema="worker_visibility_state@1",
        ),
    ]
    if event_head is not None:
        provenance_refs.append(_event_stream_ref(event_head=event_head))
    return TopologyDutyMapNode(
        actor_id=orchestrator.actor_id,
        role=orchestrator.role,
        authority_domain=orchestrator.authority_domain,
        authority_level=orchestrator.authority_level,
        current_duty=current_duty,
        scope_owned=orchestrator.scope_owned,
        blocking_state="non_blocking",
        state_origin=TOPOLOGY_DUTY_MAP_STATE_ORIGIN,
        reconciliation_status=reconciliation_status,
        last_updated_at=event_head.last_ts if event_head is not None else None,
        last_reconciled_at=last_reconciled_at,
        provenance_refs=provenance_refs,
        user_facing_boundary=orchestrator.user_facing_boundary,
        authoritative_write_access=orchestrator.authoritative_write_access,
        status=orchestrator.status,
        blockers=[],
    )


def _build_child_node(
    *,
    node: ActorState,
    worker_visibility: WorkerVisibilityEntry,
    matched_handoff: RoleHandoffEntry | None,
    current_holder_actor_id: str | None,
    source_artifacts: TopologyDutyMapSourceArtifacts,
    event_head: EventStreamHeadInput | None,
    last_reconciled_at: str | None,
) -> TopologyDutyMapNode:
    blockers = list(worker_visibility.blockers)
    blocking_state = _rendered_blocking_state(
        authority_domain=node.authority_domain,
        blocking_state=worker_visibility.blocking_state,
    )
    provenance_refs = [
        _artifact_ref(
            path=source_artifacts.execution_topology_state_path,
            source_schema="execution_topology_state@1",
        ),
        _artifact_ref(
            path=source_artifacts.worker_visibility_state_path,
            source_schema="worker_visibility_state@1",
        ),
    ]
    if node.authoritative_write_access or current_holder_actor_id == node.actor_id:
        provenance_refs.append(
            _artifact_ref(
                path=source_artifacts.write_lease_state_path,
                source_schema="write_lease_state@1",
            )
        )
    if matched_handoff is not None:
        provenance_refs.append(
            _artifact_ref(
                path=source_artifacts.role_handoff_envelope_path,
                source_schema="role_handoff_envelope@1",
            )
        )
    if event_head is not None:
        provenance_refs.append(_event_stream_ref(event_head=event_head))
    return TopologyDutyMapNode(
        actor_id=node.actor_id,
        role=node.role,
        authority_domain=node.authority_domain,
        authority_level=node.authority_level,
        current_duty=_resolve_current_duty(
            node=node,
            worker_visibility=worker_visibility,
            current_holder_actor_id=current_holder_actor_id,
        ),
        scope_owned=node.scope_owned,
        blocking_state=blocking_state,
        state_origin=TOPOLOGY_DUTY_MAP_STATE_ORIGIN,
        reconciliation_status=worker_visibility.reconciliation_status,
        last_updated_at=event_head.last_ts if event_head is not None else None,
        last_reconciled_at=last_reconciled_at,
        provenance_refs=provenance_refs,
        user_facing_boundary=node.user_facing_boundary,
        authoritative_write_access=node.authoritative_write_access,
        status=node.status,
        blockers=blockers,
    )


def _build_edge(
    *,
    edge: TopologyEdge,
    worker_visibility: WorkerVisibilityEntry,
    matched_handoff: RoleHandoffEntry | None,
    source_artifacts: TopologyDutyMapSourceArtifacts,
    event_head: EventStreamHeadInput | None,
    last_reconciled_at: str | None,
) -> TopologyDutyMapEdge:
    provenance_refs = [
        _artifact_ref(
            path=source_artifacts.execution_topology_state_path,
            source_schema="execution_topology_state@1",
        ),
        _artifact_ref(
            path=source_artifacts.worker_visibility_state_path,
            source_schema="worker_visibility_state@1",
        ),
    ]
    if edge.authoritative_write_access:
        provenance_refs.append(
            _artifact_ref(
                path=source_artifacts.write_lease_state_path,
                source_schema="write_lease_state@1",
            )
        )
    if matched_handoff is not None:
        provenance_refs.append(
            _artifact_ref(
                path=source_artifacts.role_handoff_envelope_path,
                source_schema="role_handoff_envelope@1",
            )
        )
    if event_head is not None:
        provenance_refs.append(_event_stream_ref(event_head=event_head))
    return TopologyDutyMapEdge(
        source_actor_id=edge.source_actor_id,
        target_actor_id=edge.target_actor_id,
        edge_kind=edge.edge_kind,
        blocking_state=_rendered_blocking_state(
            authority_domain=(
                "implementation" if worker_visibility.role == "builder_worker" else "advisory"
            ),
            blocking_state=worker_visibility.blocking_state,
        ),
        state_origin=TOPOLOGY_DUTY_MAP_STATE_ORIGIN,
        reconciliation_status=worker_visibility.reconciliation_status,
        last_updated_at=event_head.last_ts if event_head is not None else None,
        last_reconciled_at=last_reconciled_at,
        provenance_refs=provenance_refs,
        authoritative_write_access=edge.authoritative_write_access,
        requested_role=edge.requested_role,
        granted_role=edge.granted_role,
        delegation_task_kind=edge.delegation_task_kind,
        blockers=list(worker_visibility.blockers),
    )


def _resolve_current_duty(
    *,
    node: ActorState,
    worker_visibility: WorkerVisibilityEntry,
    current_holder_actor_id: str | None,
) -> str:
    if node.role == "builder_worker":
        if node.authoritative_write_access and node.status == "running":
            return "implementing_with_active_write_lease"
        if node.authoritative_write_access and node.status == "queued":
            return "queued_for_implementation_with_reserved_write_lease"
        if node.status == "running":
            return "implementing_without_active_write_lease"
        if node.status == "queued":
            return "queued_for_implementation"
        if node.status == "completed":
            return "implementation_completed_pending_reconciliation"
        if node.status in {"failed", "cancelled"}:
            return "implementation_issue_escalated_for_reconciliation"
        return "implementation_state_observed"
    if worker_visibility.blockers:
        return "advisory_issue_raised_for_orchestrator_attention"
    if node.status == "running":
        return "advisory_analysis_in_progress"
    if node.status == "queued":
        return "queued_for_advisory_analysis"
    if node.status == "completed":
        return "advisory_analysis_completed_pending_reconciliation"
    if node.status in {"failed", "cancelled"}:
        return "advisory_analysis_failed"
    if current_holder_actor_id == node.actor_id:
        return "write_lease_holder_pending_reconciliation"
    return "advisory_state_observed"


def _rendered_blocking_state(
    *,
    authority_domain: AuthorityDomain,
    blocking_state: BlockingState,
) -> BlockingState:
    if authority_domain == "advisory":
        return "non_blocking"
    return blocking_state


def _artifact_ref(*, path: str, source_schema: str) -> TopologyProvenanceRef:
    return TopologyProvenanceRef(
        ref_kind="artifact",
        path=path,
        source_schema=source_schema,
    )


def _event_stream_ref(*, event_head: EventStreamHeadInput) -> TopologyProvenanceRef:
    return TopologyProvenanceRef(
        ref_kind="event_stream",
        path=event_head.path,
        stream_id=event_head.stream_id,
        event_ref=event_head.last_event_ref,
    )
