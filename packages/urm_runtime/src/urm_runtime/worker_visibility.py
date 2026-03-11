from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field

from .hashing import canonical_json, sha256_canonical_json
from .orchestration_state import (
    ChildStateInput,
    CompactionSeam,
    ContinuationBridgeRef,
    EventStreamHeadInput,
    MaterializedArtifact,
    RoleHandoffEntry,
    ScopeDescriptor,
    SessionStateInput,
    build_orchestration_artifacts,
)

WORKER_VISIBILITY_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS58.md#v35c_transcript_visibility_contract@1"
)
WORKER_VISIBILITY_FOUNDATION_PACKAGE = "packages/urm_runtime"
WORKER_VISIBILITY_SCHEMA = "worker_visibility_state@1"
EPISTEMIC_LANE_ABSENCE_POLICY = "explicit_status_required_not_silent_omission"
PROGRESS_STATE_SOURCE_POLICY = (
    "derived_from_v35a_state_v35b_handoff_and_urm_runtime_events_only_no_ad_hoc_worker_summary"
)
RAW_TRANSCRIPT_AUTHORITY_POLICY = "visibility_alone_confers_no_acceptance_authority"
WORKER_SELF_REPORT_AUTHORITY_POLICY = "self_report_non_authoritative_until_reconciled"
RECONCILED_HANDOFF_SURFACE_POLICY = "present_only_after_explicit_orchestrator_reconciliation"
ORCHESTRATOR_JUDGMENT_SURFACE_POLICY = (
    "present_only_when_explicit_orchestrator_judgment_is_recorded"
)
CONTINUATION_BRIDGE_VISIBILITY_POLICY = (
    "explicit_compaction_seams_and_bridge_linkage_required_not_silent_flattening"
)
WORKER_VISIBILITY_LANE_ENUM: tuple[str, ...] = (
    "raw_transcript",
    "worker_self_report",
    "reconciled_handoff",
    "orchestrator_judgment",
)
WORKER_VISIBILITY_LANE_STATUS_ENUM: tuple[str, ...] = (
    "available",
    "pending_parse",
    "pending_reconciliation",
    "not_available",
    "parsing_failure",
    "reconciliation_aborted",
)
WORKER_VISIBILITY_DIVERGENCE_ENUM: tuple[str, ...] = (
    "aligned",
    "raw_only",
    "worker_self_report_only",
    "lane_disagreement",
    "parsing_failure",
    "reconciliation_aborted",
)

EpistemicLane = Literal[
    "raw_transcript",
    "worker_self_report",
    "reconciled_handoff",
    "orchestrator_judgment",
]
EpistemicLaneStatus = Literal[
    "available",
    "pending_parse",
    "pending_reconciliation",
    "not_available",
    "parsing_failure",
    "reconciliation_aborted",
]
DivergenceState = Literal[
    "aligned",
    "raw_only",
    "worker_self_report_only",
    "lane_disagreement",
    "parsing_failure",
    "reconciliation_aborted",
]
BlockingState = Literal["blocking", "non_blocking"]
ReconciliationStatus = Literal[
    "not_applicable",
    "pending_reconciliation",
    "reconciled",
    "reconciliation_aborted",
]


class WorkerVisibilityStateError(ValueError):
    pass


class VisibilityLaneState(BaseModel):
    model_config = ConfigDict(extra="forbid")

    lane: EpistemicLane
    status: EpistemicLaneStatus
    source_path: str | None = None
    source_ref: str | None = None
    latest_visible_event: str | None = None
    authority_policy: str = Field(min_length=1)


class WorkerVisibilityEntry(BaseModel):
    model_config = ConfigDict(extra="forbid")

    worker_id: str = Field(min_length=1)
    worker_session_id: str = Field(min_length=1)
    parent_session_id: str = Field(min_length=1)
    role: str = Field(min_length=1)
    requested_role: str = Field(min_length=1)
    granted_role: str = Field(min_length=1)
    delegation_task_kind: str = Field(min_length=1)
    status: str = Field(min_length=1)
    last_action: str = Field(min_length=1)
    blocking_state: BlockingState
    blockers: list[str] = Field(default_factory=list)
    scope_owned: list[ScopeDescriptor] = Field(default_factory=list)
    scope_remaining: list[ScopeDescriptor] = Field(default_factory=list)
    latest_visible_event: str | None = None
    reconciliation_status: ReconciliationStatus
    divergence_state: DivergenceState
    epistemic_lanes: list[VisibilityLaneState] = Field(default_factory=list)
    raw_transcript_non_authoritative: bool = True
    worker_self_report_non_authoritative_until_reconciled: bool = True
    direct_user_boundary_established: bool = False


class WorkerVisibilityState(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: Literal["worker_visibility_state@1"] = Field(
        default=WORKER_VISIBILITY_SCHEMA,
        alias="schema",
    )
    contract_source: str = WORKER_VISIBILITY_CONTRACT_SOURCE
    worker_visibility_foundation_package: str = WORKER_VISIBILITY_FOUNDATION_PACKAGE
    read_only_visibility_required: bool = True
    orchestrator_primary_interaction_boundary_required: bool = True
    deterministic_redaction_and_scope_boundary_required: bool = True
    worker_direct_user_boundary_forbidden: bool = True
    epistemic_lane_enum: list[EpistemicLane] = Field(
        default_factory=lambda: list(WORKER_VISIBILITY_LANE_ENUM)
    )
    epistemic_lane_absence_policy: str = EPISTEMIC_LANE_ABSENCE_POLICY
    epistemic_lane_status_enum: list[EpistemicLaneStatus] = Field(
        default_factory=lambda: list(WORKER_VISIBILITY_LANE_STATUS_ENUM)
    )
    divergence_state_enum: list[DivergenceState] = Field(
        default_factory=lambda: list(WORKER_VISIBILITY_DIVERGENCE_ENUM)
    )
    progress_state_source_policy: str = PROGRESS_STATE_SOURCE_POLICY
    raw_transcript_authority_policy: str = RAW_TRANSCRIPT_AUTHORITY_POLICY
    worker_self_report_authority_policy: str = WORKER_SELF_REPORT_AUTHORITY_POLICY
    reconciled_handoff_surface_policy: str = RECONCILED_HANDOFF_SURFACE_POLICY
    orchestrator_judgment_surface_policy: str = ORCHESTRATOR_JUDGMENT_SURFACE_POLICY
    continuation_bridge_visibility_policy: str = CONTINUATION_BRIDGE_VISIBILITY_POLICY
    parent_session_id: str = Field(min_length=1)
    orchestrator_session_id: str = Field(min_length=1)
    last_reconciled_event: str | None = None
    continuation_bridge_ref: ContinuationBridgeRef | None = None
    compaction_seams: list[CompactionSeam] = Field(default_factory=list)
    workers: list[WorkerVisibilityEntry] = Field(default_factory=list)


@dataclass(frozen=True)
class MaterializedWorkerVisibilityArtifacts:
    session_id: str
    output_root: str
    worker_visibility_state: MaterializedArtifact


def materialize_worker_visibility_artifacts(
    *,
    output_root: Path,
    output_root_relative: str,
    session: SessionStateInput,
    children: list[ChildStateInput],
    event_streams: list[EventStreamHeadInput],
    repo_root: str,
    branch_or_head: str,
    raw_transcript_available_by_child: dict[str, bool],
) -> MaterializedWorkerVisibilityArtifacts:
    visibility_state = build_worker_visibility_state(
        session=session,
        children=children,
        event_streams=event_streams,
        repo_root=repo_root,
        branch_or_head=branch_or_head,
        raw_transcript_available_by_child=raw_transcript_available_by_child,
    )
    output_root.mkdir(parents=True, exist_ok=True)
    artifact = _write_artifact(
        output_root=output_root,
        output_root_relative=output_root_relative,
        filename="worker_visibility_state.json",
        model=visibility_state,
    )
    return MaterializedWorkerVisibilityArtifacts(
        session_id=session.session_id,
        output_root=output_root_relative,
        worker_visibility_state=artifact,
    )


def build_worker_visibility_state(
    *,
    session: SessionStateInput,
    children: list[ChildStateInput],
    event_streams: list[EventStreamHeadInput],
    repo_root: str,
    branch_or_head: str,
    raw_transcript_available_by_child: dict[str, bool],
) -> WorkerVisibilityState:
    snapshot, topology, _write_lease, _transition_record, handoff_envelope = (
        build_orchestration_artifacts(
            session=session,
            children=children,
            event_streams=event_streams,
            repo_root=repo_root,
            branch_or_head=branch_or_head,
        )
    )
    handoff_entries_by_child = _match_handoff_entries(
        children=children,
        handoff_entries=handoff_envelope.entries,
    )
    event_heads_by_stream = {stream.stream_id: stream for stream in event_streams}
    workers = [
        _build_worker_visibility_entry(
            child=child,
            event_head=event_heads_by_stream.get(child.child_stream_id),
            handoff_entry=handoff_entries_by_child.get(child.child_id),
            raw_transcript_available=raw_transcript_available_by_child.get(child.child_id, False),
        )
        for child in sorted(children, key=_child_order_key)
    ]
    if any(worker.direct_user_boundary_established for worker in workers):
        raise WorkerVisibilityStateError("worker direct user boundary drift detected")
    return WorkerVisibilityState(
        parent_session_id=session.session_id,
        orchestrator_session_id=snapshot.orchestrator_session_id,
        last_reconciled_event=snapshot.last_reconciled_event,
        continuation_bridge_ref=snapshot.continuation_bridge_ref,
        compaction_seams=topology.compaction_seams,
        workers=workers,
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


def _match_handoff_entries(
    *,
    children: list[ChildStateInput],
    handoff_entries: list[RoleHandoffEntry],
) -> dict[str, RoleHandoffEntry]:
    matched: dict[str, RoleHandoffEntry] = {}
    consumed: set[int] = set()
    for child in sorted(children, key=_child_order_key):
        for index, entry in enumerate(handoff_entries):
            if index in consumed:
                continue
            if child.raw_jsonl_path and child.raw_jsonl_path in entry.artifacts_produced:
                matched[child.child_id] = entry
                consumed.add(index)
                break
            if child.urm_events_path and child.urm_events_path in entry.evidence_refs:
                matched[child.child_id] = entry
                consumed.add(index)
                break
    return matched


def _build_worker_visibility_entry(
    *,
    child: ChildStateInput,
    event_head: EventStreamHeadInput | None,
    handoff_entry: RoleHandoffEntry | None,
    raw_transcript_available: bool,
) -> WorkerVisibilityEntry:
    raw_lane_status = "available" if raw_transcript_available else "not_available"
    if handoff_entry is not None:
        worker_self_report_status: EpistemicLaneStatus = "available"
        reconciled_handoff_status: EpistemicLaneStatus = "pending_reconciliation"
    elif raw_transcript_available and child.status in {"queued", "running"}:
        worker_self_report_status = "pending_parse"
        reconciled_handoff_status = "not_available"
    else:
        worker_self_report_status = "not_available"
        reconciled_handoff_status = "not_available"
    orchestrator_judgment_status: EpistemicLaneStatus = "not_available"

    lanes = [
        VisibilityLaneState(
            lane="raw_transcript",
            status=raw_lane_status,
            source_path=child.raw_jsonl_path,
            source_ref=child.child_stream_id,
            latest_visible_event=event_head.last_event_ref if event_head is not None else None,
            authority_policy=RAW_TRANSCRIPT_AUTHORITY_POLICY,
        ),
        VisibilityLaneState(
            lane="worker_self_report",
            status=worker_self_report_status,
            source_ref=(
                f"role_handoff_envelope:{child.child_id}"
                if handoff_entry is not None
                else None
            ),
            authority_policy=WORKER_SELF_REPORT_AUTHORITY_POLICY,
        ),
        VisibilityLaneState(
            lane="reconciled_handoff",
            status=reconciled_handoff_status,
            source_ref=(
                f"role_handoff_envelope:{child.child_id}"
                if handoff_entry is not None
                else None
            ),
            authority_policy=RECONCILED_HANDOFF_SURFACE_POLICY,
        ),
        VisibilityLaneState(
            lane="orchestrator_judgment",
            status=orchestrator_judgment_status,
            authority_policy=ORCHESTRATOR_JUDGMENT_SURFACE_POLICY,
        ),
    ]

    blocking_state, blockers = _resolve_blocking_state(
        child=child,
        handoff_entry=handoff_entry,
    )
    scope_owned = (
        list(handoff_entry.scope_owned)
        if handoff_entry is not None
        else [_child_scope(child)]
    )
    scope_remaining = _resolve_scope_remaining(child=child, handoff_entry=handoff_entry)
    reconciliation_status: ReconciliationStatus = (
        "pending_reconciliation" if handoff_entry is not None else "not_applicable"
    )
    return WorkerVisibilityEntry(
        worker_id=child.child_id,
        worker_session_id=child.child_thread_id or child.child_id,
        parent_session_id=child.parent_session_id,
        role=child.granted_role,
        requested_role=child.requested_role,
        granted_role=child.granted_role,
        delegation_task_kind=child.delegation_task_kind,
        status=child.status,
        last_action=_resolve_last_action(child=child, event_head=event_head),
        blocking_state=blocking_state,
        blockers=blockers,
        scope_owned=scope_owned,
        scope_remaining=scope_remaining,
        latest_visible_event=event_head.last_event_ref if event_head is not None else None,
        reconciliation_status=reconciliation_status,
        divergence_state=_resolve_divergence_state(
            child=child,
            handoff_entry=handoff_entry,
            raw_lane_status=raw_lane_status,
            worker_self_report_status=worker_self_report_status,
        ),
        epistemic_lanes=lanes,
    )


def _resolve_blocking_state(
    *,
    child: ChildStateInput,
    handoff_entry: RoleHandoffEntry | None,
) -> tuple[BlockingState, list[str]]:
    if handoff_entry is not None:
        return handoff_entry.blocking_state, list(handoff_entry.blockers)
    if child.status in {"failed", "cancelled"}:
        blockers = [value for value in (child.error_code, child.error_message) if value]
        return "blocking", blockers
    if child.status == "queued":
        return "blocking", ["child_waiting_for_dispatch"]
    return "non_blocking", []


def _resolve_scope_remaining(
    *,
    child: ChildStateInput,
    handoff_entry: RoleHandoffEntry | None,
) -> list[ScopeDescriptor]:
    if handoff_entry is not None:
        return list(handoff_entry.scope_remaining)
    if child.status == "completed":
        return []
    return [_child_scope(child)]


def _resolve_last_action(
    *,
    child: ChildStateInput,
    event_head: EventStreamHeadInput | None,
) -> str:
    if event_head is not None and event_head.last_event:
        return event_head.last_event
    if child.status == "queued":
        return "WORKER_QUEUED"
    if child.status == "running":
        return "WORKER_START"
    if child.status == "completed":
        return "WORKER_PASS"
    if child.status == "cancelled":
        return "WORKER_CANCEL"
    return "WORKER_FAIL"


def _resolve_divergence_state(
    *,
    child: ChildStateInput,
    handoff_entry: RoleHandoffEntry | None,
    raw_lane_status: EpistemicLaneStatus,
    worker_self_report_status: EpistemicLaneStatus,
) -> DivergenceState:
    if raw_lane_status == "parsing_failure" or worker_self_report_status == "parsing_failure":
        return "parsing_failure"
    if worker_self_report_status == "reconciliation_aborted":
        return "reconciliation_aborted"
    if raw_lane_status == "available" and worker_self_report_status in {
        "pending_parse",
        "not_available",
    }:
        return "raw_only"
    if raw_lane_status != "available" and worker_self_report_status == "available":
        return "worker_self_report_only"
    if handoff_entry is not None and not _handoff_entry_matches_child(
        child=child,
        entry=handoff_entry,
    ):
        return "lane_disagreement"
    return "aligned"


def _handoff_entry_matches_child(*, child: ChildStateInput, entry: RoleHandoffEntry) -> bool:
    if entry.role != child.granted_role:
        return False
    if entry.status != child.status:
        return False
    expected_scope = _child_scope(child).model_dump(mode="json")
    if [scope.model_dump(mode="json") for scope in entry.scope_owned] != [expected_scope]:
        return False
    if child.granted_role == "builder_worker":
        return entry.artifact_surface == "implementation"
    return entry.artifact_surface == "none"


def _child_scope(child: ChildStateInput) -> ScopeDescriptor:
    return ScopeDescriptor(
        kind=child.delegated_scope_kind,
        values=list(child.delegated_scope_values),
        artifact_surfaces=list(child.delegated_scope_artifact_surfaces),
        rationale=child.delegated_scope_rationale,
    )


def _child_order_key(child: ChildStateInput) -> tuple[int, int, str]:
    dispatch_rank = child.dispatch_seq if child.dispatch_seq is not None else 2**30
    return (dispatch_rank, child.queue_seq, child.child_id)
