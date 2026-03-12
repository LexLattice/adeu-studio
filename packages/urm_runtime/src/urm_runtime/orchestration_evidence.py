from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any, TypeVar

from pydantic import BaseModel, ConfigDict, Field, ValidationError

from .errors import URMError
from .hashing import canonical_json, sha256_canonical_json
from .orchestration_state import (
    CONTROL_PLANE_OWNER,
    HANDOFF_EMPTY_VALUE_POLICIES,
    HANDOFF_REQUIRED_FIELDS,
    HANDOFF_TRUST_MODEL,
    ORCHESTRATION_FOUNDATION_PACKAGE,
    RECONCILIATION_MINIMUM_CHECKS,
    RUNTIME_EVENT_TRUTH_POLICY,
    SCOPE_GRANULARITY_ENUM,
    EventStreamHeadInput,
    ExecutionTopologyState,
    MaterializedArtifact,
    MaterializedOrchestrationArtifacts,
    OrchestrationStateSnapshot,
    RoleHandoffEnvelope,
    RoleTransitionRecord,
    WriteLeaseState,
)
from .roles import CHILD_DELEGATION_ROLES, SUPPORT_DELEGATION_ROLES
from .runtime_enforcement import (
    CLAIMED_WORK_HANDOFF_INVALID_CODE,
    DETERMINISTIC_DENIAL_CODES,
    INVALID_ROLE_TASK_COMBINATION_CODE,
    MATERIALIZATION_ENFORCEMENT_SURFACES,
    REQUIRED_ENFORCEMENT_SURFACES,
    ROLE_TASK_KIND_BY_ROLE,
    SCOPE_KIND_INVALID_CODE,
    SINGLE_BUILDER_DEFAULT_VIOLATION_CODE,
    SUPPORT_PROXY_AUTHORITY_CODE,
    RuntimeEnforcementCandidate,
    validate_claimed_work_handoff_field,
    validate_runtime_enforcement_candidate,
    validate_single_builder_default,
)
from .topology_duty_map import (
    EVENT_STREAM_DRILLDOWN_POLICY,
    TOPOLOGY_DUTY_MAP_CONTRACT_SOURCE,
    TOPOLOGY_DUTY_MAP_FOUNDATION_PACKAGE,
    TOPOLOGY_DUTY_MAP_STATE_ORIGIN,
    TOPOLOGY_SURFACE_AUTHORITY_POLICY,
    MaterializedTopologyDutyMapArtifacts,
    TopologyDutyMapSourceArtifacts,
    TopologyDutyMapState,
    TopologyDutyMapStateError,
    build_topology_duty_map_state,
)
from .worker_visibility import (
    CONTINUATION_BRIDGE_VISIBILITY_POLICY,
    EPISTEMIC_LANE_ABSENCE_POLICY,
    ORCHESTRATOR_JUDGMENT_SURFACE_POLICY,
    PROGRESS_STATE_SOURCE_POLICY,
    RAW_TRANSCRIPT_AUTHORITY_POLICY,
    RECONCILED_HANDOFF_SURFACE_POLICY,
    WORKER_SELF_REPORT_AUTHORITY_POLICY,
    WORKER_VISIBILITY_DIVERGENCE_ENUM,
    WORKER_VISIBILITY_FOUNDATION_PACKAGE,
    WORKER_VISIBILITY_LANE_ENUM,
    WORKER_VISIBILITY_LANE_STATUS_ENUM,
    MaterializedWorkerVisibilityArtifacts,
    WorkerVisibilityState,
)

V35A_ORCHESTRATION_STATE_EVIDENCE_SCHEMA = "v35a_orchestration_state_evidence@1"
V35A_ORCHESTRATION_STATE_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS56.md#v35a_orchestration_state_contract@1"
)
V35B_DELEGATION_HANDOFF_EVIDENCE_SCHEMA = "v35b_delegation_handoff_evidence@1"
V35B_DELEGATION_HANDOFF_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS57.md#v35b_delegation_handoff_contract@1"
)
V35C_TRANSCRIPT_VISIBILITY_EVIDENCE_SCHEMA = "v35c_transcript_visibility_evidence@1"
V35C_TRANSCRIPT_VISIBILITY_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS58.md#v35c_transcript_visibility_contract@1"
)
V35D_TOPOLOGY_DUTY_MAP_EVIDENCE_SCHEMA = "v35d_topology_duty_map_evidence@1"
V35E_RUNTIME_ENFORCEMENT_EVIDENCE_SCHEMA = "v35e_runtime_enforcement_evidence@1"
V35E_RUNTIME_ENFORCEMENT_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md#v35e_runtime_enforcement_contract@1"
)
STOP_GATE_METRICS_SCHEMA = "stop_gate_metrics@1"
EXPECTED_METRIC_KEY_CARDINALITY = 80
EXPECTED_SCOPE_GRANULARITY = list(SCOPE_GRANULARITY_ENUM)
EXPECTED_HANDOFF_REQUIRED_FIELDS = list(HANDOFF_REQUIRED_FIELDS)
EXPECTED_HANDOFF_EMPTY_VALUE_POLICIES = dict(HANDOFF_EMPTY_VALUE_POLICIES)
EXPECTED_RECONCILIATION_MINIMUM_CHECKS = list(RECONCILIATION_MINIMUM_CHECKS)
EXPECTED_CHILD_DELEGATION_ROLES = set(CHILD_DELEGATION_ROLES)
EXPECTED_SUPPORT_DELEGATION_ROLES = set(SUPPORT_DELEGATION_ROLES)
EXPECTED_DELEGATION_TASK_KINDS = {
    "write_task",
    "analysis_task",
    "validation_task",
    "docs_task",
}
EXPECTED_RECONCILIATION_ACTION = "explicit_orchestrator_reconciliation_required"

ModelT = TypeVar("ModelT", bound=BaseModel)


class OrchestrationEvidenceError(ValueError):
    pass


class V35AOrchestrationStateEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: str = Field(default=V35A_ORCHESTRATION_STATE_EVIDENCE_SCHEMA, alias="schema")
    contract_source: str = V35A_ORCHESTRATION_STATE_CONTRACT_SOURCE
    evidence_input_path: str = Field(min_length=1)
    orchestration_state_snapshot_path: str = Field(min_length=1)
    orchestration_state_snapshot_hash: str = Field(min_length=64, max_length=64)
    execution_topology_state_path: str = Field(min_length=1)
    execution_topology_state_hash: str = Field(min_length=64, max_length=64)
    write_lease_state_path: str = Field(min_length=1)
    write_lease_state_hash: str = Field(min_length=64, max_length=64)
    role_transition_record_path: str = Field(min_length=1)
    role_transition_record_hash: str = Field(min_length=64, max_length=64)
    role_handoff_envelope_path: str = Field(min_length=1)
    role_handoff_envelope_hash: str = Field(min_length=64, max_length=64)
    orchestration_foundation_package: str = ORCHESTRATION_FOUNDATION_PACKAGE
    single_writer_default_enforced: bool
    worker_direct_user_boundary_forbidden: bool
    canonical_identity_fields_recorded: bool
    last_reconciled_event_recorded: bool
    continuation_bridge_ref_recorded: bool
    zero_occurrence_empty_artifacts_materialized: bool
    scope_granularity_enum_frozen: bool
    handoff_reconciliation_required: bool
    verification_passed: bool
    metric_key_cardinality: int = Field(ge=0)
    metric_key_exact_set_equal_v55: bool
    notes: str = Field(min_length=1)


class V35BDelegationHandoffEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: str = Field(default=V35B_DELEGATION_HANDOFF_EVIDENCE_SCHEMA, alias="schema")
    contract_source: str = V35B_DELEGATION_HANDOFF_CONTRACT_SOURCE
    evidence_input_path: str = Field(min_length=1)
    orchestration_state_snapshot_path: str = Field(min_length=1)
    orchestration_state_snapshot_hash: str = Field(min_length=64, max_length=64)
    write_lease_state_path: str = Field(min_length=1)
    write_lease_state_hash: str = Field(min_length=64, max_length=64)
    role_transition_record_path: str = Field(min_length=1)
    role_transition_record_hash: str = Field(min_length=64, max_length=64)
    role_handoff_envelope_path: str = Field(min_length=1)
    role_handoff_envelope_hash: str = Field(min_length=64, max_length=64)
    builder_role_materialized: bool
    support_roles_materialized: bool
    delegated_scope_kind_recorded: bool
    single_builder_default_enforced: bool
    support_workers_non_authoritative: bool
    handoff_artifact_materialized: bool
    handoff_reconciliation_required: bool
    unreconciled_worker_output_non_authoritative: bool
    worker_direct_user_boundary_forbidden: bool
    verification_passed: bool
    metric_key_cardinality: int = Field(ge=0)
    metric_key_exact_set_equal_v56: bool
    zero_occurrence_empty_artifacts_materialized: bool
    notes: str = Field(min_length=1)


class V35CTranscriptVisibilityEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: str = Field(default=V35C_TRANSCRIPT_VISIBILITY_EVIDENCE_SCHEMA, alias="schema")
    contract_source: str = V35C_TRANSCRIPT_VISIBILITY_CONTRACT_SOURCE
    evidence_input_path: str = Field(min_length=1)
    worker_visibility_state_path: str = Field(min_length=1)
    worker_visibility_state_hash: str = Field(min_length=64, max_length=64)
    orchestration_state_snapshot_path: str = Field(min_length=1)
    orchestration_state_snapshot_hash: str = Field(min_length=64, max_length=64)
    role_handoff_envelope_path: str = Field(min_length=1)
    role_handoff_envelope_hash: str = Field(min_length=64, max_length=64)
    read_only_visibility_preserved: bool
    epistemic_lane_labels_present: bool
    explicit_lane_absence_materialized: bool
    explicit_divergence_state_materialized: bool
    continuation_bridge_visibility_present_when_available: bool
    no_ad_hoc_progress_summary_bypass: bool
    raw_transcript_non_authoritative: bool
    worker_self_report_non_authoritative_until_reconciled: bool
    worker_direct_user_boundary_forbidden: bool
    verification_passed: bool
    metric_key_cardinality: int = Field(ge=0)
    metric_key_exact_set_equal_v57: bool
    notes: str = Field(min_length=1)


class V35DTopologyDutyMapEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: str = Field(default=V35D_TOPOLOGY_DUTY_MAP_EVIDENCE_SCHEMA, alias="schema")
    contract_source: str = TOPOLOGY_DUTY_MAP_CONTRACT_SOURCE
    evidence_input_path: str = Field(min_length=1)
    topology_duty_map_state_path: str = Field(min_length=1)
    topology_duty_map_state_hash: str = Field(min_length=64, max_length=64)
    execution_topology_state_path: str = Field(min_length=1)
    execution_topology_state_hash: str = Field(min_length=64, max_length=64)
    worker_visibility_state_path: str = Field(min_length=1)
    worker_visibility_state_hash: str = Field(min_length=64, max_length=64)
    derived_from_canonical_execution_state_only: bool
    current_write_lease_holder_projected: bool
    current_duty_not_authority_inflating: bool
    provenance_markers_materialized: bool
    artifact_and_event_stream_provenance_refs_resolve: bool
    advisory_blockers_not_rendered_as_governance_blockers: bool
    continuation_bridge_and_compaction_visibility_preserved: bool
    non_authoritative_topology_surface_preserved: bool
    verification_passed: bool
    metric_key_cardinality: int = Field(ge=0)
    metric_key_exact_set_equal_v58: bool
    notes: str = Field(min_length=1)


class V35ERuntimeEnforcementEvidence(BaseModel):
    model_config = ConfigDict(extra="forbid", populate_by_name=True)

    schema_id: str = Field(default=V35E_RUNTIME_ENFORCEMENT_EVIDENCE_SCHEMA, alias="schema")
    contract_source: str = V35E_RUNTIME_ENFORCEMENT_CONTRACT_SOURCE
    evidence_input_path: str = Field(min_length=1)
    orchestration_state_snapshot_path: str = Field(min_length=1)
    orchestration_state_snapshot_hash: str = Field(min_length=64, max_length=64)
    write_lease_state_path: str = Field(min_length=1)
    write_lease_state_hash: str = Field(min_length=64, max_length=64)
    role_transition_record_path: str = Field(min_length=1)
    role_transition_record_hash: str = Field(min_length=64, max_length=64)
    role_handoff_envelope_path: str = Field(min_length=1)
    role_handoff_envelope_hash: str = Field(min_length=64, max_length=64)
    worker_visibility_state_path: str = Field(min_length=1)
    worker_visibility_state_hash: str = Field(min_length=64, max_length=64)
    topology_duty_map_state_path: str = Field(min_length=1)
    topology_duty_map_state_hash: str = Field(min_length=64, max_length=64)
    required_enforcement_surfaces_active: bool
    single_builder_default_enforced_at_runtime: bool
    support_role_proxy_authority_blocked: bool
    claimed_work_handoff_validation_enforced: bool
    scope_kind_validation_enforced: bool
    deterministic_denial_surfaces_recorded: bool
    released_happy_path_preserved_under_runtime_enforcement: bool
    observability_surfaces_remain_read_only: bool
    acceptance_and_closeout_authority_preserved: bool
    worker_direct_user_boundary_forbidden: bool
    verification_passed: bool
    metric_key_cardinality: int = Field(ge=0)
    metric_key_exact_set_equal_v59: bool
    notes: str = Field(min_length=1)


def materialize_v35a_orchestration_state_evidence(
    *,
    repo_root: Path,
    var_root: Path,
    artifacts: MaterializedOrchestrationArtifacts,
    output_path: str,
    baseline_metrics_path: str,
    current_metrics_path: str,
) -> MaterializedArtifact:
    repo_root = repo_root.resolve()
    var_root = var_root.resolve()
    if not repo_root.is_dir():
        raise OrchestrationEvidenceError("repository root does not exist")
    if not var_root.is_dir():
        raise OrchestrationEvidenceError("var root does not exist")

    output_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=output_path,
        field_name="output_path",
        required_prefix="artifacts/",
    )
    baseline_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=baseline_metrics_path,
        field_name="baseline_metrics_path",
        required_prefix="artifacts/",
    )
    current_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=current_metrics_path,
        field_name="current_metrics_path",
        required_prefix="artifacts/",
    )

    baseline_metrics = _load_stop_gate_metrics(path=baseline_metrics_file)
    current_metrics = _load_stop_gate_metrics(path=current_metrics_file)

    current_metric_keys = set(current_metrics["metrics"].keys())
    baseline_metric_keys = set(baseline_metrics["metrics"].keys())
    if len(current_metric_keys) != EXPECTED_METRIC_KEY_CARDINALITY:
        raise OrchestrationEvidenceError("metric key cardinality must remain frozen at 80")
    if baseline_metric_keys != current_metric_keys:
        raise OrchestrationEvidenceError("metric key set must remain exactly equal to v55")

    snapshot_payload, snapshot = _load_validated_artifact(
        var_root=var_root,
        artifact=artifacts.orchestration_state_snapshot,
        model_type=OrchestrationStateSnapshot,
        artifact_name="orchestration_state_snapshot",
    )
    topology_payload, topology = _load_validated_artifact(
        var_root=var_root,
        artifact=artifacts.execution_topology_state,
        model_type=ExecutionTopologyState,
        artifact_name="execution_topology_state",
    )
    write_lease_payload, write_lease = _load_validated_artifact(
        var_root=var_root,
        artifact=artifacts.write_lease_state,
        model_type=WriteLeaseState,
        artifact_name="write_lease_state",
    )
    transition_payload, transition_record = _load_validated_artifact(
        var_root=var_root,
        artifact=artifacts.role_transition_record,
        model_type=RoleTransitionRecord,
        artifact_name="role_transition_record",
    )
    handoff_payload, handoff_envelope = _load_validated_artifact(
        var_root=var_root,
        artifact=artifacts.role_handoff_envelope,
        model_type=RoleHandoffEnvelope,
        artifact_name="role_handoff_envelope",
    )

    _validate_foundation_package(
        snapshot=snapshot,
        topology=topology,
        write_lease=write_lease,
    )
    _validate_single_writer_default(snapshot=snapshot, write_lease=write_lease)
    _validate_worker_direct_user_boundary(snapshot=snapshot)
    _validate_canonical_identity_fields(snapshot_payload=snapshot_payload, snapshot=snapshot)
    continuation_bridge_ref_recorded = _validate_compaction_lineage(
        snapshot=snapshot,
        topology=topology,
    )
    _validate_role_transition_record(
        snapshot=snapshot,
        write_lease=write_lease,
        transition_record=transition_record,
    )
    _validate_handoff_envelope(handoff_payload=handoff_payload, handoff_envelope=handoff_envelope)

    if snapshot.scope_granularity_enum != EXPECTED_SCOPE_GRANULARITY:
        raise OrchestrationEvidenceError("scope granularity enum drift detected")
    if not isinstance(transition_payload.get("entries"), list):
        raise OrchestrationEvidenceError("role transition entries must be materialized as a list")
    if not isinstance(handoff_payload.get("entries"), list):
        raise OrchestrationEvidenceError("role handoff entries must be materialized as a list")

    evidence = V35AOrchestrationStateEvidence(
        evidence_input_path=output_path,
        orchestration_state_snapshot_path=artifacts.orchestration_state_snapshot.path,
        orchestration_state_snapshot_hash=artifacts.orchestration_state_snapshot.hash,
        execution_topology_state_path=artifacts.execution_topology_state.path,
        execution_topology_state_hash=artifacts.execution_topology_state.hash,
        write_lease_state_path=artifacts.write_lease_state.path,
        write_lease_state_hash=artifacts.write_lease_state.hash,
        role_transition_record_path=artifacts.role_transition_record.path,
        role_transition_record_hash=artifacts.role_transition_record.hash,
        role_handoff_envelope_path=artifacts.role_handoff_envelope.path,
        role_handoff_envelope_hash=artifacts.role_handoff_envelope.hash,
        single_writer_default_enforced=True,
        worker_direct_user_boundary_forbidden=True,
        canonical_identity_fields_recorded=True,
        last_reconciled_event_recorded=True,
        continuation_bridge_ref_recorded=continuation_bridge_ref_recorded,
        zero_occurrence_empty_artifacts_materialized=True,
        scope_granularity_enum_frozen=True,
        handoff_reconciliation_required=True,
        verification_passed=True,
        metric_key_cardinality=len(current_metric_keys),
        metric_key_exact_set_equal_v55=True,
        notes=(
            "v56 closeout-grade orchestration evidence remains state-only and "
            "pre-visibility/pre-enforcement; worker transcript UX, topology UX, and "
            "runtime constitutional enforcement remain out of scope."
        ),
    )
    payload = evidence.model_dump(mode="json", by_alias=True)
    output_file.parent.mkdir(parents=True, exist_ok=True)
    output_file.write_text(canonical_json(payload) + "\n", encoding="utf-8")
    return MaterializedArtifact(
        path=output_path,
        hash=sha256_canonical_json(payload),
        payload=payload,
    )


def materialize_v35b_delegation_handoff_evidence(
    *,
    repo_root: Path,
    var_root: Path,
    artifacts: MaterializedOrchestrationArtifacts,
    output_path: str,
    baseline_metrics_path: str,
    current_metrics_path: str,
) -> MaterializedArtifact:
    repo_root = repo_root.resolve()
    var_root = var_root.resolve()
    if not repo_root.is_dir():
        raise OrchestrationEvidenceError("repository root does not exist")
    if not var_root.is_dir():
        raise OrchestrationEvidenceError("var root does not exist")

    output_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=output_path,
        field_name="output_path",
        required_prefix="artifacts/",
    )
    baseline_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=baseline_metrics_path,
        field_name="baseline_metrics_path",
        required_prefix="artifacts/",
    )
    current_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=current_metrics_path,
        field_name="current_metrics_path",
        required_prefix="artifacts/",
    )

    baseline_metrics = _load_stop_gate_metrics(path=baseline_metrics_file)
    current_metrics = _load_stop_gate_metrics(path=current_metrics_file)

    current_metric_keys = set(current_metrics["metrics"].keys())
    baseline_metric_keys = set(baseline_metrics["metrics"].keys())
    if len(current_metric_keys) != EXPECTED_METRIC_KEY_CARDINALITY:
        raise OrchestrationEvidenceError("metric key cardinality must remain frozen at 80")
    if baseline_metric_keys != current_metric_keys:
        raise OrchestrationEvidenceError("metric key set must remain exactly equal to v56")

    snapshot_payload, snapshot = _load_validated_artifact(
        var_root=var_root,
        artifact=artifacts.orchestration_state_snapshot,
        model_type=OrchestrationStateSnapshot,
        artifact_name="orchestration_state_snapshot",
    )
    write_lease_payload, write_lease = _load_validated_artifact(
        var_root=var_root,
        artifact=artifacts.write_lease_state,
        model_type=WriteLeaseState,
        artifact_name="write_lease_state",
    )
    transition_payload, transition_record = _load_validated_artifact(
        var_root=var_root,
        artifact=artifacts.role_transition_record,
        model_type=RoleTransitionRecord,
        artifact_name="role_transition_record",
    )
    handoff_payload, handoff_envelope = _load_validated_artifact(
        var_root=var_root,
        artifact=artifacts.role_handoff_envelope,
        model_type=RoleHandoffEnvelope,
        artifact_name="role_handoff_envelope",
    )

    _validate_v35b_foundation_package(snapshot=snapshot, write_lease=write_lease)
    _validate_worker_direct_user_boundary(snapshot=snapshot)
    child_roles = _validate_v35b_child_roles(snapshot=snapshot)
    _validate_v35b_dispatch_observations(write_lease=write_lease)
    _validate_handoff_envelope(handoff_payload=handoff_payload, handoff_envelope=handoff_envelope)
    builder_role_materialized = _validate_builder_role_materialized(
        child_roles=child_roles,
        write_lease=write_lease,
        transition_record=transition_record,
        handoff_envelope=handoff_envelope,
    )
    support_roles_materialized = _validate_support_roles_materialized(
        child_roles=child_roles,
        write_lease=write_lease,
        handoff_envelope=handoff_envelope,
    )
    delegated_scope_kind_recorded = _validate_delegated_scope_kind_recorded(
        child_roles=child_roles,
        write_lease=write_lease,
        handoff_envelope=handoff_envelope,
    )
    single_builder_default_enforced = _validate_v35b_single_builder_default(
        snapshot=snapshot,
        write_lease=write_lease,
    )
    support_workers_non_authoritative = _validate_support_workers_non_authoritative(
        child_roles=child_roles,
        write_lease=write_lease,
        handoff_envelope=handoff_envelope,
    )
    _validate_role_transition_record(
        snapshot=snapshot,
        write_lease=write_lease,
        transition_record=transition_record,
    )
    _validate_v35b_builder_write_lease(
        write_lease=write_lease,
        transition_record=transition_record,
    )
    handoff_artifact_materialized = _validate_v35b_handoff_artifact(
        child_roles=child_roles,
        handoff_payload=handoff_payload,
        handoff_envelope=handoff_envelope,
    )
    handoff_reconciliation_required = _validate_v35b_handoff_reconciliation(
        handoff_envelope=handoff_envelope
    )
    unreconciled_worker_output_non_authoritative = (
        _validate_unreconciled_worker_output_non_authoritative(
            snapshot=snapshot,
            handoff_envelope=handoff_envelope,
        )
    )
    zero_occurrence_empty_artifacts_materialized = _validate_v35b_zero_occurrence_artifacts(
        child_roles=child_roles,
        transition_payload=transition_payload,
        transition_record=transition_record,
        handoff_payload=handoff_payload,
        handoff_envelope=handoff_envelope,
    )

    evidence = V35BDelegationHandoffEvidence(
        evidence_input_path=output_path,
        orchestration_state_snapshot_path=artifacts.orchestration_state_snapshot.path,
        orchestration_state_snapshot_hash=artifacts.orchestration_state_snapshot.hash,
        write_lease_state_path=artifacts.write_lease_state.path,
        write_lease_state_hash=artifacts.write_lease_state.hash,
        role_transition_record_path=artifacts.role_transition_record.path,
        role_transition_record_hash=artifacts.role_transition_record.hash,
        role_handoff_envelope_path=artifacts.role_handoff_envelope.path,
        role_handoff_envelope_hash=artifacts.role_handoff_envelope.hash,
        builder_role_materialized=builder_role_materialized,
        support_roles_materialized=support_roles_materialized,
        delegated_scope_kind_recorded=delegated_scope_kind_recorded,
        single_builder_default_enforced=single_builder_default_enforced,
        support_workers_non_authoritative=support_workers_non_authoritative,
        handoff_artifact_materialized=handoff_artifact_materialized,
        handoff_reconciliation_required=handoff_reconciliation_required,
        unreconciled_worker_output_non_authoritative=(
            unreconciled_worker_output_non_authoritative
        ),
        worker_direct_user_boundary_forbidden=True,
        verification_passed=True,
        metric_key_cardinality=len(current_metric_keys),
        metric_key_exact_set_equal_v56=True,
        zero_occurrence_empty_artifacts_materialized=(
            zero_occurrence_empty_artifacts_materialized
        ),
        notes=(
            "v57 closeout-grade delegation evidence remains pre-visibility and "
            "pre-enforcement; write_lease_state@1 proves current authoritative write "
            "ownership, role_transition_record@1 proves authority-surface transitions and "
            "explicit re-roles, and role_handoff_envelope@1 remains non-authoritative "
            "until explicit orchestrator reconciliation."
        ),
    )
    payload = evidence.model_dump(mode="json", by_alias=True)
    output_file.parent.mkdir(parents=True, exist_ok=True)
    output_file.write_text(canonical_json(payload) + "\n", encoding="utf-8")
    return MaterializedArtifact(
        path=output_path,
        hash=sha256_canonical_json(payload),
        payload=payload,
    )


def materialize_v35c_transcript_visibility_evidence(
    *,
    repo_root: Path,
    var_root: Path,
    orchestration_artifacts: MaterializedOrchestrationArtifacts,
    visibility_artifacts: MaterializedWorkerVisibilityArtifacts,
    output_path: str,
    baseline_metrics_path: str,
    current_metrics_path: str,
) -> MaterializedArtifact:
    repo_root = repo_root.resolve()
    var_root = var_root.resolve()
    if not repo_root.is_dir():
        raise OrchestrationEvidenceError("repository root does not exist")
    if not var_root.is_dir():
        raise OrchestrationEvidenceError("var root does not exist")

    output_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=output_path,
        field_name="output_path",
        required_prefix="artifacts/",
    )
    baseline_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=baseline_metrics_path,
        field_name="baseline_metrics_path",
        required_prefix="artifacts/",
    )
    current_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=current_metrics_path,
        field_name="current_metrics_path",
        required_prefix="artifacts/",
    )

    baseline_metrics = _load_stop_gate_metrics(path=baseline_metrics_file)
    current_metrics = _load_stop_gate_metrics(path=current_metrics_file)
    current_metric_keys = set(current_metrics["metrics"].keys())
    baseline_metric_keys = set(baseline_metrics["metrics"].keys())
    if len(current_metric_keys) != EXPECTED_METRIC_KEY_CARDINALITY:
        raise OrchestrationEvidenceError("metric key cardinality must remain frozen at 80")
    if baseline_metric_keys != current_metric_keys:
        raise OrchestrationEvidenceError("metric key set must remain exactly equal to v57")

    visibility_payload, visibility_state = _load_validated_artifact(
        var_root=var_root,
        artifact=visibility_artifacts.worker_visibility_state,
        model_type=WorkerVisibilityState,
        artifact_name="worker_visibility_state",
    )
    snapshot_payload, snapshot = _load_validated_artifact(
        var_root=var_root,
        artifact=orchestration_artifacts.orchestration_state_snapshot,
        model_type=OrchestrationStateSnapshot,
        artifact_name="orchestration_state_snapshot",
    )
    topology_payload, topology = _load_validated_artifact(
        var_root=var_root,
        artifact=orchestration_artifacts.execution_topology_state,
        model_type=ExecutionTopologyState,
        artifact_name="execution_topology_state",
    )
    handoff_payload, handoff_envelope = _load_validated_artifact(
        var_root=var_root,
        artifact=orchestration_artifacts.role_handoff_envelope,
        model_type=RoleHandoffEnvelope,
        artifact_name="role_handoff_envelope",
    )

    _validate_worker_direct_user_boundary(snapshot=snapshot)
    _validate_handoff_envelope(handoff_payload=handoff_payload, handoff_envelope=handoff_envelope)
    read_only_visibility_preserved = _validate_v35c_read_only_visibility(
        snapshot=snapshot,
        visibility_state=visibility_state,
    )
    (
        epistemic_lane_labels_present,
        explicit_lane_absence_materialized,
        explicit_divergence_state_materialized,
    ) = _validate_v35c_lane_projection(visibility_state=visibility_state)
    continuation_bridge_visibility_present_when_available = _validate_v35c_continuity(
        snapshot=snapshot,
        topology=topology,
        visibility_state=visibility_state,
    )
    no_ad_hoc_progress_summary_bypass = _validate_v35c_progress_fields(
        snapshot=snapshot,
        visibility_state=visibility_state,
        handoff_envelope=handoff_envelope,
    )
    raw_transcript_non_authoritative = _validate_v35c_raw_transcript_authority(
        visibility_state=visibility_state
    )
    worker_self_report_non_authoritative_until_reconciled = (
        _validate_v35c_worker_self_report_authority(visibility_state=visibility_state)
    )
    worker_direct_user_boundary_forbidden = _validate_v35c_worker_direct_user_boundary(
        visibility_state=visibility_state
    )

    evidence = V35CTranscriptVisibilityEvidence(
        evidence_input_path=output_path,
        worker_visibility_state_path=visibility_artifacts.worker_visibility_state.path,
        worker_visibility_state_hash=visibility_artifacts.worker_visibility_state.hash,
        orchestration_state_snapshot_path=orchestration_artifacts.orchestration_state_snapshot.path,
        orchestration_state_snapshot_hash=orchestration_artifacts.orchestration_state_snapshot.hash,
        role_handoff_envelope_path=orchestration_artifacts.role_handoff_envelope.path,
        role_handoff_envelope_hash=orchestration_artifacts.role_handoff_envelope.hash,
        read_only_visibility_preserved=read_only_visibility_preserved,
        epistemic_lane_labels_present=epistemic_lane_labels_present,
        explicit_lane_absence_materialized=explicit_lane_absence_materialized,
        explicit_divergence_state_materialized=explicit_divergence_state_materialized,
        continuation_bridge_visibility_present_when_available=(
            continuation_bridge_visibility_present_when_available
        ),
        no_ad_hoc_progress_summary_bypass=no_ad_hoc_progress_summary_bypass,
        raw_transcript_non_authoritative=raw_transcript_non_authoritative,
        worker_self_report_non_authoritative_until_reconciled=(
            worker_self_report_non_authoritative_until_reconciled
        ),
        worker_direct_user_boundary_forbidden=worker_direct_user_boundary_forbidden,
        verification_passed=True,
        metric_key_cardinality=len(current_metric_keys),
        metric_key_exact_set_equal_v57=True,
        notes=(
            "v58 closeout-grade visibility evidence remains observational-only and "
            "pre-topology/pre-enforcement; transcript lanes remain epistemically separated, "
            "non-authoritative by visibility alone, and continuity rendering remains explicit."
        ),
    )
    payload = evidence.model_dump(mode="json", by_alias=True)
    output_file.parent.mkdir(parents=True, exist_ok=True)
    output_file.write_text(canonical_json(payload) + "\n", encoding="utf-8")
    return MaterializedArtifact(
        path=output_path,
        hash=sha256_canonical_json(payload),
        payload=payload,
    )


def materialize_v35d_topology_duty_map_evidence(
    *,
    repo_root: Path,
    var_root: Path,
    orchestration_artifacts: MaterializedOrchestrationArtifacts,
    visibility_artifacts: MaterializedWorkerVisibilityArtifacts,
    topology_artifacts: MaterializedTopologyDutyMapArtifacts,
    output_path: str,
    baseline_metrics_path: str,
    current_metrics_path: str,
) -> MaterializedArtifact:
    repo_root = repo_root.resolve()
    var_root = var_root.resolve()
    if not repo_root.is_dir():
        raise OrchestrationEvidenceError("repository root does not exist")
    if not var_root.is_dir():
        raise OrchestrationEvidenceError("var root does not exist")

    output_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=output_path,
        field_name="output_path",
        required_prefix="artifacts/",
    )
    baseline_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=baseline_metrics_path,
        field_name="baseline_metrics_path",
        required_prefix="artifacts/",
    )
    current_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=current_metrics_path,
        field_name="current_metrics_path",
        required_prefix="artifacts/",
    )

    baseline_metrics = _load_stop_gate_metrics(path=baseline_metrics_file)
    current_metrics = _load_stop_gate_metrics(path=current_metrics_file)
    current_metric_keys = set(current_metrics["metrics"].keys())
    baseline_metric_keys = set(baseline_metrics["metrics"].keys())
    if len(current_metric_keys) != EXPECTED_METRIC_KEY_CARDINALITY:
        raise OrchestrationEvidenceError("metric key cardinality must remain frozen at 80")
    if baseline_metric_keys != current_metric_keys:
        raise OrchestrationEvidenceError("metric key set must remain exactly equal to v58")

    _snapshot_payload, snapshot = _load_validated_artifact(
        var_root=var_root,
        artifact=orchestration_artifacts.orchestration_state_snapshot,
        model_type=OrchestrationStateSnapshot,
        artifact_name="orchestration_state_snapshot",
    )
    _execution_topology_payload, execution_topology_state = _load_validated_artifact(
        var_root=var_root,
        artifact=orchestration_artifacts.execution_topology_state,
        model_type=ExecutionTopologyState,
        artifact_name="execution_topology_state",
    )
    _write_lease_payload, write_lease_state = _load_validated_artifact(
        var_root=var_root,
        artifact=orchestration_artifacts.write_lease_state,
        model_type=WriteLeaseState,
        artifact_name="write_lease_state",
    )
    handoff_payload, handoff_envelope = _load_validated_artifact(
        var_root=var_root,
        artifact=orchestration_artifacts.role_handoff_envelope,
        model_type=RoleHandoffEnvelope,
        artifact_name="role_handoff_envelope",
    )
    _visibility_payload, visibility_state = _load_validated_artifact(
        var_root=var_root,
        artifact=visibility_artifacts.worker_visibility_state,
        model_type=WorkerVisibilityState,
        artifact_name="worker_visibility_state",
    )
    _topology_payload, topology_state = _load_validated_artifact(
        var_root=var_root,
        artifact=topology_artifacts.topology_duty_map_state,
        model_type=TopologyDutyMapState,
        artifact_name="topology_duty_map_state",
    )

    _validate_worker_direct_user_boundary(snapshot=snapshot)
    _validate_handoff_envelope(handoff_payload=handoff_payload, handoff_envelope=handoff_envelope)
    _validate_v35c_worker_direct_user_boundary(visibility_state=visibility_state)
    non_authoritative_topology_surface_preserved = _validate_v35d_read_only_topology(
        topology_state=topology_state
    )
    current_write_lease_holder_projected = _validate_v35d_write_lease_projection(
        write_lease_state=write_lease_state,
        topology_state=topology_state,
    )
    current_duty_not_authority_inflating = _validate_v35d_current_duty(
        write_lease_state=write_lease_state,
        topology_state=topology_state,
    )
    provenance_markers_materialized = _validate_v35d_provenance_markers(
        snapshot=snapshot,
        execution_topology_state=execution_topology_state,
        topology_state=topology_state,
    )
    artifact_and_event_stream_provenance_refs_resolve = _validate_v35d_provenance_refs(
        var_root=var_root,
        snapshot=snapshot,
        topology_state=topology_state,
        execution_topology_path=orchestration_artifacts.execution_topology_state.path,
        write_lease_path=orchestration_artifacts.write_lease_state.path,
        visibility_path=visibility_artifacts.worker_visibility_state.path,
        handoff_path=orchestration_artifacts.role_handoff_envelope.path,
    )
    advisory_blockers_not_rendered_as_governance_blockers = _validate_v35d_advisory_blockers(
        visibility_state=visibility_state,
        topology_state=topology_state,
    )
    continuation_bridge_and_compaction_visibility_preserved = _validate_v35d_continuity(
        snapshot=snapshot,
        execution_topology_state=execution_topology_state,
        topology_state=topology_state,
    )
    derived_from_canonical_execution_state_only = _validate_v35d_projection(
        snapshot=snapshot,
        execution_topology_state=execution_topology_state,
        write_lease_state=write_lease_state,
        visibility_state=visibility_state,
        handoff_envelope=handoff_envelope,
        topology_state=topology_state,
        source_artifacts=TopologyDutyMapSourceArtifacts(
            execution_topology_state_path=orchestration_artifacts.execution_topology_state.path,
            write_lease_state_path=orchestration_artifacts.write_lease_state.path,
            worker_visibility_state_path=visibility_artifacts.worker_visibility_state.path,
            role_handoff_envelope_path=orchestration_artifacts.role_handoff_envelope.path,
        ),
    )

    evidence = V35DTopologyDutyMapEvidence(
        evidence_input_path=output_path,
        topology_duty_map_state_path=topology_artifacts.topology_duty_map_state.path,
        topology_duty_map_state_hash=topology_artifacts.topology_duty_map_state.hash,
        execution_topology_state_path=orchestration_artifacts.execution_topology_state.path,
        execution_topology_state_hash=orchestration_artifacts.execution_topology_state.hash,
        worker_visibility_state_path=visibility_artifacts.worker_visibility_state.path,
        worker_visibility_state_hash=visibility_artifacts.worker_visibility_state.hash,
        derived_from_canonical_execution_state_only=derived_from_canonical_execution_state_only,
        current_write_lease_holder_projected=current_write_lease_holder_projected,
        current_duty_not_authority_inflating=current_duty_not_authority_inflating,
        provenance_markers_materialized=provenance_markers_materialized,
        artifact_and_event_stream_provenance_refs_resolve=(
            artifact_and_event_stream_provenance_refs_resolve
        ),
        advisory_blockers_not_rendered_as_governance_blockers=(
            advisory_blockers_not_rendered_as_governance_blockers
        ),
        continuation_bridge_and_compaction_visibility_preserved=(
            continuation_bridge_and_compaction_visibility_preserved
        ),
        non_authoritative_topology_surface_preserved=(
            non_authoritative_topology_surface_preserved
        ),
        verification_passed=True,
        metric_key_cardinality=len(current_metric_keys),
        metric_key_exact_set_equal_v58=True,
        notes=(
            "v59 closeout-grade topology evidence remains observational-only and "
            "pre-enforcement; topology_duty_map_state@1 is hash-bound to canonical "
            "execution/lease/visibility/handoff inputs, provenance refs resolve to "
            "artifacts or event streams, and continuity remains explicit."
        ),
    )
    payload = evidence.model_dump(mode="json", by_alias=True)
    output_file.parent.mkdir(parents=True, exist_ok=True)
    output_file.write_text(canonical_json(payload) + "\n", encoding="utf-8")
    return MaterializedArtifact(
        path=output_path,
        hash=sha256_canonical_json(payload),
        payload=payload,
    )


def materialize_v35e_runtime_enforcement_evidence(
    *,
    repo_root: Path,
    var_root: Path,
    orchestration_artifacts: MaterializedOrchestrationArtifacts,
    visibility_artifacts: MaterializedWorkerVisibilityArtifacts,
    topology_artifacts: MaterializedTopologyDutyMapArtifacts,
    output_path: str,
    baseline_metrics_path: str,
    current_metrics_path: str,
) -> MaterializedArtifact:
    repo_root = repo_root.resolve()
    var_root = var_root.resolve()
    if not repo_root.is_dir():
        raise OrchestrationEvidenceError("repository root does not exist")
    if not var_root.is_dir():
        raise OrchestrationEvidenceError("var root does not exist")

    output_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=output_path,
        field_name="output_path",
        required_prefix="artifacts/",
    )
    baseline_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=baseline_metrics_path,
        field_name="baseline_metrics_path",
        required_prefix="artifacts/",
    )
    current_metrics_file = _resolve_repo_relative_path(
        root=repo_root,
        path_text=current_metrics_path,
        field_name="current_metrics_path",
        required_prefix="artifacts/",
    )

    baseline_metrics = _load_stop_gate_metrics(path=baseline_metrics_file)
    current_metrics = _load_stop_gate_metrics(path=current_metrics_file)
    current_metric_keys = set(current_metrics["metrics"].keys())
    baseline_metric_keys = set(baseline_metrics["metrics"].keys())
    if len(current_metric_keys) != EXPECTED_METRIC_KEY_CARDINALITY:
        raise OrchestrationEvidenceError("metric key cardinality must remain frozen at 80")
    if baseline_metric_keys != current_metric_keys:
        raise OrchestrationEvidenceError("metric key set must remain exactly equal to v59")

    snapshot_payload, snapshot = _load_validated_artifact(
        var_root=var_root,
        artifact=orchestration_artifacts.orchestration_state_snapshot,
        model_type=OrchestrationStateSnapshot,
        artifact_name="orchestration_state_snapshot",
    )
    _write_lease_payload, write_lease_state = _load_validated_artifact(
        var_root=var_root,
        artifact=orchestration_artifacts.write_lease_state,
        model_type=WriteLeaseState,
        artifact_name="write_lease_state",
    )
    transition_payload, transition_record = _load_validated_artifact(
        var_root=var_root,
        artifact=orchestration_artifacts.role_transition_record,
        model_type=RoleTransitionRecord,
        artifact_name="role_transition_record",
    )
    handoff_payload, handoff_envelope = _load_validated_artifact(
        var_root=var_root,
        artifact=orchestration_artifacts.role_handoff_envelope,
        model_type=RoleHandoffEnvelope,
        artifact_name="role_handoff_envelope",
    )
    _visibility_payload, visibility_state = _load_validated_artifact(
        var_root=var_root,
        artifact=visibility_artifacts.worker_visibility_state,
        model_type=WorkerVisibilityState,
        artifact_name="worker_visibility_state",
    )
    _topology_payload, topology_state = _load_validated_artifact(
        var_root=var_root,
        artifact=topology_artifacts.topology_duty_map_state,
        model_type=TopologyDutyMapState,
        artifact_name="topology_duty_map_state",
    )

    required_enforcement_surfaces_active = _validate_v35e_required_enforcement_surfaces()
    single_builder_default_enforced_at_runtime = _validate_v35e_single_builder_default_runtime()
    support_role_proxy_authority_blocked = _validate_v35e_support_role_proxy_authority()
    claimed_work_handoff_validation_enforced = _validate_v35e_claimed_work_handoff_validation()
    scope_kind_validation_enforced = _validate_v35e_scope_kind_validation()
    deterministic_denial_surfaces_recorded = _validate_v35e_deterministic_denial_surfaces()
    released_happy_path_preserved_under_runtime_enforcement = _validate_v35e_released_happy_path(
        snapshot=snapshot,
        snapshot_payload=snapshot_payload,
        write_lease_state=write_lease_state,
        transition_payload=transition_payload,
        transition_record=transition_record,
        handoff_payload=handoff_payload,
        handoff_envelope=handoff_envelope,
        visibility_state=visibility_state,
        topology_state=topology_state,
    )
    observability_surfaces_remain_read_only = _validate_v35e_observability_surfaces(
        snapshot=snapshot,
        visibility_state=visibility_state,
        topology_state=topology_state,
    )
    acceptance_and_closeout_authority_preserved = (
        _validate_v35e_acceptance_and_closeout_authority(
            snapshot=snapshot,
            transition_record=transition_record,
            handoff_envelope=handoff_envelope,
            topology_state=topology_state,
        )
    )
    worker_direct_user_boundary_forbidden = _validate_v35e_worker_direct_user_boundary(
        snapshot=snapshot,
        visibility_state=visibility_state,
        topology_state=topology_state,
    )

    evidence = V35ERuntimeEnforcementEvidence(
        evidence_input_path=output_path,
        orchestration_state_snapshot_path=orchestration_artifacts.orchestration_state_snapshot.path,
        orchestration_state_snapshot_hash=orchestration_artifacts.orchestration_state_snapshot.hash,
        write_lease_state_path=orchestration_artifacts.write_lease_state.path,
        write_lease_state_hash=orchestration_artifacts.write_lease_state.hash,
        role_transition_record_path=orchestration_artifacts.role_transition_record.path,
        role_transition_record_hash=orchestration_artifacts.role_transition_record.hash,
        role_handoff_envelope_path=orchestration_artifacts.role_handoff_envelope.path,
        role_handoff_envelope_hash=orchestration_artifacts.role_handoff_envelope.hash,
        worker_visibility_state_path=visibility_artifacts.worker_visibility_state.path,
        worker_visibility_state_hash=visibility_artifacts.worker_visibility_state.hash,
        topology_duty_map_state_path=topology_artifacts.topology_duty_map_state.path,
        topology_duty_map_state_hash=topology_artifacts.topology_duty_map_state.hash,
        required_enforcement_surfaces_active=required_enforcement_surfaces_active,
        single_builder_default_enforced_at_runtime=single_builder_default_enforced_at_runtime,
        support_role_proxy_authority_blocked=support_role_proxy_authority_blocked,
        claimed_work_handoff_validation_enforced=claimed_work_handoff_validation_enforced,
        scope_kind_validation_enforced=scope_kind_validation_enforced,
        deterministic_denial_surfaces_recorded=deterministic_denial_surfaces_recorded,
        released_happy_path_preserved_under_runtime_enforcement=(
            released_happy_path_preserved_under_runtime_enforcement
        ),
        observability_surfaces_remain_read_only=observability_surfaces_remain_read_only,
        acceptance_and_closeout_authority_preserved=(
            acceptance_and_closeout_authority_preserved
        ),
        worker_direct_user_boundary_forbidden=worker_direct_user_boundary_forbidden,
        verification_passed=True,
        metric_key_cardinality=len(current_metric_keys),
        metric_key_exact_set_equal_v59=True,
        notes=(
            "v60 closeout-grade runtime-enforcement evidence binds the shared denial "
            "helpers to the frozen v56-v59 state/visibility/topology substrate; "
            "all required enforcement surfaces remain active, invalid role/task/scope/"
            "authority paths fail closed with stable URM runtime-enforcement codes, "
            "and the released read-only/authority-preserving happy path remains intact."
        ),
    )
    payload = evidence.model_dump(mode="json", by_alias=True)
    output_file.parent.mkdir(parents=True, exist_ok=True)
    output_file.write_text(canonical_json(payload) + "\n", encoding="utf-8")
    return MaterializedArtifact(
        path=output_path,
        hash=sha256_canonical_json(payload),
        payload=payload,
    )


def _validate_v35e_required_enforcement_surfaces() -> bool:
    expected_surfaces = (
        "spawn_request_boundary",
        "orchestration_state_materialization_boundary",
        "worker_visibility_materialization_boundary",
        "topology_duty_map_materialization_boundary",
    )
    if REQUIRED_ENFORCEMENT_SURFACES != expected_surfaces:
        raise OrchestrationEvidenceError("required runtime enforcement surfaces drift detected")
    invalid_candidate = _invalid_role_task_candidate()
    for boundary in expected_surfaces:
        _expect_runtime_enforcement_error(
            expected_code=INVALID_ROLE_TASK_COMBINATION_CODE,
            action=lambda boundary=boundary: validate_runtime_enforcement_candidate(
                boundary=boundary,
                candidate=invalid_candidate,
                parent_writes_allowed=False,
            ),
        )
    return True


def _validate_v35e_single_builder_default_runtime() -> bool:
    builder_candidates = [
        _builder_candidate(subject_id="builder-runtime-1", status="running"),
        _builder_candidate(subject_id="builder-runtime-2", status="queued"),
    ]
    for boundary in REQUIRED_ENFORCEMENT_SURFACES:
        try:
            _expect_runtime_enforcement_error(
                expected_code=SINGLE_BUILDER_DEFAULT_VIOLATION_CODE,
                action=lambda boundary=boundary: validate_single_builder_default(
                    boundary=boundary,
                    candidates=builder_candidates,
                ),
            )
        except OrchestrationEvidenceError as exc:
            raise OrchestrationEvidenceError(
                "single-builder default violation accepted"
            ) from exc
    return True


def _validate_v35e_support_role_proxy_authority() -> bool:
    for boundary in REQUIRED_ENFORCEMENT_SURFACES:
        try:
            _expect_runtime_enforcement_error(
                expected_code=SUPPORT_PROXY_AUTHORITY_CODE,
                action=lambda boundary=boundary: validate_runtime_enforcement_candidate(
                    boundary=boundary,
                    candidate=_support_proxy_candidate(authoritative_write_lease_granted=True),
                    parent_writes_allowed=True,
                ),
            )
            _expect_runtime_enforcement_error(
                expected_code=SUPPORT_PROXY_AUTHORITY_CODE,
                action=lambda boundary=boundary: validate_runtime_enforcement_candidate(
                    boundary=boundary,
                    candidate=_support_proxy_candidate(authoritative_write_lease_granted=False),
                    parent_writes_allowed=True,
                ),
            )
        except OrchestrationEvidenceError as exc:
            raise OrchestrationEvidenceError(
                "support-role proxy authority violation accepted"
            ) from exc
    return True


def _validate_v35e_claimed_work_handoff_validation() -> bool:
    expected_surfaces = (
        "orchestration_state_materialization_boundary",
        "worker_visibility_materialization_boundary",
        "topology_duty_map_materialization_boundary",
    )
    if MATERIALIZATION_ENFORCEMENT_SURFACES != expected_surfaces:
        raise OrchestrationEvidenceError("claimed-work handoff enforcement surface drift detected")
    for boundary in expected_surfaces:
        try:
            _expect_runtime_enforcement_error(
                expected_code=CLAIMED_WORK_HANDOFF_INVALID_CODE,
                action=lambda boundary=boundary: validate_claimed_work_handoff_field(
                    boundary=boundary,
                    subject_id="claimed-work-child-1",
                    field_name="requested_role",
                    value=None,
                    claimed_work_present=True,
                    context={"session_id": "claimed-work-parent-1"},
                ),
            )
        except OrchestrationEvidenceError as exc:
            raise OrchestrationEvidenceError(
                "claimed-work handoff missing required fields accepted"
            ) from exc
    return True


def _validate_v35e_scope_kind_validation() -> bool:
    invalid_scope_candidate = _invalid_scope_kind_candidate()
    for boundary in REQUIRED_ENFORCEMENT_SURFACES:
        try:
            _expect_runtime_enforcement_error(
                expected_code=SCOPE_KIND_INVALID_CODE,
                action=lambda boundary=boundary: validate_runtime_enforcement_candidate(
                    boundary=boundary,
                    candidate=invalid_scope_candidate,
                    parent_writes_allowed=True,
                ),
            )
        except OrchestrationEvidenceError as exc:
            raise OrchestrationEvidenceError("scope kind missing or malformed accepted") from exc
    return True


def _validate_v35e_deterministic_denial_surfaces() -> bool:
    expected_codes = (
        INVALID_ROLE_TASK_COMBINATION_CODE,
        SINGLE_BUILDER_DEFAULT_VIOLATION_CODE,
        SUPPORT_PROXY_AUTHORITY_CODE,
        SCOPE_KIND_INVALID_CODE,
        CLAIMED_WORK_HANDOFF_INVALID_CODE,
    )
    if DETERMINISTIC_DENIAL_CODES != expected_codes:
        raise OrchestrationEvidenceError("deterministic denial code family drift detected")
    # Recheck one representative path for each stable code so closeout binds the exact family.
    _expect_runtime_enforcement_error(
        expected_code=INVALID_ROLE_TASK_COMBINATION_CODE,
        action=lambda: validate_runtime_enforcement_candidate(
            boundary="spawn_request_boundary",
            candidate=_invalid_role_task_candidate(),
            parent_writes_allowed=False,
        ),
    )
    _expect_runtime_enforcement_error(
        expected_code=SINGLE_BUILDER_DEFAULT_VIOLATION_CODE,
        action=lambda: validate_single_builder_default(
            boundary="spawn_request_boundary",
            candidates=[
                _builder_candidate(subject_id="builder-code-1", status="running"),
                _builder_candidate(subject_id="builder-code-2", status="queued"),
            ],
        ),
    )
    _expect_runtime_enforcement_error(
        expected_code=SUPPORT_PROXY_AUTHORITY_CODE,
        action=lambda: validate_runtime_enforcement_candidate(
            boundary="spawn_request_boundary",
            candidate=_support_proxy_candidate(authoritative_write_lease_granted=False),
            parent_writes_allowed=True,
        ),
    )
    _expect_runtime_enforcement_error(
        expected_code=SCOPE_KIND_INVALID_CODE,
        action=lambda: validate_runtime_enforcement_candidate(
            boundary="orchestration_state_materialization_boundary",
            candidate=_invalid_scope_kind_candidate(),
            parent_writes_allowed=True,
        ),
    )
    _expect_runtime_enforcement_error(
        expected_code=CLAIMED_WORK_HANDOFF_INVALID_CODE,
        action=lambda: validate_claimed_work_handoff_field(
            boundary="topology_duty_map_materialization_boundary",
            subject_id="claimed-work-child-2",
            field_name="granted_role",
            value=None,
            claimed_work_present=True,
            context={"session_id": "claimed-work-parent-2"},
        ),
    )
    return True


def _validate_v35e_released_happy_path(
    *,
    snapshot: OrchestrationStateSnapshot,
    snapshot_payload: dict[str, Any],
    write_lease_state: WriteLeaseState,
    transition_payload: dict[str, Any],
    transition_record: RoleTransitionRecord,
    handoff_payload: dict[str, Any],
    handoff_envelope: RoleHandoffEnvelope,
    visibility_state: WorkerVisibilityState,
    topology_state: TopologyDutyMapState,
) -> bool:
    _validate_v35b_foundation_package(snapshot=snapshot, write_lease=write_lease_state)
    _validate_canonical_identity_fields(snapshot_payload=snapshot_payload, snapshot=snapshot)
    child_roles = _validate_v35b_child_roles(snapshot=snapshot)
    _validate_builder_role_materialized(
        child_roles=child_roles,
        write_lease=write_lease_state,
        transition_record=transition_record,
        handoff_envelope=handoff_envelope,
    )
    _validate_support_roles_materialized(
        child_roles=child_roles,
        write_lease=write_lease_state,
        handoff_envelope=handoff_envelope,
    )
    _validate_delegated_scope_kind_recorded(
        child_roles=child_roles,
        write_lease=write_lease_state,
        handoff_envelope=handoff_envelope,
    )
    _validate_v35b_single_builder_default(snapshot=snapshot, write_lease=write_lease_state)
    _validate_support_workers_non_authoritative(
        child_roles=child_roles,
        write_lease=write_lease_state,
        handoff_envelope=handoff_envelope,
    )
    _validate_v35b_builder_write_lease(
        write_lease=write_lease_state,
        transition_record=transition_record,
    )
    _validate_v35b_handoff_artifact(
        child_roles=child_roles,
        handoff_payload=handoff_payload,
        handoff_envelope=handoff_envelope,
    )
    _validate_v35b_handoff_reconciliation(handoff_envelope=handoff_envelope)
    _validate_unreconciled_worker_output_non_authoritative(
        snapshot=snapshot,
        handoff_envelope=handoff_envelope,
    )
    _validate_v35b_zero_occurrence_artifacts(
        child_roles=child_roles,
        transition_payload=transition_payload,
        transition_record=transition_record,
        handoff_payload=handoff_payload,
        handoff_envelope=handoff_envelope,
    )
    _validate_v35c_progress_fields(
        snapshot=snapshot,
        visibility_state=visibility_state,
        handoff_envelope=handoff_envelope,
    )
    _validate_v35d_write_lease_projection(
        write_lease_state=write_lease_state,
        topology_state=topology_state,
    )
    _validate_v35d_current_duty(
        write_lease_state=write_lease_state,
        topology_state=topology_state,
    )
    return True


def _validate_v35e_observability_surfaces(
    *,
    snapshot: OrchestrationStateSnapshot,
    visibility_state: WorkerVisibilityState,
    topology_state: TopologyDutyMapState,
) -> bool:
    _validate_v35c_read_only_visibility(snapshot=snapshot, visibility_state=visibility_state)
    _validate_v35c_lane_projection(visibility_state=visibility_state)
    _validate_v35c_raw_transcript_authority(visibility_state=visibility_state)
    _validate_v35c_worker_self_report_authority(visibility_state=visibility_state)
    _validate_v35d_read_only_topology(topology_state=topology_state)
    return True


def _validate_v35e_acceptance_and_closeout_authority(
    *,
    snapshot: OrchestrationStateSnapshot,
    transition_record: RoleTransitionRecord,
    handoff_envelope: RoleHandoffEnvelope,
    topology_state: TopologyDutyMapState,
) -> bool:
    orchestrator_roles = [
        role for role in snapshot.current_roles if role.actor_id == snapshot.orchestrator_session_id
    ]
    if len(orchestrator_roles) != 1 or orchestrator_roles[0].role != "main_orchestrator":
        raise OrchestrationEvidenceError("acceptance or closeout authority released")
    for role in snapshot.current_roles:
        if role.actor_id == snapshot.orchestrator_session_id:
            continue
        if role.authority_domain == "governance":
            raise OrchestrationEvidenceError("acceptance or closeout authority released")
    for node in topology_state.nodes:
        if node.actor_id == topology_state.orchestrator_session_id:
            continue
        if node.authority_domain == "governance":
            raise OrchestrationEvidenceError("acceptance or closeout authority released")
    if any(entry.granted_by != CONTROL_PLANE_OWNER for entry in transition_record.entries):
        raise OrchestrationEvidenceError("acceptance or closeout authority released")
    _validate_unreconciled_worker_output_non_authoritative(
        snapshot=snapshot,
        handoff_envelope=handoff_envelope,
    )
    return True


def _validate_v35e_worker_direct_user_boundary(
    *,
    snapshot: OrchestrationStateSnapshot,
    visibility_state: WorkerVisibilityState,
    topology_state: TopologyDutyMapState,
) -> bool:
    _validate_worker_direct_user_boundary(snapshot=snapshot)
    _validate_v35c_worker_direct_user_boundary(visibility_state=visibility_state)
    _validate_v35d_read_only_topology(topology_state=topology_state)
    return True


def _invalid_role_task_candidate() -> RuntimeEnforcementCandidate:
    return RuntimeEnforcementCandidate(
        subject_id="invalid-role-task-child",
        requested_role="explorer",
        granted_role="explorer",
        delegation_task_kind="write_task",
        delegated_scope_kind="subtree",
        delegated_scope_artifact_surfaces=("implementation",),
        authoritative_write_lease_granted=False,
        status="queued",
    )


def _invalid_scope_kind_candidate() -> RuntimeEnforcementCandidate:
    return RuntimeEnforcementCandidate(
        subject_id="invalid-scope-kind-child",
        requested_role="explorer",
        granted_role="explorer",
        delegation_task_kind=ROLE_TASK_KIND_BY_ROLE["explorer"],
        delegated_scope_kind="invalid_scope_kind",
        delegated_scope_artifact_surfaces=("none",),
        authoritative_write_lease_granted=False,
        status="running",
    )


def _support_proxy_candidate(
    *,
    authoritative_write_lease_granted: bool,
) -> RuntimeEnforcementCandidate:
    artifact_surfaces = ("none",) if authoritative_write_lease_granted else ("implementation",)
    return RuntimeEnforcementCandidate(
        subject_id="support-proxy-child",
        requested_role="explorer",
        granted_role="explorer",
        delegation_task_kind=ROLE_TASK_KIND_BY_ROLE["explorer"],
        delegated_scope_kind="artifact_surface_only",
        delegated_scope_artifact_surfaces=artifact_surfaces,
        authoritative_write_lease_granted=authoritative_write_lease_granted,
        status="queued",
    )


def _builder_candidate(*, subject_id: str, status: str) -> RuntimeEnforcementCandidate:
    return RuntimeEnforcementCandidate(
        subject_id=subject_id,
        requested_role="builder_worker",
        granted_role="builder_worker",
        delegation_task_kind=ROLE_TASK_KIND_BY_ROLE["builder_worker"],
        delegated_scope_kind="subtree",
        delegated_scope_artifact_surfaces=("implementation",),
        authoritative_write_lease_granted=True,
        status=status,
    )


def _expect_runtime_enforcement_error(
    *,
    expected_code: str,
    action: Any,
) -> None:
    try:
        action()
    except URMError as exc:
        if exc.detail.code != expected_code:
            raise OrchestrationEvidenceError(
                "deterministic denial code missing or unstable"
            ) from exc
        boundary = exc.detail.context.get("boundary")
        if boundary not in REQUIRED_ENFORCEMENT_SURFACES:
            raise OrchestrationEvidenceError("required runtime enforcement surfaces drift detected")
        if not exc.detail.message:
            raise OrchestrationEvidenceError("deterministic denial code missing or unstable")
        return
    raise OrchestrationEvidenceError("required runtime enforcement surface missing or bypassed")


def _load_validated_artifact(
    *,
    var_root: Path,
    artifact: MaterializedArtifact,
    model_type: type[ModelT],
    artifact_name: str,
) -> tuple[dict[str, Any], ModelT]:
    artifact_path = _resolve_var_relative_path(
        root=var_root,
        path_text=artifact.path,
        field_name=f"{artifact_name}_path",
    )
    payload = _load_json_object(path=artifact_path)
    actual_hash = sha256_canonical_json(payload)
    if actual_hash != artifact.hash:
        raise OrchestrationEvidenceError(f"{artifact_name} hash mismatch")
    try:
        model = model_type.model_validate(payload)
    except ValidationError as exc:  # pragma: no cover - pydantic surface
        raise OrchestrationEvidenceError(f"{artifact_name} payload is invalid") from exc
    return payload, model


def _load_stop_gate_metrics(*, path: Path) -> dict[str, Any]:
    payload = _load_json_object(path=path)
    if payload.get("schema") != STOP_GATE_METRICS_SCHEMA:
        raise OrchestrationEvidenceError(f"{path} schema mismatch")
    metrics = payload.get("metrics")
    if not isinstance(metrics, dict):
        raise OrchestrationEvidenceError(f"{path} metrics object missing")
    if not all(isinstance(key, str) and key for key in metrics):
        raise OrchestrationEvidenceError(f"{path} metrics keys must be non-empty strings")
    return payload


def _load_json_object(*, path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise OrchestrationEvidenceError(f"{path} not found") from exc
    except json.JSONDecodeError as exc:
        raise OrchestrationEvidenceError(f"{path} contains invalid JSON") from exc
    if not isinstance(payload, dict):
        raise OrchestrationEvidenceError(f"{path} must contain a JSON object")
    return payload


def _resolve_repo_relative_path(
    *,
    root: Path,
    path_text: str,
    field_name: str,
    required_prefix: str,
) -> Path:
    if not isinstance(path_text, str) or not path_text.startswith(required_prefix):
        raise OrchestrationEvidenceError(f"{field_name} must start with {required_prefix}")
    return _resolve_relative_path(root=root, path_text=path_text, field_name=field_name)


def _resolve_var_relative_path(*, root: Path, path_text: str, field_name: str) -> Path:
    return _resolve_relative_path(root=root, path_text=path_text, field_name=field_name)


def _resolve_relative_path(*, root: Path, path_text: str, field_name: str) -> Path:
    if (
        not isinstance(path_text, str)
        or not path_text
        or "\\" in path_text
        or Path(path_text).is_absolute()
        or ".." in Path(path_text).parts
    ):
        raise OrchestrationEvidenceError(f"{field_name} must be a safe relative path")
    resolved = (root / path_text).resolve()
    if not resolved.is_relative_to(root):
        raise OrchestrationEvidenceError(f"{field_name} escapes the allowed root")
    return resolved


def _validate_foundation_package(
    *,
    snapshot: OrchestrationStateSnapshot,
    topology: ExecutionTopologyState,
    write_lease: WriteLeaseState,
) -> None:
    if snapshot.orchestration_foundation_package != ORCHESTRATION_FOUNDATION_PACKAGE:
        raise OrchestrationEvidenceError("snapshot foundation package drift detected")
    if topology.orchestration_foundation_package != ORCHESTRATION_FOUNDATION_PACKAGE:
        raise OrchestrationEvidenceError("topology foundation package drift detected")
    if write_lease.orchestration_foundation_package != ORCHESTRATION_FOUNDATION_PACKAGE:
        raise OrchestrationEvidenceError("write lease foundation package drift detected")


def _validate_v35b_foundation_package(
    *,
    snapshot: OrchestrationStateSnapshot,
    write_lease: WriteLeaseState,
) -> None:
    if snapshot.orchestration_foundation_package != ORCHESTRATION_FOUNDATION_PACKAGE:
        raise OrchestrationEvidenceError("snapshot foundation package drift detected")
    if write_lease.orchestration_foundation_package != ORCHESTRATION_FOUNDATION_PACKAGE:
        raise OrchestrationEvidenceError("write lease foundation package drift detected")


def _validate_single_writer_default(
    *,
    snapshot: OrchestrationStateSnapshot,
    write_lease: WriteLeaseState,
) -> None:
    if snapshot.single_writer_default_enforced is not True:
        raise OrchestrationEvidenceError("snapshot single-writer default must be enforced")
    if write_lease.single_writer_default_enforced is not True:
        raise OrchestrationEvidenceError("write lease single-writer default must be enforced")
    if write_lease.active_authoritative_writer_count > 1:
        raise OrchestrationEvidenceError("multiple authoritative writers active by default")
    authoritative_roles = [
        role for role in snapshot.current_roles if role.authoritative_write_access
    ]
    holder = write_lease.current_authoritative_holder
    if holder is None:
        if write_lease.active_authoritative_writer_count != 0:
            raise OrchestrationEvidenceError("authoritative writer count must be zero")
        if snapshot.current_authoritative_holder_actor_id is not None:
            raise OrchestrationEvidenceError("snapshot authoritative holder must be absent")
        if authoritative_roles:
            raise OrchestrationEvidenceError("no actor may hold authoritative writes")
    else:
        if write_lease.active_authoritative_writer_count != 1:
            raise OrchestrationEvidenceError("authoritative writer count must equal one")
        if snapshot.current_authoritative_holder_actor_id != holder.actor_id:
            raise OrchestrationEvidenceError("snapshot authoritative holder drift detected")
        if len(authoritative_roles) != 1 or authoritative_roles[0].actor_id != holder.actor_id:
            raise OrchestrationEvidenceError("authoritative write holder role drift detected")
    if any(
        observation.authoritative_write_access
        for observation in write_lease.dispatch_lease_observations
    ):
        raise OrchestrationEvidenceError("support worker dispatch lease may not grant writes")


def _validate_worker_direct_user_boundary(*, snapshot: OrchestrationStateSnapshot) -> None:
    if snapshot.worker_direct_user_boundary_forbidden is not True:
        raise OrchestrationEvidenceError("worker direct user-boundary policy drift detected")
    for role in snapshot.current_roles:
        if role.actor_id == snapshot.orchestrator_session_id:
            continue
        if role.user_facing_boundary:
            raise OrchestrationEvidenceError("support worker established a direct user boundary")


def _validate_canonical_identity_fields(
    *,
    snapshot_payload: dict[str, Any],
    snapshot: OrchestrationStateSnapshot,
) -> None:
    required_fields = {
        "orchestrator_session_id",
        "worker_session_id",
        "parent_session_id",
        "event_cursor",
        "last_reconciled_event",
        "continuation_bridge_ref",
    }
    missing = sorted(field for field in required_fields if field not in snapshot_payload)
    if missing:
        raise OrchestrationEvidenceError(f"snapshot identity fields missing: {', '.join(missing)}")
    if snapshot.parent_session_id != snapshot.orchestrator_session_id:
        raise OrchestrationEvidenceError("parent session identity drift detected")
    if not snapshot.event_cursor.streams:
        raise OrchestrationEvidenceError("event cursor must contain at least one stream")
    if not isinstance(snapshot.last_reconciled_event, str) or not snapshot.last_reconciled_event:
        raise OrchestrationEvidenceError("last reconciled event must be recorded")


def _validate_compaction_lineage(
    *,
    snapshot: OrchestrationStateSnapshot,
    topology: ExecutionTopologyState,
) -> bool:
    audit_streams = [
        stream.stream_id
        for stream in snapshot.event_cursor.streams
        if stream.stream_id == f"urm_audit:{snapshot.orchestrator_session_id}"
    ]
    if snapshot.continuation_bridge_ref is None:
        if topology.compaction_seams:
            raise OrchestrationEvidenceError("compaction seam present without continuation bridge")
        if audit_streams:
            raise OrchestrationEvidenceError("audit stream present without continuation bridge")
        return False
    if len(topology.compaction_seams) != 1:
        raise OrchestrationEvidenceError("continuation bridge requires exactly one compaction seam")
    seam = topology.compaction_seams[0]
    bridge = snapshot.continuation_bridge_ref
    if not audit_streams or bridge.target_stream_id not in audit_streams:
        raise OrchestrationEvidenceError(
            "continuation bridge target stream must appear in event cursor"
        )
    if seam.source_stream_id != bridge.source_stream_id:
        raise OrchestrationEvidenceError("compaction seam source stream drift detected")
    if seam.target_stream_id != bridge.target_stream_id:
        raise OrchestrationEvidenceError("compaction seam target stream drift detected")
    if seam.bridge_ref != bridge.bridge_ref:
        raise OrchestrationEvidenceError("compaction seam bridge ref drift detected")
    if seam.bridge_path != bridge.bridge_path:
        raise OrchestrationEvidenceError("compaction seam bridge path drift detected")
    return True


def _validate_role_transition_record(
    *,
    snapshot: OrchestrationStateSnapshot,
    write_lease: WriteLeaseState,
    transition_record: RoleTransitionRecord,
) -> None:
    current_holder = write_lease.current_authoritative_holder
    if current_holder is None:
        return
    if not transition_record.entries:
        raise OrchestrationEvidenceError(
            "role transition record is required when authoritative write access is active"
        )
    last_entry = transition_record.entries[-1]
    if last_entry.to_role != current_holder.role:
        raise OrchestrationEvidenceError("role transition current role drift detected")
    if last_entry.authority_level_after != current_holder.authority_level:
        raise OrchestrationEvidenceError("role transition authority drift detected")
    if last_entry.granted_by != CONTROL_PLANE_OWNER:
        raise OrchestrationEvidenceError("role transition grant authority drift detected")
    if snapshot.current_authoritative_holder_actor_id != current_holder.actor_id:
        raise OrchestrationEvidenceError("snapshot holder drift detected")


def _validate_handoff_envelope(
    *,
    handoff_payload: dict[str, Any],
    handoff_envelope: RoleHandoffEnvelope,
) -> None:
    if handoff_envelope.reconciliation_required is not True:
        raise OrchestrationEvidenceError("handoff reconciliation must remain required")
    if handoff_envelope.required_fields != EXPECTED_HANDOFF_REQUIRED_FIELDS:
        raise OrchestrationEvidenceError("handoff required fields drift detected")
    if handoff_envelope.empty_value_policies != EXPECTED_HANDOFF_EMPTY_VALUE_POLICIES:
        raise OrchestrationEvidenceError("handoff empty-value policy drift detected")
    if handoff_envelope.reconciliation_minimum_checks != EXPECTED_RECONCILIATION_MINIMUM_CHECKS:
        raise OrchestrationEvidenceError("handoff reconciliation checks drift detected")
    if "entries" not in handoff_payload:
        raise OrchestrationEvidenceError("handoff entries field must be materialized")


def _validate_v35b_child_roles(
    *,
    snapshot: OrchestrationStateSnapshot,
) -> list[Any]:
    child_roles = [
        role for role in snapshot.current_roles if role.role in EXPECTED_CHILD_DELEGATION_ROLES
    ]
    for role in child_roles:
        if role.requested_role not in EXPECTED_CHILD_DELEGATION_ROLES:
            raise OrchestrationEvidenceError(
                "requested_role must be recorded for delegated child roles"
            )
        if role.granted_role not in EXPECTED_CHILD_DELEGATION_ROLES:
            raise OrchestrationEvidenceError(
                "granted_role must be recorded for delegated child roles"
            )
        if role.delegation_task_kind not in EXPECTED_DELEGATION_TASK_KINDS:
            raise OrchestrationEvidenceError(
                "delegation_task_kind must be recorded for delegated child roles"
            )
        if role.scope_owned.kind not in EXPECTED_SCOPE_GRANULARITY:
            raise OrchestrationEvidenceError(
                "delegated scope kind must be recorded for delegated child roles"
            )
    return child_roles


def _validate_v35b_dispatch_observations(*, write_lease: WriteLeaseState) -> None:
    for observation in write_lease.dispatch_lease_observations:
        if observation.requested_role not in EXPECTED_CHILD_DELEGATION_ROLES:
            raise OrchestrationEvidenceError(
                "requested_role must be recorded for delegated dispatch observations"
            )
        if observation.granted_role not in EXPECTED_CHILD_DELEGATION_ROLES:
            raise OrchestrationEvidenceError(
                "granted_role must be recorded for delegated dispatch observations"
            )
        if observation.delegation_task_kind not in EXPECTED_DELEGATION_TASK_KINDS:
            raise OrchestrationEvidenceError(
                "delegation_task_kind must be recorded for delegated dispatch observations"
            )
        if observation.scope_owned.kind not in EXPECTED_SCOPE_GRANULARITY:
            raise OrchestrationEvidenceError(
                "delegated scope kind must be recorded for delegated dispatch observations"
            )


def _validate_builder_role_materialized(
    *,
    child_roles: list[Any],
    write_lease: WriteLeaseState,
    transition_record: RoleTransitionRecord,
    handoff_envelope: RoleHandoffEnvelope,
) -> bool:
    builder_present = (
        any(role.role == "builder_worker" for role in child_roles)
        or any(
            observation.granted_role == "builder_worker"
            for observation in write_lease.dispatch_lease_observations
        )
        or any(entry.to_role == "builder_worker" for entry in transition_record.entries)
        or any(entry.role == "builder_worker" for entry in handoff_envelope.entries)
    )
    if not builder_present:
        raise OrchestrationEvidenceError("builder role must be materialized")
    return True


def _validate_support_roles_materialized(
    *,
    child_roles: list[Any],
    write_lease: WriteLeaseState,
    handoff_envelope: RoleHandoffEnvelope,
) -> bool:
    support_present = (
        any(role.role in EXPECTED_SUPPORT_DELEGATION_ROLES for role in child_roles)
        or any(
            observation.granted_role in EXPECTED_SUPPORT_DELEGATION_ROLES
            for observation in write_lease.dispatch_lease_observations
        )
        or any(
            entry.role in EXPECTED_SUPPORT_DELEGATION_ROLES
            for entry in handoff_envelope.entries
        )
    )
    if not support_present:
        raise OrchestrationEvidenceError("at least one support role path must be materialized")
    return True


def _validate_delegated_scope_kind_recorded(
    *,
    child_roles: list[Any],
    write_lease: WriteLeaseState,
    handoff_envelope: RoleHandoffEnvelope,
) -> bool:
    for role in child_roles:
        if role.scope_owned.kind not in EXPECTED_SCOPE_GRANULARITY:
            raise OrchestrationEvidenceError(
                "delegated scope kind must be recorded for delegated child roles"
            )
    for observation in write_lease.dispatch_lease_observations:
        if observation.scope_owned.kind not in EXPECTED_SCOPE_GRANULARITY:
            raise OrchestrationEvidenceError(
                "delegated scope kind must be recorded for delegated dispatch observations"
            )
    for entry in handoff_envelope.entries:
        if entry.role not in EXPECTED_CHILD_DELEGATION_ROLES:
            raise OrchestrationEvidenceError("handoff entry role must remain a released role")
        if not entry.scope_owned:
            raise OrchestrationEvidenceError("handoff entry scope_owned must be materialized")
        for scope in entry.scope_owned:
            if scope.kind not in EXPECTED_SCOPE_GRANULARITY:
                raise OrchestrationEvidenceError(
                    "delegated scope kind must be recorded for handoff entries"
                )
    return True


def _validate_v35b_single_builder_default(
    *,
    snapshot: OrchestrationStateSnapshot,
    write_lease: WriteLeaseState,
) -> bool:
    if snapshot.single_writer_default_enforced is not True:
        raise OrchestrationEvidenceError("snapshot single-writer default must be enforced")
    if write_lease.single_writer_default_enforced is not True:
        raise OrchestrationEvidenceError("write lease single-writer default must be enforced")
    if write_lease.active_authoritative_writer_count > 1:
        raise OrchestrationEvidenceError("multiple authoritative builders active by default")
    authoritative_roles = [
        role for role in snapshot.current_roles if role.authoritative_write_access
    ]
    holder = write_lease.current_authoritative_holder
    if holder is None:
        if write_lease.active_authoritative_writer_count != 0:
            raise OrchestrationEvidenceError("authoritative writer count must be zero")
        if snapshot.current_authoritative_holder_actor_id is not None:
            raise OrchestrationEvidenceError("snapshot authoritative holder must be absent")
        if authoritative_roles:
            raise OrchestrationEvidenceError("no actor may hold authoritative writes")
    else:
        if write_lease.active_authoritative_writer_count != 1:
            raise OrchestrationEvidenceError("authoritative writer count must equal one")
        if snapshot.current_authoritative_holder_actor_id != holder.actor_id:
            raise OrchestrationEvidenceError("snapshot authoritative holder drift detected")
        if len(authoritative_roles) != 1 or authoritative_roles[0].actor_id != holder.actor_id:
            raise OrchestrationEvidenceError("authoritative write holder role drift detected")
        if holder.role == "builder_worker" and holder.delegation_task_kind != "write_task":
            raise OrchestrationEvidenceError(
                "builder write-task delegation must remain the only authoritative child path"
            )
        if holder.role not in {"builder_worker", "main_orchestrator"}:
            raise OrchestrationEvidenceError(
                "authoritative write ownership may only belong to "
                "builder_worker or main_orchestrator"
            )
    for observation in write_lease.dispatch_lease_observations:
        if not observation.authoritative_write_access:
            continue
        if observation.granted_role != "builder_worker":
            raise OrchestrationEvidenceError(
                "support-worker authority drift detected in dispatch observations"
            )
        if observation.delegation_task_kind != "write_task":
            raise OrchestrationEvidenceError(
                "authoritative write access requires write_task delegation"
            )
    return True


def _validate_support_workers_non_authoritative(
    *,
    child_roles: list[Any],
    write_lease: WriteLeaseState,
    handoff_envelope: RoleHandoffEnvelope,
) -> bool:
    for role in child_roles:
        if role.role not in EXPECTED_SUPPORT_DELEGATION_ROLES:
            continue
        if role.authoritative_write_access:
            raise OrchestrationEvidenceError("support-worker authority drift detected")
        if role.authority_domain != "advisory":
            raise OrchestrationEvidenceError("support-worker authority domain drift detected")
        if not role.authority_level.startswith("advisory"):
            raise OrchestrationEvidenceError("support-worker authority level drift detected")
    for observation in write_lease.dispatch_lease_observations:
        if observation.granted_role not in EXPECTED_SUPPORT_DELEGATION_ROLES:
            continue
        if observation.authoritative_write_access:
            raise OrchestrationEvidenceError("support-worker authority drift detected")
        if observation.delegation_task_kind == "write_task":
            raise OrchestrationEvidenceError(
                "support-worker path must remain non-authoritative"
            )
    for entry in handoff_envelope.entries:
        if entry.role not in EXPECTED_SUPPORT_DELEGATION_ROLES:
            continue
        if entry.authority_domain != "advisory":
            raise OrchestrationEvidenceError("support-worker handoff authority drift detected")
        if not entry.authority_level.startswith("advisory"):
            raise OrchestrationEvidenceError(
                "support-worker handoff authority level drift detected"
            )
        if entry.artifact_surface != "none":
            raise OrchestrationEvidenceError(
                "support-worker handoff artifact surface must remain non-authoritative"
            )
    return True


def _validate_v35b_builder_write_lease(
    *,
    write_lease: WriteLeaseState,
    transition_record: RoleTransitionRecord,
) -> None:
    write_task_observations = [
        observation
        for observation in write_lease.dispatch_lease_observations
        if observation.delegation_task_kind == "write_task"
    ]
    if not write_task_observations:
        raise OrchestrationEvidenceError("builder write-task delegation must be materialized")
    if any(observation.granted_role != "builder_worker" for observation in write_task_observations):
        raise OrchestrationEvidenceError("write_task delegation requires builder_worker")
    if not any(observation.authoritative_write_access for observation in write_task_observations):
        raise OrchestrationEvidenceError(
            "builder write-task delegation must record authoritative write lease"
        )
    if not any(entry.to_role == "builder_worker" for entry in transition_record.entries):
        raise OrchestrationEvidenceError(
            "builder write-task delegation must record role transition"
        )
    if any(entry.granted_by != CONTROL_PLANE_OWNER for entry in transition_record.entries):
        raise OrchestrationEvidenceError("role transition grant authority drift detected")


def _validate_v35b_handoff_artifact(
    *,
    child_roles: list[Any],
    handoff_payload: dict[str, Any],
    handoff_envelope: RoleHandoffEnvelope,
) -> bool:
    if "entries" not in handoff_payload:
        raise OrchestrationEvidenceError("handoff entries field must be materialized")
    completed_child_roles = [
        role.role for role in child_roles if role.status == "completed"
    ]
    if not completed_child_roles:
        if handoff_envelope.entries:
            raise OrchestrationEvidenceError(
                "handoff entries must be empty when no completed delegated work exists"
            )
        return True
    if not handoff_envelope.entries:
        raise OrchestrationEvidenceError(
            "completed child handoff entry is required when claimed work is present"
        )
    if len(handoff_envelope.entries) < len(completed_child_roles):
        raise OrchestrationEvidenceError(
            "completed child handoff entry is required when claimed work is present"
        )
    if Counter(entry.role for entry in handoff_envelope.entries) != Counter(completed_child_roles):
        raise OrchestrationEvidenceError(
            "handoff entries must exactly match completed delegated work"
        )
    for entry in handoff_envelope.entries:
        if entry.status != "completed":
            raise OrchestrationEvidenceError("handoff entries must describe completed child work")
        if not (
            entry.files_changed
            or entry.commands_run
            or entry.artifacts_produced
            or entry.evidence_refs
        ):
            raise OrchestrationEvidenceError(
                "completed child handoff entry is required when claimed work is present"
            )
    return True


def _validate_v35b_handoff_reconciliation(*, handoff_envelope: RoleHandoffEnvelope) -> bool:
    if handoff_envelope.reconciliation_required is not True:
        raise OrchestrationEvidenceError("handoff reconciliation must remain required")
    return True


def _validate_unreconciled_worker_output_non_authoritative(
    *,
    snapshot: OrchestrationStateSnapshot,
    handoff_envelope: RoleHandoffEnvelope,
) -> bool:
    if snapshot.runtime_event_truth_policy != RUNTIME_EVENT_TRUTH_POLICY:
        raise OrchestrationEvidenceError("runtime event truth policy drift detected")
    if handoff_envelope.trust_model != HANDOFF_TRUST_MODEL:
        raise OrchestrationEvidenceError("handoff trust model drift detected")
    for entry in handoff_envelope.entries:
        if entry.artifact_class != "advisory":
            raise OrchestrationEvidenceError(
                "worker output may not become authoritative pre-closeout"
            )
        if "pending_reconciliation" not in entry.authority_level:
            raise OrchestrationEvidenceError(
                "worker output treated as accepted truth without reconciliation"
            )
        if entry.recommended_next_action != EXPECTED_RECONCILIATION_ACTION:
            raise OrchestrationEvidenceError(
                "worker output treated as accepted truth without reconciliation"
            )
        if EXPECTED_RECONCILIATION_ACTION not in entry.open_risks:
            raise OrchestrationEvidenceError(
                "worker output treated as accepted truth without reconciliation"
            )
    return True


def _validate_v35b_zero_occurrence_artifacts(
    *,
    child_roles: list[Any],
    transition_payload: dict[str, Any],
    transition_record: RoleTransitionRecord,
    handoff_payload: dict[str, Any],
    handoff_envelope: RoleHandoffEnvelope,
) -> bool:
    if "entries" not in transition_payload:
        raise OrchestrationEvidenceError("role transition entries must be materialized")
    if "entries" not in handoff_payload:
        raise OrchestrationEvidenceError("handoff entries field must be materialized")
    if not any(role.role == "builder_worker" for role in child_roles) and transition_record.entries:
        raise OrchestrationEvidenceError(
            "role transition record must stay empty when no delegated authority transition occurs"
        )
    if not any(role.status == "completed" for role in child_roles) and handoff_envelope.entries:
        raise OrchestrationEvidenceError(
            "handoff entries must be empty when no completed delegated work exists"
        )
    return True


def _validate_v35c_read_only_visibility(
    *,
    snapshot: OrchestrationStateSnapshot,
    visibility_state: WorkerVisibilityState,
) -> bool:
    if snapshot.orchestration_foundation_package != ORCHESTRATION_FOUNDATION_PACKAGE:
        raise OrchestrationEvidenceError("snapshot foundation package drift detected")
    if (
        visibility_state.worker_visibility_foundation_package
        != WORKER_VISIBILITY_FOUNDATION_PACKAGE
    ):
        raise OrchestrationEvidenceError("worker visibility foundation package drift detected")
    if visibility_state.read_only_visibility_required is not True:
        raise OrchestrationEvidenceError("worker visibility must remain read-only")
    if visibility_state.orchestrator_primary_interaction_boundary_required is not True:
        raise OrchestrationEvidenceError(
            "orchestrator must remain the primary interaction boundary"
        )
    if visibility_state.deterministic_redaction_and_scope_boundary_required is not True:
        raise OrchestrationEvidenceError(
            "deterministic redaction and scope boundary policy drift detected"
        )
    if visibility_state.worker_direct_user_boundary_forbidden is not True:
        raise OrchestrationEvidenceError("worker direct user-boundary policy drift detected")
    if visibility_state.progress_state_source_policy != PROGRESS_STATE_SOURCE_POLICY:
        raise OrchestrationEvidenceError(
            "progress fields missing or derived from ad hoc summary"
        )
    if visibility_state.epistemic_lane_absence_policy != EPISTEMIC_LANE_ABSENCE_POLICY:
        raise OrchestrationEvidenceError("lane absence policy drift detected")
    return True


def _validate_v35c_lane_projection(
    *,
    visibility_state: WorkerVisibilityState,
) -> tuple[bool, bool, bool]:
    if visibility_state.epistemic_lane_enum != list(WORKER_VISIBILITY_LANE_ENUM):
        raise OrchestrationEvidenceError("epistemic lane labels must remain frozen")
    if visibility_state.epistemic_lane_status_enum != list(WORKER_VISIBILITY_LANE_STATUS_ENUM):
        raise OrchestrationEvidenceError("epistemic lane status enum drift detected")
    if visibility_state.divergence_state_enum != list(WORKER_VISIBILITY_DIVERGENCE_ENUM):
        raise OrchestrationEvidenceError("divergence state enum drift detected")
    if not visibility_state.workers:
        raise OrchestrationEvidenceError("worker visibility state must materialize worker entries")
    for worker in visibility_state.workers:
        lane_map = _lane_map_for_worker(worker=worker)
        if set(lane_map) != set(WORKER_VISIBILITY_LANE_ENUM):
            raise OrchestrationEvidenceError("lane absence may not be silently omitted")
        for lane_name, lane_state in lane_map.items():
            if lane_name not in WORKER_VISIBILITY_LANE_ENUM:
                raise OrchestrationEvidenceError("epistemic lane labels must remain frozen")
            if lane_state.status not in WORKER_VISIBILITY_LANE_STATUS_ENUM:
                raise OrchestrationEvidenceError("epistemic lane status must remain explicit")
        expected_divergence = _expected_divergence_state_for_worker(
            worker=worker,
            lane_map=lane_map,
        )
        if worker.divergence_state != expected_divergence:
            raise OrchestrationEvidenceError(
                "divergence state must be explicit when lanes do not align"
            )
    return True, True, True


def _validate_v35c_continuity(
    *,
    snapshot: OrchestrationStateSnapshot,
    topology: ExecutionTopologyState,
    visibility_state: WorkerVisibilityState,
) -> bool:
    if visibility_state.continuation_bridge_visibility_policy != (
        CONTINUATION_BRIDGE_VISIBILITY_POLICY
    ):
        raise OrchestrationEvidenceError("continuation bridge visibility policy drift detected")
    if snapshot.continuation_bridge_ref is None:
        if visibility_state.continuation_bridge_ref is not None:
            raise OrchestrationEvidenceError("continuation bridge visibility drift detected")
        if visibility_state.compaction_seams:
            raise OrchestrationEvidenceError("compaction visibility drift detected")
        return False
    if visibility_state.continuation_bridge_ref != snapshot.continuation_bridge_ref:
        raise OrchestrationEvidenceError("continuation bridge visibility drift detected")
    if visibility_state.compaction_seams != topology.compaction_seams:
        raise OrchestrationEvidenceError(
            "compaction or continuation bridge continuity silently flattened"
        )
    return True


def _validate_v35c_progress_fields(
    *,
    snapshot: OrchestrationStateSnapshot,
    visibility_state: WorkerVisibilityState,
    handoff_envelope: RoleHandoffEnvelope,
) -> bool:
    child_roles = {
        role.actor_id: role
        for role in snapshot.current_roles
        if role.actor_id != snapshot.orchestrator_session_id
    }
    stream_heads = {
        stream.stream_id: stream
        for stream in snapshot.event_cursor.streams
    }
    handoff_by_worker = _match_v35c_handoffs(
        workers=visibility_state.workers,
        handoff_envelope=handoff_envelope,
    )
    if set(child_roles) != {worker.worker_id for worker in visibility_state.workers}:
        raise OrchestrationEvidenceError(
            "progress fields must be derived from canonical state and child identity"
        )
    for worker in visibility_state.workers:
        child_role = child_roles[worker.worker_id]
        if worker.parent_session_id != snapshot.parent_session_id:
            raise OrchestrationEvidenceError(
                "progress fields must be derived from canonical state and child identity"
            )
        if worker.role != child_role.role:
            raise OrchestrationEvidenceError(
                "progress fields must be derived from canonical state and child role"
            )
        if worker.requested_role != child_role.requested_role:
            raise OrchestrationEvidenceError(
                "progress fields must be derived from canonical state and child role"
            )
        if worker.granted_role != child_role.granted_role:
            raise OrchestrationEvidenceError(
                "progress fields must be derived from canonical state and child role"
            )
        if worker.delegation_task_kind != child_role.delegation_task_kind:
            raise OrchestrationEvidenceError(
                "progress fields must be derived from canonical state and child role"
            )
        if worker.status != child_role.status:
            raise OrchestrationEvidenceError(
                "progress fields must be derived from canonical state and child status"
            )
        raw_lane = _lane_map_for_worker(worker=worker)["raw_transcript"]
        stream = stream_heads.get(raw_lane.source_ref or "")
        expected_last_action = _expected_last_action(worker_status=worker.status, stream=stream)
        if worker.last_action != expected_last_action:
            raise OrchestrationEvidenceError(
                "progress fields must be derived from canonical runtime events only"
            )
        expected_latest_visible_event = stream.last_event_ref if stream is not None else None
        if worker.latest_visible_event != expected_latest_visible_event:
            raise OrchestrationEvidenceError(
                "progress fields must be derived from canonical runtime events only"
            )
        if raw_lane.latest_visible_event != expected_latest_visible_event:
            raise OrchestrationEvidenceError(
                "progress fields must be derived from canonical runtime events only"
            )
        handoff_entry = handoff_by_worker.get(worker.worker_id)
        expected_scope_owned = (
            [scope.model_dump(mode="json") for scope in handoff_entry.scope_owned]
            if handoff_entry is not None
            else [child_role.scope_owned.model_dump(mode="json")]
        )
        if [scope.model_dump(mode="json") for scope in worker.scope_owned] != expected_scope_owned:
            raise OrchestrationEvidenceError(
                "progress fields must be derived from canonical scope state"
            )
        expected_scope_remaining = (
            [scope.model_dump(mode="json") for scope in handoff_entry.scope_remaining]
            if handoff_entry is not None
            else []
            if worker.status == "completed"
            else [child_role.scope_owned.model_dump(mode="json")]
        )
        if [
            scope.model_dump(mode="json") for scope in worker.scope_remaining
        ] != expected_scope_remaining:
            raise OrchestrationEvidenceError(
                "progress fields must be derived from canonical scope state"
            )
        expected_reconciliation_status = (
            "pending_reconciliation" if handoff_entry is not None else "not_applicable"
        )
        if worker.reconciliation_status != expected_reconciliation_status:
            raise OrchestrationEvidenceError(
                "progress fields must be derived from canonical reconciliation state"
            )
        expected_blocking_state = _expected_blocking_state(
            worker_status=worker.status,
            handoff_entry=handoff_entry,
        )
        if worker.blocking_state != expected_blocking_state:
            raise OrchestrationEvidenceError(
                "progress fields must be derived from canonical blocking state"
            )
    return True


def _validate_v35c_raw_transcript_authority(
    *,
    visibility_state: WorkerVisibilityState,
) -> bool:
    if visibility_state.raw_transcript_authority_policy != RAW_TRANSCRIPT_AUTHORITY_POLICY:
        raise OrchestrationEvidenceError("raw transcript rendered as authoritative")
    for worker in visibility_state.workers:
        lane = _lane_map_for_worker(worker=worker)["raw_transcript"]
        if lane.authority_policy != RAW_TRANSCRIPT_AUTHORITY_POLICY:
            raise OrchestrationEvidenceError("raw transcript rendered as authoritative")
        if worker.raw_transcript_non_authoritative is not True:
            raise OrchestrationEvidenceError("raw transcript rendered as authoritative")
        if lane.status == "available" and not lane.source_path:
            raise OrchestrationEvidenceError("raw transcript lane must record source path")
    return True


def _validate_v35c_worker_self_report_authority(
    *,
    visibility_state: WorkerVisibilityState,
) -> bool:
    if visibility_state.worker_self_report_authority_policy != WORKER_SELF_REPORT_AUTHORITY_POLICY:
        raise OrchestrationEvidenceError(
            "worker self-report rendered as reconciled without explicit reconciliation"
        )
    if visibility_state.reconciled_handoff_surface_policy != RECONCILED_HANDOFF_SURFACE_POLICY:
        raise OrchestrationEvidenceError(
            "worker self-report rendered as reconciled without explicit reconciliation"
        )
    if visibility_state.orchestrator_judgment_surface_policy != (
        ORCHESTRATOR_JUDGMENT_SURFACE_POLICY
    ):
        raise OrchestrationEvidenceError("orchestrator judgment surface policy drift detected")
    for worker in visibility_state.workers:
        lane_map = _lane_map_for_worker(worker=worker)
        if worker.worker_self_report_non_authoritative_until_reconciled is not True:
            raise OrchestrationEvidenceError(
                "worker self-report rendered as reconciled without explicit reconciliation"
            )
        if lane_map["worker_self_report"].authority_policy != WORKER_SELF_REPORT_AUTHORITY_POLICY:
            raise OrchestrationEvidenceError(
                "worker self-report rendered as reconciled without explicit reconciliation"
            )
        if lane_map["reconciled_handoff"].authority_policy != RECONCILED_HANDOFF_SURFACE_POLICY:
            raise OrchestrationEvidenceError(
                "worker self-report rendered as reconciled without explicit reconciliation"
            )
        if lane_map["orchestrator_judgment"].authority_policy != (
            ORCHESTRATOR_JUDGMENT_SURFACE_POLICY
        ):
            raise OrchestrationEvidenceError("orchestrator judgment surface policy drift detected")
        if lane_map["reconciled_handoff"].status == "available":
            raise OrchestrationEvidenceError(
                "worker self-report rendered as reconciled without explicit reconciliation"
            )
        if lane_map["orchestrator_judgment"].status == "available":
            raise OrchestrationEvidenceError("orchestrator judgment may not appear in v58 closeout")
    return True


def _validate_v35c_worker_direct_user_boundary(
    *,
    visibility_state: WorkerVisibilityState,
) -> bool:
    if visibility_state.worker_direct_user_boundary_forbidden is not True:
        raise OrchestrationEvidenceError("worker direct user-boundary policy drift detected")
    for worker in visibility_state.workers:
        if worker.direct_user_boundary_established:
            raise OrchestrationEvidenceError("worker direct user boundary established")
    return True


def _validate_v35d_read_only_topology(
    *,
    topology_state: TopologyDutyMapState,
) -> bool:
    if topology_state.topology_duty_map_foundation_package != TOPOLOGY_DUTY_MAP_FOUNDATION_PACKAGE:
        raise OrchestrationEvidenceError("topology foundation package drift detected")
    if topology_state.read_only_topology_required is not True:
        raise OrchestrationEvidenceError("topology surface treated as authoritative")
    if topology_state.topology_surface_authority_policy != TOPOLOGY_SURFACE_AUTHORITY_POLICY:
        raise OrchestrationEvidenceError("topology surface treated as authoritative")
    if topology_state.event_stream_drilldown_policy != EVENT_STREAM_DRILLDOWN_POLICY:
        raise OrchestrationEvidenceError("event stream drilldown policy drift detected")
    if any(node.user_facing_boundary for node in topology_state.nodes[1:]):
        raise OrchestrationEvidenceError("worker direct user boundary rendered or implied")
    if any(node.authority_domain == "governance" for node in topology_state.nodes[1:]):
        raise OrchestrationEvidenceError("topology surface treated as authoritative")
    return True


def _validate_v35d_projection(
    *,
    snapshot: OrchestrationStateSnapshot,
    execution_topology_state: ExecutionTopologyState,
    write_lease_state: WriteLeaseState,
    visibility_state: WorkerVisibilityState,
    handoff_envelope: RoleHandoffEnvelope,
    topology_state: TopologyDutyMapState,
    source_artifacts: TopologyDutyMapSourceArtifacts,
) -> bool:
    try:
        expected_topology_state = build_topology_duty_map_state(
            execution_topology_state=execution_topology_state,
            write_lease_state=write_lease_state,
            worker_visibility_state=visibility_state,
            role_handoff_envelope=handoff_envelope,
            source_artifacts=source_artifacts,
            event_streams=_event_stream_heads_from_snapshot(snapshot=snapshot),
        )
    except TopologyDutyMapStateError as exc:
        raise OrchestrationEvidenceError(
            "topology view invents state not present in canonical artifacts"
        ) from exc
    if topology_state.model_dump(mode="json", by_alias=True) != expected_topology_state.model_dump(
        mode="json",
        by_alias=True,
    ):
        raise OrchestrationEvidenceError(
            "topology view invents state not present in canonical artifacts"
        )
    return True


def _validate_v35d_write_lease_projection(
    *,
    write_lease_state: WriteLeaseState,
    topology_state: TopologyDutyMapState,
) -> bool:
    holder = write_lease_state.current_authoritative_holder
    authoritative_nodes = [
        node.actor_id for node in topology_state.nodes if node.authoritative_write_access
    ]
    authoritative_edges = [
        edge.target_actor_id for edge in topology_state.edges if edge.authoritative_write_access
    ]
    if holder is None:
        if topology_state.current_authoritative_holder_actor_id is not None:
            raise OrchestrationEvidenceError("current write lease holder rendered incorrectly")
        if authoritative_nodes or authoritative_edges:
            raise OrchestrationEvidenceError("current write lease holder rendered incorrectly")
        return True
    if topology_state.current_authoritative_holder_actor_id != holder.actor_id:
        raise OrchestrationEvidenceError("current write lease holder rendered incorrectly")
    if authoritative_nodes != [holder.actor_id]:
        raise OrchestrationEvidenceError("current write lease holder rendered incorrectly")
    if (
        holder.actor_id != topology_state.orchestrator_session_id
        and holder.actor_id not in authoritative_edges
    ):
        raise OrchestrationEvidenceError("current write lease holder rendered incorrectly")
    return True


def _validate_v35d_current_duty(
    *,
    write_lease_state: WriteLeaseState,
    topology_state: TopologyDutyMapState,
) -> bool:
    forbidden_labels = {
        node.authority_level
        for node in topology_state.nodes
    } | {
        "governance_authority",
        "implementation_write_lease_holder_pending_reconciliation",
        "implementation_delegated_pending_reconciliation",
        "advisory_information_only",
    }
    for node in topology_state.nodes:
        if node.current_duty in forbidden_labels or "authority" in node.current_duty:
            raise OrchestrationEvidenceError("current_duty rendered as authority surface")
    holder = write_lease_state.current_authoritative_holder
    if holder is not None:
        holder_node = next(
            (node for node in topology_state.nodes if node.actor_id == holder.actor_id),
            None,
        )
        if holder_node is None:
            raise OrchestrationEvidenceError("write lease holder not found in topology nodes")
        if holder.role == "builder_worker" and holder_node.current_duty not in {
            "implementing_with_active_write_lease",
            "queued_for_implementation_with_reserved_write_lease",
            "implementation_completed_pending_reconciliation",
        }:
            raise OrchestrationEvidenceError("current_duty rendered as authority surface")
    return True


def _validate_v35d_provenance_markers(
    *,
    snapshot: OrchestrationStateSnapshot,
    execution_topology_state: ExecutionTopologyState,
    topology_state: TopologyDutyMapState,
) -> bool:
    error_message = "topology node or edge missing required provenance markers"
    if len(topology_state.nodes) != len(execution_topology_state.nodes):
        raise OrchestrationEvidenceError(error_message)
    if len(topology_state.edges) != len(execution_topology_state.edges):
        raise OrchestrationEvidenceError(error_message)
    expected_last_reconciled_at = _last_reconciled_at_from_snapshot(snapshot=snapshot)
    for item in [*topology_state.nodes, *topology_state.edges]:
        if item.state_origin != TOPOLOGY_DUTY_MAP_STATE_ORIGIN:
            raise OrchestrationEvidenceError(error_message)
        if not item.reconciliation_status:
            raise OrchestrationEvidenceError(error_message)
        if not item.provenance_refs:
            raise OrchestrationEvidenceError(error_message)
        if topology_state.last_reconciled_event is not None:
            if item.last_reconciled_at != expected_last_reconciled_at:
                raise OrchestrationEvidenceError(error_message)
    return True


def _validate_v35d_provenance_refs(
    *,
    var_root: Path,
    snapshot: OrchestrationStateSnapshot,
    topology_state: TopologyDutyMapState,
    execution_topology_path: str,
    write_lease_path: str,
    visibility_path: str,
    handoff_path: str,
) -> bool:
    allowed_artifact_paths = {
        execution_topology_path: "execution_topology_state@1",
        write_lease_path: "write_lease_state@1",
        visibility_path: "worker_visibility_state@1",
        handoff_path: "role_handoff_envelope@1",
    }
    event_streams_by_id = {
        stream.stream_id: stream for stream in snapshot.event_cursor.streams
    }
    event_stream_ref_count = 0
    for item in [*topology_state.nodes, *topology_state.edges]:
        for ref in item.provenance_refs:
            resolved = _resolve_var_relative_path(
                root=var_root,
                path_text=ref.path,
                field_name="provenance_ref_path",
            )
            if not resolved.exists():
                raise OrchestrationEvidenceError("provenance ref missing or unresolvable")
            if ref.ref_kind == "artifact":
                expected_schema = allowed_artifact_paths.get(ref.path)
                if expected_schema is None or ref.source_schema != expected_schema:
                    raise OrchestrationEvidenceError("provenance ref missing or unresolvable")
                continue
            event_stream_ref_count += 1
            stream = event_streams_by_id.get(ref.stream_id or "")
            if stream is None:
                raise OrchestrationEvidenceError("provenance ref missing or unresolvable")
            if stream.path != ref.path or stream.last_event_ref != ref.event_ref:
                raise OrchestrationEvidenceError("provenance ref missing or unresolvable")
    if snapshot.event_cursor.streams and event_stream_ref_count == 0:
        raise OrchestrationEvidenceError("provenance ref missing or unresolvable")
    return True


def _validate_v35d_advisory_blockers(
    *,
    visibility_state: WorkerVisibilityState,
    topology_state: TopologyDutyMapState,
) -> bool:
    worker_by_id = {worker.worker_id: worker for worker in visibility_state.workers}
    edge_by_target = {edge.target_actor_id: edge for edge in topology_state.edges}
    for node in topology_state.nodes:
        if node.actor_id == topology_state.orchestrator_session_id:
            continue
        worker = worker_by_id.get(node.actor_id)
        if worker is None:
            raise OrchestrationEvidenceError(
                "topology view invents state not present in canonical artifacts"
            )
        if worker.role in EXPECTED_SUPPORT_DELEGATION_ROLES:
            if node.blockers != worker.blockers:
                raise OrchestrationEvidenceError(
                    "advisory blocker rendered as governance equivalent"
                )
            if node.blocking_state != "non_blocking":
                raise OrchestrationEvidenceError(
                    "advisory blocker rendered as governance equivalent"
                )
            if node.authoritative_write_access:
                raise OrchestrationEvidenceError(
                    "advisory blocker rendered as governance equivalent"
                )
            edge = edge_by_target.get(node.actor_id)
            if edge is None or edge.blocking_state != "non_blocking":
                raise OrchestrationEvidenceError(
                    "advisory blocker rendered as governance equivalent"
                )
    return True


def _validate_v35d_continuity(
    *,
    snapshot: OrchestrationStateSnapshot,
    execution_topology_state: ExecutionTopologyState,
    topology_state: TopologyDutyMapState,
) -> bool:
    if topology_state.continuation_bridge_ref != snapshot.continuation_bridge_ref:
        raise OrchestrationEvidenceError(
            "compaction or continuation bridge visibility silently flattened"
        )
    if topology_state.continuation_bridge_ref != execution_topology_state.continuation_bridge_ref:
        raise OrchestrationEvidenceError(
            "compaction or continuation bridge visibility silently flattened"
        )
    if topology_state.compaction_seams != execution_topology_state.compaction_seams:
        raise OrchestrationEvidenceError(
            "compaction or continuation bridge visibility silently flattened"
        )
    if snapshot.continuation_bridge_ref is None and topology_state.compaction_seams:
        raise OrchestrationEvidenceError(
            "compaction or continuation bridge visibility silently flattened"
        )
    return True


def _event_stream_heads_from_snapshot(
    *,
    snapshot: OrchestrationStateSnapshot,
) -> list[EventStreamHeadInput]:
    return [
        EventStreamHeadInput(
            stream_id=stream.stream_id,
            path=stream.path,
            event_count=stream.event_count,
            last_seq=stream.last_seq,
            last_event=stream.last_event,
            last_event_ref=stream.last_event_ref,
            last_ts=stream.last_ts,
        )
        for stream in snapshot.event_cursor.streams
    ]


def _last_reconciled_at_from_snapshot(*, snapshot: OrchestrationStateSnapshot) -> str | None:
    if snapshot.last_reconciled_event is None:
        return None
    for stream in snapshot.event_cursor.streams:
        if stream.last_event_ref == snapshot.last_reconciled_event:
            return stream.last_ts
    return None


def _lane_map_for_worker(*, worker: Any) -> dict[str, Any]:
    return {lane.lane: lane for lane in worker.epistemic_lanes}


def _expected_divergence_state_for_worker(*, worker: Any, lane_map: dict[str, Any]) -> str:
    raw_status = lane_map["raw_transcript"].status
    self_report_status = lane_map["worker_self_report"].status
    if raw_status == "parsing_failure" or self_report_status == "parsing_failure":
        return "parsing_failure"
    if self_report_status == "reconciliation_aborted":
        return "reconciliation_aborted"
    if raw_status == "available" and self_report_status in {"pending_parse", "not_available"}:
        return "raw_only"
    if raw_status != "available" and self_report_status == "available":
        return "worker_self_report_only"
    if lane_map["reconciled_handoff"].status == "available":
        return "lane_disagreement"
    return "aligned"


def _match_v35c_handoffs(
    *,
    workers: list[Any],
    handoff_envelope: RoleHandoffEnvelope,
) -> dict[str, Any]:
    matched: dict[str, Any] = {}
    consumed: set[int] = set()
    for worker in workers:
        raw_lane = _lane_map_for_worker(worker=worker)["raw_transcript"]
        for index, entry in enumerate(handoff_envelope.entries):
            if index in consumed:
                continue
            if raw_lane.source_path and raw_lane.source_path in entry.artifacts_produced:
                matched[worker.worker_id] = entry
                consumed.add(index)
                break
    return matched


def _expected_last_action(
    *,
    worker_status: str,
    stream: Any | None,
) -> str:
    if stream is not None and stream.last_event:
        return stream.last_event
    if worker_status == "queued":
        return "WORKER_QUEUED"
    if worker_status == "running":
        return "WORKER_START"
    if worker_status == "completed":
        return "WORKER_PASS"
    if worker_status == "cancelled":
        return "WORKER_CANCEL"
    return "WORKER_FAIL"


def _expected_blocking_state(*, worker_status: str, handoff_entry: Any | None) -> str:
    if handoff_entry is not None:
        return handoff_entry.blocking_state
    if worker_status in {"failed", "cancelled", "queued"}:
        return "blocking"
    return "non_blocking"
