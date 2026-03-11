from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any, TypeVar

from pydantic import BaseModel, ConfigDict, Field, ValidationError

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
    ExecutionTopologyState,
    MaterializedArtifact,
    MaterializedOrchestrationArtifacts,
    OrchestrationStateSnapshot,
    RoleHandoffEnvelope,
    RoleTransitionRecord,
    WriteLeaseState,
)
from .roles import CHILD_DELEGATION_ROLES, SUPPORT_DELEGATION_ROLES
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
        child_role = child_roles.get(worker.worker_id)
        if child_role is None:
            raise OrchestrationEvidenceError(
                "progress fields must be derived from canonical state and child identity"
            )
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
