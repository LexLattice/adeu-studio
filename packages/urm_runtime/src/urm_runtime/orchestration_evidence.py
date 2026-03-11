from __future__ import annotations

import json
from pathlib import Path
from typing import Any, TypeVar

from pydantic import BaseModel, ConfigDict, Field, ValidationError

from .hashing import canonical_json, sha256_canonical_json
from .orchestration_state import (
    CONTROL_PLANE_OWNER,
    HANDOFF_EMPTY_VALUE_POLICIES,
    HANDOFF_REQUIRED_FIELDS,
    ORCHESTRATION_FOUNDATION_PACKAGE,
    RECONCILIATION_MINIMUM_CHECKS,
    SCOPE_GRANULARITY_ENUM,
    ExecutionTopologyState,
    MaterializedArtifact,
    MaterializedOrchestrationArtifacts,
    OrchestrationStateSnapshot,
    RoleHandoffEnvelope,
    RoleTransitionRecord,
    WriteLeaseState,
)

V35A_ORCHESTRATION_STATE_EVIDENCE_SCHEMA = "v35a_orchestration_state_evidence@1"
V35A_ORCHESTRATION_STATE_CONTRACT_SOURCE = (
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS56.md#v35a_orchestration_state_contract@1"
)
STOP_GATE_METRICS_SCHEMA = "stop_gate_metrics@1"
EXPECTED_METRIC_KEY_CARDINALITY = 80
EXPECTED_SCOPE_GRANULARITY = list(SCOPE_GRANULARITY_ENUM)
EXPECTED_HANDOFF_REQUIRED_FIELDS = list(HANDOFF_REQUIRED_FIELDS)
EXPECTED_HANDOFF_EMPTY_VALUE_POLICIES = dict(HANDOFF_EMPTY_VALUE_POLICIES)
EXPECTED_RECONCILIATION_MINIMUM_CHECKS = list(RECONCILIATION_MINIMUM_CHECKS)

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
