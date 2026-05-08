from __future__ import annotations

import re
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .programbench_cleanroom_adapter import (
    ProgrambenchAdapterHandoff,
    ProgrambenchAdapterReadinessSummary,
    ProgrambenchCleanroomAdapterFamilyCloseoutAlignment,
    ProgrambenchReconstructionCasePacket,
)

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

PROGRAMBENCH_RECONSTRUCTION_WORK_ORDER_SCHEMA = (
    "programbench_reconstruction_work_order@1"
)
PROGRAMBENCH_RECONSTRUCTION_WORKER_CONTEXT_PACKET_SCHEMA = (
    "programbench_reconstruction_worker_context_packet@1"
)
PROGRAMBENCH_RECONSTRUCTION_CONTEXT_EXCLUSION_MANIFEST_SCHEMA = (
    "programbench_reconstruction_context_exclusion_manifest@1"
)
PROGRAMBENCH_RECONSTRUCTION_SANDBOX_POLICY_SCHEMA = (
    "programbench_reconstruction_sandbox_policy@1"
)
PROGRAMBENCH_RECONSTRUCTION_RUN_BUDGET_SCHEMA = (
    "programbench_reconstruction_run_budget@1"
)
PROGRAMBENCH_RECONSTRUCTION_WORKBENCH_NON_AUTHORITY_GUARDRAIL_SCHEMA = (
    "programbench_reconstruction_workbench_non_authority_guardrail@1"
)

PROGRAMBENCH_RECONSTRUCTION_CANDIDATE_ARTIFACT_MANIFEST_SCHEMA = (
    "programbench_reconstruction_candidate_artifact_manifest@1"
)
PROGRAMBENCH_RECONSTRUCTION_LOCAL_RUN_TRACE_SCHEMA = (
    "programbench_reconstruction_local_run_trace@1"
)
PROGRAMBENCH_RECONSTRUCTION_PROBE_RESULT_LOG_SCHEMA = (
    "programbench_reconstruction_probe_result_log@1"
)
PROGRAMBENCH_RECONSTRUCTION_REMAND_CORRECTION_RECORD_SCHEMA = (
    "programbench_reconstruction_remand_correction_record@1"
)
PROGRAMBENCH_RECONSTRUCTION_EQUIVALENCE_AUDIT_SCHEMA = (
    "programbench_reconstruction_equivalence_audit@1"
)
PROGRAMBENCH_RECONSTRUCTION_RESULT_SUMMARY_SCHEMA = (
    "programbench_reconstruction_result_summary@1"
)
PROGRAMBENCH_RECONSTRUCTION_HANDOFF_SCHEMA = "programbench_reconstruction_handoff@1"
PROGRAMBENCH_RECONSTRUCTION_WORKBENCH_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "programbench_reconstruction_workbench_family_closeout_alignment@1"
)

PB_RECON_0A_ARTIFACT_KINDS = {
    PROGRAMBENCH_RECONSTRUCTION_WORK_ORDER_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_WORKER_CONTEXT_PACKET_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_CONTEXT_EXCLUSION_MANIFEST_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_SANDBOX_POLICY_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_RUN_BUDGET_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_WORKBENCH_NON_AUTHORITY_GUARDRAIL_SCHEMA,
}
PB_RECON_0B_ARTIFACT_KINDS = {
    PROGRAMBENCH_RECONSTRUCTION_CANDIDATE_ARTIFACT_MANIFEST_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_LOCAL_RUN_TRACE_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_PROBE_RESULT_LOG_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_REMAND_CORRECTION_RECORD_SCHEMA,
}
PB_RECON_0C_ARTIFACT_KINDS = {
    PROGRAMBENCH_RECONSTRUCTION_EQUIVALENCE_AUDIT_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_RESULT_SUMMARY_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_HANDOFF_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_WORKBENCH_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
}
PB_RECON_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS = (
    PB_RECON_0B_ARTIFACT_KINDS | PB_RECON_0C_ARTIFACT_KINDS
)

_SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
_REQUIRED_SANDBOX_WITNESSES = {
    "network_disabled",
    "no_source_lookup",
    "no_decompilation",
    "no_docker_socket",
    "no_host_secrets",
    "bounded_filesystem_write_scope",
    "argv_shaped_command_policy",
}


def _ensure_non_empty_trimmed(values: list[str], *, field_name: str) -> None:
    for value in values:
        if not isinstance(value, str) or not value or value != value.strip():
            raise ValueError(f"{field_name} entries must be non-empty trimmed strings")


def _ensure_non_empty_unique(values: list[str], *, field_name: str) -> None:
    if not values:
        raise ValueError(f"{field_name} must contain at least one entry")
    _ensure_non_empty_trimmed(values, field_name=field_name)
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")


def _ensure_sorted_unique(values: list[str], *, field_name: str) -> None:
    _ensure_non_empty_unique(values, field_name=field_name)
    if values != sorted(values):
        raise ValueError(f"{field_name} must be lexicographically sorted")


def _ensure_sorted_unique_allow_empty(values: list[str], *, field_name: str) -> None:
    _ensure_non_empty_trimmed(values, field_name=field_name)
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")
    if values != sorted(values):
        raise ValueError(f"{field_name} must be lexicographically sorted")


def _ensure_hash(value: str, *, field_name: str) -> None:
    if not _SHA256_RE.fullmatch(value):
        raise ValueError(f"{field_name} must be a sha256:<64 lowercase hex> hash")


def _ensure_refs_resolve(
    values: list[str],
    *,
    field_label: str,
    released_refs: set[str],
) -> None:
    value_set = set(values)
    unknown = value_set - released_refs
    if unknown:
        raise ValueError(f"{field_label} references non-worker-visible refs: {sorted(unknown)}")
    missing = released_refs - value_set
    if missing:
        raise ValueError(f"{field_label} missing released refs: {sorted(missing)}")


class _WorkbenchBase(BaseModel):
    model_config = MODEL_CONFIG


class ProgrambenchReconstructionContextDerivationRow(_WorkbenchBase):
    derivation_ref: str
    source_ref: str
    derived_ref: str
    derivation_kind: Literal[
        "cleanroom_visible_case_packet_ref",
        "advisory_realization_ref",
        "concept_profile_ref",
        "local_probe_observation_ref",
        "io_artifact_index_ref",
        "side_effect_observation_ref",
    ]
    worker_visibility_posture: Literal["worker_visible_cleanroom_context"]
    limitation_note: str


class ProgrambenchReconstructionContextDerivationHashRow(_WorkbenchBase):
    derivation_hash_ref: str
    context_ref: str
    source_refs: list[str] = Field(min_length=1)
    context_hash: str
    hash_role: Literal[
        "worker_context_source_set",
        "derived_context_entry",
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_hash_row(self) -> "ProgrambenchReconstructionContextDerivationHashRow":
        _ensure_hash(self.context_hash, field_name="context_hash")
        _ensure_sorted_unique(self.source_refs, field_name="source_refs")
        return self


class ProgrambenchReconstructionExclusionReasonRow(_WorkbenchBase):
    exclusion_ref: str
    excluded_ref: str
    exclusion_kind: Literal[
        "worker_hidden_source",
        "forbidden_source",
        "postmortem_only",
        "excluded_derived_summary",
    ]
    exclusion_reason_posture: Literal[
        "excluded_from_worker_context",
        "auditor_only_evidence",
    ]
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_exclusion_reason(self) -> "ProgrambenchReconstructionExclusionReasonRow":
        _ensure_sorted_unique(self.source_refs, field_name="source_refs")
        return self


class ProgrambenchReconstructionWorkOrder(_WorkbenchBase):
    schema_id: Literal[PROGRAMBENCH_RECONSTRUCTION_WORK_ORDER_SCHEMA] = Field(
        alias="schema"
    )
    work_order_ref: str
    case_packet_ref: str
    adapter_readiness_summary_ref: str
    adapter_handoff_ref: str
    adapter_candidate_ref: str
    task_instance_ref: str
    pb_py_0_profile_refs: list[str] = Field(min_length=1)
    python_realization_pack_refs: list[str] = Field(min_length=1)
    worker_context_packet_ref: str
    context_exclusion_manifest_ref: str
    sandbox_policy_ref: str
    run_budget_ref: str
    guardrail_refs: list[str] = Field(min_length=1)
    case_packet_readiness_posture: Literal[
        "released_ready_case_packet",
        "blocked_case_packet_rejected",
        "future_family_only",
    ]
    contamination_gate_posture: Literal[
        "clean_contamination_gate_closed",
        "contamination_blocked",
        "unknown_contamination_blocked",
    ]
    work_order_scope_posture: Literal[
        "local_reconstruction_boundary_definition_only",
        "future_family_only",
    ]
    dispatch_authority_posture: Literal[
        "no_worker_dispatch_authority_granted_by_pb_recon_0a"
    ]
    execution_authority_posture: Literal[
        "no_execution_authority_granted_by_pb_recon_0a"
    ]
    official_programbench_posture: Literal[
        "no_official_programbench_participation_by_pb_recon_0a"
    ]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_work_order(self) -> "ProgrambenchReconstructionWorkOrder":
        if self.case_packet_readiness_posture != "released_ready_case_packet":
            raise ValueError("work orders require a released ready case packet")
        if self.contamination_gate_posture != "clean_contamination_gate_closed":
            raise ValueError("work orders require a clean contamination gate")
        if self.work_order_scope_posture != "local_reconstruction_boundary_definition_only":
            raise ValueError("work orders must define local boundary only")
        for field_name in (
            "pb_py_0_profile_refs",
            "python_realization_pack_refs",
            "guardrail_refs",
        ):
            _ensure_sorted_unique(getattr(self, field_name), field_name=field_name)
        return self


class ProgrambenchReconstructionWorkerContextPacket(_WorkbenchBase):
    schema_id: Literal[PROGRAMBENCH_RECONSTRUCTION_WORKER_CONTEXT_PACKET_SCHEMA] = Field(
        alias="schema"
    )
    worker_context_packet_ref: str
    work_order_ref: str
    case_packet_ref: str
    task_instance_ref: str
    worker_visible_source_refs: list[str] = Field(min_length=1)
    advisory_realization_refs: list[str] = Field(min_length=1)
    concept_profile_refs: list[str] = Field(min_length=1)
    probe_observation_refs: list[str] = Field(min_length=1)
    io_artifact_index_refs: list[str] = Field(min_length=1)
    side_effect_observation_refs: list[str] = Field(min_length=1)
    context_derivation_rows: list[ProgrambenchReconstructionContextDerivationRow] = Field(
        min_length=1
    )
    context_derivation_hash_rows: list[
        ProgrambenchReconstructionContextDerivationHashRow
    ] = Field(min_length=1)
    context_source_set_hash: str
    context_visibility_posture: Literal["worker_context_cleanroom_visible_only"]
    derived_summary_policy: Literal[
        "no_hidden_or_forbidden_derived_summaries_in_worker_context"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_worker_context(self) -> "ProgrambenchReconstructionWorkerContextPacket":
        _ensure_hash(self.context_source_set_hash, field_name="context_source_set_hash")
        for field_name in (
            "worker_visible_source_refs",
            "advisory_realization_refs",
            "concept_profile_refs",
            "probe_observation_refs",
            "io_artifact_index_refs",
            "side_effect_observation_refs",
        ):
            _ensure_sorted_unique(getattr(self, field_name), field_name=field_name)
        derivation_refs = [row.derivation_ref for row in self.context_derivation_rows]
        _ensure_sorted_unique(derivation_refs, field_name="context_derivation_rows")
        hash_refs = [row.derivation_hash_ref for row in self.context_derivation_hash_rows]
        _ensure_sorted_unique(hash_refs, field_name="context_derivation_hash_rows")
        all_visible_refs = self._all_worker_context_refs()
        for row in self.context_derivation_rows:
            if row.source_ref not in all_visible_refs or row.derived_ref not in all_visible_refs:
                raise ValueError("context derivation rows must use worker-visible refs")
        for row in self.context_derivation_hash_rows:
            missing_refs = set(row.source_refs) - all_visible_refs
            if missing_refs:
                raise ValueError(
                    "context derivation hash rows must use worker-visible refs: "
                    f"{sorted(missing_refs)}"
                )
        return self

    def _all_worker_context_refs(self) -> set[str]:
        return (
            set(self.worker_visible_source_refs)
            | set(self.advisory_realization_refs)
            | set(self.concept_profile_refs)
            | set(self.probe_observation_refs)
            | set(self.io_artifact_index_refs)
            | set(self.side_effect_observation_refs)
        )


class ProgrambenchReconstructionContextExclusionManifest(_WorkbenchBase):
    schema_id: Literal[
        PROGRAMBENCH_RECONSTRUCTION_CONTEXT_EXCLUSION_MANIFEST_SCHEMA
    ] = Field(alias="schema")
    context_exclusion_manifest_ref: str
    work_order_ref: str
    worker_context_packet_ref: str
    case_packet_ref: str
    task_instance_ref: str
    worker_hidden_source_refs: list[str]
    forbidden_source_refs: list[str]
    postmortem_only_refs: list[str]
    excluded_derived_summary_refs: list[str]
    exclusion_reason_rows: list[ProgrambenchReconstructionExclusionReasonRow] = Field(
        min_length=1
    )
    auditor_only_posture: Literal["auditor_only_not_worker_visible"]
    worker_visibility_posture: Literal["not_worker_visible"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_exclusion_manifest(
        self,
    ) -> "ProgrambenchReconstructionContextExclusionManifest":
        for field_name in (
            "worker_hidden_source_refs",
            "forbidden_source_refs",
            "postmortem_only_refs",
            "excluded_derived_summary_refs",
        ):
            _ensure_sorted_unique_allow_empty(getattr(self, field_name), field_name=field_name)
        reason_refs = [row.exclusion_ref for row in self.exclusion_reason_rows]
        _ensure_sorted_unique(reason_refs, field_name="exclusion_reason_rows")
        excluded_by_kind = {
            "worker_hidden_source": set(self.worker_hidden_source_refs),
            "forbidden_source": set(self.forbidden_source_refs),
            "postmortem_only": set(self.postmortem_only_refs),
            "excluded_derived_summary": set(self.excluded_derived_summary_refs),
        }
        all_excluded_refs = set().union(*excluded_by_kind.values())
        if not all_excluded_refs:
            raise ValueError("exclusion manifest must record at least one excluded ref")
        for row in self.exclusion_reason_rows:
            if row.excluded_ref not in excluded_by_kind[row.exclusion_kind]:
                raise ValueError("exclusion reason rows must match excluded ref kind")
        reasoned_refs = {row.excluded_ref for row in self.exclusion_reason_rows}
        missing_reason_rows = all_excluded_refs - reasoned_refs
        if missing_reason_rows:
            raise ValueError(
                "all excluded refs require exclusion reason rows: "
                f"{sorted(missing_reason_rows)}"
            )
        return self

    def all_excluded_refs(self) -> set[str]:
        return (
            set(self.worker_hidden_source_refs)
            | set(self.forbidden_source_refs)
            | set(self.postmortem_only_refs)
            | set(self.excluded_derived_summary_refs)
        )


class ProgrambenchReconstructionSandboxPolicy(_WorkbenchBase):
    schema_id: Literal[PROGRAMBENCH_RECONSTRUCTION_SANDBOX_POLICY_SCHEMA] = Field(
        alias="schema"
    )
    sandbox_policy_ref: str
    work_order_ref: str
    worker_context_packet_ref: str
    context_exclusion_manifest_ref: str
    allowed_runtime_kind: Literal[
        "python_stdlib_local_sandbox",
        "future_family_only",
    ]
    network_policy: Literal["network_disabled"]
    filesystem_policy: Literal["bounded_filesystem_write_scope"]
    dependency_policy: Literal[
        "stdlib_only",
        "declared_dependency_allowlist_only",
    ]
    environment_policy: Literal[
        "minimal_cleanroom_environment",
        "explicit_env_allowlist_only",
    ]
    command_shape_policy: Literal["argv_shaped_commands_only"]
    allowed_write_scope_refs: list[str] = Field(min_length=1)
    forbidden_path_refs: list[str]
    timeout_policy: Literal["bounded_timeout_required"]
    resource_limit_policy: Literal["bounded_resource_limits_required"]
    sandbox_enforcement_witness_requirements: list[
        Literal[
            "network_disabled",
            "no_source_lookup",
            "no_decompilation",
            "no_docker_socket",
            "no_host_secrets",
            "bounded_filesystem_write_scope",
            "argv_shaped_command_policy",
        ]
    ] = Field(min_length=7)
    secret_exposure_policy: Literal["host_secrets_forbidden"]
    docker_socket_policy: Literal["docker_socket_forbidden"]
    source_lookup_policy: Literal["source_lookup_forbidden"]
    decompilation_policy: Literal["decompilation_forbidden"]
    external_repo_lookup_policy: Literal["external_repo_lookup_forbidden"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_sandbox_policy(self) -> "ProgrambenchReconstructionSandboxPolicy":
        if self.allowed_runtime_kind == "future_family_only":
            raise ValueError("sandbox policy must select a local workbench runtime boundary")
        _ensure_sorted_unique(
            self.allowed_write_scope_refs, field_name="allowed_write_scope_refs"
        )
        _ensure_sorted_unique_allow_empty(
            self.forbidden_path_refs, field_name="forbidden_path_refs"
        )
        if set(self.allowed_write_scope_refs) & set(self.forbidden_path_refs):
            raise ValueError("allowed write scopes cannot overlap forbidden paths")
        witness_set = set(self.sandbox_enforcement_witness_requirements)
        missing = _REQUIRED_SANDBOX_WITNESSES - witness_set
        if missing:
            raise ValueError(
                "sandbox enforcement witness requirements missing: " f"{sorted(missing)}"
            )
        if len(witness_set) != len(self.sandbox_enforcement_witness_requirements):
            raise ValueError("sandbox enforcement witness requirements must not repeat")
        if self.sandbox_enforcement_witness_requirements != sorted(
            self.sandbox_enforcement_witness_requirements
        ):
            raise ValueError(
                "sandbox enforcement witness requirements must be lexicographically sorted"
            )
        return self


class ProgrambenchReconstructionRunBudget(_WorkbenchBase):
    schema_id: Literal[PROGRAMBENCH_RECONSTRUCTION_RUN_BUDGET_SCHEMA] = Field(
        alias="schema"
    )
    run_budget_ref: str
    work_order_ref: str
    max_candidate_artifact_count: int = Field(ge=0)
    max_local_run_count: int = Field(ge=0)
    max_probe_run_count: int = Field(ge=0)
    max_remand_count: int = Field(ge=0)
    timeout_budget_policy: Literal["bounded_timeout_budget_declared"]
    token_budget_policy: Literal["bounded_token_budget_declared"]
    filesystem_budget_policy: Literal["bounded_filesystem_budget_declared"]
    budget_authority_posture: Literal[
        "budget_constraints_only_no_execution_authority_by_pb_recon_0a"
    ]
    limitation_note: str


class ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail(_WorkbenchBase):
    schema_id: Literal[
        PROGRAMBENCH_RECONSTRUCTION_WORKBENCH_NON_AUTHORITY_GUARDRAIL_SCHEMA
    ] = Field(alias="schema")
    guardrail_ref: str
    work_order_refs: list[str] = Field(min_length=1)
    worker_context_packet_refs: list[str] = Field(min_length=1)
    context_exclusion_manifest_refs: list[str] = Field(min_length=1)
    sandbox_policy_refs: list[str] = Field(min_length=1)
    run_budget_refs: list[str] = Field(min_length=1)
    forbidden_future_artifact_kinds: list[str] = Field(min_length=1)
    non_authority_posture: Literal[
        "reconstruction_workbench_metadata_only_no_execution_authority"
    ]
    execution_posture: Literal["no_execution_authority_granted_by_pb_recon_0a"]
    official_programbench_posture: Literal[
        "no_official_programbench_participation_by_pb_recon_0a"
    ]
    hidden_test_posture: Literal["hidden_tests_not_visible_not_inference_evidence"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    submission_authority_posture: Literal["no_submission_authority_by_pb_recon_0a"]
    model_ranking_posture: Literal["no_model_ranking_claimed_by_pb_recon_0a"]
    future_family_selection_posture: Literal["no_future_family_selected_by_pb_recon_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_guardrail(
        self,
    ) -> "ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail":
        for field_name in (
            "work_order_refs",
            "worker_context_packet_refs",
            "context_exclusion_manifest_refs",
            "sandbox_policy_refs",
            "run_budget_refs",
            "forbidden_future_artifact_kinds",
        ):
            _ensure_sorted_unique(getattr(self, field_name), field_name=field_name)
        missing = PB_RECON_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS - set(
            self.forbidden_future_artifact_kinds
        )
        if missing:
            raise ValueError(
                "guardrail missing future slice artifact forbiddance: "
                f"{sorted(missing)}"
            )
        forbidden_current = set(self.forbidden_future_artifact_kinds) & (
            PB_RECON_0A_ARTIFACT_KINDS
        )
        if forbidden_current:
            raise ValueError(
                "guardrail must not forbid current slice artifact kinds: "
                f"{sorted(forbidden_current)}"
            )
        return self


def validate_pb_recon_0a_work_order_bundle(
    *,
    case_packet: ProgrambenchReconstructionCasePacket,
    readiness_summary: ProgrambenchAdapterReadinessSummary,
    adapter_handoff: ProgrambenchAdapterHandoff,
    adapter_family_closeout: ProgrambenchCleanroomAdapterFamilyCloseoutAlignment,
    work_order: ProgrambenchReconstructionWorkOrder,
    worker_context_packet: ProgrambenchReconstructionWorkerContextPacket,
    context_exclusion_manifest: ProgrambenchReconstructionContextExclusionManifest,
    sandbox_policy: ProgrambenchReconstructionSandboxPolicy,
    run_budget: ProgrambenchReconstructionRunBudget,
    guardrail: ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail,
) -> None:
    if readiness_summary.case_packet_ref != case_packet.case_packet_ref:
        raise ValueError("readiness summary must reference released case packet")
    if adapter_handoff.case_packet_ref != case_packet.case_packet_ref:
        raise ValueError("adapter handoff must reference released case packet")
    if adapter_handoff.readiness_summary_ref != readiness_summary.readiness_summary_ref:
        raise ValueError("adapter handoff must reference released readiness summary")
    if case_packet.case_packet_ref not in adapter_family_closeout.case_packet_refs:
        raise ValueError("adapter family closeout must reference released case packet")
    if (
        readiness_summary.readiness_summary_ref
        not in adapter_family_closeout.readiness_summary_refs
    ):
        raise ValueError("adapter family closeout must reference released readiness summary")
    if adapter_handoff.handoff_ref not in adapter_family_closeout.handoff_refs:
        raise ValueError("adapter family closeout must reference released handoff")

    if readiness_summary.contamination_status != "clean":
        raise ValueError("work orders require clean adapter readiness contamination")
    if (
        readiness_summary.readiness_posture
        != "ready_for_later_cleanroom_reconstruction_review"
    ):
        raise ValueError("work orders require ready adapter readiness posture")
    if readiness_summary.carried_blocker_refs:
        raise ValueError("work orders require readiness with no carried blockers")
    exposure_fields = (
        "forbidden_source_exposure_refs",
        "hidden_evidence_exposure_refs",
        "derived_summary_exposure_refs",
        "access_contract_violation_refs",
        "probe_scope_violation_refs",
    )
    for field_name in exposure_fields:
        if getattr(readiness_summary, field_name):
            raise ValueError(f"work orders reject readiness exposure field: {field_name}")

    if work_order.case_packet_ref != case_packet.case_packet_ref:
        raise ValueError("work order must reference released case packet")
    if work_order.adapter_readiness_summary_ref != readiness_summary.readiness_summary_ref:
        raise ValueError("work order must reference released readiness summary")
    if work_order.adapter_handoff_ref != adapter_handoff.handoff_ref:
        raise ValueError("work order must reference released adapter handoff")
    if work_order.adapter_candidate_ref != case_packet.adapter_candidate_ref:
        raise ValueError("work order must preserve adapter candidate lineage")
    if work_order.task_instance_ref != case_packet.task_instance_ref:
        raise ValueError("work order must preserve task instance lineage")
    _ensure_refs_resolve(
        work_order.pb_py_0_profile_refs,
        field_label="work order PB-PY-0 profile refs",
        released_refs=set(case_packet.pb_py_0_profile_refs),
    )
    _ensure_refs_resolve(
        work_order.python_realization_pack_refs,
        field_label="work order Python realization pack refs",
        released_refs=set(case_packet.pb_py_0_realization_pack_refs),
    )

    if worker_context_packet.work_order_ref != work_order.work_order_ref:
        raise ValueError("worker context packet must reference work order")
    if worker_context_packet.case_packet_ref != case_packet.case_packet_ref:
        raise ValueError("worker context packet must reference released case packet")
    if worker_context_packet.task_instance_ref != case_packet.task_instance_ref:
        raise ValueError("worker context packet must preserve task instance lineage")
    if work_order.worker_context_packet_ref != worker_context_packet.worker_context_packet_ref:
        raise ValueError("work order must reference worker context packet")

    if context_exclusion_manifest.work_order_ref != work_order.work_order_ref:
        raise ValueError("context exclusion manifest must reference work order")
    if (
        context_exclusion_manifest.worker_context_packet_ref
        != worker_context_packet.worker_context_packet_ref
    ):
        raise ValueError("context exclusion manifest must reference worker context packet")
    if context_exclusion_manifest.case_packet_ref != case_packet.case_packet_ref:
        raise ValueError("context exclusion manifest must reference released case packet")
    if context_exclusion_manifest.task_instance_ref != case_packet.task_instance_ref:
        raise ValueError("context exclusion manifest must preserve task instance lineage")
    if (
        work_order.context_exclusion_manifest_ref
        != context_exclusion_manifest.context_exclusion_manifest_ref
    ):
        raise ValueError("work order must reference context exclusion manifest")

    allowed_worker_source_refs = {
        case_packet.task_intake_ref,
        case_packet.task_artifact_manifest_ref,
        case_packet.visibility_manifest_ref,
        case_packet.worker_access_contract_ref,
        *case_packet.guardrail_refs,
        *case_packet.probe_plan_refs,
        *case_packet.probe_observation_refs,
        *case_packet.io_artifact_index_refs,
        *case_packet.side_effect_observation_refs,
        *case_packet.pb_py_0_profile_refs,
        *case_packet.pb_py_0_realization_pack_refs,
        *case_packet.pb_py_0_fixture_refs,
    }
    _ensure_refs_resolve(
        worker_context_packet.worker_visible_source_refs,
        field_label="worker context visible source refs",
        released_refs=allowed_worker_source_refs,
    )
    _ensure_refs_resolve(
        worker_context_packet.advisory_realization_refs,
        field_label="worker context advisory realization refs",
        released_refs=set(case_packet.pb_py_0_realization_pack_refs),
    )
    _ensure_refs_resolve(
        worker_context_packet.concept_profile_refs,
        field_label="worker context concept profile refs",
        released_refs=set(case_packet.pb_py_0_profile_refs),
    )
    _ensure_refs_resolve(
        worker_context_packet.probe_observation_refs,
        field_label="worker context probe observation refs",
        released_refs=set(case_packet.probe_observation_refs),
    )
    _ensure_refs_resolve(
        worker_context_packet.io_artifact_index_refs,
        field_label="worker context I/O artifact index refs",
        released_refs=set(case_packet.io_artifact_index_refs),
    )
    _ensure_refs_resolve(
        worker_context_packet.side_effect_observation_refs,
        field_label="worker context side-effect observation refs",
        released_refs=set(case_packet.side_effect_observation_refs),
    )

    excluded_refs = context_exclusion_manifest.all_excluded_refs()
    worker_context_refs = worker_context_packet._all_worker_context_refs()
    leaked_refs = worker_context_refs & excluded_refs
    if leaked_refs:
        raise ValueError(
            "worker context contains auditor-only or forbidden refs: "
            f"{sorted(leaked_refs)}"
        )

    if sandbox_policy.work_order_ref != work_order.work_order_ref:
        raise ValueError("sandbox policy must reference work order")
    if sandbox_policy.worker_context_packet_ref != worker_context_packet.worker_context_packet_ref:
        raise ValueError("sandbox policy must reference worker context packet")
    if (
        sandbox_policy.context_exclusion_manifest_ref
        != context_exclusion_manifest.context_exclusion_manifest_ref
    ):
        raise ValueError("sandbox policy must reference context exclusion manifest")
    if work_order.sandbox_policy_ref != sandbox_policy.sandbox_policy_ref:
        raise ValueError("work order must reference sandbox policy")

    if run_budget.work_order_ref != work_order.work_order_ref:
        raise ValueError("run budget must reference work order")
    if work_order.run_budget_ref != run_budget.run_budget_ref:
        raise ValueError("work order must reference run budget")

    if work_order.work_order_ref not in guardrail.work_order_refs:
        raise ValueError("guardrail must reference work order")
    if worker_context_packet.worker_context_packet_ref not in (
        guardrail.worker_context_packet_refs
    ):
        raise ValueError("guardrail must reference worker context packet")
    if context_exclusion_manifest.context_exclusion_manifest_ref not in (
        guardrail.context_exclusion_manifest_refs
    ):
        raise ValueError("guardrail must reference context exclusion manifest")
    if sandbox_policy.sandbox_policy_ref not in guardrail.sandbox_policy_refs:
        raise ValueError("guardrail must reference sandbox policy")
    if run_budget.run_budget_ref not in guardrail.run_budget_refs:
        raise ValueError("guardrail must reference run budget")
    _ensure_refs_resolve(
        work_order.guardrail_refs,
        field_label="work order guardrail refs",
        released_refs={guardrail.guardrail_ref},
    )
