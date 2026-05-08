from __future__ import annotations

import re
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .cleanroom_reconstruction import ProgrambenchRealizationFamilyCloseoutAlignment
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
PB_RECON_0B_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS = PB_RECON_0C_ARTIFACT_KINDS

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


def _ensure_refs_are_released(
    values: list[str],
    *,
    field_label: str,
    released_refs: set[str],
) -> None:
    unknown = set(values) - released_refs
    if unknown:
        raise ValueError(
            f"{field_label} references unreleased PB-PY-0 refs: {sorted(unknown)}"
        )


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


class ProgrambenchReconstructionGeneratedFileRow(_WorkbenchBase):
    generated_file_ref: str
    path_ref: str
    file_role: Literal[
        "candidate_source_file",
        "candidate_config_file",
        "candidate_support_file",
        "generated_output_artifact",
    ]
    write_scope_ref: str
    artifact_visibility_posture: Literal["local_workbench_generated_artifact"]
    limitation_note: str


class ProgrambenchReconstructionGeneratedArtifactHashRow(_WorkbenchBase):
    artifact_hash_ref: str
    generated_file_ref: str
    content_hash: str
    hash_role: Literal["candidate_artifact_content_hash"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_hash_row(
        self,
    ) -> "ProgrambenchReconstructionGeneratedArtifactHashRow":
        _ensure_hash(self.content_hash, field_name="content_hash")
        return self


class ProgrambenchReconstructionCandidateArtifactManifest(_WorkbenchBase):
    schema_id: Literal[
        PROGRAMBENCH_RECONSTRUCTION_CANDIDATE_ARTIFACT_MANIFEST_SCHEMA
    ] = Field(alias="schema")
    candidate_artifact_manifest_ref: str
    work_order_ref: str
    worker_context_packet_ref: str
    sandbox_policy_ref: str
    run_budget_ref: str
    adapter_candidate_ref: str
    task_instance_ref: str
    candidate_attempt_ref: str
    generated_file_rows: list[ProgrambenchReconstructionGeneratedFileRow] = Field(
        min_length=1
    )
    generated_artifact_hash_rows: list[
        ProgrambenchReconstructionGeneratedArtifactHashRow
    ] = Field(min_length=1)
    artifact_visibility_posture: Literal["local_workbench_artifacts_only"]
    submission_authority_posture: Literal[
        "no_official_submission_authority_by_pb_recon_0b"
    ]
    official_programbench_posture: Literal[
        "no_official_programbench_participation_by_pb_recon_0b"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_candidate_artifact_manifest(
        self,
    ) -> "ProgrambenchReconstructionCandidateArtifactManifest":
        generated_file_refs = [row.generated_file_ref for row in self.generated_file_rows]
        _ensure_sorted_unique(generated_file_refs, field_name="generated_file_rows")
        generated_path_refs = [row.path_ref for row in self.generated_file_rows]
        _ensure_sorted_unique(generated_path_refs, field_name="generated_file_paths")
        hash_refs = [row.artifact_hash_ref for row in self.generated_artifact_hash_rows]
        _ensure_sorted_unique(hash_refs, field_name="generated_artifact_hash_rows")
        hashed_file_refs = {
            row.generated_file_ref for row in self.generated_artifact_hash_rows
        }
        if hashed_file_refs != set(generated_file_refs):
            raise ValueError(
                "generated artifact hash rows must cover exactly generated files"
            )
        return self


class ProgrambenchReconstructionCommandArgvRow(_WorkbenchBase):
    argv_ref: str
    arg_index: int = Field(ge=0)
    argv_value: str
    argv_role: Literal[
        "executable",
        "flag",
        "argument",
        "input_path",
        "output_path",
    ]
    command_shape_posture: Literal["argv_token_no_shell"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_command_argv_row(self) -> "ProgrambenchReconstructionCommandArgvRow":
        if not self.argv_value or self.argv_value != self.argv_value.strip():
            raise ValueError("argv_value must be a non-empty trimmed string")
        return self


class ProgrambenchReconstructionLocalRunTrace(_WorkbenchBase):
    schema_id: Literal[PROGRAMBENCH_RECONSTRUCTION_LOCAL_RUN_TRACE_SCHEMA] = Field(
        alias="schema"
    )
    local_run_trace_ref: str
    candidate_artifact_manifest_ref: str
    work_order_ref: str
    sandbox_policy_ref: str
    run_budget_ref: str
    command_authority_ref: str
    command_allowlist_match_ref: str
    sandbox_attestation_ref: str
    network_attestation_ref: str
    secret_absence_attestation_ref: str
    dependency_resolution_posture: Literal[
        "stdlib_only_resolved",
        "declared_allowlist_resolved",
        "blocked_dependency_resolution",
        "unknown_dependency_resolution_blocked",
    ]
    write_scope_attestation_ref: str
    artifact_capture_policy_ref: str
    command_argv_rows: list[ProgrambenchReconstructionCommandArgvRow] = Field(
        min_length=1
    )
    working_directory_ref: str
    environment_ref: str
    stdin_artifact_ref: str
    stdout_hash: str
    stdout_excerpt_bounded: str = Field(max_length=512)
    stderr_hash: str
    stderr_excerpt_bounded: str = Field(max_length=512)
    exit_code: int
    duration_ms: int = Field(ge=0)
    timeout_status: Literal[
        "completed_without_timeout",
        "timed_out",
        "not_run_plan_only",
    ]
    pre_fs_manifest_ref: str
    post_fs_manifest_ref: str
    fs_diff_ref: str
    sandbox_violation_refs: list[str]
    hidden_test_posture: Literal["hidden_tests_not_visible_not_inference_evidence"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_local_run_trace(self) -> "ProgrambenchReconstructionLocalRunTrace":
        if self.dependency_resolution_posture not in {
            "stdlib_only_resolved",
            "declared_allowlist_resolved",
        }:
            raise ValueError("local run traces require resolved dependencies")
        if self.timeout_status == "not_run_plan_only":
            raise ValueError("local run traces must capture an observed local run")
        _ensure_hash(self.stdout_hash, field_name="stdout_hash")
        _ensure_hash(self.stderr_hash, field_name="stderr_hash")
        _ensure_sorted_unique_allow_empty(
            self.sandbox_violation_refs, field_name="sandbox_violation_refs"
        )
        argv_refs = [row.argv_ref for row in self.command_argv_rows]
        _ensure_sorted_unique(argv_refs, field_name="command_argv_rows")
        indices = [row.arg_index for row in self.command_argv_rows]
        if indices != list(range(len(indices))):
            raise ValueError("command argv rows must use contiguous arg_index values")
        if self.command_argv_rows[0].argv_role != "executable":
            raise ValueError("first command argv row must be the executable")
        return self


class ProgrambenchReconstructionProbeResultRow(_WorkbenchBase):
    probe_result_ref: str
    local_run_trace_ref: str
    probe_ref: str
    result_posture: Literal[
        "passed_local_probe",
        "failed_local_probe",
        "inconclusive_local_probe",
    ]
    evidence_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_probe_result_row(self) -> "ProgrambenchReconstructionProbeResultRow":
        _ensure_sorted_unique(self.evidence_refs, field_name="evidence_refs")
        return self


class ProgrambenchReconstructionProbeResultLog(_WorkbenchBase):
    schema_id: Literal[PROGRAMBENCH_RECONSTRUCTION_PROBE_RESULT_LOG_SCHEMA] = Field(
        alias="schema"
    )
    probe_result_log_ref: str
    work_order_ref: str
    candidate_artifact_manifest_ref: str
    local_run_trace_refs: list[str] = Field(min_length=1)
    probe_result_rows: list[ProgrambenchReconstructionProbeResultRow] = Field(
        min_length=1
    )
    expected_behavior_refs: list[str] = Field(min_length=1)
    observed_behavior_refs: list[str] = Field(min_length=1)
    stdout_stderr_separation_posture: Literal[
        "stdout_stderr_separation_satisfied",
        "stdout_stderr_separation_failed",
        "not_applicable_with_reason",
    ]
    exit_code_posture: Literal[
        "exit_code_expectation_satisfied",
        "exit_code_expectation_failed",
        "not_applicable_with_reason",
    ]
    filesystem_side_effect_posture: Literal[
        "filesystem_side_effect_expectation_satisfied",
        "filesystem_side_effect_expectation_failed",
        "not_applicable_with_reason",
    ]
    probe_truth_posture: Literal["local_probe_evidence_only_not_benchmark_truth"]
    hidden_test_equivalence_posture: Literal["local_probe_not_hidden_test_equivalence"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_probe_result_log(
        self,
    ) -> "ProgrambenchReconstructionProbeResultLog":
        _ensure_sorted_unique(self.local_run_trace_refs, field_name="local_run_trace_refs")
        _ensure_sorted_unique(
            self.expected_behavior_refs, field_name="expected_behavior_refs"
        )
        _ensure_sorted_unique(
            self.observed_behavior_refs, field_name="observed_behavior_refs"
        )
        result_refs = [row.probe_result_ref for row in self.probe_result_rows]
        _ensure_sorted_unique(result_refs, field_name="probe_result_rows")
        unknown_trace_refs = {
            row.local_run_trace_ref for row in self.probe_result_rows
        } - set(self.local_run_trace_refs)
        if unknown_trace_refs:
            raise ValueError(
                "probe result rows reference unknown local run traces: "
                f"{sorted(unknown_trace_refs)}"
            )
        return self


class ProgrambenchReconstructionRemandReasonRow(_WorkbenchBase):
    remand_reason_ref: str
    source_ref: str
    reason_kind: Literal[
        "local_probe_failure",
        "local_sandbox_violation",
        "missing_required_artifact",
        "unsupported_behavior_gap",
        "inconclusive_trace",
    ]
    severity: Literal["blocking", "nonblocking"]
    limitation_note: str


class ProgrambenchReconstructionCorrectionAttemptRow(_WorkbenchBase):
    correction_attempt_ref: str
    candidate_attempt_ref: str
    correction_scope_posture: Literal[
        "local_candidate_artifact_only",
        "future_family_only",
    ]
    changed_artifact_refs: list[str]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_correction_attempt(
        self,
    ) -> "ProgrambenchReconstructionCorrectionAttemptRow":
        if self.correction_scope_posture != "local_candidate_artifact_only":
            raise ValueError("correction attempts must stay local to candidate artifacts")
        _ensure_sorted_unique_allow_empty(
            self.changed_artifact_refs, field_name="changed_artifact_refs"
        )
        return self


class ProgrambenchReconstructionRemandCorrectionRecord(_WorkbenchBase):
    schema_id: Literal[
        PROGRAMBENCH_RECONSTRUCTION_REMAND_CORRECTION_RECORD_SCHEMA
    ] = Field(alias="schema")
    remand_correction_record_ref: str
    work_order_ref: str
    candidate_attempt_ref: str
    remand_reason_source: Literal[
        "local_probe_failure",
        "local_sandbox_violation",
        "missing_required_artifact",
        "unsupported_behavior_gap",
        "inconclusive_trace",
    ]
    remand_reason_rows: list[ProgrambenchReconstructionRemandReasonRow] = Field(
        min_length=1
    )
    correction_attempt_rows: list[
        ProgrambenchReconstructionCorrectionAttemptRow
    ] = Field(min_length=1)
    semantic_route_preservation_posture: Literal[
        "semantic_route_preserved",
        "semantic_route_not_assessed",
        "semantic_route_mutated_forbidden",
    ]
    case_packet_mutation_posture: Literal["released_case_packet_not_mutated"]
    hidden_evidence_use_posture: Literal["no_hidden_or_forbidden_evidence_used"]
    budget_consumption_refs: list[str] = Field(min_length=1)
    remand_outcome_posture: Literal[
        "corrected_for_local_reprobe",
        "remand_recorded_no_correction",
        "blocked_after_remand",
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_remand_correction_record(
        self,
    ) -> "ProgrambenchReconstructionRemandCorrectionRecord":
        if self.semantic_route_preservation_posture == "semantic_route_mutated_forbidden":
            raise ValueError("remand records must preserve the semantic route")
        reason_refs = [row.remand_reason_ref for row in self.remand_reason_rows]
        _ensure_sorted_unique(reason_refs, field_name="remand_reason_rows")
        correction_refs = [
            row.correction_attempt_ref for row in self.correction_attempt_rows
        ]
        _ensure_sorted_unique(
            correction_refs, field_name="correction_attempt_rows"
        )
        _ensure_sorted_unique(
            self.budget_consumption_refs, field_name="budget_consumption_refs"
        )
        if {row.reason_kind for row in self.remand_reason_rows} != {
            self.remand_reason_source
        }:
            raise ValueError("remand reason rows must match remand_reason_source")
        for row in self.correction_attempt_rows:
            if row.candidate_attempt_ref != self.candidate_attempt_ref:
                raise ValueError("correction attempts must preserve candidate attempt ref")
        return self


def validate_pb_recon_0a_work_order_bundle(
    *,
    case_packet: ProgrambenchReconstructionCasePacket,
    pb_py_0_family_closeout: ProgrambenchRealizationFamilyCloseoutAlignment,
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

    _ensure_refs_are_released(
        case_packet.pb_py_0_profile_refs,
        field_label="case packet PB-PY-0 profile refs",
        released_refs=set(pb_py_0_family_closeout.released_profile_refs),
    )
    _ensure_refs_are_released(
        case_packet.pb_py_0_realization_pack_refs,
        field_label="case packet Python realization pack refs",
        released_refs=set(pb_py_0_family_closeout.released_realization_pack_refs),
    )
    _ensure_refs_are_released(
        case_packet.pb_py_0_fixture_refs,
        field_label="case packet PB-PY-0 fixture refs",
        released_refs=set(pb_py_0_family_closeout.released_fixture_refs),
    )

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
    _ensure_refs_are_released(
        work_order.pb_py_0_profile_refs,
        field_label="work order PB-PY-0 profile refs",
        released_refs=set(pb_py_0_family_closeout.released_profile_refs),
    )
    _ensure_refs_are_released(
        work_order.python_realization_pack_refs,
        field_label="work order Python realization pack refs",
        released_refs=set(pb_py_0_family_closeout.released_realization_pack_refs),
    )
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


def _validate_pb_recon_0a_row_linkage(
    *,
    work_order: ProgrambenchReconstructionWorkOrder,
    worker_context_packet: ProgrambenchReconstructionWorkerContextPacket,
    context_exclusion_manifest: ProgrambenchReconstructionContextExclusionManifest,
    sandbox_policy: ProgrambenchReconstructionSandboxPolicy,
    run_budget: ProgrambenchReconstructionRunBudget,
    guardrail: ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail,
) -> None:
    if worker_context_packet.work_order_ref != work_order.work_order_ref:
        raise ValueError("worker context packet must reference work order")
    if (
        context_exclusion_manifest.work_order_ref != work_order.work_order_ref
        or context_exclusion_manifest.worker_context_packet_ref
        != worker_context_packet.worker_context_packet_ref
    ):
        raise ValueError("context exclusion manifest must preserve A workbench linkage")
    if (
        sandbox_policy.work_order_ref != work_order.work_order_ref
        or sandbox_policy.worker_context_packet_ref
        != worker_context_packet.worker_context_packet_ref
        or sandbox_policy.context_exclusion_manifest_ref
        != context_exclusion_manifest.context_exclusion_manifest_ref
    ):
        raise ValueError("sandbox policy must preserve A workbench linkage")
    if run_budget.work_order_ref != work_order.work_order_ref:
        raise ValueError("run budget must reference work order")
    if work_order.work_order_ref not in guardrail.work_order_refs:
        raise ValueError("guardrail must reference work order")
    if worker_context_packet.worker_context_packet_ref not in (
        guardrail.worker_context_packet_refs
    ):
        raise ValueError("guardrail must reference worker context packet")
    if sandbox_policy.sandbox_policy_ref not in guardrail.sandbox_policy_refs:
        raise ValueError("guardrail must reference sandbox policy")
    if run_budget.run_budget_ref not in guardrail.run_budget_refs:
        raise ValueError("guardrail must reference run budget")


def validate_pb_recon_0b_local_evidence_bundle(
    *,
    work_order: ProgrambenchReconstructionWorkOrder,
    worker_context_packet: ProgrambenchReconstructionWorkerContextPacket,
    context_exclusion_manifest: ProgrambenchReconstructionContextExclusionManifest,
    sandbox_policy: ProgrambenchReconstructionSandboxPolicy,
    run_budget: ProgrambenchReconstructionRunBudget,
    guardrail: ProgrambenchReconstructionWorkbenchNonAuthorityGuardrail,
    candidate_artifact_manifest: ProgrambenchReconstructionCandidateArtifactManifest,
    local_run_traces: list[ProgrambenchReconstructionLocalRunTrace],
    probe_result_log: ProgrambenchReconstructionProbeResultLog,
    remand_correction_records: list[ProgrambenchReconstructionRemandCorrectionRecord],
) -> None:
    _validate_pb_recon_0a_row_linkage(
        work_order=work_order,
        worker_context_packet=worker_context_packet,
        context_exclusion_manifest=context_exclusion_manifest,
        sandbox_policy=sandbox_policy,
        run_budget=run_budget,
        guardrail=guardrail,
    )
    if not local_run_traces:
        raise ValueError("PB-RECON-0-B requires at least one local run trace")
    if not remand_correction_records:
        raise ValueError("PB-RECON-0-B requires remand/correction records")

    if candidate_artifact_manifest.work_order_ref != work_order.work_order_ref:
        raise ValueError("candidate artifact manifest must reference work order")
    if (
        candidate_artifact_manifest.worker_context_packet_ref
        != worker_context_packet.worker_context_packet_ref
    ):
        raise ValueError("candidate artifact manifest must reference worker context")
    if candidate_artifact_manifest.sandbox_policy_ref != sandbox_policy.sandbox_policy_ref:
        raise ValueError("candidate artifact manifest must reference sandbox policy")
    if candidate_artifact_manifest.run_budget_ref != run_budget.run_budget_ref:
        raise ValueError("candidate artifact manifest must reference run budget")
    if candidate_artifact_manifest.adapter_candidate_ref != work_order.adapter_candidate_ref:
        raise ValueError("candidate artifact manifest must preserve adapter lineage")
    if candidate_artifact_manifest.task_instance_ref != work_order.task_instance_ref:
        raise ValueError("candidate artifact manifest must preserve task lineage")
    if len(candidate_artifact_manifest.generated_file_rows) > (
        run_budget.max_candidate_artifact_count
    ):
        raise ValueError("candidate artifact manifest exceeds candidate artifact budget")

    trace_refs = [trace.local_run_trace_ref for trace in local_run_traces]
    _ensure_sorted_unique(trace_refs, field_name="local_run_traces")
    if len(local_run_traces) > run_budget.max_local_run_count:
        raise ValueError("local run traces exceed released run budget")

    trace_by_ref = {trace.local_run_trace_ref: trace for trace in local_run_traces}
    for trace in local_run_traces:
        if (
            trace.candidate_artifact_manifest_ref
            != candidate_artifact_manifest.candidate_artifact_manifest_ref
        ):
            raise ValueError("local run traces must reference candidate artifact manifest")
        if trace.work_order_ref != work_order.work_order_ref:
            raise ValueError("local run traces must reference work order")
        if trace.sandbox_policy_ref != sandbox_policy.sandbox_policy_ref:
            raise ValueError("local run traces must reference sandbox policy")
        if trace.run_budget_ref != run_budget.run_budget_ref:
            raise ValueError("local run traces must reference run budget")

    if probe_result_log.work_order_ref != work_order.work_order_ref:
        raise ValueError("probe result log must reference work order")
    if (
        probe_result_log.candidate_artifact_manifest_ref
        != candidate_artifact_manifest.candidate_artifact_manifest_ref
    ):
        raise ValueError("probe result log must reference candidate artifact manifest")
    if set(probe_result_log.local_run_trace_refs) != set(trace_refs):
        raise ValueError("probe result log must cover exactly local run traces")
    if len(probe_result_log.probe_result_rows) > run_budget.max_probe_run_count:
        raise ValueError("probe result rows exceed released probe budget")
    for row in probe_result_log.probe_result_rows:
        trace = trace_by_ref[row.local_run_trace_ref]
        if trace.sandbox_violation_refs and row.result_posture == "passed_local_probe":
            raise ValueError("sandbox violations cannot be treated as passed probes")

    remand_refs = [
        record.remand_correction_record_ref for record in remand_correction_records
    ]
    _ensure_sorted_unique(remand_refs, field_name="remand_correction_records")
    if len(remand_correction_records) > run_budget.max_remand_count:
        raise ValueError("remand/correction records exceed released remand budget")
    for record in remand_correction_records:
        if record.work_order_ref != work_order.work_order_ref:
            raise ValueError("remand/correction records must reference work order")
        if record.candidate_attempt_ref != (
            candidate_artifact_manifest.candidate_attempt_ref
        ):
            raise ValueError("remand/correction records must preserve candidate attempt")
        if run_budget.run_budget_ref not in record.budget_consumption_refs:
            raise ValueError("remand/correction records must reference run budget")
