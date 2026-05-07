from __future__ import annotations

import re
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

PROGRAMBENCH_CLEANROOM_TASK_INTAKE_SCHEMA = "programbench_cleanroom_task_intake@1"
PROGRAMBENCH_TASK_ARTIFACT_MANIFEST_SCHEMA = "programbench_task_artifact_manifest@1"
PROGRAMBENCH_TASK_VISIBILITY_MANIFEST_SCHEMA = "programbench_task_visibility_manifest@1"
PROGRAMBENCH_ADAPTER_WORKER_ACCESS_CONTRACT_SCHEMA = (
    "programbench_adapter_worker_access_contract@1"
)
PROGRAMBENCH_ADAPTER_NON_AUTHORITY_GUARDRAIL_SCHEMA = (
    "programbench_adapter_non_authority_guardrail@1"
)

PB_ADAPTER_0A_ARTIFACT_KINDS = {
    PROGRAMBENCH_CLEANROOM_TASK_INTAKE_SCHEMA,
    PROGRAMBENCH_TASK_ARTIFACT_MANIFEST_SCHEMA,
    PROGRAMBENCH_TASK_VISIBILITY_MANIFEST_SCHEMA,
    PROGRAMBENCH_ADAPTER_WORKER_ACCESS_CONTRACT_SCHEMA,
    PROGRAMBENCH_ADAPTER_NON_AUTHORITY_GUARDRAIL_SCHEMA,
}
PB_ADAPTER_0B_ARTIFACT_KINDS = {
    "programbench_adapter_probe_plan@1",
    "programbench_probe_observation_log@1",
    "programbench_io_artifact_observation_index@1",
    "programbench_filesystem_side_effect_observation@1",
}
PB_ADAPTER_0C_ARTIFACT_KINDS = {
    "programbench_reconstruction_case_packet@1",
    "programbench_adapter_readiness_summary@1",
    "programbench_adapter_handoff@1",
    "programbench_cleanroom_adapter_family_closeout_alignment@1",
}
PB_ADAPTER_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS = (
    PB_ADAPTER_0B_ARTIFACT_KINDS | PB_ADAPTER_0C_ARTIFACT_KINDS
)

_SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
_EXPOSURE_FORBIDDEN_VISIBILITY_CLASSES = {
    "evaluation_oracle_hidden",
    "postmortem_only",
    "forbidden_original_source",
    "forbidden_decompilation",
    "forbidden_internet_lookup",
    "forbidden_external_repo",
    "forbidden_host_secret",
    "forbidden_docker_socket",
}
_EXPOSURE_FORBIDDEN_BASIS = {
    "known_hidden",
    "known_forbidden",
}
_CLEANROOM_WORKER_SUMMARY_POLICIES = {
    "cleanroom_visible_summary_allowed",
}
_WORKER_VISIBLE_POLICIES = {
    "worker_visible_allowed",
}

AdapterVisibilityClass = Literal[
    "cleanroom_visible",
    "worker_generated_probe",
    "worker_generated_submission",
    "reference_executable_observation",
    "public_descriptor_context",
    "support_context_only",
    "postmortem_only",
    "evaluation_oracle_hidden",
    "forbidden_original_source",
    "forbidden_decompilation",
    "forbidden_internet_lookup",
    "forbidden_external_repo",
    "forbidden_host_secret",
    "forbidden_docker_socket",
]
VisibilityBasis = Literal[
    "known_visible",
    "known_hidden",
    "known_forbidden",
    "known_support_only",
    "unknown_not_indexed",
    "declared_absent",
]
StorePresencePosture = Literal[
    "present",
    "declared_absent",
    "unknown_not_indexed",
]
DerivedSummaryPolicy = Literal[
    "cleanroom_visible_summary_allowed",
    "hidden_summary_forbidden_for_worker",
    "forbidden_summary_forbidden_for_worker",
    "support_summary_context_only",
    "no_summary_available",
]
WorkerExposurePolicy = Literal[
    "worker_visible_allowed",
    "worker_hidden",
    "worker_exposure_forbidden",
    "support_context_only_not_decisive",
]
TaskOriginPosture = Literal[
    "synthetic_local_task",
    "repo_internal_task",
    "programbench_style_public_context_only",
    "official_programbench_task_not_selected",
    "unknown_origin_blocked",
]
ArtifactOriginPosture = Literal[
    "synthetic_local_task_artifact",
    "repo_internal_task_artifact",
    "programbench_style_public_context_only",
    "official_programbench_artifact_not_selected",
    "unknown_origin_blocked",
]


def _ensure_non_empty_unique(values: list[str], *, field_name: str) -> None:
    for value in values:
        if not isinstance(value, str) or not value or value != value.strip():
            raise ValueError(f"{field_name} entries must be non-empty trimmed strings")
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")


def _ensure_hash(value: str, *, field_name: str) -> None:
    if not _SHA256_RE.fullmatch(value):
        raise ValueError(f"{field_name} must be a sha256:<64 lowercase hex> hash")


def _visibility_blocks_worker_exposure(
    *,
    visibility_class: str,
    visibility_basis: str,
    worker_exposure_policy: str,
    derived_summary_policy: str,
    field_name: str,
) -> None:
    is_hidden_or_forbidden = (
        visibility_class in _EXPOSURE_FORBIDDEN_VISIBILITY_CLASSES
        or visibility_basis in _EXPOSURE_FORBIDDEN_BASIS
    )
    if not is_hidden_or_forbidden:
        return
    if worker_exposure_policy in _WORKER_VISIBLE_POLICIES:
        raise ValueError(f"{field_name} hidden or forbidden stores must not be worker-visible")
    if derived_summary_policy in _CLEANROOM_WORKER_SUMMARY_POLICIES:
        raise ValueError(
            f"{field_name} hidden or forbidden stores must not become worker summaries"
        )


class _AdapterBase(BaseModel):
    model_config = MODEL_CONFIG


class ProgrambenchArtifactHashRow(_AdapterBase):
    artifact_ref: str
    artifact_hash: str
    artifact_role: Literal[
        "reference_executable",
        "usage_doc",
        "visible_input_artifact",
        "source_set",
    ]
    observed_at: str
    snapshot_ref: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_hash_row(self) -> "ProgrambenchArtifactHashRow":
        _ensure_hash(self.artifact_hash, field_name="artifact_hash")
        return self


class ProgrambenchCleanroomTaskIntake(_AdapterBase):
    schema_id: Literal[PROGRAMBENCH_CLEANROOM_TASK_INTAKE_SCHEMA] = Field(alias="schema")
    task_intake_ref: str
    adapter_candidate_ref: str
    task_instance_ref: str
    source_refs: list[str] = Field(min_length=1)
    task_artifact_manifest_ref: str
    task_origin_posture: TaskOriginPosture
    task_identifier_posture: Literal[
        "stable_task_instance_ref_declared",
        "task_identifier_context_only",
        "unknown_task_identifier_blocked",
    ]
    benchmark_context_refs: list[str]
    pb_py_0_profile_refs: list[str] = Field(min_length=1)
    pb_py_0_fixture_contract_refs: list[str] = Field(min_length=1)
    target_language_posture: Literal["python_target_language_for_later_reconstruction_review"]
    reference_executable_ref: str
    usage_docs_refs: list[str] = Field(min_length=1)
    visible_input_artifact_refs: list[str]
    forbidden_inference_source_refs: list[str]
    official_participation_posture: Literal[
        "no_official_programbench_participation_by_pb_adapter_0a"
    ]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_task_intake(self) -> "ProgrambenchCleanroomTaskIntake":
        if self.task_origin_posture in {
            "official_programbench_task_not_selected",
            "unknown_origin_blocked",
        }:
            raise ValueError("task intake origin is not selectable for PB-ADAPTER-0-A")
        for field_name in (
            "source_refs",
            "benchmark_context_refs",
            "pb_py_0_profile_refs",
            "pb_py_0_fixture_contract_refs",
            "usage_docs_refs",
            "visible_input_artifact_refs",
            "forbidden_inference_source_refs",
        ):
            _ensure_non_empty_unique(getattr(self, field_name), field_name=field_name)
        return self


class ProgrambenchTaskArtifactManifest(_AdapterBase):
    schema_id: Literal[PROGRAMBENCH_TASK_ARTIFACT_MANIFEST_SCHEMA] = Field(alias="schema")
    task_artifact_manifest_ref: str
    task_intake_ref: str
    adapter_candidate_ref: str
    task_instance_ref: str
    reference_executable_ref: str
    reference_executable_hash: str
    usage_docs_hash_rows: list[ProgrambenchArtifactHashRow] = Field(min_length=1)
    visible_input_artifact_hash_rows: list[ProgrambenchArtifactHashRow]
    source_set_hash: str
    artifact_origin_posture: ArtifactOriginPosture
    observed_at: str
    snapshot_ref: str
    ingestion_method: Literal[
        "repo_snapshot",
        "local_synthetic_fixture_snapshot",
        "public_descriptor_observation",
        "manual_cleanroom_manifest",
    ]
    artifact_identity_posture: Literal["hashes_and_snapshot_bound"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_artifact_manifest(self) -> "ProgrambenchTaskArtifactManifest":
        _ensure_hash(self.reference_executable_hash, field_name="reference_executable_hash")
        _ensure_hash(self.source_set_hash, field_name="source_set_hash")
        if self.artifact_origin_posture in {
            "official_programbench_artifact_not_selected",
            "unknown_origin_blocked",
        }:
            raise ValueError("artifact origin is not selectable for PB-ADAPTER-0-A")
        usage_refs = [row.artifact_ref for row in self.usage_docs_hash_rows]
        visible_refs = [row.artifact_ref for row in self.visible_input_artifact_hash_rows]
        _ensure_non_empty_unique(usage_refs, field_name="usage_docs_hash_rows.artifact_ref")
        _ensure_non_empty_unique(
            visible_refs,
            field_name="visible_input_artifact_hash_rows.artifact_ref",
        )
        for row in self.usage_docs_hash_rows:
            if row.artifact_role != "usage_doc":
                raise ValueError("usage_docs_hash_rows must use usage_doc role")
        for row in self.visible_input_artifact_hash_rows:
            if row.artifact_role != "visible_input_artifact":
                raise ValueError(
                    "visible_input_artifact_hash_rows must use visible_input_artifact role"
                )
        return self


class ProgrambenchTaskVisibilityStoreRow(_AdapterBase):
    store_ref: str
    source_refs: list[str]
    visibility_class: AdapterVisibilityClass
    visibility_basis: VisibilityBasis
    store_presence_posture: StorePresencePosture
    derived_summary_policy: DerivedSummaryPolicy
    worker_exposure_policy: WorkerExposurePolicy
    limitation_note: str

    @model_validator(mode="after")
    def _validate_store_row(self) -> "ProgrambenchTaskVisibilityStoreRow":
        _ensure_non_empty_unique(self.source_refs, field_name="source_refs")
        _visibility_blocks_worker_exposure(
            visibility_class=self.visibility_class,
            visibility_basis=self.visibility_basis,
            worker_exposure_policy=self.worker_exposure_policy,
            derived_summary_policy=self.derived_summary_policy,
            field_name=self.store_ref,
        )
        return self


class ProgrambenchVisibilityBasisRow(_AdapterBase):
    basis_ref: str
    store_ref: str
    visibility_basis: VisibilityBasis
    basis_source_refs: list[str] = Field(min_length=1)
    limitation_note: str


class ProgrambenchStorePresenceRow(_AdapterBase):
    presence_ref: str
    store_ref: str
    store_presence_posture: StorePresencePosture
    presence_source_refs: list[str]
    limitation_note: str


class ProgrambenchDerivedSummaryPolicyRow(_AdapterBase):
    policy_ref: str
    store_ref: str
    source_visibility_class: AdapterVisibilityClass
    source_visibility_basis: VisibilityBasis
    derived_summary_policy: DerivedSummaryPolicy
    worker_summary_visibility_posture: Literal[
        "cleanroom_visible_to_worker",
        "not_worker_visible",
        "support_context_only_not_decisive",
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_summary_policy(self) -> "ProgrambenchDerivedSummaryPolicyRow":
        worker_policy = (
            "worker_visible_allowed"
            if self.worker_summary_visibility_posture == "cleanroom_visible_to_worker"
            else "worker_exposure_forbidden"
        )
        _visibility_blocks_worker_exposure(
            visibility_class=self.source_visibility_class,
            visibility_basis=self.source_visibility_basis,
            worker_exposure_policy=worker_policy,
            derived_summary_policy=self.derived_summary_policy,
            field_name=self.policy_ref,
        )
        return self


class ProgrambenchWorkerExposurePolicyRow(_AdapterBase):
    exposure_policy_ref: str
    store_ref: str
    worker_exposure_policy: WorkerExposurePolicy
    phase: Literal["intake_phase", "inference_phase", "probe_observation_phase"]
    limitation_note: str


class ProgrambenchTaskVisibilityManifest(_AdapterBase):
    schema_id: Literal[PROGRAMBENCH_TASK_VISIBILITY_MANIFEST_SCHEMA] = Field(alias="schema")
    visibility_manifest_ref: str
    task_intake_ref: str
    task_artifact_manifest_ref: str
    adapter_candidate_ref: str
    task_instance_ref: str
    visible_store_rows: list[ProgrambenchTaskVisibilityStoreRow] = Field(min_length=1)
    hidden_store_rows: list[ProgrambenchTaskVisibilityStoreRow]
    forbidden_store_rows: list[ProgrambenchTaskVisibilityStoreRow]
    support_context_rows: list[ProgrambenchTaskVisibilityStoreRow]
    visibility_basis_rows: list[ProgrambenchVisibilityBasisRow] = Field(min_length=1)
    store_presence_rows: list[ProgrambenchStorePresenceRow] = Field(min_length=1)
    derived_summary_policy_rows: list[ProgrambenchDerivedSummaryPolicyRow] = Field(
        min_length=1
    )
    worker_exposure_policy_rows: list[ProgrambenchWorkerExposurePolicyRow] = Field(
        min_length=1
    )
    worker_visible_file_refs: list[str]
    worker_hidden_file_refs: list[str]
    inference_visibility_posture: Literal["cleanroom_visible_artifacts_only"]
    forbidden_store_reachability_posture: Literal[
        "forbidden_and_hidden_stores_unreachable_during_inference"
    ]
    source_visibility_policy: Literal[
        "hidden_and_forbidden_sources_not_summarized_for_worker"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_visibility_manifest(self) -> "ProgrambenchTaskVisibilityManifest":
        store_rows = (
            self.visible_store_rows
            + self.hidden_store_rows
            + self.forbidden_store_rows
            + self.support_context_rows
        )
        store_refs = [row.store_ref for row in store_rows]
        if len(store_refs) != len(set(store_refs)):
            raise ValueError("visibility store rows must not repeat store_ref")
        for row in self.visible_store_rows:
            if row.visibility_basis != "known_visible":
                raise ValueError("visible_store_rows must use known_visible basis")
            if row.worker_exposure_policy != "worker_visible_allowed":
                raise ValueError("visible_store_rows must be worker-visible")
        for row in self.hidden_store_rows:
            if row.visibility_basis != "known_hidden":
                raise ValueError("hidden_store_rows must use known_hidden basis")
        for row in self.forbidden_store_rows:
            if row.visibility_basis != "known_forbidden":
                raise ValueError("forbidden_store_rows must use known_forbidden basis")
        for row in self.support_context_rows:
            if row.visibility_basis != "known_support_only":
                raise ValueError("support_context_rows must use known_support_only basis")
        hidden_or_forbidden_refs = {
            row.store_ref for row in self.hidden_store_rows + self.forbidden_store_rows
        }
        worker_visible_overlap = hidden_or_forbidden_refs & set(self.worker_visible_file_refs)
        if worker_visible_overlap:
            raise ValueError(
                "hidden or forbidden stores cannot be worker-visible refs: "
                f"{sorted(worker_visible_overlap)}"
            )
        hidden_visible_file_overlap = set(self.worker_hidden_file_refs) & set(
            self.worker_visible_file_refs
        )
        if hidden_visible_file_overlap:
            raise ValueError(
                "worker-hidden files cannot be worker-visible: "
                f"{sorted(hidden_visible_file_overlap)}"
            )
        known_store_refs = set(store_refs)
        for rows, ref_field in (
            (self.visibility_basis_rows, "basis_ref"),
            (self.store_presence_rows, "presence_ref"),
            (self.derived_summary_policy_rows, "policy_ref"),
            (self.worker_exposure_policy_rows, "exposure_policy_ref"),
        ):
            refs = [getattr(row, ref_field) for row in rows]
            if len(refs) != len(set(refs)):
                raise ValueError(f"{ref_field} rows must not repeat refs")
            missing_store_refs = {row.store_ref for row in rows} - known_store_refs
            if missing_store_refs:
                raise ValueError(
                    f"{ref_field} rows reference unknown stores: {sorted(missing_store_refs)}"
                )
        return self


class ProgrambenchAdapterWorkerAccessContract(_AdapterBase):
    schema_id: Literal[PROGRAMBENCH_ADAPTER_WORKER_ACCESS_CONTRACT_SCHEMA] = Field(
        alias="schema"
    )
    worker_access_contract_ref: str
    task_intake_ref: str
    task_artifact_manifest_ref: str
    visibility_manifest_ref: str
    adapter_candidate_ref: str
    task_instance_ref: str
    allowed_inference_source_refs: list[str] = Field(min_length=1)
    forbidden_inference_source_refs: list[str]
    allowed_network_posture: Literal["network_disabled_during_inference"]
    internet_lookup_posture: Literal["internet_lookup_forbidden_during_inference"]
    external_repo_lookup_posture: Literal["external_repo_lookup_forbidden_during_inference"]
    source_lookup_posture: Literal["source_lookup_forbidden_during_inference"]
    decompilation_posture: Literal["decompilation_forbidden_during_inference"]
    docker_socket_posture: Literal["docker_socket_forbidden_during_inference"]
    host_secret_posture: Literal["host_secret_access_forbidden_during_inference"]
    allowed_command_posture: Literal["no_command_execution_authority_by_pb_adapter_0a"]
    probe_execution_authority_posture: Literal[
        "no_probe_execution_authority_by_pb_adapter_0a"
    ]
    submission_generation_posture: Literal[
        "no_submission_generation_authority_by_pb_adapter_0a"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_access_contract(self) -> "ProgrambenchAdapterWorkerAccessContract":
        for field_name in ("allowed_inference_source_refs", "forbidden_inference_source_refs"):
            _ensure_non_empty_unique(getattr(self, field_name), field_name=field_name)
        overlap = set(self.allowed_inference_source_refs) & set(
            self.forbidden_inference_source_refs
        )
        if overlap:
            raise ValueError(
                f"forbidden sources cannot be allowed for inference: {sorted(overlap)}"
            )
        return self


class ProgrambenchAdapterNonAuthorityGuardrail(_AdapterBase):
    schema_id: Literal[PROGRAMBENCH_ADAPTER_NON_AUTHORITY_GUARDRAIL_SCHEMA] = Field(
        alias="schema"
    )
    guardrail_ref: str
    task_intake_refs: list[str] = Field(min_length=1)
    task_artifact_manifest_refs: list[str] = Field(min_length=1)
    visibility_manifest_refs: list[str] = Field(min_length=1)
    worker_access_contract_refs: list[str] = Field(min_length=1)
    forbidden_future_artifact_kinds: list[str] = Field(min_length=1)
    non_authority_posture: Literal["adapter_metadata_only_no_execution_authority"]
    official_programbench_posture: Literal[
        "no_official_programbench_participation_by_pb_adapter_0a"
    ]
    hidden_test_posture: Literal["hidden_tests_not_visible_not_inference_evidence"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    submission_authority_posture: Literal["no_submission_authority_by_pb_adapter_0a"]
    model_ranking_posture: Literal["no_model_ranking_claimed_by_pb_adapter_0a"]
    future_family_selection_posture: Literal["no_future_family_selected_by_pb_adapter_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_guardrail(self) -> "ProgrambenchAdapterNonAuthorityGuardrail":
        for field_name in (
            "task_intake_refs",
            "task_artifact_manifest_refs",
            "visibility_manifest_refs",
            "worker_access_contract_refs",
            "forbidden_future_artifact_kinds",
        ):
            _ensure_non_empty_unique(getattr(self, field_name), field_name=field_name)
        missing = PB_ADAPTER_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS - set(
            self.forbidden_future_artifact_kinds
        )
        if missing:
            raise ValueError(
                f"guardrail missing future slice artifact forbiddance: {sorted(missing)}"
            )
        forbidden_current = set(self.forbidden_future_artifact_kinds) & (
            PB_ADAPTER_0A_ARTIFACT_KINDS
        )
        if forbidden_current:
            raise ValueError(
                "guardrail must not forbid current slice artifact kinds: "
                f"{sorted(forbidden_current)}"
            )
        return self


def validate_pb_adapter_0a_task_intake_bundle(
    *,
    task_intake: ProgrambenchCleanroomTaskIntake,
    artifact_manifest: ProgrambenchTaskArtifactManifest,
    visibility_manifest: ProgrambenchTaskVisibilityManifest,
    worker_access_contract: ProgrambenchAdapterWorkerAccessContract,
    guardrail: ProgrambenchAdapterNonAuthorityGuardrail,
) -> None:
    lineage = {
        task_intake.adapter_candidate_ref,
        artifact_manifest.adapter_candidate_ref,
        visibility_manifest.adapter_candidate_ref,
        worker_access_contract.adapter_candidate_ref,
    }
    if len(lineage) != 1:
        raise ValueError("adapter_candidate_ref lineage must match across PB-ADAPTER-0-A rows")
    task_instances = {
        task_intake.task_instance_ref,
        artifact_manifest.task_instance_ref,
        visibility_manifest.task_instance_ref,
        worker_access_contract.task_instance_ref,
    }
    if len(task_instances) != 1:
        raise ValueError("task_instance_ref lineage must match across PB-ADAPTER-0-A rows")
    if task_intake.task_artifact_manifest_ref != artifact_manifest.task_artifact_manifest_ref:
        raise ValueError("task intake must reference the task artifact manifest")
    if artifact_manifest.task_intake_ref != task_intake.task_intake_ref:
        raise ValueError("artifact manifest must reference the task intake")
    if visibility_manifest.task_intake_ref != task_intake.task_intake_ref:
        raise ValueError("visibility manifest must reference the task intake")
    if visibility_manifest.task_artifact_manifest_ref != (
        artifact_manifest.task_artifact_manifest_ref
    ):
        raise ValueError("visibility manifest must reference the artifact manifest")
    if worker_access_contract.task_intake_ref != task_intake.task_intake_ref:
        raise ValueError("worker access contract must reference the task intake")
    if worker_access_contract.task_artifact_manifest_ref != (
        artifact_manifest.task_artifact_manifest_ref
    ):
        raise ValueError("worker access contract must reference the artifact manifest")
    if worker_access_contract.visibility_manifest_ref != (
        visibility_manifest.visibility_manifest_ref
    ):
        raise ValueError("worker access contract must reference the visibility manifest")

    if task_intake.reference_executable_ref != artifact_manifest.reference_executable_ref:
        raise ValueError("artifact manifest must preserve reference executable identity")
    usage_doc_refs = {row.artifact_ref for row in artifact_manifest.usage_docs_hash_rows}
    if set(task_intake.usage_docs_refs) != usage_doc_refs:
        raise ValueError("artifact manifest must hash exactly the task intake usage docs")
    visible_artifact_refs = {
        row.artifact_ref for row in artifact_manifest.visible_input_artifact_hash_rows
    }
    if set(task_intake.visible_input_artifact_refs) != visible_artifact_refs:
        raise ValueError("artifact manifest must hash exactly the visible input artifacts")

    visible_store_refs = {row.store_ref for row in visibility_manifest.visible_store_rows}
    hidden_forbidden_store_refs = {
        row.store_ref
        for row in visibility_manifest.hidden_store_rows + visibility_manifest.forbidden_store_rows
    }
    forbidden_allowed_refs = hidden_forbidden_store_refs & set(
        worker_access_contract.allowed_inference_source_refs
    )
    if forbidden_allowed_refs:
        raise ValueError(
            "worker access contract allows hidden or forbidden inference refs: "
            f"{sorted(forbidden_allowed_refs)}"
        )
    if not set(worker_access_contract.allowed_inference_source_refs) <= visible_store_refs:
        raise ValueError(
            "worker access contract allowed refs must resolve to visible store rows"
        )
    missing_forbidden_refs = set(task_intake.forbidden_inference_source_refs) - set(
        worker_access_contract.forbidden_inference_source_refs
    )
    if missing_forbidden_refs:
        raise ValueError(
            "worker access contract must carry task intake forbidden source refs: "
            f"{sorted(missing_forbidden_refs)}"
        )

    if task_intake.task_intake_ref not in guardrail.task_intake_refs:
        raise ValueError("guardrail must reference the task intake")
    if artifact_manifest.task_artifact_manifest_ref not in guardrail.task_artifact_manifest_refs:
        raise ValueError("guardrail must reference the task artifact manifest")
    if visibility_manifest.visibility_manifest_ref not in guardrail.visibility_manifest_refs:
        raise ValueError("guardrail must reference the visibility manifest")
    if (
        worker_access_contract.worker_access_contract_ref
        not in guardrail.worker_access_contract_refs
    ):
        raise ValueError("guardrail must reference the worker access contract")
