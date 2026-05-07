from __future__ import annotations

from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_PROFILE_SCHEMA = (
    "programbench_cleanroom_reconstruction_profile@1"
)
PROGRAM_ODEU_CONCEPT_BOUNDARY_SEED_SCHEMA = "program_odeu_concept_boundary_seed@1"
PROGRAMBENCH_CLEANROOM_EVIDENCE_SOURCE_INDEX_SCHEMA = (
    "programbench_cleanroom_evidence_source_index@1"
)
PROGRAMBENCH_RECONSTRUCTION_NON_AUTHORITY_GUARDRAIL_SCHEMA = (
    "programbench_reconstruction_non_authority_guardrail@1"
)
PROGRAMBENCH_LOCAL_CLEANROOM_FIXTURE_CONTRACT_SCHEMA = (
    "programbench_local_cleanroom_fixture_contract@1"
)

PROGRAM_ODEU_CONCEPT_ID_VOCABULARY = [
    "program_behavior",
    "command",
    "subcommand",
    "cli_flag",
    "positional_argument",
    "stdin_input",
    "stdout_output",
    "stderr_diagnostic",
    "exit_code",
    "config_file",
    "environment_variable",
    "default_value",
    "precedence_rule",
    "parser_error",
    "runtime_error",
    "generated_output_artifact",
    "filesystem_side_effect",
    "probe_log",
]

CleanroomPhase = Literal[
    "inference_phase",
    "local_development_phase",
    "evaluation_phase",
    "postmortem_phase",
]
CleanroomVisibilityClass = Literal[
    "cleanroom_visible",
    "worker_generated_probe",
    "worker_generated_submission",
    "evaluation_oracle_hidden",
    "forbidden_original_source",
    "forbidden_decompilation",
    "forbidden_internet_lookup",
    "forbidden_external_repo",
    "forbidden_host_secret",
    "forbidden_docker_socket",
    "support_context_only",
    "public_descriptor_context",
    "postmortem_only",
]
SourceKind = Literal[
    "cleanroom_usage_doc",
    "reference_executable_observation",
    "worker_generated_probe",
    "worker_generated_submission",
    "evaluation_oracle_hidden",
    "original_source",
    "decompilation_artifact",
    "internet_lookup",
    "external_repository",
    "host_secret",
    "docker_socket",
    "support_doc",
    "public_programbench_descriptor",
    "postmortem_observation",
]
AuthorityLayer = Literal["lock", "architecture", "planning", "support", "fixture", "oracle"]
PhaseVisibility = Literal[
    "visible_during_inference",
    "visible_during_local_development",
    "visible_during_evaluation_only",
    "visible_during_postmortem_only",
    "never_worker_visible",
]
SourceCurrentness = Literal[
    "current",
    "current_public_observation",
    "support_context_only",
    "historical_context_only",
    "stale",
    "unknown_needs_review",
]
SourcePresencePosture = Literal[
    "present",
    "explicit_absence_marker",
    "not_registered",
    "unknown_needs_review",
]
SourceAccessPosture = Literal[
    "registered_cleanroom_visible",
    "registered_local_development_only",
    "registered_evaluation_oracle_only",
    "registered_postmortem_only",
    "registered_or_mounted_for_worker",
    "queried_by_worker",
    "exposed_to_worker",
    "not_registered_or_mounted",
]
WorkerVisibilityPosture = Literal[
    "worker_visible",
    "not_worker_visible",
    "worker_visible_after_inference_only",
]
InferenceAdmissibilityPosture = Literal[
    "admissible_for_inference",
    "context_only_not_decisive",
    "forbidden_for_inference",
    "postmortem_only_not_inference",
]
PostmortemAdmissibilityPosture = Literal[
    "admissible_for_postmortem_research",
    "not_admissible",
    "not_applicable",
]
BenchmarkTruthPosture = Literal[
    "not_benchmark_truth",
    "public_descriptor_context_only",
    "local_fixture_research_only",
    "official_benchmark_authority_required",
    "no_benchmark_truth_claimed_by_pb_py_0a",
]
ConceptBoundaryPosture = Literal[
    "boundary_seeded_incomplete",
    "boundary_context_only",
    "boundary_requires_later_realization",
    "boundary_not_claimed_for_task",
]
ConceptRole = Literal[
    "program_ontology_seed",
    "io_behavior_seed",
    "cli_behavior_seed",
    "config_behavior_seed",
    "error_behavior_seed",
    "artifact_behavior_seed",
    "probe_behavior_seed",
]

_FORBIDDEN_VISIBILITY_CLASSES = {
    "forbidden_original_source",
    "forbidden_decompilation",
    "forbidden_internet_lookup",
    "forbidden_external_repo",
    "forbidden_host_secret",
    "forbidden_docker_socket",
}
_INFERENCE_FORBIDDEN_VISIBILITY_CLASSES = _FORBIDDEN_VISIBILITY_CLASSES | {
    "evaluation_oracle_hidden",
    "postmortem_only",
}
_WORKER_ACCESS_POSTURES = {
    "registered_or_mounted_for_worker",
    "queried_by_worker",
    "exposed_to_worker",
}
_PROFILE_ALLOWED_INFERENCE_POSTURES = {
    "admissible_for_inference",
    "context_only_not_decisive",
}
_REQUIRED_PHASES = [
    "inference_phase",
    "local_development_phase",
    "evaluation_phase",
    "postmortem_phase",
]
_REQUIRED_FORBIDDEN_DOWNSTREAM_ACTIONS = {
    "concept_realization_record_created",
    "python_reconstruction_plan_created",
    "python_realization_witness_template_created",
    "local_fixture_implemented",
    "comparison_packet_created",
    "probe_equivalence_audit_created",
    "official_programbench_runner_integrated",
    "official_programbench_task_executed",
    "hidden_test_handling",
    "hidden_test_inference",
    "generated_python_code",
    "benchmark_score_created",
    "model_ranking_claimed",
    "v86_selection",
    "v87_selection",
    "v88_selection",
}


def _sorted_unique(values: list[str], *, field_name: str) -> list[str]:
    for value in values:
        if not isinstance(value, str) or not value or value != value.strip():
            raise ValueError(f"{field_name} entries must be non-empty trimmed strings")
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")
    if values != sorted(values):
        raise ValueError(f"{field_name} must be sorted for deterministic review")
    return values


class _CleanroomBase(BaseModel):
    model_config = MODEL_CONFIG


class ProgrambenchPublicDescriptorObservationRow(_CleanroomBase):
    observation_ref: str
    source_url: str
    retrieved_at: str
    descriptor_summary: str
    advisory_posture: Literal["advisory_only"]
    evaluation_truth_posture: Literal["not_used_as_evaluation_truth"]
    benchmark_truth_posture: Literal["public_descriptor_context_only"]
    limitation_note: str


class ProgrambenchCleanroomPhaseRow(_CleanroomBase):
    phase_ref: str
    phase: CleanroomPhase
    allowed_visibility_classes: list[CleanroomVisibilityClass] = Field(min_length=1)
    forbidden_visibility_classes: list[CleanroomVisibilityClass] = Field(min_length=1)
    phase_law: str

    @model_validator(mode="after")
    def _phase_visibility_law(self) -> "ProgrambenchCleanroomPhaseRow":
        overlap = set(self.allowed_visibility_classes) & set(self.forbidden_visibility_classes)
        if overlap:
            raise ValueError(
                f"phase visibility classes cannot be both allowed and forbidden: {sorted(overlap)}"
            )
        if self.phase == "inference_phase":
            forbidden_allowed = _INFERENCE_FORBIDDEN_VISIBILITY_CLASSES & set(
                self.allowed_visibility_classes
            )
            if forbidden_allowed:
                raise ValueError(
                    "inference_phase cannot allow forbidden, evaluation, or postmortem evidence"
                )
        return self


class ProgrambenchCleanroomReconstructionProfile(_CleanroomBase):
    schema_id: Literal[PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_PROFILE_SCHEMA] = Field(
        alias="schema"
    )
    profile_ref: str
    profile_kind: Literal["programbench_cleanroom_reconstruction_profile"]
    program_family_ref: str
    source_index_refs: list[str] = Field(min_length=1)
    concept_boundary_seed_refs: list[str] = Field(min_length=1)
    phase_rows: list[ProgrambenchCleanroomPhaseRow] = Field(min_length=4)
    cleanroom_visibility_posture: Literal["cleanroom_visible_evidence_only_during_inference"]
    public_descriptor_observation_refs: list[str]
    public_descriptor_observation_rows: list[ProgrambenchPublicDescriptorObservationRow]
    allowed_inference_source_refs: list[str]
    forbidden_inference_source_refs: list[str]
    worker_probe_posture: Literal["worker_generated_probes_allowed_local_development_only"]
    local_development_posture: Literal["local_development_without_forbidden_evidence"]
    evaluation_oracle_posture: Literal["hidden_tests_external_court_not_inference_evidence"]
    postmortem_posture: Literal["postmortem_research_not_retroactive_inference"]
    benchmark_truth_posture: BenchmarkTruthPosture
    implementation_authority_posture: Literal["no_implementation_authority_granted_by_pb_py_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_profile(self) -> "ProgrambenchCleanroomReconstructionProfile":
        observed_phases = [row.phase for row in self.phase_rows]
        if sorted(observed_phases) != sorted(_REQUIRED_PHASES):
            raise ValueError("phase_rows must include each PB-PY-0-A phase exactly once")
        if self.benchmark_truth_posture != "not_benchmark_truth":
            raise ValueError("cleanroom reconstruction profile must not claim benchmark truth")
        source_overlap = set(self.allowed_inference_source_refs) & set(
            self.forbidden_inference_source_refs
        )
        if source_overlap:
            raise ValueError(
                "inference source refs cannot be both allowed and forbidden: "
                f"{sorted(source_overlap)}"
            )
        observed_descriptor_refs = {
            row.observation_ref for row in self.public_descriptor_observation_rows
        }
        missing = set(self.public_descriptor_observation_refs) - observed_descriptor_refs
        if missing:
            raise ValueError(f"public descriptor refs missing rows: {sorted(missing)}")
        return self


class ProgramOdeuDistinguishingQuestionRow(_CleanroomBase):
    question_ref: str
    question_text: str
    distinguishes_from_concept_ids: list[str]
    required_witness_kind_refs: list[str]


class ProgramOdeuConceptBoundarySeedRow(_CleanroomBase):
    concept_seed_ref: str
    concept_id: str
    concept_label: str
    concept_boundary_posture: ConceptBoundaryPosture
    concept_role: ConceptRole
    boundary_outline_advisory: str
    positive_example_labels: list[str] = Field(min_length=1)
    negative_example_labels: list[str]
    nearest_confusable_concept_ids: list[str]
    required_witness_kind_refs: list[str] = Field(min_length=1)
    invalid_witness_kind_refs: list[str]
    distinguishing_question_rows: list[ProgramOdeuDistinguishingQuestionRow]
    source_refs: list[str] = Field(min_length=1)
    later_realization_posture: Literal["seed_only_realization_deferred_to_pb_py_0b"]
    implementation_authority_posture: Literal["no_implementation_authority_granted_by_pb_py_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_unique_lists(self) -> "ProgramOdeuConceptBoundarySeedRow":
        if self.concept_id not in PROGRAM_ODEU_CONCEPT_ID_VOCABULARY:
            raise ValueError(f"unsupported concept_id: {self.concept_id}")
        for field_name in (
            "positive_example_labels",
            "negative_example_labels",
            "nearest_confusable_concept_ids",
            "required_witness_kind_refs",
            "invalid_witness_kind_refs",
        ):
            _sorted_unique(getattr(self, field_name), field_name=field_name)
        return self


class ProgramOdeuConceptBoundarySeed(_CleanroomBase):
    schema_id: Literal[PROGRAM_ODEU_CONCEPT_BOUNDARY_SEED_SCHEMA] = Field(alias="schema")
    concept_seed_set_ref: str
    source_refs: list[str] = Field(min_length=1)
    concept_seed_rows: list[ProgramOdeuConceptBoundarySeedRow] = Field(min_length=1)
    later_realization_posture: Literal["seed_set_only_realization_deferred_to_pb_py_0b"]
    implementation_authority_posture: Literal["no_implementation_authority_granted_by_pb_py_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_seed_set(self) -> "ProgramOdeuConceptBoundarySeed":
        observed = [row.concept_id for row in self.concept_seed_rows]
        if observed != PROGRAM_ODEU_CONCEPT_ID_VOCABULARY:
            raise ValueError(
                "concept_seed_rows must include the PB-PY-0-A seed ids in canonical order"
            )
        return self


class ProgrambenchCleanroomEvidenceSourceRow(_CleanroomBase):
    source_ref: str
    source_kind: SourceKind
    authority_layer: AuthorityLayer
    phase_visibility: PhaseVisibility
    cleanroom_visibility_class: CleanroomVisibilityClass
    source_currentness: SourceCurrentness
    source_presence_posture: SourcePresencePosture
    source_access_posture: SourceAccessPosture
    worker_visibility_posture: WorkerVisibilityPosture
    inference_admissibility_posture: InferenceAdmissibilityPosture
    postmortem_admissibility_posture: PostmortemAdmissibilityPosture
    benchmark_truth_posture: BenchmarkTruthPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_visibility_law(self) -> "ProgrambenchCleanroomEvidenceSourceRow":
        if self.cleanroom_visibility_class in _FORBIDDEN_VISIBILITY_CLASSES:
            if self.worker_visibility_posture != "not_worker_visible":
                raise ValueError("forbidden evidence must not be worker-visible")
            if self.inference_admissibility_posture != "forbidden_for_inference":
                raise ValueError("forbidden evidence must be forbidden for inference")
            if self.source_access_posture in _WORKER_ACCESS_POSTURES:
                raise ValueError(
                    "forbidden evidence must not be registered, mounted, queried, or exposed"
                )
        if self.cleanroom_visibility_class == "evaluation_oracle_hidden":
            if self.inference_admissibility_posture != "forbidden_for_inference":
                raise ValueError("hidden evaluation oracle cannot be inference evidence")
            if self.worker_visibility_posture != "not_worker_visible":
                raise ValueError("hidden evaluation oracle must not be worker-visible")
            if self.source_access_posture in _WORKER_ACCESS_POSTURES:
                raise ValueError(
                    "hidden evaluation oracle must not be registered, mounted, queried, or exposed"
                )
        if self.cleanroom_visibility_class == "postmortem_only":
            if self.inference_admissibility_posture != "postmortem_only_not_inference":
                raise ValueError("postmortem-only evidence cannot be inference evidence")
        if self.cleanroom_visibility_class == "public_descriptor_context":
            if self.benchmark_truth_posture != "public_descriptor_context_only":
                raise ValueError("public descriptors must remain advisory context only")
        return self


class ProgrambenchCleanroomEvidenceSourceIndex(_CleanroomBase):
    schema_id: Literal[PROGRAMBENCH_CLEANROOM_EVIDENCE_SOURCE_INDEX_SCHEMA] = Field(
        alias="schema"
    )
    source_index_ref: str
    source_rows: list[ProgrambenchCleanroomEvidenceSourceRow] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_source_index(self) -> "ProgrambenchCleanroomEvidenceSourceIndex":
        refs = [row.source_ref for row in self.source_rows]
        if len(refs) != len(set(refs)):
            raise ValueError("source_rows must not repeat source_ref")
        return self


class ProgrambenchLocalCleanroomFixtureContract(_CleanroomBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CLEANROOM_FIXTURE_CONTRACT_SCHEMA] = Field(
        alias="schema"
    )
    fixture_id: str
    reference_executable_ref: str
    usage_docs_ref: str
    allowed_inference_sources: list[str] = Field(min_length=1)
    forbidden_inference_sources: list[str]
    worker_visible_files: list[str]
    worker_hidden_files: list[str]
    probe_allowed_commands: list[str]
    network_policy: Literal["network_disabled_during_inference"]
    source_visibility_policy: Literal["forbidden_sources_unreachable_during_inference"]
    expected_submission_shape: str
    evaluation_oracle_posture: Literal["local_oracle_contract_only_no_hidden_test_authority"]
    non_benchmark_truth_posture: Literal["local_fixture_contract_not_benchmark_truth"]
    fixture_implementation_posture: Literal[
        "contract_only_no_fixture_implemented_by_pb_py_0a"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_contract(self) -> "ProgrambenchLocalCleanroomFixtureContract":
        overlap = set(self.forbidden_inference_sources) & set(self.allowed_inference_sources)
        if overlap:
            raise ValueError(
                f"forbidden sources cannot be allowed for inference: {sorted(overlap)}"
            )
        hidden_visible = set(self.worker_hidden_files) & set(self.worker_visible_files)
        if hidden_visible:
            raise ValueError(
                f"worker-hidden files cannot be worker-visible: {sorted(hidden_visible)}"
            )
        return self


class ProgrambenchReconstructionNonAuthorityGuardrail(_CleanroomBase):
    schema_id: Literal[PROGRAMBENCH_RECONSTRUCTION_NON_AUTHORITY_GUARDRAIL_SCHEMA] = Field(
        alias="schema"
    )
    guardrail_ref: str
    source_refs: list[str] = Field(min_length=1)
    forbidden_inference_actions: list[str] = Field(min_length=1)
    forbidden_downstream_actions: list[str] = Field(min_length=1)
    required_later_authority_refs: list[str]
    benchmark_truth_posture: Literal["no_benchmark_truth_claimed_by_pb_py_0a"]
    implementation_posture: Literal["no_implementation_performed_by_pb_py_0a"]
    python_realization_posture: Literal["no_python_realization_records_created_by_pb_py_0a"]
    fixture_implementation_posture: Literal["no_fixture_implemented_by_pb_py_0a"]
    official_programbench_posture: Literal["no_official_programbench_participation_by_pb_py_0a"]
    future_family_selection_posture: Literal["no_future_family_selected_by_pb_py_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_guardrail(self) -> "ProgrambenchReconstructionNonAuthorityGuardrail":
        missing = _REQUIRED_FORBIDDEN_DOWNSTREAM_ACTIONS - set(self.forbidden_downstream_actions)
        if missing:
            raise ValueError(f"guardrail missing forbidden downstream actions: {sorted(missing)}")
        if "hidden_test_inference" not in set(self.forbidden_inference_actions):
            raise ValueError("guardrail must forbid hidden-test inference")
        return self


def validate_pb_py_0a_cleanroom_reconstruction_bundle(
    *,
    profile: ProgrambenchCleanroomReconstructionProfile,
    concept_seed: ProgramOdeuConceptBoundarySeed,
    source_index: ProgrambenchCleanroomEvidenceSourceIndex,
    guardrail: ProgrambenchReconstructionNonAuthorityGuardrail,
    fixture_contract: ProgrambenchLocalCleanroomFixtureContract,
) -> None:
    if source_index.source_index_ref not in profile.source_index_refs:
        raise ValueError("profile must reference the released source index")
    if concept_seed.concept_seed_set_ref not in profile.concept_boundary_seed_refs:
        raise ValueError("profile must reference the concept boundary seed set")
    source_rows_by_ref = {row.source_ref: row for row in source_index.source_rows}
    source_refs = set(source_rows_by_ref)
    missing_allowed = set(profile.allowed_inference_source_refs) - source_refs
    if missing_allowed:
        raise ValueError(f"profile allowed inference refs missing source rows: {missing_allowed}")
    for source_ref in profile.allowed_inference_source_refs:
        source_row = source_rows_by_ref[source_ref]
        if (
            source_row.inference_admissibility_posture
            not in _PROFILE_ALLOWED_INFERENCE_POSTURES
        ):
            raise ValueError(
                f"profile allowed inference ref is not inference-admissible: {source_ref}"
            )
    missing_forbidden = set(profile.forbidden_inference_source_refs) - source_refs
    if missing_forbidden:
        raise ValueError(
            f"profile forbidden inference refs missing source rows: {missing_forbidden}"
        )
    if not set(guardrail.source_refs) <= source_refs:
        raise ValueError("guardrail source refs must resolve through the source index")
    if not set(fixture_contract.allowed_inference_sources) <= source_refs:
        raise ValueError(
            "fixture contract allowed source refs must resolve through the source index"
        )
