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
CONCEPT_REALIZATION_RECORD_SCHEMA = "concept_realization_record@1"
PYTHON_RECONSTRUCTION_REALIZATION_PACK_SCHEMA = "python_reconstruction_realization_pack@1"
PYTHON_RECONSTRUCTION_PLAN_SCHEMA = "python_reconstruction_plan@1"
PYTHON_REALIZATION_WITNESS_TEMPLATE_SCHEMA = "python_realization_witness_template@1"
PROGRAMBENCH_LOCAL_CLEANROOM_FIXTURE_SCHEMA = "programbench_local_cleanroom_fixture@1"
PROGRAMBENCH_RECONSTRUCTION_COMPARISON_PACKET_SCHEMA = (
    "programbench_reconstruction_comparison_packet@1"
)
PROGRAMBENCH_PROBE_EQUIVALENCE_AUDIT_SCHEMA = "programbench_probe_equivalence_audit@1"
PROGRAMBENCH_REALIZATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "programbench_realization_family_closeout_alignment@1"
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
PythonTargetLanguage = Literal["python"]
PythonRealizationRole = Literal[
    "cli_argument_parsing",
    "stdin_stdout_stderr_io",
    "file_path_io",
    "config_data_loading",
    "environment_variable_loading",
    "precedence_resolution",
    "exit_code_behavior",
    "deterministic_output_ordering",
    "error_diagnostic_behavior",
    "generated_artifact_behavior",
    "filesystem_side_effect_behavior",
]
PythonStdlibSurface = Literal[
    "argparse",
    "sys_argv",
    "sys_stdin",
    "sys_stdout",
    "sys_stderr",
    "pathlib",
    "open",
    "json",
    "csv",
    "configparser",
    "tomllib",
    "os_environ",
    "glob",
    "text_binary_mode",
    "subprocess_for_probe_only",
]
PythonProbeKind = Literal[
    "help_probe",
    "missing_value_probe",
    "invalid_flag_probe",
    "repeated_flag_probe",
    "stdin_stdout_probe",
    "stderr_diagnostic_probe",
    "exit_code_probe",
    "missing_file_probe",
    "malformed_config_probe",
    "deterministic_sorting_probe",
    "generated_file_probe",
    "directory_side_effect_probe",
]
ExpectedObservationKind = Literal[
    "help_text",
    "stdout_text",
    "stderr_text",
    "exit_code",
    "stdout_stderr_split",
    "filesystem_observation",
    "deterministic_order",
    "parse_error",
    "runtime_error",
]
FixtureOriginPosture = Literal[
    "synthetic_local_fixture",
    "repo_internal_fixture",
    "toy_cleanroom_fixture",
    "official_programbench_task_forbidden_in_pb_py_0c",
]
ComparisonLaneId = Literal[
    "base_adeu_harness",
    "adeu_plus_conceptual_profile",
    "adeu_plus_conceptual_profile_plus_python_overlay",
]
ComparisonContaminationStatus = Literal[
    "same_condition_controls_closed",
    "contaminated_conditions_detected",
    "non_comparable_conditions",
]
ComparisonLaneDeltaPosture = Literal[
    "base_no_conceptual_profile_no_python_overlay",
    "conceptual_profile_only",
    "conceptual_profile_plus_python_overlay",
]
FullPointerLocalProbeStatus = Literal["local_probe_passed", "local_probe_failed"]

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
_PYTHON_STDLIB_SURFACE_VOCABULARY = [
    "argparse",
    "sys_argv",
    "sys_stdin",
    "sys_stdout",
    "sys_stderr",
    "pathlib",
    "open",
    "json",
    "csv",
    "configparser",
    "tomllib",
    "os_environ",
    "glob",
    "text_binary_mode",
    "subprocess_for_probe_only",
]
_PB_PY_0C_LANE_IDS = [
    "base_adeu_harness",
    "adeu_plus_conceptual_profile",
    "adeu_plus_conceptual_profile_plus_python_overlay",
]
_PB_PY_0_CLOSED_SLICE_REFS = [
    "PB-PY-0-A",
    "PB-PY-0-B",
    "PB-PY-0-C",
]
_CODE_OR_COMMAND_MARKERS = (
    "\n",
    "def ",
    "class ",
    "import ",
    "subprocess.",
    "os.system",
    "pytest ",
    "make ",
    "python ",
    "bash ",
    " && ",
    "$ ",
)
_INTERNET_OR_EXTERNAL_SOURCE_MARKERS = (
    "curl ",
    "wget ",
    "git clone",
    "pip install",
    "http://",
    "https://",
    "internet lookup",
    "external repo",
)
_EXECUTABLE_PATH_RE = re.compile(
    r"(^|\s)(/[^ \t\n]+|\./|[a-z]:\\|[a-z0-9_.-]+\.py\b|packages/|apps/)"
)
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


def _ensure_no_code_command_or_path_payload(value: object, *, field_name: str) -> None:
    if isinstance(value, dict):
        for nested_field, nested_value in value.items():
            _ensure_no_code_command_or_path_payload(
                nested_value,
                field_name=f"{field_name}.{nested_field}",
            )
        return
    if isinstance(value, list):
        for index, item in enumerate(value):
            _ensure_no_code_command_or_path_payload(
                item,
                field_name=f"{field_name}[{index}]",
            )
        return
    if not isinstance(value, str):
        return

    lowered = value.lower()
    if any(marker in lowered for marker in _CODE_OR_COMMAND_MARKERS):
        raise ValueError(f"{field_name} must not contain source code or command payloads")
    if _EXECUTABLE_PATH_RE.search(lowered):
        raise ValueError(f"{field_name} must not contain executable file paths")


def _ensure_no_internet_or_external_lookup(value: str, *, field_name: str) -> None:
    lowered = value.lower()
    if any(marker in lowered for marker in _INTERNET_OR_EXTERNAL_SOURCE_MARKERS):
        raise ValueError(f"{field_name} must not authorize internet or external source lookup")


def _ensure_source_refs_resolve(
    source_refs: list[str],
    *,
    row_ref: str,
    source_refs_by_ref: set[str],
) -> None:
    missing = set(source_refs) - source_refs_by_ref
    if missing:
        raise ValueError(f"{row_ref} source refs missing source rows: {sorted(missing)}")


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
    schema_id: Literal[PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_PROFILE_SCHEMA] = Field(alias="schema")
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
    schema_id: Literal[PROGRAMBENCH_CLEANROOM_EVIDENCE_SOURCE_INDEX_SCHEMA] = Field(alias="schema")
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
    schema_id: Literal[PROGRAMBENCH_LOCAL_CLEANROOM_FIXTURE_CONTRACT_SCHEMA] = Field(alias="schema")
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
    fixture_implementation_posture: Literal["contract_only_no_fixture_implemented_by_pb_py_0a"]
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


class ConceptRealizationRecord(_CleanroomBase):
    schema_id: Literal[CONCEPT_REALIZATION_RECORD_SCHEMA] = Field(alias="schema")
    realization_ref: str
    concept_seed_ref: str
    concept_id: str
    target_language: PythonTargetLanguage
    realization_role: PythonRealizationRole
    canonical_instruction: str
    preferred_stdlib_surfaces: list[PythonStdlibSurface] = Field(min_length=1)
    implementation_patterns: list[str] = Field(min_length=1)
    contraindicated_patterns: list[str]
    boundary_conditions: list[str]
    failure_modes: list[str]
    required_witness_refs: list[str] = Field(min_length=1)
    probe_template_refs: list[str] = Field(min_length=1)
    example_snippets_advisory: list[str]
    example_snippet_posture: Literal["advisory_only_not_generated_implementation"]
    concept_definition_posture: Literal["realization_option_not_concept_definition"]
    implementation_authority_posture: Literal["no_implementation_authority_granted_by_pb_py_0b"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_realization_record(self) -> "ConceptRealizationRecord":
        if self.concept_id not in PROGRAM_ODEU_CONCEPT_ID_VOCABULARY:
            raise ValueError(f"unsupported concept_id: {self.concept_id}")
        if self.concept_seed_ref != f"concept-seed:{self.concept_id}":
            raise ValueError("concept_seed_ref must match the realized concept_id")
        for field_name in (
            "preferred_stdlib_surfaces",
            "implementation_patterns",
            "contraindicated_patterns",
            "boundary_conditions",
            "failure_modes",
            "required_witness_refs",
            "probe_template_refs",
            "example_snippets_advisory",
        ):
            _sorted_unique(getattr(self, field_name), field_name=field_name)
        return self


class PythonStdlibSurfaceRow(_CleanroomBase):
    surface_ref: str
    stdlib_surface: PythonStdlibSurface
    realization_role_refs: list[PythonRealizationRole] = Field(min_length=1)
    source_refs: list[str] = Field(min_length=1)
    surface_use_posture: Literal[
        "realization_option_only",
        "probe_surface_only_no_execution_authority",
    ]
    implementation_authority_posture: Literal["no_execution_or_implementation_authority"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_stdlib_surface(self) -> "PythonStdlibSurfaceRow":
        _sorted_unique(self.realization_role_refs, field_name="realization_role_refs")
        _sorted_unique(self.source_refs, field_name="source_refs")
        if (
            self.stdlib_surface == "subprocess_for_probe_only"
            and self.surface_use_posture != "probe_surface_only_no_execution_authority"
        ):
            raise ValueError("subprocess_for_probe_only may appear only as probe-only")
        return self


class PythonBoundaryConditionRow(_CleanroomBase):
    boundary_condition_ref: str
    concept_id: str
    boundary_condition: str
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_boundary_condition(self) -> "PythonBoundaryConditionRow":
        if self.concept_id not in PROGRAM_ODEU_CONCEPT_ID_VOCABULARY:
            raise ValueError(f"unsupported concept_id: {self.concept_id}")
        _sorted_unique(self.source_refs, field_name="source_refs")
        return self


class PythonFailureModeRow(_CleanroomBase):
    failure_mode_ref: str
    concept_id: str
    failure_mode: str
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_failure_mode(self) -> "PythonFailureModeRow":
        if self.concept_id not in PROGRAM_ODEU_CONCEPT_ID_VOCABULARY:
            raise ValueError(f"unsupported concept_id: {self.concept_id}")
        _sorted_unique(self.source_refs, field_name="source_refs")
        return self


class PythonContraindicatedPatternRow(_CleanroomBase):
    contraindicated_pattern_ref: str
    concept_id: str
    pattern_label: str
    contraindication_reason: str
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_contraindicated_pattern(self) -> "PythonContraindicatedPatternRow":
        if self.concept_id not in PROGRAM_ODEU_CONCEPT_ID_VOCABULARY:
            raise ValueError(f"unsupported concept_id: {self.concept_id}")
        _sorted_unique(self.source_refs, field_name="source_refs")
        return self


class PythonReconstructionRealizationPack(_CleanroomBase):
    schema_id: Literal[PYTHON_RECONSTRUCTION_REALIZATION_PACK_SCHEMA] = Field(alias="schema")
    pack_ref: str
    target_language: PythonTargetLanguage
    source_profile_refs: list[str] = Field(min_length=1)
    concept_seed_refs: list[str] = Field(min_length=1)
    source_index_refs: list[str] = Field(min_length=1)
    guardrail_refs: list[str] = Field(min_length=1)
    fixture_contract_refs: list[str] = Field(min_length=1)
    realization_record_refs: list[str] = Field(min_length=1)
    stdlib_surface_rows: list[PythonStdlibSurfaceRow] = Field(min_length=1)
    boundary_condition_rows: list[PythonBoundaryConditionRow]
    failure_mode_rows: list[PythonFailureModeRow]
    witness_template_refs: list[str] = Field(min_length=1)
    contraindicated_pattern_rows: list[PythonContraindicatedPatternRow]
    pack_scope_posture: Literal["python_stdlib_realization_overlay_only"]
    fixture_authority_posture: Literal["no_fixture_implemented_by_pb_py_0b"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    implementation_authority_posture: Literal["no_implementation_authority_granted_by_pb_py_0b"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_realization_pack(self) -> "PythonReconstructionRealizationPack":
        for field_name in (
            "source_profile_refs",
            "concept_seed_refs",
            "source_index_refs",
            "guardrail_refs",
            "fixture_contract_refs",
            "realization_record_refs",
            "witness_template_refs",
        ):
            _sorted_unique(getattr(self, field_name), field_name=field_name)
        surface_refs = [row.surface_ref for row in self.stdlib_surface_rows]
        if len(surface_refs) != len(set(surface_refs)):
            raise ValueError("stdlib_surface_rows must not repeat surface_ref")
        observed_surfaces = [row.stdlib_surface for row in self.stdlib_surface_rows]
        if observed_surfaces != _PYTHON_STDLIB_SURFACE_VOCABULARY:
            raise ValueError("stdlib_surface_rows must include Python surfaces in canonical order")
        for rows, ref_field in (
            (self.boundary_condition_rows, "boundary_condition_ref"),
            (self.failure_mode_rows, "failure_mode_ref"),
            (self.contraindicated_pattern_rows, "contraindicated_pattern_ref"),
        ):
            refs = [getattr(row, ref_field) for row in rows]
            if len(refs) != len(set(refs)):
                raise ValueError(f"{ref_field} rows must not repeat refs")
        return self


class PythonPlannedObligationRow(_CleanroomBase):
    planned_obligation_ref: str
    concept_id: str
    concept_realization_refs: list[str] = Field(min_length=1)
    obligation_statement: str
    obligation_scope_posture: Literal["planned_obligation_only_not_implementation"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_planned_obligation(self) -> "PythonPlannedObligationRow":
        if self.concept_id not in PROGRAM_ODEU_CONCEPT_ID_VOCABULARY:
            raise ValueError(f"unsupported concept_id: {self.concept_id}")
        _sorted_unique(self.concept_realization_refs, field_name="concept_realization_refs")
        _ensure_no_code_command_or_path_payload(
            self.obligation_statement,
            field_name="obligation_statement",
        )
        return self


class PythonReconstructionPlan(_CleanroomBase):
    schema_id: Literal[PYTHON_RECONSTRUCTION_PLAN_SCHEMA] = Field(alias="schema")
    plan_ref: str
    source_profile_refs: list[str] = Field(min_length=1)
    realization_pack_refs: list[str] = Field(min_length=1)
    concept_realization_refs: list[str] = Field(min_length=1)
    planned_obligation_rows: list[PythonPlannedObligationRow] = Field(min_length=1)
    planned_witness_refs: list[str] = Field(min_length=1)
    plan_scope_posture: Literal["review_plan_only_not_implementation_packet"]
    code_generation_posture: Literal["no_code_generated_by_pb_py_0b"]
    execution_authority_posture: Literal["no_execution_authority_granted_by_pb_py_0b"]
    fixture_authority_posture: Literal["no_fixture_implemented_by_pb_py_0b"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_reconstruction_plan(self) -> "PythonReconstructionPlan":
        for field_name in (
            "source_profile_refs",
            "realization_pack_refs",
            "concept_realization_refs",
            "planned_witness_refs",
        ):
            _sorted_unique(getattr(self, field_name), field_name=field_name)
        obligation_refs = [row.planned_obligation_ref for row in self.planned_obligation_rows]
        if len(obligation_refs) != len(set(obligation_refs)):
            raise ValueError("planned_obligation_rows must not repeat refs")
        _ensure_no_code_command_or_path_payload(
            [row.obligation_statement for row in self.planned_obligation_rows],
            field_name="planned_obligation_rows.obligation_statement",
        )
        _ensure_no_code_command_or_path_payload(
            self.planned_witness_refs,
            field_name="planned_witness_refs",
        )
        return self


class PythonRealizationWitnessTemplate(_CleanroomBase):
    schema_id: Literal[PYTHON_REALIZATION_WITNESS_TEMPLATE_SCHEMA] = Field(alias="schema")
    witness_template_ref: str
    concept_id: str
    target_language: PythonTargetLanguage
    realization_refs: list[str] = Field(min_length=1)
    probe_kind: PythonProbeKind
    probe_command_shape: str
    expected_observation_kind: ExpectedObservationKind
    positive_witness_requirement: str
    negative_witness_requirement: str
    stdout_stderr_split_required: bool
    exit_code_required: bool
    filesystem_observation_required: bool
    hidden_test_equivalence_posture: Literal["local_probe_not_hidden_test_equivalence"]
    execution_authority_posture: Literal["probe_template_only_no_execution_by_pb_py_0b"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_witness_template(self) -> "PythonRealizationWitnessTemplate":
        if self.concept_id not in PROGRAM_ODEU_CONCEPT_ID_VOCABULARY:
            raise ValueError(f"unsupported concept_id: {self.concept_id}")
        _sorted_unique(self.realization_refs, field_name="realization_refs")
        _ensure_no_code_command_or_path_payload(
            self.probe_command_shape,
            field_name="probe_command_shape",
        )
        return self


class ProgrambenchAllowedProbeCommandRow(_CleanroomBase):
    probe_command_ref: str
    command_shape: str
    command_authority_posture: Literal["local_probe_shape_only_no_execution_authority"]
    network_policy: Literal["network_disabled_during_inference"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_probe_command(self) -> "ProgrambenchAllowedProbeCommandRow":
        _ensure_no_internet_or_external_lookup(self.command_shape, field_name="command_shape")
        return self


class ProgrambenchForbiddenSourceRow(_CleanroomBase):
    source_ref: str
    source_kind: SourceKind
    cleanroom_visibility_class: CleanroomVisibilityClass
    source_access_posture: SourceAccessPosture
    worker_visibility_posture: WorkerVisibilityPosture
    inference_admissibility_posture: InferenceAdmissibilityPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_forbidden_source(self) -> "ProgrambenchForbiddenSourceRow":
        if self.cleanroom_visibility_class not in _INFERENCE_FORBIDDEN_VISIBILITY_CLASSES:
            raise ValueError("forbidden_source_rows must use forbidden or hidden source classes")
        if self.worker_visibility_posture != "not_worker_visible":
            raise ValueError("forbidden source rows must not be worker-visible")
        if self.inference_admissibility_posture not in {
            "forbidden_for_inference",
            "postmortem_only_not_inference",
        }:
            raise ValueError("forbidden source rows must not be inference-admissible")
        if self.source_access_posture in _WORKER_ACCESS_POSTURES:
            raise ValueError("forbidden source rows must not be mounted, queried, or exposed")
        return self


class ProgrambenchEvaluationOracleRow(_CleanroomBase):
    oracle_ref: str
    oracle_visibility_posture: Literal["local_oracle_hidden_from_worker"]
    evaluation_oracle_posture: Literal["local_oracle_only_not_hidden_test_authority"]
    benchmark_truth_posture: Literal["local_fixture_research_only_not_benchmark_truth"]
    worker_visibility_posture: Literal["not_worker_visible"]
    limitation_note: str


class ProgrambenchLocalCleanroomFixture(_CleanroomBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CLEANROOM_FIXTURE_SCHEMA] = Field(alias="schema")
    fixture_ref: str
    fixture_contract_ref: str
    reference_executable_ref: str
    usage_docs_ref: str
    worker_visible_file_refs: list[str] = Field(min_length=1)
    worker_hidden_file_refs: list[str] = Field(min_length=1)
    allowed_probe_command_rows: list[ProgrambenchAllowedProbeCommandRow] = Field(min_length=1)
    forbidden_source_rows: list[ProgrambenchForbiddenSourceRow] = Field(min_length=1)
    fixture_origin_posture: FixtureOriginPosture
    network_policy: Literal["network_disabled_during_inference"]
    source_visibility_policy: Literal["forbidden_sources_unreachable_during_inference"]
    expected_submission_shape: str
    evaluation_oracle_rows: list[ProgrambenchEvaluationOracleRow] = Field(min_length=1)
    local_fixture_scope_posture: Literal["one_local_cleanroom_fixture_only"]
    official_programbench_posture: Literal[
        "no_official_programbench_participation_by_pb_py_0c"
    ]
    benchmark_truth_posture: Literal["local_fixture_research_only_not_benchmark_truth"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_local_fixture(self) -> "ProgrambenchLocalCleanroomFixture":
        if self.fixture_origin_posture == "official_programbench_task_forbidden_in_pb_py_0c":
            raise ValueError("official ProgramBench tasks cannot be used as local fixtures")
        hidden_visible = set(self.worker_hidden_file_refs) & set(self.worker_visible_file_refs)
        if hidden_visible:
            raise ValueError(
                f"worker-hidden files cannot be worker-visible: {sorted(hidden_visible)}"
            )
        command_refs = [row.probe_command_ref for row in self.allowed_probe_command_rows]
        if len(command_refs) != len(set(command_refs)):
            raise ValueError("allowed_probe_command_rows must not repeat probe_command_ref")
        forbidden_refs = [row.source_ref for row in self.forbidden_source_rows]
        if len(forbidden_refs) != len(set(forbidden_refs)):
            raise ValueError("forbidden_source_rows must not repeat source_ref")
        oracle_refs = [row.oracle_ref for row in self.evaluation_oracle_rows]
        if len(oracle_refs) != len(set(oracle_refs)):
            raise ValueError("evaluation_oracle_rows must not repeat oracle_ref")
        for field_name in (
            "reference_executable_ref",
            "usage_docs_ref",
            "expected_submission_shape",
        ):
            _ensure_no_internet_or_external_lookup(getattr(self, field_name), field_name=field_name)
        return self


class ProgrambenchComparisonControlRow(_CleanroomBase):
    control_ref: str
    shared_fixture_ref: str
    shared_model_or_worker_profile_ref: str
    shared_budget_policy: str
    shared_allowed_tool_policy: str
    shared_cleanroom_policy: str
    shared_probe_budget: str
    shared_submission_shape: str
    shared_evaluation_oracle_rows: list[str] = Field(min_length=1)
    lane_difference_declaration: Literal[
        "only_profile_and_python_overlay_substrate_varies_across_lanes"
    ]


class ProgrambenchComparisonLaneRow(_CleanroomBase):
    lane_ref: str
    lane_id: ComparisonLaneId
    fixture_ref: str
    model_or_worker_profile_ref: str
    budget_policy: str
    allowed_tool_policy: str
    cleanroom_policy: str
    probe_budget: str
    submission_shape: str
    evaluation_oracle_refs: list[str] = Field(min_length=1)
    profile_refs: list[str]
    realization_pack_refs: list[str]
    lane_delta_posture: ComparisonLaneDeltaPosture
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    model_ranking_posture: Literal["no_model_ranking_claimed_by_pb_py_0c"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_lane_delta(self) -> "ProgrambenchComparisonLaneRow":
        if self.lane_id == "base_adeu_harness":
            if self.profile_refs or self.realization_pack_refs:
                raise ValueError("base lane must not consume profile or Python overlay refs")
            if self.lane_delta_posture != "base_no_conceptual_profile_no_python_overlay":
                raise ValueError("base lane delta posture mismatch")
        if self.lane_id == "adeu_plus_conceptual_profile":
            if not self.profile_refs or self.realization_pack_refs:
                raise ValueError("conceptual profile lane must consume profile refs only")
            if self.lane_delta_posture != "conceptual_profile_only":
                raise ValueError("conceptual profile lane delta posture mismatch")
        if self.lane_id == "adeu_plus_conceptual_profile_plus_python_overlay":
            if not self.profile_refs or not self.realization_pack_refs:
                raise ValueError("overlay lane must consume profile and realization pack refs")
            if self.lane_delta_posture != "conceptual_profile_plus_python_overlay":
                raise ValueError("overlay lane delta posture mismatch")
        return self


class ProgrambenchReconstructionComparisonPacket(_CleanroomBase):
    schema_id: Literal[PROGRAMBENCH_RECONSTRUCTION_COMPARISON_PACKET_SCHEMA] = Field(
        alias="schema"
    )
    comparison_packet_ref: str
    fixture_ref: str
    comparison_control_rows: list[ProgrambenchComparisonControlRow] = Field(min_length=1)
    comparison_lane_rows: list[ProgrambenchComparisonLaneRow] = Field(min_length=3)
    profile_refs: list[str]
    realization_pack_refs: list[str]
    witness_template_refs: list[str]
    local_probe_refs: list[str] = Field(min_length=1)
    comparison_scope_posture: Literal["local_fixture_research_comparison_only"]
    comparison_contamination_status: ComparisonContaminationStatus
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    model_ranking_posture: Literal["no_model_ranking_claimed_by_pb_py_0c"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_comparison_packet(self) -> "ProgrambenchReconstructionComparisonPacket":
        lane_ids = [row.lane_id for row in self.comparison_lane_rows]
        if lane_ids != _PB_PY_0C_LANE_IDS:
            raise ValueError("comparison_lane_rows must use the PB-PY-0-C lane ids in order")
        control_refs = [row.control_ref for row in self.comparison_control_rows]
        if len(control_refs) != len(set(control_refs)):
            raise ValueError("comparison_control_rows must not repeat control_ref")
        if len(self.comparison_control_rows) != 1:
            raise ValueError("PB-PY-0-C comparison packet must use one shared control row")
        control = self.comparison_control_rows[0]
        contaminated_fields: list[str] = []
        for lane in self.comparison_lane_rows:
            if lane.fixture_ref != control.shared_fixture_ref:
                contaminated_fields.append("fixture")
            if lane.model_or_worker_profile_ref != control.shared_model_or_worker_profile_ref:
                contaminated_fields.append("model_or_worker_profile")
            if lane.budget_policy != control.shared_budget_policy:
                contaminated_fields.append("budget")
            if lane.allowed_tool_policy != control.shared_allowed_tool_policy:
                contaminated_fields.append("allowed_tool")
            if lane.cleanroom_policy != control.shared_cleanroom_policy:
                contaminated_fields.append("cleanroom_policy")
            if lane.probe_budget != control.shared_probe_budget:
                contaminated_fields.append("probe_budget")
            if lane.submission_shape != control.shared_submission_shape:
                contaminated_fields.append("submission_shape")
            if lane.evaluation_oracle_refs != control.shared_evaluation_oracle_rows:
                contaminated_fields.append("evaluation_oracle")
        if contaminated_fields and self.comparison_contamination_status == (
            "same_condition_controls_closed"
        ):
            raise ValueError(
                "contaminated comparison conditions cannot be marked same-condition clean: "
                f"{sorted(set(contaminated_fields))}"
            )
        if not contaminated_fields and self.comparison_contamination_status != (
            "same_condition_controls_closed"
        ):
            raise ValueError("same-condition controls are closed but comparison is marked dirty")
        return self


class ProgrambenchLocalProbeRow(_CleanroomBase):
    local_probe_ref: str
    fixture_ref: str
    probe_kind: PythonProbeKind
    local_probe_status: FullPointerLocalProbeStatus
    local_probe_scope_posture: Literal["local_probe_only_not_hidden_test_equivalence"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    limitation_note: str


class ProgrambenchProbeObservationRow(_CleanroomBase):
    observation_ref: str
    local_probe_ref: str
    observed_value: str
    observation_posture: Literal["local_observation_only_not_benchmark_truth"]
    limitation_note: str


class ProgrambenchProbeEquivalenceAudit(_CleanroomBase):
    schema_id: Literal[PROGRAMBENCH_PROBE_EQUIVALENCE_AUDIT_SCHEMA] = Field(alias="schema")
    audit_ref: str
    fixture_ref: str
    comparison_packet_ref: str
    local_probe_rows: list[ProgrambenchLocalProbeRow] = Field(min_length=1)
    positive_observation_rows: list[ProgrambenchProbeObservationRow]
    negative_observation_rows: list[ProgrambenchProbeObservationRow]
    stdout_stderr_observation_rows: list[ProgrambenchProbeObservationRow]
    exit_code_observation_rows: list[ProgrambenchProbeObservationRow]
    filesystem_observation_rows: list[ProgrambenchProbeObservationRow]
    known_limitation_rows: list[str]
    hidden_test_equivalence_posture: Literal["local_probe_pass_not_hidden_test_equivalence"]
    benchmark_truth_posture: Literal["local_audit_not_benchmark_truth"]
    postmortem_feedback_posture: Literal["no_hidden_test_feedback_used_for_inference"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_probe_audit(self) -> "ProgrambenchProbeEquivalenceAudit":
        probe_refs = [row.local_probe_ref for row in self.local_probe_rows]
        if len(probe_refs) != len(set(probe_refs)):
            raise ValueError("local_probe_rows must not repeat local_probe_ref")
        if any(row.fixture_ref != self.fixture_ref for row in self.local_probe_rows):
            raise ValueError("local probe rows must reference the audit fixture")
        probe_ref_set = set(probe_refs)
        for rows, field_name in (
            (self.positive_observation_rows, "positive_observation_rows"),
            (self.negative_observation_rows, "negative_observation_rows"),
            (self.stdout_stderr_observation_rows, "stdout_stderr_observation_rows"),
            (self.exit_code_observation_rows, "exit_code_observation_rows"),
            (self.filesystem_observation_rows, "filesystem_observation_rows"),
        ):
            refs = [row.observation_ref for row in rows]
            if len(refs) != len(set(refs)):
                raise ValueError(f"{field_name} must not repeat observation_ref")
            missing = {row.local_probe_ref for row in rows} - probe_ref_set
            if missing:
                raise ValueError(f"{field_name} references missing local probes: {sorted(missing)}")
        return self


class ProgrambenchRealizationFamilyCloseoutAlignment(_CleanroomBase):
    schema_id: Literal[PROGRAMBENCH_REALIZATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA] = Field(
        alias="schema"
    )
    family_closeout_ref: str
    family: Literal["PB-PY-0"]
    closed_slice_refs: list[str] = Field(min_length=3)
    released_profile_refs: list[str] = Field(min_length=1)
    released_source_index_refs: list[str] = Field(min_length=1)
    released_concept_seed_refs: list[str] = Field(min_length=1)
    released_fixture_contract_refs: list[str] = Field(min_length=1)
    released_realization_pack_refs: list[str] = Field(min_length=1)
    released_fixture_refs: list[str] = Field(min_length=1)
    released_comparison_packet_refs: list[str] = Field(min_length=1)
    released_audit_refs: list[str] = Field(min_length=1)
    family_alignment_posture: Literal["pb_py_0_closed_local_research_fixture_only"]
    official_programbench_posture: Literal["no_official_programbench_participation_by_pb_py_0"]
    benchmark_truth_posture: Literal["no_benchmark_truth_claimed_by_pb_py_0"]
    future_family_selection_status: Literal["no_future_family_selected_by_pb_py_0"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_family_closeout(self) -> "ProgrambenchRealizationFamilyCloseoutAlignment":
        if self.closed_slice_refs != _PB_PY_0_CLOSED_SLICE_REFS:
            raise ValueError("closed_slice_refs must close PB-PY-0-A/B/C in order")
        for field_name in (
            "released_profile_refs",
            "released_source_index_refs",
            "released_concept_seed_refs",
            "released_fixture_contract_refs",
            "released_realization_pack_refs",
            "released_fixture_refs",
            "released_comparison_packet_refs",
            "released_audit_refs",
        ):
            _sorted_unique(getattr(self, field_name), field_name=field_name)
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
        if source_row.inference_admissibility_posture not in _PROFILE_ALLOWED_INFERENCE_POSTURES:
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


def validate_pb_py_0b_python_realization_bundle(
    *,
    profile: ProgrambenchCleanroomReconstructionProfile,
    concept_seed: ProgramOdeuConceptBoundarySeed,
    source_index: ProgrambenchCleanroomEvidenceSourceIndex,
    guardrail: ProgrambenchReconstructionNonAuthorityGuardrail,
    fixture_contract: ProgrambenchLocalCleanroomFixtureContract,
    realization_records: list[ConceptRealizationRecord],
    realization_pack: PythonReconstructionRealizationPack,
    reconstruction_plan: PythonReconstructionPlan,
    witness_templates: list[PythonRealizationWitnessTemplate],
) -> None:
    validate_pb_py_0a_cleanroom_reconstruction_bundle(
        profile=profile,
        concept_seed=concept_seed,
        source_index=source_index,
        guardrail=guardrail,
        fixture_contract=fixture_contract,
    )
    seed_rows_by_ref = {row.concept_seed_ref: row for row in concept_seed.concept_seed_rows}
    realization_records_by_ref = {row.realization_ref: row for row in realization_records}
    if len(realization_records_by_ref) != len(realization_records):
        raise ValueError("realization_records must not repeat realization_ref")
    witness_templates_by_ref = {row.witness_template_ref: row for row in witness_templates}
    if len(witness_templates_by_ref) != len(witness_templates):
        raise ValueError("witness_templates must not repeat witness_template_ref")
    source_refs_by_ref = {row.source_ref for row in source_index.source_rows}

    for record in realization_records:
        seed_row = seed_rows_by_ref.get(record.concept_seed_ref)
        if seed_row is None:
            raise ValueError(f"realization record missing concept seed: {record.realization_ref}")
        if seed_row.concept_id != record.concept_id:
            raise ValueError("realization record concept_id must match concept seed row")
        missing_probe_templates = set(record.probe_template_refs) - set(witness_templates_by_ref)
        if missing_probe_templates:
            raise ValueError(
                f"realization record probe templates missing: {sorted(missing_probe_templates)}"
            )
        missing_witness_templates = set(record.required_witness_refs) - set(
            witness_templates_by_ref
        )
        if missing_witness_templates:
            raise ValueError(
                "realization record required witnesses missing: "
                f"{sorted(missing_witness_templates)}"
            )

    if profile.profile_ref not in realization_pack.source_profile_refs:
        raise ValueError("realization pack must reference the released profile")
    if concept_seed.concept_seed_set_ref not in realization_pack.concept_seed_refs:
        raise ValueError("realization pack must reference the released concept seed")
    if source_index.source_index_ref not in realization_pack.source_index_refs:
        raise ValueError("realization pack must reference the released source index")
    if guardrail.guardrail_ref not in realization_pack.guardrail_refs:
        raise ValueError("realization pack must reference the released guardrail")
    if fixture_contract.fixture_id not in realization_pack.fixture_contract_refs:
        raise ValueError("realization pack must reference the released fixture contract")
    missing_records = set(realization_pack.realization_record_refs) - set(
        realization_records_by_ref
    )
    if missing_records:
        raise ValueError(f"realization pack refs missing records: {sorted(missing_records)}")
    missing_witnesses = set(realization_pack.witness_template_refs) - set(witness_templates_by_ref)
    if missing_witnesses:
        raise ValueError(
            f"realization pack witness refs missing templates: {sorted(missing_witnesses)}"
        )
    for row in realization_pack.stdlib_surface_rows:
        _ensure_source_refs_resolve(
            row.source_refs,
            row_ref=row.surface_ref,
            source_refs_by_ref=source_refs_by_ref,
        )
    for row in realization_pack.boundary_condition_rows:
        _ensure_source_refs_resolve(
            row.source_refs,
            row_ref=row.boundary_condition_ref,
            source_refs_by_ref=source_refs_by_ref,
        )
    for row in realization_pack.failure_mode_rows:
        _ensure_source_refs_resolve(
            row.source_refs,
            row_ref=row.failure_mode_ref,
            source_refs_by_ref=source_refs_by_ref,
        )
    for row in realization_pack.contraindicated_pattern_rows:
        _ensure_source_refs_resolve(
            row.source_refs,
            row_ref=row.contraindicated_pattern_ref,
            source_refs_by_ref=source_refs_by_ref,
        )

    if profile.profile_ref not in reconstruction_plan.source_profile_refs:
        raise ValueError("reconstruction plan must reference the released profile")
    if realization_pack.pack_ref not in reconstruction_plan.realization_pack_refs:
        raise ValueError("reconstruction plan must reference the realization pack")
    missing_plan_records = set(reconstruction_plan.concept_realization_refs) - set(
        realization_records_by_ref
    )
    if missing_plan_records:
        raise ValueError(
            f"reconstruction plan refs missing records: {sorted(missing_plan_records)}"
        )
    missing_plan_witnesses = set(reconstruction_plan.planned_witness_refs) - set(
        witness_templates_by_ref
    )
    if missing_plan_witnesses:
        raise ValueError(
            f"reconstruction plan witness refs missing templates: {sorted(missing_plan_witnesses)}"
        )
    for obligation in reconstruction_plan.planned_obligation_rows:
        missing_obligation_records = set(obligation.concept_realization_refs) - set(
            realization_records_by_ref
        )
        if missing_obligation_records:
            raise ValueError(
                "planned obligation refs missing realization records: "
                f"{sorted(missing_obligation_records)}"
            )
    for template in witness_templates:
        missing_template_records = set(template.realization_refs) - set(realization_records_by_ref)
        if missing_template_records:
            raise ValueError(
                f"witness template refs missing records: {sorted(missing_template_records)}"
            )


def validate_pb_py_0c_local_fixture_comparison_bundle(
    *,
    profile: ProgrambenchCleanroomReconstructionProfile,
    concept_seed: ProgramOdeuConceptBoundarySeed,
    source_index: ProgrambenchCleanroomEvidenceSourceIndex,
    guardrail: ProgrambenchReconstructionNonAuthorityGuardrail,
    fixture_contract: ProgrambenchLocalCleanroomFixtureContract,
    realization_records: list[ConceptRealizationRecord],
    realization_pack: PythonReconstructionRealizationPack,
    reconstruction_plan: PythonReconstructionPlan,
    witness_templates: list[PythonRealizationWitnessTemplate],
    local_fixture: ProgrambenchLocalCleanroomFixture,
    comparison_packet: ProgrambenchReconstructionComparisonPacket,
    probe_audit: ProgrambenchProbeEquivalenceAudit,
    family_closeout: ProgrambenchRealizationFamilyCloseoutAlignment,
) -> None:
    validate_pb_py_0b_python_realization_bundle(
        profile=profile,
        concept_seed=concept_seed,
        source_index=source_index,
        guardrail=guardrail,
        fixture_contract=fixture_contract,
        realization_records=realization_records,
        realization_pack=realization_pack,
        reconstruction_plan=reconstruction_plan,
        witness_templates=witness_templates,
    )
    source_refs_by_ref = {row.source_ref for row in source_index.source_rows}
    witness_templates_by_ref = {row.witness_template_ref for row in witness_templates}

    if local_fixture.fixture_contract_ref != fixture_contract.fixture_id:
        raise ValueError("local fixture must reference the released fixture contract")
    if local_fixture.reference_executable_ref != fixture_contract.reference_executable_ref:
        raise ValueError("local fixture must preserve the contract reference executable ref")
    if local_fixture.usage_docs_ref != fixture_contract.usage_docs_ref:
        raise ValueError("local fixture must preserve the contract usage docs ref")
    missing_forbidden_sources = {
        row.source_ref for row in local_fixture.forbidden_source_rows
    } - source_refs_by_ref
    if missing_forbidden_sources:
        raise ValueError(
            f"local fixture forbidden source rows missing source refs: "
            f"{sorted(missing_forbidden_sources)}"
        )
    hidden_visible = set(local_fixture.worker_hidden_file_refs) & set(
        local_fixture.worker_visible_file_refs
    )
    if hidden_visible:
        raise ValueError(f"local fixture hidden refs visible to worker: {sorted(hidden_visible)}")

    if comparison_packet.fixture_ref != local_fixture.fixture_ref:
        raise ValueError("comparison packet must reference the local fixture")
    missing_comparison_profiles = set(comparison_packet.profile_refs) - {profile.profile_ref}
    if missing_comparison_profiles:
        raise ValueError(
            f"comparison packet profile refs missing released profile: "
            f"{sorted(missing_comparison_profiles)}"
        )
    missing_comparison_packs = set(comparison_packet.realization_pack_refs) - {
        realization_pack.pack_ref
    }
    if missing_comparison_packs:
        raise ValueError(
            f"comparison packet realization pack refs missing released pack: "
            f"{sorted(missing_comparison_packs)}"
        )
    missing_comparison_witnesses = set(comparison_packet.witness_template_refs) - set(
        witness_templates_by_ref
    )
    if missing_comparison_witnesses:
        raise ValueError(
            "comparison packet witness template refs missing released templates: "
            f"{sorted(missing_comparison_witnesses)}"
        )

    if probe_audit.fixture_ref != local_fixture.fixture_ref:
        raise ValueError("probe audit must reference the local fixture")
    if probe_audit.comparison_packet_ref != comparison_packet.comparison_packet_ref:
        raise ValueError("probe audit must reference the comparison packet")
    audit_probe_refs = {row.local_probe_ref for row in probe_audit.local_probe_rows}
    missing_probe_refs = set(comparison_packet.local_probe_refs) - audit_probe_refs
    if missing_probe_refs:
        raise ValueError(
            f"comparison packet local probe refs missing audit rows: {sorted(missing_probe_refs)}"
        )

    if profile.profile_ref not in family_closeout.released_profile_refs:
        raise ValueError("family closeout must reference the released profile")
    if source_index.source_index_ref not in family_closeout.released_source_index_refs:
        raise ValueError("family closeout must reference the released source index")
    if concept_seed.concept_seed_set_ref not in family_closeout.released_concept_seed_refs:
        raise ValueError("family closeout must reference the released concept seed")
    if fixture_contract.fixture_id not in family_closeout.released_fixture_contract_refs:
        raise ValueError("family closeout must reference the released fixture contract")
    if realization_pack.pack_ref not in family_closeout.released_realization_pack_refs:
        raise ValueError("family closeout must reference the released realization pack")
    if local_fixture.fixture_ref not in family_closeout.released_fixture_refs:
        raise ValueError("family closeout must reference the released local fixture")
    if (
        comparison_packet.comparison_packet_ref
        not in family_closeout.released_comparison_packet_refs
    ):
        raise ValueError("family closeout must reference the released comparison packet")
    if probe_audit.audit_ref not in family_closeout.released_audit_refs:
        raise ValueError("family closeout must reference the released probe audit")
