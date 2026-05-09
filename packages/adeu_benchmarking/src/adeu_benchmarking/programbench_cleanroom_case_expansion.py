from __future__ import annotations

import re
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .programbench_cleanroom_matrix import ProgrambenchLocalCaseMatrixFamilyCloseoutAlignment

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

PROGRAMBENCH_LOCAL_CASE_EXPANSION_REQUEST_SCHEMA = (
    "programbench_local_case_expansion_request@1"
)
PROGRAMBENCH_LOCAL_CASE_SOURCE_POOL_MANIFEST_SCHEMA = (
    "programbench_local_case_source_pool_manifest@1"
)
PROGRAMBENCH_LOCAL_CASE_EXPANSION_ELIGIBILITY_REVIEW_SCHEMA = (
    "programbench_local_case_expansion_eligibility_review@1"
)
PROGRAMBENCH_LOCAL_CASE_EXPANSION_CONTROL_CONTRACT_SCHEMA = (
    "programbench_local_case_expansion_control_contract@1"
)
PROGRAMBENCH_LOCAL_CASE_EXPANSION_NON_AUTHORITY_GUARDRAIL_SCHEMA = (
    "programbench_local_case_expansion_non_authority_guardrail@1"
)

PROGRAMBENCH_LOCAL_CASE_BLUEPRINT_SCHEMA = "programbench_local_case_blueprint@1"
PROGRAMBENCH_LOCAL_CASE_CLEANROOM_EVIDENCE_PACK_SCHEMA = (
    "programbench_local_case_cleanroom_evidence_pack@1"
)
PROGRAMBENCH_LOCAL_CASE_PROBE_CONTRACT_SCHEMA = "programbench_local_case_probe_contract@1"
PROGRAMBENCH_LOCAL_CASE_ORACLE_BOUNDARY_SCHEMA = "programbench_local_case_oracle_boundary@1"
PROGRAMBENCH_LOCAL_CASE_CONTAMINATION_SCREEN_SCHEMA = (
    "programbench_local_case_contamination_screen@1"
)
PROGRAMBENCH_LOCAL_CASE_LINEAGE_REGISTRATION_SCHEMA = (
    "programbench_local_case_lineage_registration@1"
)
PROGRAMBENCH_LOCAL_CASE_EXPANSION_READINESS_SUMMARY_SCHEMA = (
    "programbench_local_case_expansion_readiness_summary@1"
)
PROGRAMBENCH_LOCAL_CASE_MATRIX_CANDIDATE_HANDOFF_SCHEMA = (
    "programbench_local_case_matrix_candidate_handoff@1"
)
PROGRAMBENCH_LOCAL_CASE_EXPANSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "programbench_local_case_expansion_family_closeout_alignment@1"
)

PB_CASE_EXPANSION_0A_ARTIFACT_KINDS = {
    PROGRAMBENCH_LOCAL_CASE_EXPANSION_REQUEST_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_SOURCE_POOL_MANIFEST_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_EXPANSION_ELIGIBILITY_REVIEW_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_EXPANSION_CONTROL_CONTRACT_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_EXPANSION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
}
PB_CASE_EXPANSION_0B_ARTIFACT_KINDS = {
    PROGRAMBENCH_LOCAL_CASE_BLUEPRINT_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_CLEANROOM_EVIDENCE_PACK_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_PROBE_CONTRACT_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_ORACLE_BOUNDARY_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_CONTAMINATION_SCREEN_SCHEMA,
}
PB_CASE_EXPANSION_0C_ARTIFACT_KINDS = {
    PROGRAMBENCH_LOCAL_CASE_LINEAGE_REGISTRATION_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_EXPANSION_READINESS_SUMMARY_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_MATRIX_CANDIDATE_HANDOFF_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_EXPANSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
}
PB_CASE_EXPANSION_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS = (
    PB_CASE_EXPANSION_0B_ARTIFACT_KINDS | PB_CASE_EXPANSION_0C_ARTIFACT_KINDS
)
PB_CASE_EXPANSION_0B_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS = (
    PB_CASE_EXPANSION_0C_ARTIFACT_KINDS
)

_SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
_FORBIDDEN_REF_MARKERS = (
    "benchmark-score",
    "decompilation",
    "docker-socket",
    "external-repo",
    "hidden-test",
    "host-secret",
    "internet-lookup",
    "model-ranking",
    "official-evaluator",
    "original-source",
    "postmortem-only",
    "source-lookup",
)
_NO_DERIVED_SUMMARY_LAUNDERING_MARKERS = (
    "decompilation",
    "evaluator edge",
    "external repo",
    "hidden artifact",
    "hidden test",
    "official evaluator",
    "original source",
    "postmortem",
    "source lookup",
)
_SOFT_SCORING_LANGUAGE_MARKERS = (
    "baseline comparison",
    "benchmark score",
    "benchmark subset",
    "benchmark-like",
    "beats baseline",
    "leaderboard",
    "model ranking",
    "pass rate",
    "representative sample",
    "solve rate",
    "success rate",
)


def _ensure_non_empty_trimmed(values: list[str], *, field_name: str) -> None:
    for value in values:
        if not isinstance(value, str) or not value or value != value.strip():
            raise ValueError(f"{field_name} entries must be non-empty trimmed strings")


def _ensure_sorted_unique(values: list[str], *, field_name: str) -> None:
    if not values:
        raise ValueError(f"{field_name} must contain at least one entry")
    _ensure_non_empty_trimmed(values, field_name=field_name)
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")
    if values != sorted(values):
        raise ValueError(f"{field_name} must be lexicographically sorted")


def _ensure_sorted_unique_allow_empty(values: list[str], *, field_name: str) -> None:
    if values:
        _ensure_non_empty_trimmed(values, field_name=field_name)
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")
    if values != sorted(values):
        raise ValueError(f"{field_name} must be lexicographically sorted")


def _ensure_hash(value: str, *, field_name: str) -> None:
    if not _SHA256_RE.match(value):
        raise ValueError(f"{field_name} must be a sha256:<64 lowercase hex> hash")


def _ensure_no_forbidden_refs(values: list[str], *, field_name: str) -> None:
    leaked = sorted(
        ref for ref in values if any(marker in ref for marker in _FORBIDDEN_REF_MARKERS)
    )
    if leaked:
        raise ValueError(f"{field_name} contains forbidden case-expansion refs: {leaked}")


def _ensure_no_soft_scoring_language(value: str, *, field_name: str) -> None:
    lowered = value.lower()
    leaked = [marker for marker in _SOFT_SCORING_LANGUAGE_MARKERS if marker in lowered]
    if leaked:
        raise ValueError(
            f"{field_name} contains benchmark-like scoring or ranking language: {leaked}"
        )


def _ensure_no_laundered_summary(value: str, *, field_name: str) -> None:
    lowered = value.lower()
    leaked = [marker for marker in _NO_DERIVED_SUMMARY_LAUNDERING_MARKERS if marker in lowered]
    if leaked:
        raise ValueError(
            f"{field_name} contains hidden/forbidden derived-summary leakage: {leaked}"
        )
    _ensure_no_soft_scoring_language(value, field_name=field_name)


def _ensure_refs_resolve(
    values: list[str],
    allowed_refs: set[str],
    *,
    field_name: str,
) -> None:
    unknown = sorted(set(values) - allowed_refs)
    if unknown:
        raise ValueError(f"{field_name} contains unresolved refs: {unknown}")


class _CaseExpansionBase(BaseModel):
    model_config = MODEL_CONFIG


class ProgrambenchLocalCaseSelectionRationaleRow(_CaseExpansionBase):
    selection_rationale_ref: str
    rationale_kind: Literal[
        "local_coverage_probe_case_expansion",
        "local_regression_case_expansion",
        "local_research_case_expansion",
        "local_smoke_case_expansion",
    ]
    candidate_case_idea_refs: list[str] = Field(min_length=1)
    rationale_scope_posture: Literal["local_case_selection_only_not_representative"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_rationale(self) -> "ProgrambenchLocalCaseSelectionRationaleRow":
        _ensure_sorted_unique(
            self.candidate_case_idea_refs,
            field_name="candidate_case_idea_refs",
        )
        _ensure_no_forbidden_refs(
            self.candidate_case_idea_refs,
            field_name="candidate_case_idea_refs",
        )
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseSourcePoolRow(_CaseExpansionBase):
    source_ref: str
    source_kind: Literal[
        "cleanroom_usage_doc",
        "cleanroom_visible_input_artifact",
        "local_matrix_handoff_pressure",
        "local_probe_observation",
        "support_context",
        "decompilation_source",
        "external_repo_source",
        "hidden_test",
        "internet_lookup_source",
        "official_evaluator_source",
        "original_source",
        "postmortem_only",
    ]
    source_identity_hash: str
    source_origin_posture: Literal[
        "cleanroom_visible",
        "support_only",
        "decompilation_derived",
        "external_repo_derived",
        "hidden",
        "internet_derived",
        "official_evaluator_derived",
        "original_source_derived",
        "postmortem_only",
    ]
    source_visibility_posture: Literal[
        "auditor_only",
        "blocked_for_expansion",
        "blueprint_visible_later_if_selected",
        "cleanroom_visible",
        "support_only",
    ]
    store_presence_posture: Literal[
        "known_available_cleanroom_store",
        "known_forbidden_store_unmounted",
        "known_hidden_store_unmounted",
        "known_support_store",
    ]
    derived_summary_policy: Literal[
        "no_derived_summary_allowed",
        "redacted_category_count_reason_only",
        "visible_summary_allowed_cleanroom_only",
    ]
    allowed_for_expansion: bool
    exclusion_reason: Literal[
        "not_applicable",
        "blocked_decompilation_source",
        "blocked_external_repo_source",
        "blocked_hidden_test_source",
        "blocked_internet_lookup_source",
        "blocked_official_evaluator_source",
        "blocked_original_source",
        "blocked_postmortem_only_source",
        "support_only_not_sufficient",
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_source_row(self) -> "ProgrambenchLocalCaseSourcePoolRow":
        _ensure_hash(self.source_identity_hash, field_name="source_identity_hash")
        is_forbidden = (
            self.source_kind
            in {
                "decompilation_source",
                "external_repo_source",
                "hidden_test",
                "internet_lookup_source",
                "official_evaluator_source",
                "original_source",
                "postmortem_only",
            }
            or self.source_origin_posture
            in {
                "decompilation_derived",
                "external_repo_derived",
                "hidden",
                "internet_derived",
                "official_evaluator_derived",
                "original_source_derived",
                "postmortem_only",
            }
        )
        if self.allowed_for_expansion:
            if is_forbidden:
                raise ValueError("forbidden source kind/origin cannot be allowed for expansion")
            if self.source_origin_posture != "cleanroom_visible":
                raise ValueError("allowed expansion sources require cleanroom-visible origin")
            if self.source_visibility_posture != "cleanroom_visible":
                raise ValueError("allowed expansion sources require cleanroom-visible posture")
            if self.exclusion_reason != "not_applicable":
                raise ValueError("allowed expansion sources require not_applicable exclusion")
            if self.derived_summary_policy != "visible_summary_allowed_cleanroom_only":
                raise ValueError(
                    "allowed expansion sources require cleanroom-only derived summary policy"
                )
        else:
            if self.exclusion_reason == "not_applicable":
                raise ValueError("blocked source rows require an exclusion reason")
            if self.source_kind == "support_context":
                if self.exclusion_reason != "support_only_not_sufficient":
                    raise ValueError(
                        "support context sources require support_only_not_sufficient "
                        "exclusion reason"
                    )
                if self.source_visibility_posture != "support_only":
                    raise ValueError("support context sources require support_only visibility")
        if is_forbidden:
            if self.derived_summary_policy != "no_derived_summary_allowed":
                raise ValueError("forbidden source rows cannot permit derived summaries")
            if self.source_visibility_posture in {
                "blueprint_visible_later_if_selected",
                "cleanroom_visible",
            }:
                raise ValueError("forbidden sources cannot have visible postures")
        if self.source_visibility_posture == "cleanroom_visible":
            _ensure_no_forbidden_refs([self.source_ref], field_name="source_ref")
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseCandidateIdeaRow(_CaseExpansionBase):
    candidate_case_idea_ref: str
    case_expansion_ref: str
    source_refs: list[str] = Field(min_length=1)
    candidate_case_idea_hash: str
    source_pool_subset_hash: str
    dedupe_against_existing_case_lineages: bool
    existing_case_lineage_overlap_refs: list[str] = Field(default_factory=list)
    nearest_existing_case_refs: list[str] = Field(default_factory=list)
    novelty_or_duplication_posture: Literal[
        "duplicate_allowed_for_regression_or_smoke",
        "duplicate_blocked",
        "novel_local_case_idea",
        "overlap_requires_review",
    ]
    case_idea_label: str
    case_origin_posture: Literal[
        "cleanroom_visible_source_witnessed",
        "support_only",
        "hidden_or_forbidden_derived",
    ]
    case_visibility_posture: Literal[
        "blueprint_deferred_cleanroom_visible",
        "blocked_by_forbidden_source",
        "support_only_context",
    ]
    candidate_scope_posture: Literal[
        "case_idea_only_not_blueprint",
        "case_idea_support_only",
        "case_idea_blocked",
    ]
    expected_blueprint_deferred_posture: Literal["blueprint_deferred_to_pb_case_expansion_0b"]
    eligibility_claim: Literal[
        "blocked",
        "eligible_for_later_blueprint_review",
        "support_only_not_eligible",
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_candidate(self) -> "ProgrambenchLocalCaseCandidateIdeaRow":
        _ensure_sorted_unique(self.source_refs, field_name="source_refs")
        _ensure_hash(self.candidate_case_idea_hash, field_name="candidate_case_idea_hash")
        _ensure_hash(self.source_pool_subset_hash, field_name="source_pool_subset_hash")
        _ensure_sorted_unique_allow_empty(
            self.existing_case_lineage_overlap_refs,
            field_name="existing_case_lineage_overlap_refs",
        )
        _ensure_sorted_unique_allow_empty(
            self.nearest_existing_case_refs,
            field_name="nearest_existing_case_refs",
        )
        _ensure_no_laundered_summary(self.case_idea_label, field_name="case_idea_label")
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        has_overlap = bool(self.existing_case_lineage_overlap_refs)
        if not self.dedupe_against_existing_case_lineages:
            raise ValueError("candidate case ideas must declare dedupe against existing lineages")
        if has_overlap and self.novelty_or_duplication_posture == "novel_local_case_idea":
            raise ValueError("overlapping candidate ideas cannot claim novelty")
        if has_overlap and self.novelty_or_duplication_posture == "duplicate_blocked":
            if self.eligibility_claim != "blocked":
                raise ValueError("duplicate-blocked case ideas cannot be eligible")
        if has_overlap and self.novelty_or_duplication_posture != (
            "duplicate_allowed_for_regression_or_smoke"
        ):
            if self.eligibility_claim == "eligible_for_later_blueprint_review":
                raise ValueError(
                    "duplicate case ideas require explicit regression/smoke allowance"
                )
        if self.eligibility_claim == "eligible_for_later_blueprint_review":
            if self.case_origin_posture != "cleanroom_visible_source_witnessed":
                raise ValueError("eligible case ideas require cleanroom-visible source witnesses")
            if self.case_visibility_posture != "blueprint_deferred_cleanroom_visible":
                raise ValueError("eligible case ideas require blueprint-deferred visibility")
            if self.candidate_scope_posture != "case_idea_only_not_blueprint":
                raise ValueError("eligible case ideas must remain case ideas, not blueprints")
        elif self.case_origin_posture == "hidden_or_forbidden_derived":
            if self.eligibility_claim != "blocked":
                raise ValueError("hidden/forbidden-derived case ideas must be blocked")
        return self


class ProgrambenchLocalCaseExpansionEligibilityRow(_CaseExpansionBase):
    eligibility_row_ref: str
    candidate_case_idea_ref: str
    eligibility_posture: Literal[
        "blocked_by_duplicate_without_rationale",
        "blocked_by_forbidden_source",
        "blocked_by_support_only_source",
        "deferred_for_later_review",
        "eligible_for_later_blueprint_review",
    ]
    source_witness_refs: list[str] = Field(default_factory=list)
    blocker_refs: list[str] = Field(default_factory=list)
    warning_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_eligibility_row(self) -> "ProgrambenchLocalCaseExpansionEligibilityRow":
        _ensure_no_forbidden_refs(
            [self.candidate_case_idea_ref],
            field_name="candidate_case_idea_ref",
        )
        for field_name in ("source_witness_refs", "blocker_refs", "warning_refs"):
            values = getattr(self, field_name)
            _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        if self.eligibility_posture == "eligible_for_later_blueprint_review":
            if not self.source_witness_refs:
                raise ValueError("eligible case ideas require source witness refs")
            if self.blocker_refs:
                raise ValueError("eligible case ideas cannot carry blockers")
        elif self.eligibility_posture.startswith("blocked_by_") and not self.blocker_refs:
            raise ValueError("blocked eligibility rows require blocker refs")
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseExpansionAllowedActionRow(_CaseExpansionBase):
    allowed_action_ref: str
    action_kind: Literal[
        "case_idea_eligibility_review",
        "control_contract_review",
        "non_authority_guardrail_review",
        "source_pool_manifest_review",
    ]
    action_scope_posture: Literal["allowed_for_pb_case_expansion_0a_review_only"]
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_allowed_action(self) -> "ProgrambenchLocalCaseExpansionAllowedActionRow":
        _ensure_sorted_unique(self.source_refs, field_name="allowed action source_refs")
        _ensure_no_forbidden_refs(self.source_refs, field_name="allowed action source_refs")
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseExpansionForbiddenActionRow(_CaseExpansionBase):
    forbidden_action_ref: str
    action_kind: Literal[
        "baseline_comparison",
        "batch_command_execution",
        "benchmark_scoring",
        "case_blueprinting",
        "case_lineage_registration",
        "decompilation",
        "docker_socket_access",
        "external_repo_lookup",
        "hidden_test_access",
        "host_secret_access",
        "internet_lookup",
        "local_trial_execution",
        "matrix_inclusion",
        "model_ranking",
        "official_evaluator_access",
        "official_submission",
        "source_lookup",
        "widen_write_scope",
    ]
    forbiddance_posture: Literal["forbidden_by_pb_case_expansion_0a"]
    limitation_note: str


class ProgrambenchLocalCaseExpansionForbiddenAuthorityRow(_CaseExpansionBase):
    forbidden_authority_ref: str
    authority_kind: Literal[
        "baseline_comparison",
        "batch_execution",
        "benchmark_score",
        "benchmark_truth",
        "case_blueprint",
        "case_lineage_registration",
        "future_family_selection",
        "hidden_test_inference",
        "local_trial_execution",
        "matrix_inclusion",
        "model_ranking",
        "official_programbench_participation",
        "official_submission",
        "retry_chain",
        "second_retry",
    ]
    forbiddance_posture: Literal["forbidden_by_pb_case_expansion_0a"]
    limitation_note: str


class ProgrambenchLocalCaseExpansionRequest(_CaseExpansionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_EXPANSION_REQUEST_SCHEMA] = Field(alias="schema")
    case_expansion_ref: str
    case_expansion_request_ref: str
    source_pool_manifest_ref: str
    expansion_eligibility_review_ref: str
    expansion_control_contract_ref: str
    expansion_horizon: Literal[
        "local_coverage_probe_case_expansion",
        "local_regression_case_expansion",
        "local_research_case_expansion",
        "local_smoke_case_expansion",
    ]
    expansion_max_case_count: int = Field(ge=1)
    candidate_case_idea_refs: list[str] = Field(min_length=1)
    requested_case_count: int = Field(ge=1)
    matrix_pressure_refs: list[str] = Field(min_length=1)
    matrix_pressure_kind: Literal[
        "future_local_case_expansion_review",
        "local_matrix_gap_pressure",
        "local_matrix_research_pressure",
    ]
    case_selection_horizon: Literal[
        "local_coverage_probe_case_expansion",
        "local_regression_case_expansion",
        "local_research_case_expansion",
        "local_smoke_case_expansion",
    ]
    case_selection_rationale_rows: list[ProgrambenchLocalCaseSelectionRationaleRow] = Field(
        min_length=1
    )
    case_selection_bias_posture: Literal["bias_declared_not_representative_benchmark_sample"]
    case_diversity_posture: Literal[
        "local_diversity_accounting_only",
        "not_representative_diversity_claim",
    ]
    representativeness_posture: Literal["not_representative_benchmark_sample"]
    dedupe_policy_ref: str
    official_benchmark_authority_posture: Literal[
        "no_official_programbench_authority_granted_by_pb_case_expansion_0a"
    ]
    benchmark_score_authority_posture: Literal["no_benchmark_score_authority_granted_by_0a"]
    baseline_comparison_authority_posture: Literal[
        "no_baseline_comparison_authority_granted_by_0a"
    ]
    model_ranking_posture: Literal["no_model_ranking_claimed_by_pb_case_expansion_0a"]
    batch_execution_authority_posture: Literal[
        "no_batch_execution_authority_granted_by_pb_case_expansion_0a"
    ]
    future_family_selection_posture: Literal[
        "no_future_family_selected_by_pb_case_expansion_0a"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_request(self) -> "ProgrambenchLocalCaseExpansionRequest":
        _ensure_sorted_unique(
            self.candidate_case_idea_refs,
            field_name="candidate_case_idea_refs",
        )
        _ensure_sorted_unique(self.matrix_pressure_refs, field_name="matrix_pressure_refs")
        if self.requested_case_count > self.expansion_max_case_count:
            raise ValueError("requested_case_count cannot exceed expansion_max_case_count")
        rationale_refs = [
            row.selection_rationale_ref for row in self.case_selection_rationale_rows
        ]
        _ensure_sorted_unique(rationale_refs, field_name="case_selection_rationale_rows")
        selected_refs = set().union(
            *(row.candidate_case_idea_refs for row in self.case_selection_rationale_rows)
        )
        if not set(self.candidate_case_idea_refs).issubset(selected_refs):
            raise ValueError("candidate case ideas must be covered by selection rationale rows")
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseSourcePoolManifest(_CaseExpansionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_SOURCE_POOL_MANIFEST_SCHEMA] = Field(
        alias="schema"
    )
    source_pool_manifest_ref: str
    case_expansion_ref: str
    source_pool_rows: list[ProgrambenchLocalCaseSourcePoolRow] = Field(min_length=1)
    candidate_case_idea_rows: list[ProgrambenchLocalCaseCandidateIdeaRow] = Field(min_length=1)
    allowed_source_refs: list[str] = Field(min_length=1)
    blocked_source_refs: list[str] = Field(default_factory=list)
    auditor_only_source_refs: list[str] = Field(default_factory=list)
    support_only_source_refs: list[str] = Field(default_factory=list)
    forbidden_source_refs: list[str] = Field(default_factory=list)
    source_set_hash: str
    visible_source_set_hash: str
    forbidden_source_set_hash: str
    derived_summary_policy: Literal["no_derived_summary_laundering"]
    worker_visible_policy: Literal["cleanroom_visible_sources_only"]
    blueprint_visible_policy: Literal["blueprint_visibility_deferred_to_pb_case_expansion_0b"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_manifest(self) -> "ProgrambenchLocalCaseSourcePoolManifest":
        source_refs = [row.source_ref for row in self.source_pool_rows]
        _ensure_sorted_unique(source_refs, field_name="source_pool_rows")
        candidate_refs = [row.candidate_case_idea_ref for row in self.candidate_case_idea_rows]
        _ensure_sorted_unique(candidate_refs, field_name="candidate_case_idea_rows")
        for field_name in (
            "allowed_source_refs",
            "blocked_source_refs",
            "auditor_only_source_refs",
            "support_only_source_refs",
            "forbidden_source_refs",
        ):
            values = getattr(self, field_name)
            if field_name == "allowed_source_refs":
                _ensure_sorted_unique(values, field_name=field_name)
            else:
                _ensure_sorted_unique_allow_empty(values, field_name=field_name)
        for field_name in (
            "source_set_hash",
            "visible_source_set_hash",
            "forbidden_source_set_hash",
        ):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        rows_by_ref = {row.source_ref: row for row in self.source_pool_rows}
        for field_name in (
            "allowed_source_refs",
            "blocked_source_refs",
            "auditor_only_source_refs",
            "support_only_source_refs",
            "forbidden_source_refs",
        ):
            _ensure_refs_resolve(
                getattr(self, field_name),
                set(rows_by_ref),
                field_name=field_name,
            )
        allowed_from_rows = {
            row.source_ref for row in self.source_pool_rows if row.allowed_for_expansion
        }
        if set(self.allowed_source_refs) != allowed_from_rows:
            raise ValueError("allowed_source_refs must match allowed source pool rows")
        forbidden_from_rows = {
            row.source_ref
            for row in self.source_pool_rows
            if row.source_kind in {
                "decompilation_source",
                "external_repo_source",
                "hidden_test",
                "internet_lookup_source",
                "official_evaluator_source",
                "original_source",
                "postmortem_only",
            }
            or row.source_origin_posture
            in {
                "decompilation_derived",
                "external_repo_derived",
                "hidden",
                "internet_derived",
                "official_evaluator_derived",
                "original_source_derived",
                "postmortem_only",
            }
        }
        if set(self.forbidden_source_refs) != forbidden_from_rows:
            raise ValueError("forbidden_source_refs must match forbidden source pool rows")
        blocked_from_rows = {
            row.source_ref
            for row in self.source_pool_rows
            if row.exclusion_reason.startswith("blocked_")
        }
        if set(self.blocked_source_refs) != blocked_from_rows:
            raise ValueError("blocked_source_refs must match blocked source pool rows")
        auditor_from_rows = {
            row.source_ref
            for row in self.source_pool_rows
            if row.source_visibility_posture == "auditor_only"
        }
        if set(self.auditor_only_source_refs) != auditor_from_rows:
            raise ValueError("auditor_only_source_refs must match auditor-only source pool rows")
        support_from_rows = {
            row.source_ref for row in self.source_pool_rows if row.source_kind == "support_context"
        }
        if support_from_rows != set(self.support_only_source_refs):
            raise ValueError("support_only_source_refs must match support source rows")
        candidate_source_refs = {
            source_ref for row in self.candidate_case_idea_rows for source_ref in row.source_refs
        }
        _ensure_refs_resolve(
            sorted(candidate_source_refs),
            set(self.allowed_source_refs) | set(self.support_only_source_refs),
            field_name="candidate case idea source_refs",
        )
        for row in self.candidate_case_idea_rows:
            if row.case_expansion_ref != self.case_expansion_ref:
                raise ValueError("candidate case idea rows must match manifest case_expansion_ref")
            if row.eligibility_claim == "eligible_for_later_blueprint_review":
                if not set(row.source_refs) & set(self.allowed_source_refs):
                    raise ValueError("eligible case ideas require cleanroom-visible source witness")
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseExpansionEligibilityReview(_CaseExpansionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_EXPANSION_ELIGIBILITY_REVIEW_SCHEMA] = Field(
        alias="schema"
    )
    expansion_eligibility_review_ref: str
    case_expansion_ref: str
    candidate_eligibility_rows: list[ProgrambenchLocalCaseExpansionEligibilityRow] = Field(
        min_length=1
    )
    eligible_candidate_case_idea_refs: list[str] = Field(min_length=1)
    blocked_candidate_case_idea_refs: list[str] = Field(default_factory=list)
    deferred_candidate_case_idea_refs: list[str] = Field(default_factory=list)
    carried_blocker_refs: list[str] = Field(default_factory=list)
    carried_warning_refs: list[str] = Field(default_factory=list)
    released_family_closeout_refs: list[str] = Field(min_length=1)
    non_authority_guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_review(self) -> "ProgrambenchLocalCaseExpansionEligibilityReview":
        row_refs = [row.eligibility_row_ref for row in self.candidate_eligibility_rows]
        _ensure_sorted_unique(row_refs, field_name="candidate_eligibility_rows")
        candidate_refs = [
            row.candidate_case_idea_ref for row in self.candidate_eligibility_rows
        ]
        _ensure_sorted_unique(
            candidate_refs,
            field_name="candidate_eligibility_rows.candidate_case_idea_ref",
        )
        eligible_from_rows = {
            row.candidate_case_idea_ref
            for row in self.candidate_eligibility_rows
            if row.eligibility_posture == "eligible_for_later_blueprint_review"
        }
        blocked_from_rows = {
            row.candidate_case_idea_ref
            for row in self.candidate_eligibility_rows
            if row.eligibility_posture.startswith("blocked_by_")
        }
        deferred_from_rows = {
            row.candidate_case_idea_ref
            for row in self.candidate_eligibility_rows
            if row.eligibility_posture == "deferred_for_later_review"
        }
        for field_name in (
            "eligible_candidate_case_idea_refs",
            "blocked_candidate_case_idea_refs",
            "deferred_candidate_case_idea_refs",
            "carried_blocker_refs",
            "carried_warning_refs",
            "released_family_closeout_refs",
            "non_authority_guardrail_refs",
        ):
            values = getattr(self, field_name)
            if field_name in {
                "eligible_candidate_case_idea_refs",
                "released_family_closeout_refs",
                "non_authority_guardrail_refs",
            }:
                _ensure_sorted_unique(values, field_name=field_name)
            else:
                _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        if set(self.eligible_candidate_case_idea_refs) != eligible_from_rows:
            raise ValueError("eligible_candidate_case_idea_refs must match eligibility rows")
        if set(self.blocked_candidate_case_idea_refs) != blocked_from_rows:
            raise ValueError("blocked_candidate_case_idea_refs must match eligibility rows")
        if set(self.deferred_candidate_case_idea_refs) != deferred_from_rows:
            raise ValueError("deferred_candidate_case_idea_refs must match eligibility rows")
        top_level_posture_refs = (
            set(self.eligible_candidate_case_idea_refs),
            set(self.blocked_candidate_case_idea_refs),
            set(self.deferred_candidate_case_idea_refs),
        )
        overlaps = sorted(
            ref
            for ref in set().union(*top_level_posture_refs)
            if sum(ref in refs for refs in top_level_posture_refs) > 1
        )
        if overlaps:
            raise ValueError(f"candidate eligibility posture refs must be disjoint: {overlaps}")
        row_blockers = set().union(*(row.blocker_refs for row in self.candidate_eligibility_rows))
        if not set(self.carried_blocker_refs).issubset(row_blockers):
            raise ValueError("carried blockers must resolve to eligibility row blocker refs")
        row_warnings = set().union(*(row.warning_refs for row in self.candidate_eligibility_rows))
        if not set(self.carried_warning_refs).issubset(row_warnings):
            raise ValueError("carried warnings must resolve to eligibility row warning refs")
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseExpansionControlContract(_CaseExpansionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_EXPANSION_CONTROL_CONTRACT_SCHEMA] = Field(
        alias="schema"
    )
    expansion_control_contract_ref: str
    case_expansion_ref: str
    source_visibility_control_ref: str
    source_derivation_control_ref: str
    candidate_count_control_ref: str
    blueprint_deferred_control_ref: str
    execution_deferred_control_ref: str
    matrix_inclusion_deferred_control_ref: str
    scoring_deferred_control_ref: str
    model_ranking_deferred_control_ref: str
    allowed_expansion_action_rows: list[ProgrambenchLocalCaseExpansionAllowedActionRow] = Field(
        min_length=1
    )
    forbidden_expansion_action_rows: list[ProgrambenchLocalCaseExpansionForbiddenActionRow] = Field(
        min_length=1
    )
    limitation_note: str

    @model_validator(mode="after")
    def _validate_contract(self) -> "ProgrambenchLocalCaseExpansionControlContract":
        allowed_refs = [row.allowed_action_ref for row in self.allowed_expansion_action_rows]
        _ensure_sorted_unique(allowed_refs, field_name="allowed_expansion_action_rows")
        forbidden_refs = [
            row.forbidden_action_ref for row in self.forbidden_expansion_action_rows
        ]
        _ensure_sorted_unique(forbidden_refs, field_name="forbidden_expansion_action_rows")
        required_forbidden_actions = {
            "baseline_comparison",
            "batch_command_execution",
            "benchmark_scoring",
            "case_blueprinting",
            "case_lineage_registration",
            "decompilation",
            "docker_socket_access",
            "external_repo_lookup",
            "hidden_test_access",
            "host_secret_access",
            "internet_lookup",
            "local_trial_execution",
            "matrix_inclusion",
            "model_ranking",
            "official_evaluator_access",
            "official_submission",
            "source_lookup",
            "widen_write_scope",
        }
        observed = {row.action_kind for row in self.forbidden_expansion_action_rows}
        if len(observed) != len(self.forbidden_expansion_action_rows):
            raise ValueError("forbidden_expansion_action_rows must not duplicate action kinds")
        missing = sorted(required_forbidden_actions - observed)
        if missing:
            raise ValueError(f"case expansion control missing forbidden action kinds: {missing}")
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseExpansionNonAuthorityGuardrail(_CaseExpansionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_EXPANSION_NON_AUTHORITY_GUARDRAIL_SCHEMA] = Field(
        alias="schema"
    )
    expansion_guardrail_ref: str
    case_expansion_refs: list[str] = Field(min_length=1)
    guardrail_source_refs: list[str] = Field(min_length=1)
    non_authority_rows: list[ProgrambenchLocalCaseExpansionForbiddenAuthorityRow] = Field(
        min_length=1
    )
    forbidden_future_artifact_kinds: list[str] = Field(min_length=1)
    official_programbench_posture: Literal[
        "no_official_programbench_authority_granted_by_pb_case_expansion_0a"
    ]
    hidden_test_posture: Literal["hidden_tests_not_visible_not_inference_evidence"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    benchmark_score_posture: Literal["no_benchmark_score_authority_granted_by_0a"]
    baseline_comparison_posture: Literal["no_baseline_comparison_authority_granted_by_0a"]
    model_ranking_posture: Literal["no_model_ranking_claimed_by_pb_case_expansion_0a"]
    batch_execution_posture: Literal[
        "no_batch_execution_authority_granted_by_pb_case_expansion_0a"
    ]
    trial_execution_posture: Literal["no_local_trial_execution_authority_granted_by_0a"]
    future_family_posture: Literal["no_future_family_selected_by_pb_case_expansion_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_guardrail(self) -> "ProgrambenchLocalCaseExpansionNonAuthorityGuardrail":
        _ensure_sorted_unique(self.case_expansion_refs, field_name="case_expansion_refs")
        _ensure_sorted_unique(self.guardrail_source_refs, field_name="guardrail_source_refs")
        row_refs = [row.forbidden_authority_ref for row in self.non_authority_rows]
        _ensure_sorted_unique(row_refs, field_name="non_authority_rows")
        required_authorities = {
            "baseline_comparison",
            "batch_execution",
            "benchmark_score",
            "benchmark_truth",
            "case_blueprint",
            "case_lineage_registration",
            "future_family_selection",
            "hidden_test_inference",
            "local_trial_execution",
            "matrix_inclusion",
            "model_ranking",
            "official_programbench_participation",
            "official_submission",
            "retry_chain",
            "second_retry",
        }
        observed = {row.authority_kind for row in self.non_authority_rows}
        if len(observed) != len(self.non_authority_rows):
            raise ValueError("non_authority_rows must not duplicate authority kinds")
        missing = sorted(required_authorities - observed)
        if missing:
            raise ValueError(f"case expansion guardrail missing authorities: {missing}")
        _ensure_sorted_unique(
            self.forbidden_future_artifact_kinds,
            field_name="forbidden_future_artifact_kinds",
        )
        missing_future = sorted(
            PB_CASE_EXPANSION_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS
            - set(self.forbidden_future_artifact_kinds)
        )
        if missing_future:
            raise ValueError(
                f"case expansion guardrail missing future artifact kinds: {missing_future}"
            )
        current = sorted(
            PB_CASE_EXPANSION_0A_ARTIFACT_KINDS & set(self.forbidden_future_artifact_kinds)
        )
        if current:
            raise ValueError(
                f"case expansion guardrail cannot forbid current A artifact kinds: {current}"
            )
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseSourceWitnessRow(_CaseExpansionBase):
    source_witness_ref: str
    source_refs: list[str] = Field(min_length=1)
    witness_kind: Literal[
        "artifact_obligation_witness",
        "behavior_obligation_witness",
        "io_observation_witness",
        "support_context_witness",
    ]
    witness_strength: Literal["direct", "indirect", "support_only"]
    witnessed_obligation_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_source_witness(self) -> "ProgrambenchLocalCaseSourceWitnessRow":
        _ensure_sorted_unique(self.source_refs, field_name="source_witness.source_refs")
        _ensure_sorted_unique(
            self.witnessed_obligation_refs,
            field_name="source_witness.witnessed_obligation_refs",
        )
        _ensure_no_forbidden_refs(self.source_refs, field_name="source_witness.source_refs")
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseBehaviorObligationRow(_CaseExpansionBase):
    obligation_ref: str
    obligation_kind: Literal[
        "cli_argument_behavior",
        "exit_code_behavior",
        "filesystem_side_effect_behavior",
        "stderr_diagnostic_behavior",
        "stdout_output_behavior",
    ]
    obligation_status: Literal["locally_witnessed", "support_only", "unknown"]
    local_obligation_posture: Literal[
        "local_blueprint_obligation_only_not_official_task_truth"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_behavior_obligation(self) -> "ProgrambenchLocalCaseBehaviorObligationRow":
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseBehaviorObligationBasisRow(_CaseExpansionBase):
    obligation_ref: str
    source_witness_refs: list[str] = Field(min_length=1)
    support_kind: Literal[
        "cleanroom_artifact",
        "cleanroom_usage_doc",
        "local_probe_observation",
        "support_context_only",
    ]
    support_strength: Literal["direct", "indirect", "support_only"]
    unresolved_counterevidence_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_behavior_obligation_basis(
        self,
    ) -> "ProgrambenchLocalCaseBehaviorObligationBasisRow":
        _ensure_sorted_unique(
            self.source_witness_refs,
            field_name="behavior_obligation_basis.source_witness_refs",
        )
        _ensure_sorted_unique_allow_empty(
            self.unresolved_counterevidence_refs,
            field_name="behavior_obligation_basis.unresolved_counterevidence_refs",
        )
        if self.support_kind == "support_context_only" and self.support_strength != "support_only":
            raise ValueError("support-context basis rows require support_only strength")
        _ensure_no_forbidden_refs(
            self.source_witness_refs,
            field_name="behavior_obligation_basis.source_witness_refs",
        )
        _ensure_no_forbidden_refs(
            self.unresolved_counterevidence_refs,
            field_name="behavior_obligation_basis.unresolved_counterevidence_refs",
        )
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseIOObservationRow(_CaseExpansionBase):
    io_observation_ref: str
    obligation_ref: str
    source_witness_refs: list[str] = Field(min_length=1)
    io_channel: Literal["stderr", "stdin", "stdout"]
    observation_posture: Literal["local_cleanroom_observation_only"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_io_observation(self) -> "ProgrambenchLocalCaseIOObservationRow":
        _ensure_sorted_unique(
            self.source_witness_refs,
            field_name="io_observation.source_witness_refs",
        )
        _ensure_no_forbidden_refs(
            self.source_witness_refs,
            field_name="io_observation.source_witness_refs",
        )
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseArtifactObligationRow(_CaseExpansionBase):
    artifact_obligation_ref: str
    obligation_ref: str
    source_witness_refs: list[str] = Field(min_length=1)
    artifact_kind: Literal[
        "expected_input_artifact",
        "expected_output_artifact",
        "filesystem_side_effect",
    ]
    artifact_obligation_posture: Literal[
        "local_blueprint_artifact_obligation_only_not_materialized"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_artifact_obligation(self) -> "ProgrambenchLocalCaseArtifactObligationRow":
        _ensure_sorted_unique(
            self.source_witness_refs,
            field_name="artifact_obligation.source_witness_refs",
        )
        _ensure_no_forbidden_refs(
            self.source_witness_refs,
            field_name="artifact_obligation.source_witness_refs",
        )
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseProbeTemplateRow(_CaseExpansionBase):
    probe_ref: str
    obligation_refs: list[str] = Field(min_length=1)
    probe_kind: Literal[
        "exit_code_probe",
        "filesystem_side_effect_probe",
        "stderr_probe",
        "stdout_probe",
    ]
    probe_template_posture: Literal["local_probe_template_only_not_executed"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_probe_template(self) -> "ProgrambenchLocalCaseProbeTemplateRow":
        _ensure_sorted_unique(self.obligation_refs, field_name="probe_template.obligation_refs")
        _ensure_no_forbidden_refs(
            self.obligation_refs,
            field_name="probe_template.obligation_refs",
        )
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseProbeCommandShapeRow(_CaseExpansionBase):
    probe_ref: str
    argv_template: list[str] = Field(min_length=1)
    stdin_fixture_ref: str | None = None
    expected_stdout_ref: str | None = None
    expected_stderr_ref: str | None = None
    expected_exit_code_ref: str | None = None
    filesystem_expectation_refs: list[str] = Field(default_factory=list)
    execution_deferred_posture: Literal["probe_execution_deferred_to_later_trial"]

    @model_validator(mode="after")
    def _validate_probe_command_shape(self) -> "ProgrambenchLocalCaseProbeCommandShapeRow":
        _ensure_non_empty_trimmed(self.argv_template, field_name="argv_template")
        shell_markers = ("&&", ";", "|", "`", "$(", ">", "<")
        if len(self.argv_template) == 1 and " " in self.argv_template[0]:
            raise ValueError("probe command rows must use argv templates, not raw shell strings")
        leaked = [
            token
            for token in self.argv_template
            if any(marker in token for marker in shell_markers)
        ]
        if leaked:
            raise ValueError(f"argv_template contains shell metacharacters: {leaked}")
        optional_refs = [
            ref
            for ref in (
                self.stdin_fixture_ref,
                self.expected_stdout_ref,
                self.expected_stderr_ref,
                self.expected_exit_code_ref,
            )
            if ref is not None
        ]
        _ensure_no_forbidden_refs(optional_refs, field_name="probe command refs")
        _ensure_sorted_unique_allow_empty(
            self.filesystem_expectation_refs,
            field_name="filesystem_expectation_refs",
        )
        _ensure_no_forbidden_refs(
            self.filesystem_expectation_refs,
            field_name="filesystem_expectation_refs",
        )
        return self


class ProgrambenchLocalCaseProbeRequirementRow(_CaseExpansionBase):
    requirement_ref: str
    probe_ref: str
    obligation_refs: list[str] = Field(min_length=1)
    requirement_kind: Literal[
        "negative_probe_requirement",
        "positive_probe_requirement",
    ]
    requirement_posture: Literal["local_probe_requirement_only_not_executed"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_probe_requirement(self) -> "ProgrambenchLocalCaseProbeRequirementRow":
        _ensure_sorted_unique(
            self.obligation_refs,
            field_name="probe_requirement.obligation_refs",
        )
        _ensure_no_forbidden_refs(
            [self.probe_ref, *self.obligation_refs],
            field_name="probe_requirement refs",
        )
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseStdoutStderrExpectationRow(_CaseExpansionBase):
    expectation_ref: str
    probe_ref: str
    stream_kind: Literal["stderr", "stdout"]
    expected_artifact_ref: str
    expectation_posture: Literal["local_stream_expectation_only"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_stream_expectation(self) -> "ProgrambenchLocalCaseStdoutStderrExpectationRow":
        _ensure_no_forbidden_refs(
            [self.probe_ref, self.expected_artifact_ref],
            field_name="stream expectation refs",
        )
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseExitCodeExpectationRow(_CaseExpansionBase):
    expectation_ref: str
    probe_ref: str
    expected_exit_code: int = Field(ge=0)
    expectation_posture: Literal["local_exit_code_expectation_only"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_exit_code_expectation(self) -> "ProgrambenchLocalCaseExitCodeExpectationRow":
        _ensure_no_forbidden_refs([self.probe_ref], field_name="exit code expectation refs")
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseFilesystemSideEffectExpectationRow(_CaseExpansionBase):
    expectation_ref: str
    probe_ref: str
    expected_artifact_ref: str
    side_effect_kind: Literal["file_created", "file_not_created", "file_updated"]
    expectation_posture: Literal["local_filesystem_expectation_only_not_executed"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_fs_expectation(
        self,
    ) -> "ProgrambenchLocalCaseFilesystemSideEffectExpectationRow":
        _ensure_no_forbidden_refs(
            [self.probe_ref, self.expected_artifact_ref],
            field_name="filesystem expectation refs",
        )
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseOracleBasisRow(_CaseExpansionBase):
    oracle_basis_ref: str
    source_witness_refs: list[str] = Field(min_length=1)
    basis_kind: Literal[
        "artifact_obligation_basis",
        "behavior_obligation_basis",
        "io_observation_basis",
    ]
    support_strength: Literal["direct", "indirect"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_oracle_basis(self) -> "ProgrambenchLocalCaseOracleBasisRow":
        _ensure_sorted_unique(
            self.source_witness_refs,
            field_name="oracle_basis.source_witness_refs",
        )
        _ensure_no_forbidden_refs(
            self.source_witness_refs,
            field_name="oracle_basis.source_witness_refs",
        )
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseOracleBehaviorBoundaryRow(_CaseExpansionBase):
    behavior_boundary_ref: str
    obligation_ref: str
    oracle_basis_refs: list[str] = Field(default_factory=list)
    behavior_boundary_kind: Literal[
        "expected_behavior",
        "out_of_scope_behavior",
        "unknown_behavior",
    ]
    boundary_posture: Literal[
        "local_blueprint_expected_behavior",
        "local_blueprint_out_of_scope_behavior",
        "local_blueprint_unknown_behavior",
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_oracle_behavior_boundary(
        self,
    ) -> "ProgrambenchLocalCaseOracleBehaviorBoundaryRow":
        _ensure_sorted_unique_allow_empty(
            self.oracle_basis_refs,
            field_name="oracle_behavior_boundary.oracle_basis_refs",
        )
        if self.behavior_boundary_kind == "expected_behavior":
            if self.boundary_posture != "local_blueprint_expected_behavior":
                raise ValueError("expected behavior rows require expected behavior posture")
            if not self.oracle_basis_refs:
                raise ValueError("expected behavior rows require oracle basis refs")
        elif self.behavior_boundary_kind == "unknown_behavior":
            if self.boundary_posture != "local_blueprint_unknown_behavior":
                raise ValueError("unknown behavior rows require unknown behavior posture")
        elif self.boundary_posture != "local_blueprint_out_of_scope_behavior":
            raise ValueError("out-of-scope behavior rows require out-of-scope posture")
        _ensure_no_forbidden_refs(
            self.oracle_basis_refs,
            field_name="oracle_behavior_boundary.oracle_basis_refs",
        )
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseContaminationRow(_CaseExpansionBase):
    contamination_ref: str
    source_ref: str
    contamination_kind: Literal[
        "clean",
        "decompilation_or_source_lookup_exposure",
        "forbidden_source_exposure",
        "hidden_evidence_exposure",
        "official_evaluator_exposure",
    ]
    contamination_posture: Literal["blocked", "clean"]
    redacted_detail_note: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_contamination_row(self) -> "ProgrambenchLocalCaseContaminationRow":
        for field_name in ("redacted_detail_note", "limitation_note"):
            _ensure_no_laundered_summary(getattr(self, field_name), field_name=field_name)
        if self.contamination_kind == "clean":
            if self.contamination_posture != "clean":
                raise ValueError("clean contamination rows require clean posture")
            _ensure_no_forbidden_refs([self.source_ref], field_name="contamination source_ref")
        elif self.contamination_posture != "blocked":
            raise ValueError("non-clean contamination rows require blocked posture")
        return self


class ProgrambenchLocalCaseBlueprint(_CaseExpansionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_BLUEPRINT_SCHEMA] = Field(alias="schema")
    case_blueprint_ref: str
    case_expansion_ref: str
    candidate_case_idea_ref: str
    source_pool_manifest_ref: str
    expansion_eligibility_review_ref: str
    expansion_control_contract_ref: str
    expansion_guardrail_ref: str
    cleanroom_evidence_pack_ref: str
    probe_contract_ref: str
    oracle_boundary_ref: str
    contamination_screen_ref: str
    source_refs: list[str] = Field(min_length=1)
    case_kind: Literal[
        "cli_behavior_case",
        "filesystem_side_effect_case",
        "io_artifact_case",
    ]
    case_blueprint_status: Literal[
        "blocked_by_contamination",
        "blocked_missing_evidence",
        "blueprint_ready_for_later_lineage_review",
    ]
    expected_submission_shape: Literal[
        "python_package_entrypoint",
        "python_program_file",
    ]
    expected_input_artifact_refs: list[str] = Field(default_factory=list)
    expected_output_artifact_refs: list[str] = Field(default_factory=list)
    filesystem_side_effect_expectation_refs: list[str] = Field(default_factory=list)
    source_pool_subset_hash: str
    blueprint_hash: str
    execution_deferred_posture: Literal["execution_deferred_to_later_trial_family"]
    matrix_inclusion_deferred_posture: Literal[
        "matrix_inclusion_deferred_to_pb_case_expansion_0c_or_later"
    ]
    benchmark_score_posture: Literal["no_benchmark_score_authority_granted_by_0b"]
    baseline_comparison_posture: Literal["no_baseline_comparison_authority_granted_by_0b"]
    model_ranking_posture: Literal["no_model_ranking_claimed_by_pb_case_expansion_0b"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_blueprint(self) -> "ProgrambenchLocalCaseBlueprint":
        for field_name in (
            "source_refs",
            "expected_input_artifact_refs",
            "expected_output_artifact_refs",
            "filesystem_side_effect_expectation_refs",
        ):
            values = getattr(self, field_name)
            if field_name == "source_refs":
                _ensure_sorted_unique(values, field_name=field_name)
            else:
                _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        _ensure_hash(self.source_pool_subset_hash, field_name="source_pool_subset_hash")
        _ensure_hash(self.blueprint_hash, field_name="blueprint_hash")
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseCleanroomEvidencePack(_CaseExpansionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_CLEANROOM_EVIDENCE_PACK_SCHEMA] = Field(
        alias="schema"
    )
    cleanroom_evidence_pack_ref: str
    case_expansion_ref: str
    case_blueprint_ref: str
    source_witness_rows: list[ProgrambenchLocalCaseSourceWitnessRow] = Field(min_length=1)
    behavior_obligation_rows: list[ProgrambenchLocalCaseBehaviorObligationRow] = Field(
        min_length=1
    )
    behavior_obligation_basis_rows: list[
        ProgrambenchLocalCaseBehaviorObligationBasisRow
    ] = Field(min_length=1)
    io_observation_rows: list[ProgrambenchLocalCaseIOObservationRow] = Field(
        default_factory=list
    )
    artifact_obligation_rows: list[ProgrambenchLocalCaseArtifactObligationRow] = Field(
        default_factory=list
    )
    source_identity_hashes: list[str] = Field(min_length=1)
    evidence_pack_hash: str
    forbidden_source_exclusion_refs: list[str] = Field(default_factory=list)
    support_only_context_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_evidence_pack(self) -> "ProgrambenchLocalCaseCleanroomEvidencePack":
        witness_refs = [row.source_witness_ref for row in self.source_witness_rows]
        _ensure_sorted_unique(witness_refs, field_name="source_witness_rows")
        obligation_refs = [row.obligation_ref for row in self.behavior_obligation_rows]
        _ensure_sorted_unique(obligation_refs, field_name="behavior_obligation_rows")
        basis_obligations = [row.obligation_ref for row in self.behavior_obligation_basis_rows]
        _ensure_sorted_unique(
            basis_obligations,
            field_name="behavior_obligation_basis_rows.obligation_ref",
        )
        if set(basis_obligations) != set(obligation_refs):
            raise ValueError("every behavior obligation requires exactly one basis row")
        witness_ref_set = set(witness_refs)
        for row in self.behavior_obligation_basis_rows:
            _ensure_refs_resolve(
                row.source_witness_refs,
                witness_ref_set,
                field_name="behavior_obligation_basis.source_witness_refs",
            )
        for row in self.source_witness_rows:
            _ensure_refs_resolve(
                row.witnessed_obligation_refs,
                set(obligation_refs),
                field_name="source_witness.witnessed_obligation_refs",
            )
        for row in self.io_observation_rows:
            if row.obligation_ref not in set(obligation_refs):
                raise ValueError("io observation rows must reference behavior obligations")
            _ensure_refs_resolve(
                row.source_witness_refs,
                witness_ref_set,
                field_name="io_observation.source_witness_refs",
            )
        for row in self.artifact_obligation_rows:
            if row.obligation_ref not in set(obligation_refs):
                raise ValueError("artifact obligation rows must reference behavior obligations")
            _ensure_refs_resolve(
                row.source_witness_refs,
                witness_ref_set,
                field_name="artifact_obligation.source_witness_refs",
            )
        for value in self.source_identity_hashes:
            _ensure_hash(value, field_name="source_identity_hashes")
        _ensure_sorted_unique(self.source_identity_hashes, field_name="source_identity_hashes")
        _ensure_hash(self.evidence_pack_hash, field_name="evidence_pack_hash")
        _ensure_sorted_unique_allow_empty(
            self.forbidden_source_exclusion_refs,
            field_name="forbidden_source_exclusion_refs",
        )
        _ensure_sorted_unique_allow_empty(
            self.support_only_context_refs,
            field_name="support_only_context_refs",
        )
        _ensure_no_forbidden_refs(
            self.support_only_context_refs,
            field_name="support_only_context_refs",
        )
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseProbeContract(_CaseExpansionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_PROBE_CONTRACT_SCHEMA] = Field(
        alias="schema"
    )
    probe_contract_ref: str
    case_expansion_ref: str
    case_blueprint_ref: str
    probe_template_rows: list[ProgrambenchLocalCaseProbeTemplateRow] = Field(min_length=1)
    probe_command_shape_rows: list[ProgrambenchLocalCaseProbeCommandShapeRow] = Field(
        min_length=1
    )
    positive_probe_requirement_rows: list[ProgrambenchLocalCaseProbeRequirementRow] = Field(
        min_length=1
    )
    negative_probe_requirement_rows: list[ProgrambenchLocalCaseProbeRequirementRow] = Field(
        min_length=1
    )
    stdout_stderr_expectation_rows: list[
        ProgrambenchLocalCaseStdoutStderrExpectationRow
    ] = Field(default_factory=list)
    exit_code_expectation_rows: list[ProgrambenchLocalCaseExitCodeExpectationRow] = Field(
        min_length=1
    )
    filesystem_side_effect_expectation_rows: list[
        ProgrambenchLocalCaseFilesystemSideEffectExpectationRow
    ] = Field(default_factory=list)
    command_execution_posture: Literal["no_command_execution_authority_granted_by_0b"]
    probe_execution_deferred_posture: Literal["probe_execution_deferred_to_later_trial"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_probe_contract(self) -> "ProgrambenchLocalCaseProbeContract":
        probe_refs = [row.probe_ref for row in self.probe_template_rows]
        _ensure_sorted_unique(probe_refs, field_name="probe_template_rows")
        command_probe_refs = [row.probe_ref for row in self.probe_command_shape_rows]
        _ensure_sorted_unique(command_probe_refs, field_name="probe_command_shape_rows")
        if set(command_probe_refs) != set(probe_refs):
            raise ValueError("probe command rows must match probe template rows")
        obligation_refs = {
            obligation_ref
            for row in self.probe_template_rows
            for obligation_ref in row.obligation_refs
        }
        for rows, field_name, requirement_kind in (
            (
                self.positive_probe_requirement_rows,
                "positive_probe_requirement_rows",
                "positive_probe_requirement",
            ),
            (
                self.negative_probe_requirement_rows,
                "negative_probe_requirement_rows",
                "negative_probe_requirement",
            ),
        ):
            row_refs = [row.requirement_ref for row in rows]
            _ensure_sorted_unique(row_refs, field_name=field_name)
            for row in rows:
                if row.requirement_kind != requirement_kind:
                    raise ValueError(f"{field_name} contains wrong requirement kind")
                if row.probe_ref not in set(probe_refs):
                    raise ValueError(f"{field_name} must reference declared probes")
                _ensure_refs_resolve(
                    row.obligation_refs,
                    obligation_refs,
                    field_name=f"{field_name}.obligation_refs",
                )
        for rows, field_name in (
            (self.stdout_stderr_expectation_rows, "stdout_stderr_expectation_rows"),
            (self.exit_code_expectation_rows, "exit_code_expectation_rows"),
            (
                self.filesystem_side_effect_expectation_rows,
                "filesystem_side_effect_expectation_rows",
            ),
        ):
            row_refs = [row.expectation_ref for row in rows]
            _ensure_sorted_unique_allow_empty(row_refs, field_name=field_name)
            for row in rows:
                if row.probe_ref not in set(probe_refs):
                    raise ValueError(f"{field_name} must reference declared probes")
        if not self.stdout_stderr_expectation_rows and not (
            self.filesystem_side_effect_expectation_rows
        ):
            raise ValueError("probe contract requires stream or filesystem expectations")
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseOracleBoundary(_CaseExpansionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_ORACLE_BOUNDARY_SCHEMA] = Field(
        alias="schema"
    )
    oracle_boundary_ref: str
    case_expansion_ref: str
    case_blueprint_ref: str
    local_oracle_basis_rows: list[ProgrambenchLocalCaseOracleBasisRow] = Field(min_length=1)
    expected_behavior_boundary_rows: list[
        ProgrambenchLocalCaseOracleBehaviorBoundaryRow
    ] = Field(min_length=1)
    unknown_behavior_boundary_rows: list[
        ProgrambenchLocalCaseOracleBehaviorBoundaryRow
    ] = Field(default_factory=list)
    out_of_scope_behavior_rows: list[
        ProgrambenchLocalCaseOracleBehaviorBoundaryRow
    ] = Field(default_factory=list)
    oracle_boundary_scope_hash: str
    unknown_behavior_policy: Literal["preserve_unknown_behavior_as_local_gap"]
    out_of_scope_behavior_policy: Literal["exclude_from_local_oracle_claim"]
    local_oracle_not_task_truth_posture: Literal[
        "local_blueprint_oracle_only_not_official_programbench_truth"
    ]
    hidden_test_equivalence_posture: Literal["no_hidden_test_equivalence_claimed"]
    official_evaluator_equivalence_posture: Literal[
        "no_official_evaluator_equivalence_claimed"
    ]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_oracle_boundary(self) -> "ProgrambenchLocalCaseOracleBoundary":
        basis_refs = [row.oracle_basis_ref for row in self.local_oracle_basis_rows]
        _ensure_sorted_unique(basis_refs, field_name="local_oracle_basis_rows")
        basis_ref_set = set(basis_refs)
        expected_refs = [
            row.behavior_boundary_ref for row in self.expected_behavior_boundary_rows
        ]
        _ensure_sorted_unique(expected_refs, field_name="expected_behavior_boundary_rows")
        for rows, field_name, expected_kind in (
            (
                self.expected_behavior_boundary_rows,
                "expected_behavior_boundary_rows",
                "expected_behavior",
            ),
            (
                self.unknown_behavior_boundary_rows,
                "unknown_behavior_boundary_rows",
                "unknown_behavior",
            ),
            (
                self.out_of_scope_behavior_rows,
                "out_of_scope_behavior_rows",
                "out_of_scope_behavior",
            ),
        ):
            row_refs = [row.behavior_boundary_ref for row in rows]
            if field_name != "expected_behavior_boundary_rows":
                _ensure_sorted_unique_allow_empty(row_refs, field_name=field_name)
            for row in rows:
                if row.behavior_boundary_kind != expected_kind:
                    raise ValueError(f"{field_name} contains wrong behavior boundary kind")
                _ensure_refs_resolve(
                    row.oracle_basis_refs,
                    basis_ref_set,
                    field_name=f"{field_name}.oracle_basis_refs",
                )
        _ensure_hash(self.oracle_boundary_scope_hash, field_name="oracle_boundary_scope_hash")
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseContaminationScreen(_CaseExpansionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_CONTAMINATION_SCREEN_SCHEMA] = Field(
        alias="schema"
    )
    contamination_screen_ref: str
    case_expansion_ref: str
    case_blueprint_ref: str
    screened_source_refs: list[str] = Field(min_length=1)
    contamination_status: Literal[
        "blocked_by_contamination",
        "clean",
        "inconclusive_requires_review",
    ]
    contamination_rows: list[ProgrambenchLocalCaseContaminationRow] = Field(min_length=1)
    forbidden_source_exposure_refs: list[str] = Field(default_factory=list)
    hidden_evidence_exposure_refs: list[str] = Field(default_factory=list)
    official_evaluator_exposure_refs: list[str] = Field(default_factory=list)
    decompilation_or_source_lookup_exposure_refs: list[str] = Field(default_factory=list)
    redaction_policy: Literal["redacted_category_count_reason_only"]
    screen_verdict: Literal[
        "blocked_contamination_detected",
        "inconclusive_requires_review",
        "passed_cleanroom_screen",
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_contamination_screen(self) -> "ProgrambenchLocalCaseContaminationScreen":
        _ensure_sorted_unique(self.screened_source_refs, field_name="screened_source_refs")
        _ensure_no_forbidden_refs(self.screened_source_refs, field_name="screened_source_refs")
        row_refs = [row.contamination_ref for row in self.contamination_rows]
        _ensure_sorted_unique(row_refs, field_name="contamination_rows")
        row_source_refs = {row.source_ref for row in self.contamination_rows}
        if row_source_refs != set(self.screened_source_refs):
            raise ValueError("contamination rows must cover screened source refs")
        lists_by_kind = {
            "forbidden_source_exposure": self.forbidden_source_exposure_refs,
            "hidden_evidence_exposure": self.hidden_evidence_exposure_refs,
            "official_evaluator_exposure": self.official_evaluator_exposure_refs,
            "decompilation_or_source_lookup_exposure": (
                self.decompilation_or_source_lookup_exposure_refs
            ),
        }
        for field_name in (
            "forbidden_source_exposure_refs",
            "hidden_evidence_exposure_refs",
            "official_evaluator_exposure_refs",
            "decompilation_or_source_lookup_exposure_refs",
        ):
            _ensure_sorted_unique_allow_empty(getattr(self, field_name), field_name=field_name)
        for kind, refs in lists_by_kind.items():
            from_rows = {
                row.source_ref
                for row in self.contamination_rows
                if row.contamination_kind == kind
            }
            if set(refs) != from_rows:
                raise ValueError(f"{kind} refs must match contamination rows")
        has_blocked = any(row.contamination_posture == "blocked" for row in self.contamination_rows)
        if self.screen_verdict == "passed_cleanroom_screen":
            if self.contamination_status != "clean" or has_blocked:
                raise ValueError("passed contamination screens require clean rows and status")
        elif self.contamination_status == "clean":
            raise ValueError("clean contamination status requires passed screen verdict")
        _ensure_no_laundered_summary(self.limitation_note, field_name="limitation_note")
        return self


def validate_pb_case_expansion_0a_bundle(
    *,
    matrix_family_closeout: ProgrambenchLocalCaseMatrixFamilyCloseoutAlignment,
    expansion_request: ProgrambenchLocalCaseExpansionRequest,
    source_pool_manifest: ProgrambenchLocalCaseSourcePoolManifest,
    eligibility_review: ProgrambenchLocalCaseExpansionEligibilityReview,
    control_contract: ProgrambenchLocalCaseExpansionControlContract,
    non_authority_guardrail: ProgrambenchLocalCaseExpansionNonAuthorityGuardrail,
) -> None:
    if matrix_family_closeout.closed_family_ref != "PB-MATRIX-0":
        raise ValueError("case expansion requires released PB-MATRIX-0 closeout")
    if matrix_family_closeout.future_family_authority_posture != (
        "no_future_family_authority_granted_by_pb_matrix_0c"
    ):
        raise ValueError("PB-MATRIX-0 closeout cannot grant family authority")

    if source_pool_manifest.case_expansion_ref != expansion_request.case_expansion_ref:
        raise ValueError("source pool manifest must reference case expansion request")
    if expansion_request.source_pool_manifest_ref != (
        source_pool_manifest.source_pool_manifest_ref
    ):
        raise ValueError("expansion request must reference source pool manifest")
    if eligibility_review.case_expansion_ref != expansion_request.case_expansion_ref:
        raise ValueError("eligibility review must reference case expansion request")
    if expansion_request.expansion_eligibility_review_ref != (
        eligibility_review.expansion_eligibility_review_ref
    ):
        raise ValueError("expansion request must reference eligibility review")
    if control_contract.case_expansion_ref != expansion_request.case_expansion_ref:
        raise ValueError("control contract must reference case expansion request")
    if expansion_request.expansion_control_contract_ref != (
        control_contract.expansion_control_contract_ref
    ):
        raise ValueError("expansion request must reference control contract")
    if expansion_request.case_expansion_ref not in non_authority_guardrail.case_expansion_refs:
        raise ValueError("guardrail must reference case expansion request")

    manifest_candidate_refs = [
        row.candidate_case_idea_ref for row in source_pool_manifest.candidate_case_idea_rows
    ]
    if expansion_request.candidate_case_idea_refs != manifest_candidate_refs:
        raise ValueError("expansion request candidate refs must match source pool candidates")
    if expansion_request.requested_case_count != len(
        eligibility_review.eligible_candidate_case_idea_refs
    ):
        raise ValueError("requested case count must equal eligible candidate count")
    if expansion_request.requested_case_count > expansion_request.expansion_max_case_count:
        raise ValueError("eligible candidate count cannot exceed expansion max case count")

    eligibility_candidate_refs = {
        row.candidate_case_idea_ref for row in eligibility_review.candidate_eligibility_rows
    }
    if set(manifest_candidate_refs) != eligibility_candidate_refs:
        missing = sorted(set(manifest_candidate_refs) - eligibility_candidate_refs)
        extra = sorted(eligibility_candidate_refs - set(manifest_candidate_refs))
        raise ValueError(
            "eligibility rows must cover every candidate case idea; "
            f"missing={missing}, extra={extra}"
        )
    eligible_refs = set(eligibility_review.eligible_candidate_case_idea_refs)
    candidate_by_ref = {
        row.candidate_case_idea_ref: row
        for row in source_pool_manifest.candidate_case_idea_rows
    }
    for candidate_ref in eligible_refs:
        row = candidate_by_ref[candidate_ref]
        if row.eligibility_claim != "eligible_for_later_blueprint_review":
            raise ValueError("eligible review refs must match candidate eligibility claims")
        if row.existing_case_lineage_overlap_refs and row.novelty_or_duplication_posture != (
            "duplicate_allowed_for_regression_or_smoke"
        ):
            raise ValueError(
                "eligible duplicate case ideas require explicit regression/smoke rationale"
            )
    allowed_sources = set(source_pool_manifest.allowed_source_refs)
    for row in source_pool_manifest.candidate_case_idea_rows:
        if row.candidate_case_idea_ref not in eligible_refs:
            continue
        if not set(row.source_refs) & allowed_sources:
            raise ValueError("eligible candidate case ideas require allowed source witness")

    if non_authority_guardrail.expansion_guardrail_ref not in (
        eligibility_review.non_authority_guardrail_refs
    ):
        raise ValueError("eligibility review must release case expansion guardrail")
    if (
        matrix_family_closeout.matrix_family_closeout_ref
        not in eligibility_review.released_family_closeout_refs
    ):
        raise ValueError("eligibility review must cite released PB-MATRIX-0 closeout")
    if expansion_request.representativeness_posture != (
        "not_representative_benchmark_sample"
    ):
        raise ValueError("case expansion request must deny benchmark representativeness")
    if non_authority_guardrail.benchmark_truth_posture != "not_benchmark_truth":
        raise ValueError("case expansion guardrail must deny benchmark truth")


def validate_pb_case_expansion_0b_blueprint_bundle(
    *,
    expansion_request: ProgrambenchLocalCaseExpansionRequest,
    source_pool_manifest: ProgrambenchLocalCaseSourcePoolManifest,
    eligibility_review: ProgrambenchLocalCaseExpansionEligibilityReview,
    control_contract: ProgrambenchLocalCaseExpansionControlContract,
    non_authority_guardrail: ProgrambenchLocalCaseExpansionNonAuthorityGuardrail,
    case_blueprint: ProgrambenchLocalCaseBlueprint,
    cleanroom_evidence_pack: ProgrambenchLocalCaseCleanroomEvidencePack,
    probe_contract: ProgrambenchLocalCaseProbeContract,
    oracle_boundary: ProgrambenchLocalCaseOracleBoundary,
    contamination_screen: ProgrambenchLocalCaseContaminationScreen,
) -> None:
    if case_blueprint.case_expansion_ref != expansion_request.case_expansion_ref:
        raise ValueError("case blueprint must reference released A request")
    if case_blueprint.source_pool_manifest_ref != source_pool_manifest.source_pool_manifest_ref:
        raise ValueError("case blueprint must reference released A source pool manifest")
    if case_blueprint.expansion_eligibility_review_ref != (
        eligibility_review.expansion_eligibility_review_ref
    ):
        raise ValueError("case blueprint must reference released A eligibility review")
    if case_blueprint.expansion_control_contract_ref != (
        control_contract.expansion_control_contract_ref
    ):
        raise ValueError("case blueprint must reference released A control contract")
    if case_blueprint.expansion_guardrail_ref != non_authority_guardrail.expansion_guardrail_ref:
        raise ValueError("case blueprint must reference released A guardrail")

    for artifact in (
        cleanroom_evidence_pack,
        probe_contract,
        oracle_boundary,
        contamination_screen,
    ):
        if artifact.case_expansion_ref != expansion_request.case_expansion_ref:
            raise ValueError("PB-CASE-EXPANSION-0-B artifacts must share case_expansion_ref")
        if artifact.case_blueprint_ref != case_blueprint.case_blueprint_ref:
            raise ValueError("PB-CASE-EXPANSION-0-B artifacts must share case_blueprint_ref")

    if case_blueprint.cleanroom_evidence_pack_ref != (
        cleanroom_evidence_pack.cleanroom_evidence_pack_ref
    ):
        raise ValueError("case blueprint must reference cleanroom evidence pack")
    if case_blueprint.probe_contract_ref != probe_contract.probe_contract_ref:
        raise ValueError("case blueprint must reference probe contract")
    if case_blueprint.oracle_boundary_ref != oracle_boundary.oracle_boundary_ref:
        raise ValueError("case blueprint must reference oracle boundary")
    if case_blueprint.contamination_screen_ref != contamination_screen.contamination_screen_ref:
        raise ValueError("case blueprint must reference contamination screen")

    candidate_by_ref = {
        row.candidate_case_idea_ref: row
        for row in source_pool_manifest.candidate_case_idea_rows
    }
    if case_blueprint.candidate_case_idea_ref not in candidate_by_ref:
        raise ValueError("case blueprint candidate must exist in released A manifest")
    candidate = candidate_by_ref[case_blueprint.candidate_case_idea_ref]
    if case_blueprint.candidate_case_idea_ref not in (
        eligibility_review.eligible_candidate_case_idea_refs
    ):
        raise ValueError("case blueprint cannot target an A-blocked candidate")
    if candidate.eligibility_claim != "eligible_for_later_blueprint_review":
        raise ValueError("case blueprint candidate must carry eligible A claim")

    allowed_sources = set(source_pool_manifest.allowed_source_refs)
    blueprint_sources = set(case_blueprint.source_refs)
    if not blueprint_sources.issubset(allowed_sources):
        raise ValueError("case blueprint source refs must be subset of A-allowed sources")
    if not blueprint_sources.issubset(set(candidate.source_refs)):
        raise ValueError("case blueprint source refs must be subset of candidate sources")

    evidence_sources = {
        source_ref
        for row in cleanroom_evidence_pack.source_witness_rows
        for source_ref in row.source_refs
    }
    if evidence_sources != blueprint_sources:
        raise ValueError("evidence source witnesses must match blueprint sources")
    source_hash_by_ref = {
        row.source_ref: row.source_identity_hash
        for row in source_pool_manifest.source_pool_rows
        if row.source_ref in blueprint_sources
    }
    if set(cleanroom_evidence_pack.source_identity_hashes) != set(source_hash_by_ref.values()):
        raise ValueError("evidence pack source hashes must match A source identity hashes")

    obligation_refs = {
        row.obligation_ref for row in cleanroom_evidence_pack.behavior_obligation_rows
    }
    probe_obligations = {
        obligation_ref
        for row in probe_contract.probe_template_rows
        for obligation_ref in row.obligation_refs
    }
    if not probe_obligations.issubset(obligation_refs):
        raise ValueError("probe contract obligations must be declared in evidence pack")

    oracle_expected = {
        row.obligation_ref for row in oracle_boundary.expected_behavior_boundary_rows
    }
    if not oracle_expected.issubset(obligation_refs):
        raise ValueError("oracle expected behavior must be declared in evidence pack")
    if not oracle_expected:
        raise ValueError("oracle boundary requires expected behavior rows")

    if contamination_screen.screen_verdict != "passed_cleanroom_screen":
        raise ValueError("B lineage candidates require clean contamination screen")
    if contamination_screen.contamination_status != "clean":
        raise ValueError("B lineage candidates require clean contamination status")
    if set(contamination_screen.screened_source_refs) != blueprint_sources:
        raise ValueError("contamination screen must cover blueprint sources")

    if control_contract.execution_deferred_control_ref != "control:execution-deferred":
        raise ValueError("B requires A execution-deferred control")
    if non_authority_guardrail.benchmark_truth_posture != "not_benchmark_truth":
        raise ValueError("B requires A benchmark truth denial")
    if case_blueprint.benchmark_score_posture != "no_benchmark_score_authority_granted_by_0b":
        raise ValueError("case blueprint cannot grant scoring authority")
    if probe_contract.command_execution_posture != "no_command_execution_authority_granted_by_0b":
        raise ValueError("probe contract cannot grant command execution authority")
    if oracle_boundary.benchmark_truth_posture != "not_benchmark_truth":
        raise ValueError("oracle boundary must deny benchmark truth")
