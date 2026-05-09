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
        forbidden_source_kind = self.source_kind in {
            "decompilation_source",
            "external_repo_source",
            "hidden_test",
            "internet_lookup_source",
            "official_evaluator_source",
            "original_source",
            "postmortem_only",
        }
        if self.allowed_for_expansion:
            if forbidden_source_kind:
                raise ValueError("forbidden source kinds cannot be allowed for expansion")
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
        if forbidden_source_kind and self.derived_summary_policy != "no_derived_summary_allowed":
            raise ValueError("forbidden source rows cannot permit derived summaries")
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
            if row.source_kind
            in {
                "decompilation_source",
                "external_repo_source",
                "hidden_test",
                "internet_lookup_source",
                "official_evaluator_source",
                "original_source",
                "postmortem_only",
            }
        }
        if not forbidden_from_rows.issubset(set(self.forbidden_source_refs)):
            missing = sorted(forbidden_from_rows - set(self.forbidden_source_refs))
            raise ValueError(f"forbidden_source_refs missing forbidden source rows: {missing}")
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
        row_blockers = {
            blocker for row in self.candidate_eligibility_rows for blocker in row.blocker_refs
        }
        if not set(self.carried_blocker_refs).issubset(row_blockers):
            raise ValueError("carried blockers must resolve to eligibility row blocker refs")
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
