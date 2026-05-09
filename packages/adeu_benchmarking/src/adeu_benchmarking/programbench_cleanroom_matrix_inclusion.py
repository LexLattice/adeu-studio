from __future__ import annotations

import re
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .programbench_cleanroom_case_expansion import (
    ProgrambenchLocalCaseExpansionFamilyCloseoutAlignment,
    ProgrambenchLocalCaseExpansionReadinessSummary,
    ProgrambenchLocalCaseLineageRegistration,
    ProgrambenchLocalCaseMatrixCandidateHandoff,
)
from .programbench_cleanroom_matrix import ProgrambenchLocalCaseMatrixFamilyCloseoutAlignment

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_REQUEST_SCHEMA = (
    "programbench_local_matrix_inclusion_request@1"
)
PROGRAMBENCH_LOCAL_MATRIX_CANDIDATE_INTAKE_SCHEMA = (
    "programbench_local_matrix_candidate_intake@1"
)
PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_ELIGIBILITY_REVIEW_SCHEMA = (
    "programbench_local_matrix_inclusion_eligibility_review@1"
)
PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_CONTROL_CONTRACT_SCHEMA = (
    "programbench_local_matrix_inclusion_control_contract@1"
)
PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_NON_AUTHORITY_GUARDRAIL_SCHEMA = (
    "programbench_local_matrix_inclusion_non_authority_guardrail@1"
)

PROGRAMBENCH_LOCAL_MATRIX_AMENDMENT_PLAN_SCHEMA = (
    "programbench_local_matrix_amendment_plan@1"
)
PROGRAMBENCH_LOCAL_MATRIX_CASE_DELTA_MANIFEST_SCHEMA = (
    "programbench_local_matrix_case_delta_manifest@1"
)
PROGRAMBENCH_LOCAL_MATRIX_COMPARABILITY_DELTA_REVIEW_SCHEMA = (
    "programbench_local_matrix_comparability_delta_review@1"
)
PROGRAMBENCH_LOCAL_MATRIX_CONTAMINATION_DELTA_REVIEW_SCHEMA = (
    "programbench_local_matrix_contamination_delta_review@1"
)
PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_DECISION_RECORD_SCHEMA = (
    "programbench_local_matrix_inclusion_decision_record@1"
)
PROGRAMBENCH_LOCAL_MATRIX_REVISION_REGISTRATION_SCHEMA = (
    "programbench_local_matrix_revision_registration@1"
)
PROGRAMBENCH_LOCAL_MATRIX_REVISION_READINESS_SUMMARY_SCHEMA = (
    "programbench_local_matrix_revision_readiness_summary@1"
)
PROGRAMBENCH_LOCAL_MATRIX_POST_INCLUSION_HANDOFF_SCHEMA = (
    "programbench_local_matrix_post_inclusion_handoff@1"
)
PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "programbench_local_matrix_inclusion_family_closeout_alignment@1"
)

PB_MATRIX_INCLUSION_0A_ARTIFACT_KINDS = {
    PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_REQUEST_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_CANDIDATE_INTAKE_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_ELIGIBILITY_REVIEW_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_CONTROL_CONTRACT_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
}
PB_MATRIX_INCLUSION_0B_ARTIFACT_KINDS = {
    PROGRAMBENCH_LOCAL_MATRIX_AMENDMENT_PLAN_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_CASE_DELTA_MANIFEST_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_COMPARABILITY_DELTA_REVIEW_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_CONTAMINATION_DELTA_REVIEW_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_DECISION_RECORD_SCHEMA,
}
PB_MATRIX_INCLUSION_0C_ARTIFACT_KINDS = {
    PROGRAMBENCH_LOCAL_MATRIX_REVISION_REGISTRATION_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_REVISION_READINESS_SUMMARY_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_POST_INCLUSION_HANDOFF_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
}
PB_MATRIX_INCLUSION_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS = (
    PB_MATRIX_INCLUSION_0B_ARTIFACT_KINDS | PB_MATRIX_INCLUSION_0C_ARTIFACT_KINDS
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
_SOFT_SCORING_LANGUAGE_MARKERS = (
    "baseline comparison",
    "baseline delta",
    "baseline improvement",
    "benchmark score",
    "benchmark-representative",
    "benchmark-like",
    "expected score",
    "expected to pass",
    "leaderboard",
    "likely pass",
    "model advantage",
    "model ranking",
    "pass rate",
    "representative benchmark",
    "score improvement",
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
        ref
        for ref in values
        if any(marker in ref.lower() for marker in _FORBIDDEN_REF_MARKERS)
    )
    if leaked:
        raise ValueError(f"{field_name} contains forbidden matrix-inclusion refs: {leaked}")


def _ensure_no_soft_scoring_language(value: str, *, field_name: str) -> None:
    lowered = value.lower()
    leaked = [marker for marker in _SOFT_SCORING_LANGUAGE_MARKERS if marker in lowered]
    if leaked:
        raise ValueError(
            f"{field_name} contains benchmark-like scoring or ranking language: {leaked}"
        )


class _MatrixInclusionBase(BaseModel):
    model_config = MODEL_CONFIG


class ProgrambenchLocalMatrixInclusionSelectionRationaleRow(_MatrixInclusionBase):
    selection_rationale_ref: str
    rationale_kind: Literal[
        "eligible_lineage_ready",
        "local_matrix_membership_accounting",
        "local_regression_membership_update",
        "local_smoke_membership_update",
    ]
    candidate_case_lineage_refs: list[str] = Field(min_length=1)
    rationale_scope_posture: Literal["local_matrix_inclusion_only_not_quality_selection"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_rationale(
        self,
    ) -> "ProgrambenchLocalMatrixInclusionSelectionRationaleRow":
        _ensure_sorted_unique(
            self.candidate_case_lineage_refs,
            field_name="candidate_case_lineage_refs",
        )
        _ensure_no_forbidden_refs(
            self.candidate_case_lineage_refs,
            field_name="candidate_case_lineage_refs",
        )
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalMatrixInclusionCandidateRow(_MatrixInclusionBase):
    candidate_case_lineage_ref: str
    lineage_registration_ref: str
    readiness_summary_ref: str
    handoff_pressure_ref: str
    case_lineage_hash: str
    source_boundary_hash: str
    probe_contract_hash: str
    oracle_boundary_hash: str
    contamination_screen_hash: str
    expansion_family_closeout_ref: str
    prior_matrix_membership_status: Literal[
        "absent_from_base_matrix",
        "present_in_base_matrix",
    ]
    duplicate_case_refs: list[str] = Field(default_factory=list)
    dedupe_basis_refs: list[str] = Field(default_factory=list)
    dedupe_status: Literal[
        "no_duplicate_detected",
        "duplicate_allowed_for_regression_or_smoke",
        "duplicate_blocked_existing_member",
        "replacement_or_update_explicit",
    ]
    duplicate_of_case_lineage_refs: list[str] = Field(default_factory=list)
    duplicate_allowed_posture: Literal[
        "not_applicable_no_duplicate",
        "duplicate_allowed_for_regression_or_smoke",
        "duplicate_blocked_without_replacement_or_update",
        "replacement_or_update_declared",
    ]
    candidate_origin_posture: Literal["released_case_expansion_lineage"]
    case_readiness_posture: Literal[
        "blocked",
        "deferred",
        "ready_for_later_matrix_candidate_handoff",
    ]
    contamination_posture: Literal["clean", "contaminated"]
    matrix_candidate_status: Literal[
        "blocked_by_contamination",
        "blocked_by_duplicate_existing_member",
        "eligible_for_later_matrix_amendment_review",
        "ineligible_not_ready",
    ]
    candidate_intake_status: Literal[
        "blocked",
        "recorded_for_eligibility_review",
    ]
    intake_blocker_refs: list[str] = Field(default_factory=list)
    intake_warning_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_candidate_row(self) -> "ProgrambenchLocalMatrixInclusionCandidateRow":
        for field_name in (
            "case_lineage_hash",
            "source_boundary_hash",
            "probe_contract_hash",
            "oracle_boundary_hash",
            "contamination_screen_hash",
        ):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        for field_name in (
            "duplicate_case_refs",
            "dedupe_basis_refs",
            "duplicate_of_case_lineage_refs",
            "intake_blocker_refs",
            "intake_warning_refs",
        ):
            values = getattr(self, field_name)
            _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        _ensure_no_forbidden_refs(
            [
                self.candidate_case_lineage_ref,
                self.lineage_registration_ref,
                self.readiness_summary_ref,
                self.handoff_pressure_ref,
                self.expansion_family_closeout_ref,
            ],
            field_name="matrix inclusion candidate refs",
        )
        if self.prior_matrix_membership_status == "present_in_base_matrix":
            if self.dedupe_status not in {
                "duplicate_allowed_for_regression_or_smoke",
                "replacement_or_update_explicit",
            }:
                raise ValueError(
                    "existing base matrix members require replacement/update or "
                    "allowed duplicate posture"
                )
            if self.duplicate_allowed_posture not in {
                "duplicate_allowed_for_regression_or_smoke",
                "replacement_or_update_declared",
            }:
                raise ValueError(
                    "existing base matrix members require explicit duplicate allowance"
                )
        if self.matrix_candidate_status == "eligible_for_later_matrix_amendment_review":
            if self.case_readiness_posture != "ready_for_later_matrix_candidate_handoff":
                raise ValueError("eligible matrix inclusion candidates must be ready")
            if self.contamination_posture != "clean":
                raise ValueError("eligible matrix inclusion candidates must be clean")
            if self.candidate_intake_status != "recorded_for_eligibility_review":
                raise ValueError("eligible candidates must be recorded for eligibility review")
            if self.intake_blocker_refs:
                raise ValueError("eligible candidates cannot carry intake blockers")
        else:
            if not self.intake_blocker_refs:
                raise ValueError("blocked matrix inclusion candidates require blocker refs")
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalMatrixInclusionEligibilityRow(_MatrixInclusionBase):
    eligibility_row_ref: str
    candidate_case_lineage_ref: str
    eligibility_posture: Literal[
        "blocked_by_contamination",
        "blocked_by_duplicate_existing_member",
        "blocked_by_missing_probe_or_oracle_coverage",
        "blocked_by_missing_released_lineage",
        "blocked_by_missing_handoff_pressure",
        "deferred",
        "eligible_for_later_matrix_amendment_review",
    ]
    source_candidate_row_ref: str
    blocker_refs: list[str] = Field(default_factory=list)
    warning_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_eligibility_row(self) -> "ProgrambenchLocalMatrixInclusionEligibilityRow":
        for field_name in ("blocker_refs", "warning_refs"):
            values = getattr(self, field_name)
            _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        _ensure_no_forbidden_refs(
            [self.candidate_case_lineage_ref, self.source_candidate_row_ref],
            field_name="matrix inclusion eligibility refs",
        )
        if self.eligibility_posture == "eligible_for_later_matrix_amendment_review":
            if self.blocker_refs:
                raise ValueError("eligible matrix inclusion rows cannot carry blockers")
        elif self.eligibility_posture != "deferred" and not self.blocker_refs:
            raise ValueError("blocked matrix inclusion rows require blocker refs")
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalMatrixInclusionForbiddenAuthorityRow(_MatrixInclusionBase):
    forbidden_authority_ref: str
    authority_kind: Literal[
        "baseline_comparison",
        "batch_execution",
        "benchmark_score",
        "benchmark_truth",
        "candidate_materialization",
        "direct_matrix_inclusion",
        "future_family_selection",
        "hidden_test_inference",
        "inclusion_decision",
        "matrix_amendment_plan",
        "matrix_revision_registration",
        "matrix_summary",
        "model_ranking",
        "official_programbench_participation",
        "official_submission",
        "probe_execution",
        "result_projection",
    ]
    forbiddance_posture: Literal["forbidden_by_pb_matrix_inclusion_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_forbidden_row(
        self,
    ) -> "ProgrambenchLocalMatrixInclusionForbiddenAuthorityRow":
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalMatrixInclusionRequest(_MatrixInclusionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_REQUEST_SCHEMA] = Field(
        alias="schema"
    )
    matrix_inclusion_request_ref: str
    base_matrix_ref: str
    base_matrix_revision_ref: str
    base_matrix_revision_hash: str
    target_matrix_revision_candidate_ref: str
    target_matrix_revision_candidate_hash: str
    prior_membership_manifest_hash: str
    proposed_membership_manifest_hash: str
    revision_delta_hash: str
    case_expansion_ref: str
    case_expansion_readiness_summary_ref: str
    case_matrix_candidate_handoff_ref: str
    requested_case_lineage_refs: list[str] = Field(min_length=1)
    matrix_inclusion_horizon: Literal[
        "local_matrix_membership_revision",
        "local_regression_matrix_membership_update",
        "local_smoke_matrix_membership_update",
    ]
    matrix_revision_horizon: Literal["local_accounting_revision_only"]
    matrix_max_added_case_count: int = Field(ge=1)
    selection_rationale_rows: list[ProgrambenchLocalMatrixInclusionSelectionRationaleRow] = Field(
        min_length=1
    )
    representativeness_posture: Literal["not_representative_benchmark_sample"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    execution_authority_posture: Literal[
        "no_execution_authority_granted_by_pb_matrix_inclusion_0a"
    ]
    result_projection_authority_posture: Literal[
        "no_result_projection_authority_granted_by_pb_matrix_inclusion_0a"
    ]
    future_family_selection_posture: Literal[
        "no_future_family_selection_authority_granted_by_pb_matrix_inclusion_0a"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_request(self) -> "ProgrambenchLocalMatrixInclusionRequest":
        for field_name in (
            "base_matrix_revision_hash",
            "target_matrix_revision_candidate_hash",
            "prior_membership_manifest_hash",
            "proposed_membership_manifest_hash",
            "revision_delta_hash",
        ):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        _ensure_sorted_unique(
            self.requested_case_lineage_refs,
            field_name="requested_case_lineage_refs",
        )
        _ensure_no_forbidden_refs(
            self.requested_case_lineage_refs,
            field_name="requested_case_lineage_refs",
        )
        if len(self.requested_case_lineage_refs) > self.matrix_max_added_case_count:
            raise ValueError("requested case lineage count cannot exceed matrix max added count")
        rationale_refs = [
            row.selection_rationale_ref for row in self.selection_rationale_rows
        ]
        _ensure_sorted_unique(rationale_refs, field_name="selection_rationale_rows")
        rationale_case_refs = set().union(
            *(row.candidate_case_lineage_refs for row in self.selection_rationale_rows)
        )
        if not set(self.requested_case_lineage_refs).issubset(rationale_case_refs):
            raise ValueError("requested case lineages must be covered by rationale rows")
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalMatrixCandidateIntake(_MatrixInclusionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_MATRIX_CANDIDATE_INTAKE_SCHEMA] = Field(
        alias="schema"
    )
    matrix_candidate_intake_ref: str
    matrix_inclusion_request_ref: str
    candidate_case_rows: list[ProgrambenchLocalMatrixInclusionCandidateRow] = Field(
        min_length=1
    )
    limitation_note: str

    @model_validator(mode="after")
    def _validate_intake(self) -> "ProgrambenchLocalMatrixCandidateIntake":
        candidate_refs = [row.candidate_case_lineage_ref for row in self.candidate_case_rows]
        _ensure_sorted_unique(candidate_refs, field_name="candidate_case_rows")
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalMatrixInclusionEligibilityReview(_MatrixInclusionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_ELIGIBILITY_REVIEW_SCHEMA] = (
        Field(alias="schema")
    )
    matrix_inclusion_eligibility_review_ref: str
    matrix_inclusion_request_ref: str
    matrix_candidate_intake_ref: str
    eligible_case_lineage_refs: list[str] = Field(default_factory=list)
    blocked_case_lineage_refs: list[str] = Field(default_factory=list)
    deferred_case_lineage_refs: list[str] = Field(default_factory=list)
    eligibility_row_refs: list[str] = Field(min_length=1)
    eligibility_rows: list[ProgrambenchLocalMatrixInclusionEligibilityRow] = Field(
        min_length=1
    )
    eligibility_status: Literal[
        "blocked",
        "eligible_for_later_matrix_amendment_review",
        "open_with_deferred_candidates",
    ]
    blocker_refs: list[str] = Field(default_factory=list)
    warning_refs: list[str] = Field(default_factory=list)
    cleanroom_boundary_status: Literal["clean", "blocked"]
    probe_oracle_coverage_status: Literal["complete", "missing_required_coverage"]
    contamination_status: Literal["clean", "contaminated"]
    dedupe_status: Literal[
        "all_candidates_unique_or_allowed",
        "blocked_by_duplicate_existing_member",
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_review(self) -> "ProgrambenchLocalMatrixInclusionEligibilityReview":
        row_refs = [row.eligibility_row_ref for row in self.eligibility_rows]
        _ensure_sorted_unique(row_refs, field_name="eligibility_rows")
        if self.eligibility_row_refs != row_refs:
            raise ValueError("eligibility_row_refs must match eligibility rows")
        for field_name in (
            "eligible_case_lineage_refs",
            "blocked_case_lineage_refs",
            "deferred_case_lineage_refs",
            "blocker_refs",
            "warning_refs",
        ):
            values = getattr(self, field_name)
            _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        lineage_sets = [
            set(self.eligible_case_lineage_refs),
            set(self.blocked_case_lineage_refs),
            set(self.deferred_case_lineage_refs),
        ]
        if sum(len(values) for values in lineage_sets) != len(set().union(*lineage_sets)):
            raise ValueError("eligible, blocked, and deferred lineage refs must be disjoint")
        eligible_from_rows = {
            row.candidate_case_lineage_ref
            for row in self.eligibility_rows
            if row.eligibility_posture == "eligible_for_later_matrix_amendment_review"
        }
        if set(self.eligible_case_lineage_refs) != eligible_from_rows:
            raise ValueError("eligible_case_lineage_refs must match eligible rows")
        blocked_from_rows = {
            row.candidate_case_lineage_ref
            for row in self.eligibility_rows
            if row.eligibility_posture.startswith("blocked_by_")
        }
        if set(self.blocked_case_lineage_refs) != blocked_from_rows:
            raise ValueError("blocked_case_lineage_refs must match blocked rows")
        deferred_from_rows = {
            row.candidate_case_lineage_ref
            for row in self.eligibility_rows
            if row.eligibility_posture == "deferred"
        }
        if set(self.deferred_case_lineage_refs) != deferred_from_rows:
            raise ValueError("deferred_case_lineage_refs must match deferred rows")
        if self.eligibility_status == "eligible_for_later_matrix_amendment_review":
            if not self.eligible_case_lineage_refs:
                raise ValueError("eligible status requires eligible case lineages")
            if self.blocker_refs:
                raise ValueError("eligible status cannot carry blockers")
            if self.cleanroom_boundary_status != "clean":
                raise ValueError("eligible status requires clean boundary")
            if self.probe_oracle_coverage_status != "complete":
                raise ValueError("eligible status requires probe/oracle coverage")
            if self.contamination_status != "clean":
                raise ValueError("eligible status requires clean contamination")
            if self.dedupe_status != "all_candidates_unique_or_allowed":
                raise ValueError("eligible status requires dedupe closure")
        elif not self.blocker_refs and self.eligibility_status == "blocked":
            raise ValueError("blocked matrix inclusion review requires blockers")
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalMatrixInclusionControlContract(_MatrixInclusionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_CONTROL_CONTRACT_SCHEMA] = (
        Field(alias="schema")
    )
    matrix_inclusion_control_contract_ref: str
    matrix_inclusion_request_ref: str
    matrix_horizon: Literal[
        "local_matrix_membership_revision",
        "local_regression_matrix_membership_update",
        "local_smoke_matrix_membership_update",
    ]
    matrix_revision_scope_posture: Literal["local_accounting_revision_only"]
    representativeness_posture: Literal["not_representative_benchmark_sample"]
    inventory_count_posture: Literal["local_membership_accounting_only"]
    benchmark_denominator_posture: Literal["not_benchmark_denominator"]
    baseline_comparison_authority_posture: Literal["no_baseline_comparison_authority"]
    worker_profile_continuity_posture: Literal[
        "unchanged",
        "changed_non_comparable_local_accounting_only",
    ]
    model_profile_continuity_posture: Literal[
        "unchanged",
        "changed_non_comparable_local_accounting_only",
    ]
    tool_policy_continuity_posture: Literal[
        "unchanged",
        "changed_non_comparable_local_accounting_only",
    ]
    probe_basis_continuity_posture: Literal[
        "unchanged",
        "changed_non_comparable_local_accounting_only",
    ]
    sandbox_write_scope_continuity_posture: Literal[
        "unchanged",
        "changed_non_comparable_local_accounting_only",
    ]
    source_visibility_continuity_posture: Literal[
        "unchanged",
        "changed_non_comparable_local_accounting_only",
    ]
    multi_profile_matrix_posture: Literal[
        "single_profile_matrix",
        "non_comparable_local_accounting_only",
    ]
    aggregate_count_posture: Literal["local_membership_accounting_only"]
    non_ranking_posture: Literal["no_model_ranking_authority"]
    non_scoring_posture: Literal["no_benchmark_scoring_authority"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_control(self) -> "ProgrambenchLocalMatrixInclusionControlContract":
        continuity_fields = (
            "worker_profile_continuity_posture",
            "model_profile_continuity_posture",
            "tool_policy_continuity_posture",
            "probe_basis_continuity_posture",
            "sandbox_write_scope_continuity_posture",
            "source_visibility_continuity_posture",
        )
        changed = [
            field_name
            for field_name in continuity_fields
            if getattr(self, field_name) != "unchanged"
        ]
        if changed and self.multi_profile_matrix_posture != (
            "non_comparable_local_accounting_only"
        ):
            raise ValueError(
                "matrix control widening requires non-comparable local accounting posture"
            )
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalMatrixInclusionNonAuthorityGuardrail(_MatrixInclusionBase):
    schema_id: Literal[
        PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_NON_AUTHORITY_GUARDRAIL_SCHEMA
    ] = Field(alias="schema")
    matrix_inclusion_guardrail_ref: str
    matrix_inclusion_request_ref: str
    forbidden_authority_rows: list[
        ProgrambenchLocalMatrixInclusionForbiddenAuthorityRow
    ] = Field(min_length=1)
    forbidden_future_artifact_kinds: list[str] = Field(min_length=1)
    matrix_amendment_deferred_posture: Literal[
        "matrix_amendment_deferred_to_pb_matrix_inclusion_0b"
    ]
    direct_inclusion_authority_posture: Literal[
        "no_direct_matrix_inclusion_authority_granted_by_pb_matrix_inclusion_0a"
    ]
    execution_authority_posture: Literal[
        "no_execution_authority_granted_by_pb_matrix_inclusion_0a"
    ]
    result_projection_authority_posture: Literal[
        "no_result_projection_authority_granted_by_pb_matrix_inclusion_0a"
    ]
    benchmark_score_authority_posture: Literal[
        "no_benchmark_score_authority_granted_by_pb_matrix_inclusion_0a"
    ]
    baseline_comparison_authority_posture: Literal[
        "no_baseline_comparison_authority_granted_by_pb_matrix_inclusion_0a"
    ]
    model_ranking_authority_posture: Literal[
        "no_model_ranking_authority_granted_by_pb_matrix_inclusion_0a"
    ]
    official_programbench_authority_posture: Literal[
        "no_official_programbench_authority_granted_by_pb_matrix_inclusion_0a"
    ]
    future_family_selection_posture: Literal[
        "no_future_family_selection_authority_granted_by_pb_matrix_inclusion_0a"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_guardrail(
        self,
    ) -> "ProgrambenchLocalMatrixInclusionNonAuthorityGuardrail":
        row_refs = [row.forbidden_authority_ref for row in self.forbidden_authority_rows]
        _ensure_sorted_unique(row_refs, field_name="forbidden_authority_rows")
        required_authorities = {
            "baseline_comparison",
            "batch_execution",
            "benchmark_score",
            "benchmark_truth",
            "candidate_materialization",
            "direct_matrix_inclusion",
            "future_family_selection",
            "hidden_test_inference",
            "inclusion_decision",
            "matrix_amendment_plan",
            "matrix_revision_registration",
            "matrix_summary",
            "model_ranking",
            "official_programbench_participation",
            "official_submission",
            "probe_execution",
            "result_projection",
        }
        observed = {row.authority_kind for row in self.forbidden_authority_rows}
        if len(observed) != len(self.forbidden_authority_rows):
            raise ValueError("forbidden_authority_rows must not duplicate authority kinds")
        missing = sorted(required_authorities - observed)
        if missing:
            raise ValueError(f"matrix inclusion guardrail missing authorities: {missing}")
        _ensure_sorted_unique(
            self.forbidden_future_artifact_kinds,
            field_name="forbidden_future_artifact_kinds",
        )
        missing_future = sorted(
            PB_MATRIX_INCLUSION_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS
            - set(self.forbidden_future_artifact_kinds)
        )
        if missing_future:
            raise ValueError(
                f"matrix inclusion guardrail missing future artifact kinds: {missing_future}"
            )
        current = sorted(
            PB_MATRIX_INCLUSION_0A_ARTIFACT_KINDS & set(self.forbidden_future_artifact_kinds)
        )
        if current:
            raise ValueError(
                f"matrix inclusion guardrail cannot forbid current A artifact kinds: {current}"
            )
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


def validate_pb_matrix_inclusion_0a_bundle(
    *,
    matrix_family_closeout: ProgrambenchLocalCaseMatrixFamilyCloseoutAlignment,
    case_expansion_family_closeout: ProgrambenchLocalCaseExpansionFamilyCloseoutAlignment,
    lineage_registration: ProgrambenchLocalCaseLineageRegistration,
    readiness_summary: ProgrambenchLocalCaseExpansionReadinessSummary,
    matrix_candidate_handoff: ProgrambenchLocalCaseMatrixCandidateHandoff,
    inclusion_request: ProgrambenchLocalMatrixInclusionRequest,
    candidate_intake: ProgrambenchLocalMatrixCandidateIntake,
    eligibility_review: ProgrambenchLocalMatrixInclusionEligibilityReview,
    control_contract: ProgrambenchLocalMatrixInclusionControlContract,
    non_authority_guardrail: ProgrambenchLocalMatrixInclusionNonAuthorityGuardrail,
) -> None:
    if matrix_family_closeout.closed_family_ref != "PB-MATRIX-0":
        raise ValueError("matrix inclusion requires released PB-MATRIX-0 closeout")
    if case_expansion_family_closeout.closed_family_ref != "PB-CASE-EXPANSION-0":
        raise ValueError(
            "matrix inclusion requires released PB-CASE-EXPANSION-0 closeout"
        )
    if matrix_family_closeout.future_family_authority_posture != (
        "no_future_family_authority_granted_by_pb_matrix_0c"
    ):
        raise ValueError("PB-MATRIX-0 closeout cannot grant family authority")
    if case_expansion_family_closeout.future_family_authority_posture != (
        "no_future_family_selection_authority_granted_by_0c"
    ):
        raise ValueError("PB-CASE-EXPANSION-0 closeout cannot grant family authority")

    if candidate_intake.matrix_inclusion_request_ref != (
        inclusion_request.matrix_inclusion_request_ref
    ):
        raise ValueError("candidate intake must reference matrix inclusion request")
    if eligibility_review.matrix_inclusion_request_ref != (
        inclusion_request.matrix_inclusion_request_ref
    ):
        raise ValueError("eligibility review must reference matrix inclusion request")
    if eligibility_review.matrix_candidate_intake_ref != (
        candidate_intake.matrix_candidate_intake_ref
    ):
        raise ValueError("eligibility review must reference candidate intake")
    if control_contract.matrix_inclusion_request_ref != (
        inclusion_request.matrix_inclusion_request_ref
    ):
        raise ValueError("control contract must reference matrix inclusion request")
    if non_authority_guardrail.matrix_inclusion_request_ref != (
        inclusion_request.matrix_inclusion_request_ref
    ):
        raise ValueError("guardrail must reference matrix inclusion request")

    if not all(
        (
            inclusion_request.base_matrix_ref,
            inclusion_request.base_matrix_revision_ref,
            inclusion_request.target_matrix_revision_candidate_ref,
        )
    ):
        raise ValueError("matrix inclusion request requires base and revision identity")
    if len(inclusion_request.requested_case_lineage_refs) != 1:
        raise ValueError(
            "PB-MATRIX-INCLUSION-0-A bundle validation accepts exactly one "
            "requested case lineage"
        )
    if len(candidate_intake.candidate_case_rows) != 1:
        raise ValueError(
            "PB-MATRIX-INCLUSION-0-A bundle validation accepts exactly one "
            "candidate intake row"
        )
    if len(eligibility_review.eligibility_rows) != 1:
        raise ValueError(
            "PB-MATRIX-INCLUSION-0-A bundle validation accepts exactly one "
            "eligibility row"
        )
    if inclusion_request.base_matrix_revision_ref == (
        inclusion_request.target_matrix_revision_candidate_ref
    ):
        raise ValueError("target matrix revision candidate must differ from base revision")

    if inclusion_request.case_expansion_ref != lineage_registration.case_expansion_ref:
        raise ValueError("inclusion request must reference case expansion lineage")
    if inclusion_request.case_expansion_readiness_summary_ref != (
        readiness_summary.case_expansion_readiness_summary_ref
    ):
        raise ValueError("inclusion request must reference expansion readiness summary")
    if inclusion_request.case_matrix_candidate_handoff_ref != (
        matrix_candidate_handoff.case_matrix_candidate_handoff_ref
    ):
        raise ValueError("inclusion request must reference matrix candidate handoff")
    if matrix_candidate_handoff.case_expansion_ref != inclusion_request.case_expansion_ref:
        raise ValueError("matrix candidate handoff must share case expansion ref")
    if matrix_candidate_handoff.case_expansion_readiness_summary_ref != (
        readiness_summary.case_expansion_readiness_summary_ref
    ):
        raise ValueError("matrix candidate handoff must reference readiness summary")

    lineage_ref = lineage_registration.registered_case_lineage_ref
    if lineage_ref not in readiness_summary.ready_case_lineage_refs:
        raise ValueError("requested lineage must be ready in expansion readiness summary")
    if lineage_ref not in matrix_candidate_handoff.ready_case_lineage_refs:
        raise ValueError("requested lineage must appear in matrix candidate handoff")
    if lineage_ref not in inclusion_request.requested_case_lineage_refs:
        raise ValueError("inclusion request must request registered case lineage")
    if lineage_registration.lineage_registration_status != (
        "registered_for_later_matrix_review"
    ):
        raise ValueError("matrix inclusion requires registered case lineage")

    row_by_lineage = {
        row.candidate_case_lineage_ref: row for row in candidate_intake.candidate_case_rows
    }
    if set(inclusion_request.requested_case_lineage_refs) - set(row_by_lineage):
        raise ValueError("candidate intake must cover every requested case lineage")
    candidate_row = row_by_lineage[lineage_ref]
    if candidate_row.lineage_registration_ref != (
        lineage_registration.case_lineage_registration_ref
    ):
        raise ValueError("candidate row must reference lineage registration")
    if candidate_row.readiness_summary_ref != (
        readiness_summary.case_expansion_readiness_summary_ref
    ):
        raise ValueError("candidate row must reference readiness summary")
    handoff_pressure_refs = {
        row.handoff_pressure_ref for row in matrix_candidate_handoff.handoff_pressure_rows
    }
    if candidate_row.handoff_pressure_ref not in handoff_pressure_refs:
        raise ValueError("candidate row must reference handoff pressure row")
    if candidate_row.case_lineage_hash != lineage_registration.registered_case_lineage_hash:
        raise ValueError("candidate row lineage hash must match lineage registration")
    if candidate_row.source_boundary_hash != lineage_registration.source_pool_subset_hash:
        raise ValueError("candidate row source boundary hash must match lineage registration")
    if candidate_row.probe_contract_hash != lineage_registration.probe_contract_hash:
        raise ValueError("candidate row probe contract hash must match lineage registration")
    if candidate_row.oracle_boundary_hash != lineage_registration.oracle_boundary_hash:
        raise ValueError("candidate row oracle boundary hash must match lineage registration")
    if candidate_row.contamination_screen_hash != (
        lineage_registration.contamination_screen_hash
    ):
        raise ValueError(
            "candidate row contamination screen hash must match lineage registration"
        )
    if candidate_row.expansion_family_closeout_ref != (
        case_expansion_family_closeout.case_expansion_family_closeout_ref
    ):
        raise ValueError("candidate row must reference case expansion family closeout")

    eligible_refs = set(eligibility_review.eligible_case_lineage_refs)
    if set(inclusion_request.requested_case_lineage_refs) != eligible_refs:
        raise ValueError("requested case lineage refs must match eligible refs")
    eligibility_case_refs = {
        row.candidate_case_lineage_ref for row in eligibility_review.eligibility_rows
    }
    candidate_case_refs = {
        row.candidate_case_lineage_ref for row in candidate_intake.candidate_case_rows
    }
    if candidate_case_refs != eligibility_case_refs:
        raise ValueError("eligibility rows must cover candidate intake rows")
    if non_authority_guardrail.direct_inclusion_authority_posture != (
        "no_direct_matrix_inclusion_authority_granted_by_pb_matrix_inclusion_0a"
    ):
        raise ValueError("A guardrail cannot grant direct matrix inclusion")
    if control_contract.benchmark_denominator_posture != "not_benchmark_denominator":
        raise ValueError("control contract must deny benchmark denominator posture")
    if control_contract.baseline_comparison_authority_posture != (
        "no_baseline_comparison_authority"
    ):
        raise ValueError("control contract must deny baseline comparison authority")
