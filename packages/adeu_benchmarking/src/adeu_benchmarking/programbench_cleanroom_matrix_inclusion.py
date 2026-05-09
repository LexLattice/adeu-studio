from __future__ import annotations

import re
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

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
PB_MATRIX_INCLUSION_0_ARTIFACT_KINDS = (
    PB_MATRIX_INCLUSION_0A_ARTIFACT_KINDS
    | PB_MATRIX_INCLUSION_0B_ARTIFACT_KINDS
    | PB_MATRIX_INCLUSION_0C_ARTIFACT_KINDS
)
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
_FORBIDDEN_CONTENT_LANGUAGE_MARKERS = (
    "decompilation",
    "external repo",
    "external-repo",
    "hidden test",
    "hidden-test",
    "official evaluator",
    "official-evaluator",
    "original source",
    "original-source",
    "postmortem only",
    "postmortem-only",
    "source lookup",
    "source-lookup",
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


def _model_hash(value: BaseModel) -> str:
    return f"sha256:{sha256_canonical_json(value.model_dump(by_alias=True, mode='json'))}"


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


def _ensure_no_forbidden_content_language(value: str, *, field_name: str) -> None:
    lowered = value.lower()
    leaked = [
        marker for marker in _FORBIDDEN_CONTENT_LANGUAGE_MARKERS if marker in lowered
    ]
    if leaked:
        raise ValueError(
            f"{field_name} contains hidden, forbidden, or source-derived content markers: "
            f"{leaked}"
        )


def _ensure_no_soft_or_forbidden_language(value: str, *, field_name: str) -> None:
    _ensure_no_soft_scoring_language(value, field_name=field_name)
    _ensure_no_forbidden_content_language(value, field_name=field_name)


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


class ProgrambenchLocalMatrixCaseDeltaRow(_MatrixInclusionBase):
    case_delta_ref: str
    case_delta_kind: Literal[
        "added_to_revision_candidate",
        "deferred_from_revision_candidate",
        "rejected_from_revision_candidate",
    ]
    case_lineage_ref: str
    case_lineage_hash: str
    prior_matrix_membership_status: Literal[
        "absent_from_base_matrix",
        "present_in_base_matrix",
    ]
    new_matrix_membership_candidate_status: Literal[
        "planned_added",
        "planned_deferred",
        "planned_rejected",
    ]
    dedupe_status: Literal[
        "no_duplicate_detected",
        "duplicate_allowed_for_regression_or_smoke",
        "duplicate_blocked_existing_member",
        "replacement_or_update_explicit",
    ]
    delta_reason: Literal[
        "lineage_eligible",
        "dedupe_blocked",
        "contamination_blocked",
        "comparability_blocked",
        "matrix_capacity_deferred",
        "horizon_mismatch_deferred",
        "missing_readiness_refs_blocked",
    ]
    decision_basis_posture: Literal[
        "governance_accounting_reason_only_not_performance_selection"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_delta_row(self) -> "ProgrambenchLocalMatrixCaseDeltaRow":
        _ensure_hash(self.case_lineage_hash, field_name="case_lineage_hash")
        _ensure_no_forbidden_refs(
            [self.case_delta_ref, self.case_lineage_ref],
            field_name="case_delta_row_refs",
        )
        expected_status_by_kind = {
            "added_to_revision_candidate": "planned_added",
            "deferred_from_revision_candidate": "planned_deferred",
            "rejected_from_revision_candidate": "planned_rejected",
        }
        if self.new_matrix_membership_candidate_status != expected_status_by_kind[
            self.case_delta_kind
        ]:
            raise ValueError("case delta kind must match candidate membership status")
        if self.case_delta_kind == "added_to_revision_candidate":
            if self.delta_reason != "lineage_eligible":
                raise ValueError("added matrix deltas must use lineage_eligible reason")
            if self.dedupe_status == "duplicate_blocked_existing_member":
                raise ValueError("added matrix deltas cannot carry blocked dedupe status")
        elif self.delta_reason == "lineage_eligible":
            raise ValueError("non-added matrix deltas cannot use lineage_eligible reason")
        _ensure_no_soft_or_forbidden_language(
            self.limitation_note,
            field_name="limitation_note",
        )
        return self


class ProgrambenchLocalMatrixAmendmentPlan(_MatrixInclusionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_MATRIX_AMENDMENT_PLAN_SCHEMA] = Field(
        alias="schema"
    )
    matrix_amendment_plan_ref: str
    matrix_inclusion_request_ref: str
    matrix_inclusion_control_contract_ref: str
    target_matrix_ref: str
    target_matrix_revision_candidate_ref: str
    planned_added_case_lineage_refs: list[str] = Field(default_factory=list)
    planned_deferred_case_lineage_refs: list[str] = Field(default_factory=list)
    planned_rejected_case_lineage_refs: list[str] = Field(default_factory=list)
    amendment_scope_posture: Literal[
        "local_matrix_membership_accounting_only_not_revision_registration"
    ]
    execution_authority_posture: Literal[
        "no_execution_authority_granted_by_pb_matrix_inclusion_0b"
    ]
    result_projection_authority_posture: Literal[
        "no_result_projection_authority_granted_by_pb_matrix_inclusion_0b"
    ]
    benchmark_score_authority_posture: Literal[
        "no_benchmark_score_authority_granted_by_pb_matrix_inclusion_0b"
    ]
    future_family_selection_posture: Literal[
        "no_future_family_selection_authority_granted_by_pb_matrix_inclusion_0b"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_amendment_plan(self) -> "ProgrambenchLocalMatrixAmendmentPlan":
        lineage_sets = []
        for field_name in (
            "planned_added_case_lineage_refs",
            "planned_deferred_case_lineage_refs",
            "planned_rejected_case_lineage_refs",
        ):
            values = getattr(self, field_name)
            _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
            lineage_sets.append(set(values))
        if not set().union(*lineage_sets):
            raise ValueError("matrix amendment plan requires at least one planned case")
        if sum(len(values) for values in lineage_sets) != len(set().union(*lineage_sets)):
            raise ValueError("planned added, deferred, and rejected case refs must be disjoint")
        _ensure_no_forbidden_refs(
            [
                self.matrix_amendment_plan_ref,
                self.matrix_inclusion_request_ref,
                self.matrix_inclusion_control_contract_ref,
                self.target_matrix_ref,
                self.target_matrix_revision_candidate_ref,
            ],
            field_name="matrix_amendment_plan_refs",
        )
        _ensure_no_soft_or_forbidden_language(
            self.limitation_note,
            field_name="limitation_note",
        )
        return self


class ProgrambenchLocalMatrixCaseDeltaManifest(_MatrixInclusionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_MATRIX_CASE_DELTA_MANIFEST_SCHEMA] = Field(
        alias="schema"
    )
    matrix_case_delta_manifest_ref: str
    matrix_amendment_plan_ref: str
    case_delta_rows: list[ProgrambenchLocalMatrixCaseDeltaRow] = Field(min_length=1)
    delta_manifest_hash: str
    local_accounting_scope_posture: Literal["local_matrix_membership_accounting_only"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_delta_manifest(
        self,
    ) -> "ProgrambenchLocalMatrixCaseDeltaManifest":
        _ensure_hash(self.delta_manifest_hash, field_name="delta_manifest_hash")
        row_refs = [row.case_delta_ref for row in self.case_delta_rows]
        _ensure_sorted_unique(row_refs, field_name="case_delta_rows")
        lineage_refs = [row.case_lineage_ref for row in self.case_delta_rows]
        _ensure_sorted_unique(lineage_refs, field_name="case_delta_lineage_refs")
        _ensure_no_soft_or_forbidden_language(
            self.limitation_note,
            field_name="limitation_note",
        )
        return self


class ProgrambenchLocalMatrixComparabilityDeltaReview(_MatrixInclusionBase):
    schema_id: Literal[
        PROGRAMBENCH_LOCAL_MATRIX_COMPARABILITY_DELTA_REVIEW_SCHEMA
    ] = Field(alias="schema")
    matrix_comparability_delta_review_ref: str
    matrix_amendment_plan_ref: str
    matrix_case_delta_manifest_ref: str
    base_worker_profile_hash: str
    candidate_worker_profile_hash: str
    base_model_profile_hash: str
    candidate_model_profile_hash: str
    base_tool_policy_hash: str
    candidate_tool_policy_hash: str
    base_probe_basis_hash: str
    candidate_probe_basis_hash: str
    base_source_visibility_hash: str
    candidate_source_visibility_hash: str
    base_sandbox_write_scope_hash: str
    candidate_sandbox_write_scope_hash: str
    comparability_delta_hash: str
    worker_profile_delta_posture: Literal[
        "unchanged",
        "changed_non_comparable_local_accounting_only",
    ]
    model_profile_delta_posture: Literal[
        "unchanged",
        "changed_non_comparable_local_accounting_only",
    ]
    tool_policy_delta_posture: Literal[
        "unchanged",
        "changed_non_comparable_local_accounting_only",
    ]
    probe_basis_delta_posture: Literal[
        "unchanged",
        "changed_non_comparable_local_accounting_only",
    ]
    sandbox_write_scope_delta_posture: Literal[
        "unchanged",
        "changed_non_comparable_local_accounting_only",
    ]
    source_visibility_delta_posture: Literal[
        "unchanged",
        "changed_non_comparable_local_accounting_only",
    ]
    comparability_accounting_posture: Literal[
        "local_accounting_only_no_model_or_baseline_comparison"
    ]
    non_comparable_local_accounting_posture: Literal[
        "not_applicable_all_controls_unchanged",
        "changed_controls_non_comparable_local_accounting_only",
    ]
    model_ranking_authority_posture: Literal["no_model_ranking_authority"]
    baseline_comparison_authority_posture: Literal[
        "no_baseline_comparison_authority"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_comparability(
        self,
    ) -> "ProgrambenchLocalMatrixComparabilityDeltaReview":
        for field_name in (
            "base_worker_profile_hash",
            "candidate_worker_profile_hash",
            "base_model_profile_hash",
            "candidate_model_profile_hash",
            "base_tool_policy_hash",
            "candidate_tool_policy_hash",
            "base_probe_basis_hash",
            "candidate_probe_basis_hash",
            "base_source_visibility_hash",
            "candidate_source_visibility_hash",
            "base_sandbox_write_scope_hash",
            "candidate_sandbox_write_scope_hash",
            "comparability_delta_hash",
        ):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        delta_fields = (
            "worker_profile_delta_posture",
            "model_profile_delta_posture",
            "tool_policy_delta_posture",
            "probe_basis_delta_posture",
            "sandbox_write_scope_delta_posture",
            "source_visibility_delta_posture",
        )
        changed = [field for field in delta_fields if getattr(self, field) != "unchanged"]
        hash_pairs_by_delta_field = {
            "worker_profile_delta_posture": (
                self.base_worker_profile_hash,
                self.candidate_worker_profile_hash,
            ),
            "model_profile_delta_posture": (
                self.base_model_profile_hash,
                self.candidate_model_profile_hash,
            ),
            "tool_policy_delta_posture": (
                self.base_tool_policy_hash,
                self.candidate_tool_policy_hash,
            ),
            "probe_basis_delta_posture": (
                self.base_probe_basis_hash,
                self.candidate_probe_basis_hash,
            ),
            "sandbox_write_scope_delta_posture": (
                self.base_sandbox_write_scope_hash,
                self.candidate_sandbox_write_scope_hash,
            ),
            "source_visibility_delta_posture": (
                self.base_source_visibility_hash,
                self.candidate_source_visibility_hash,
            ),
        }
        for field_name, (base_hash, candidate_hash) in hash_pairs_by_delta_field.items():
            delta_posture = getattr(self, field_name)
            if delta_posture == "unchanged" and base_hash != candidate_hash:
                raise ValueError(
                    f"{field_name} cannot be unchanged when base and candidate hashes differ"
                )
            if (
                delta_posture == "changed_non_comparable_local_accounting_only"
                and base_hash == candidate_hash
            ):
                raise ValueError(
                    f"{field_name} cannot be changed when base and candidate hashes match"
                )
        if changed:
            if self.non_comparable_local_accounting_posture != (
                "changed_controls_non_comparable_local_accounting_only"
            ):
                raise ValueError(
                    "changed comparability controls require non-comparable local "
                    "accounting posture"
                )
        elif self.non_comparable_local_accounting_posture != (
            "not_applicable_all_controls_unchanged"
        ):
            raise ValueError(
                "unchanged comparability controls require not-applicable posture"
            )
        _ensure_no_soft_or_forbidden_language(
            self.limitation_note,
            field_name="limitation_note",
        )
        return self


class ProgrambenchLocalMatrixContaminationDeltaRow(_MatrixInclusionBase):
    contamination_delta_ref: str
    case_lineage_ref: str
    contamination_source_kind: Literal[
        "clean_candidate",
        "hidden_or_forbidden_exposure",
        "postmortem_only_exposure",
        "official_evaluator_derived_exposure",
        "source_derived_exposure",
        "decompilation_derived_exposure",
        "internet_derived_exposure",
        "external_repo_derived_exposure",
    ]
    contamination_delta_status: Literal["clean", "blocked"]
    redaction_posture: Literal["category_count_reason_only_no_content_detail"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_contamination_delta_row(
        self,
    ) -> "ProgrambenchLocalMatrixContaminationDeltaRow":
        _ensure_no_forbidden_refs(
            [self.contamination_delta_ref, self.case_lineage_ref],
            field_name="contamination_delta_row_refs",
        )
        if self.contamination_source_kind == "clean_candidate":
            if self.contamination_delta_status != "clean":
                raise ValueError("clean contamination rows must have clean status")
        elif self.contamination_delta_status != "blocked":
            raise ValueError("contaminating source kinds must be blocked")
        _ensure_no_soft_or_forbidden_language(
            self.limitation_note,
            field_name="limitation_note",
        )
        return self


class ProgrambenchLocalMatrixContaminationDeltaReview(_MatrixInclusionBase):
    schema_id: Literal[
        PROGRAMBENCH_LOCAL_MATRIX_CONTAMINATION_DELTA_REVIEW_SCHEMA
    ] = Field(alias="schema")
    matrix_contamination_delta_review_ref: str
    matrix_amendment_plan_ref: str
    matrix_case_delta_manifest_ref: str
    contamination_delta_rows: list[ProgrambenchLocalMatrixContaminationDeltaRow] = Field(
        min_length=1
    )
    contamination_transfer_status: Literal["clean", "blocked"]
    contamination_redaction_policy: Literal["category_count_reason_only"]
    contamination_detail_posture: Literal[
        "no_content_bearing_hidden_or_forbidden_detail"
    ]
    hidden_or_forbidden_exposure_refs: list[str] = Field(default_factory=list)
    cleanroom_boundary_status: Literal["clean", "blocked"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_contamination_review(
        self,
    ) -> "ProgrambenchLocalMatrixContaminationDeltaReview":
        row_refs = [row.contamination_delta_ref for row in self.contamination_delta_rows]
        _ensure_sorted_unique(row_refs, field_name="contamination_delta_rows")
        lineage_refs = [row.case_lineage_ref for row in self.contamination_delta_rows]
        _ensure_sorted_unique(lineage_refs, field_name="contamination_delta_lineage_refs")
        _ensure_sorted_unique_allow_empty(
            self.hidden_or_forbidden_exposure_refs,
            field_name="hidden_or_forbidden_exposure_refs",
        )
        has_blocked_row = any(
            row.contamination_delta_status == "blocked"
            for row in self.contamination_delta_rows
        )
        if self.contamination_transfer_status == "clean":
            if has_blocked_row:
                raise ValueError("clean contamination transfer cannot include blocked rows")
            if self.hidden_or_forbidden_exposure_refs:
                raise ValueError("clean contamination transfer cannot carry exposure refs")
            if self.cleanroom_boundary_status != "clean":
                raise ValueError("clean contamination transfer requires clean boundary")
        else:
            if self.cleanroom_boundary_status != "blocked":
                raise ValueError("blocked contamination transfer requires blocked boundary")
        _ensure_no_soft_or_forbidden_language(
            self.limitation_note,
            field_name="limitation_note",
        )
        return self


class ProgrambenchLocalMatrixInclusionDecisionBasisRow(_MatrixInclusionBase):
    decision_basis_ref: str
    case_lineage_ref: str
    decision_basis_kind: Literal[
        "lineage_eligible",
        "dedupe_blocked",
        "contamination_blocked",
        "comparability_blocked",
        "matrix_capacity_deferred",
        "horizon_mismatch_deferred",
        "missing_readiness_refs_blocked",
    ]
    decision_basis_posture: Literal[
        "governance_accounting_reason_only_not_performance_selection"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_decision_basis(
        self,
    ) -> "ProgrambenchLocalMatrixInclusionDecisionBasisRow":
        _ensure_no_forbidden_refs(
            [self.decision_basis_ref, self.case_lineage_ref],
            field_name="decision_basis_refs",
        )
        _ensure_no_soft_or_forbidden_language(
            self.limitation_note,
            field_name="limitation_note",
        )
        return self


class ProgrambenchLocalMatrixInclusionDecisionRecord(_MatrixInclusionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_DECISION_RECORD_SCHEMA] = (
        Field(alias="schema")
    )
    matrix_inclusion_decision_ref: str
    matrix_amendment_plan_ref: str
    matrix_case_delta_manifest_ref: str
    matrix_comparability_delta_review_ref: str
    matrix_contamination_delta_review_ref: str
    included_case_lineage_refs: list[str] = Field(default_factory=list)
    deferred_case_lineage_refs: list[str] = Field(default_factory=list)
    rejected_case_lineage_refs: list[str] = Field(default_factory=list)
    inclusion_decision_status: Literal[
        "local_accounting_membership_decision_recorded",
        "blocked_by_contamination",
        "open_with_deferred_candidates",
    ]
    decision_basis_posture: Literal[
        "governance_accounting_only_not_result_or_quality_selection"
    ]
    decision_basis_rows: list[ProgrambenchLocalMatrixInclusionDecisionBasisRow] = Field(
        min_length=1
    )
    decision_is_not_result_posture: Literal["decision_is_not_result_projection"]
    decision_is_not_quality_score_posture: Literal["decision_is_not_quality_score"]
    decision_is_not_benchmark_selection_posture: Literal[
        "decision_is_not_benchmark_selection"
    ]
    local_accounting_scope_posture: Literal["local_matrix_membership_accounting_only"]
    result_projection_authority_posture: Literal[
        "no_result_projection_authority_granted_by_pb_matrix_inclusion_0b"
    ]
    execution_authority_posture: Literal[
        "no_execution_authority_granted_by_pb_matrix_inclusion_0b"
    ]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    future_family_selection_posture: Literal[
        "no_future_family_selection_authority_granted_by_pb_matrix_inclusion_0b"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_decision_record(
        self,
    ) -> "ProgrambenchLocalMatrixInclusionDecisionRecord":
        lineage_sets = []
        for field_name in (
            "included_case_lineage_refs",
            "deferred_case_lineage_refs",
            "rejected_case_lineage_refs",
        ):
            values = getattr(self, field_name)
            _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
            lineage_sets.append(set(values))
        decided = set().union(*lineage_sets)
        if not decided:
            raise ValueError("inclusion decision requires at least one lineage decision")
        if sum(len(values) for values in lineage_sets) != len(decided):
            raise ValueError("included, deferred, and rejected lineage refs must be disjoint")
        basis_refs = [row.decision_basis_ref for row in self.decision_basis_rows]
        _ensure_sorted_unique(basis_refs, field_name="decision_basis_rows")
        basis_lineages = {row.case_lineage_ref for row in self.decision_basis_rows}
        if basis_lineages != decided:
            raise ValueError("decision basis rows must cover all decided lineage refs")
        basis_by_lineage = {
            row.case_lineage_ref: row.decision_basis_kind
            for row in self.decision_basis_rows
        }
        for case_lineage_ref in self.included_case_lineage_refs:
            if basis_by_lineage[case_lineage_ref] != "lineage_eligible":
                raise ValueError("included lineage refs require lineage_eligible basis")
        deferred_basis_kinds = {
            "horizon_mismatch_deferred",
            "matrix_capacity_deferred",
        }
        for case_lineage_ref in self.deferred_case_lineage_refs:
            if basis_by_lineage[case_lineage_ref] not in deferred_basis_kinds:
                raise ValueError("deferred lineage refs require deferred decision basis")
        rejected_basis_kinds = {
            "comparability_blocked",
            "contamination_blocked",
            "dedupe_blocked",
            "missing_readiness_refs_blocked",
        }
        for case_lineage_ref in self.rejected_case_lineage_refs:
            if basis_by_lineage[case_lineage_ref] not in rejected_basis_kinds:
                raise ValueError("rejected lineage refs require blocked decision basis")
        if self.inclusion_decision_status == "local_accounting_membership_decision_recorded":
            if self.deferred_case_lineage_refs:
                raise ValueError("deferred cases require open_with_deferred status")
        elif self.inclusion_decision_status == "blocked_by_contamination":
            if self.included_case_lineage_refs:
                raise ValueError("contamination-blocked decisions cannot include cases")
            if not self.rejected_case_lineage_refs:
                raise ValueError("contamination-blocked decisions require rejected cases")
        elif not self.deferred_case_lineage_refs:
            raise ValueError("open-with-deferred decisions require deferred cases")
        _ensure_no_soft_or_forbidden_language(
            self.limitation_note,
            field_name="limitation_note",
        )
        return self


class ProgrambenchLocalMatrixPostInclusionHandoffPressureRow(_MatrixInclusionBase):
    handoff_pressure_ref: str
    handoff_pressure_kind: Literal[
        "future_local_matrix_result_projection_review",
        "future_local_batch_execution_governance_review",
        "future_case_expansion_review",
        "future_official_participation_governance_review",
        "future_benchmark_result_governance_review",
        "future_family_only",
    ]
    source_ref: str
    handoff_non_selection_posture: Literal[
        "pressure_only_no_future_family_selection"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_handoff_pressure_row(
        self,
    ) -> "ProgrambenchLocalMatrixPostInclusionHandoffPressureRow":
        _ensure_no_forbidden_refs(
            [self.handoff_pressure_ref, self.source_ref],
            field_name="handoff_pressure_row_refs",
        )
        _ensure_no_soft_or_forbidden_language(
            self.limitation_note,
            field_name="limitation_note",
        )
        return self


class ProgrambenchLocalMatrixRevisionRegistration(_MatrixInclusionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_MATRIX_REVISION_REGISTRATION_SCHEMA] = Field(
        alias="schema"
    )
    matrix_revision_registration_ref: str
    matrix_inclusion_request_ref: str
    matrix_amendment_plan_ref: str
    matrix_case_delta_manifest_ref: str
    matrix_inclusion_decision_ref: str
    target_matrix_ref: str
    registered_matrix_revision_ref: str
    registered_matrix_revision_hash: str
    base_matrix_revision_hash: str
    matrix_amendment_plan_hash: str
    case_delta_manifest_hash: str
    comparability_delta_review_hash: str
    contamination_delta_review_hash: str
    inclusion_decision_hash: str
    registered_membership_manifest_hash: str
    included_case_lineage_refs: list[str] = Field(default_factory=list)
    deferred_case_lineage_refs: list[str] = Field(default_factory=list)
    rejected_case_lineage_refs: list[str] = Field(default_factory=list)
    matrix_revision_scope_posture: Literal[
        "local_matrix_membership_revision_registration_only"
    ]
    local_accounting_scope_posture: Literal[
        "local_membership_accounting_only_not_result_projection"
    ]
    execution_authority_posture: Literal[
        "no_execution_authority_granted_by_pb_matrix_inclusion_0c"
    ]
    result_projection_authority_posture: Literal[
        "no_result_projection_authority_granted_by_pb_matrix_inclusion_0c"
    ]
    benchmark_score_authority_posture: Literal[
        "no_benchmark_score_authority_granted_by_pb_matrix_inclusion_0c"
    ]
    future_family_selection_posture: Literal[
        "no_future_family_selection_authority_granted_by_pb_matrix_inclusion_0c"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_revision_registration(
        self,
    ) -> "ProgrambenchLocalMatrixRevisionRegistration":
        for field_name in (
            "registered_matrix_revision_hash",
            "base_matrix_revision_hash",
            "matrix_amendment_plan_hash",
            "case_delta_manifest_hash",
            "comparability_delta_review_hash",
            "contamination_delta_review_hash",
            "inclusion_decision_hash",
            "registered_membership_manifest_hash",
        ):
            _ensure_hash(getattr(self, field_name), field_name=field_name)
        lineage_sets = []
        for field_name in (
            "included_case_lineage_refs",
            "deferred_case_lineage_refs",
            "rejected_case_lineage_refs",
        ):
            values = getattr(self, field_name)
            _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
            lineage_sets.append(set(values))
        if not set().union(*lineage_sets):
            raise ValueError("matrix revision registration requires at least one lineage")
        if sum(len(values) for values in lineage_sets) != len(set().union(*lineage_sets)):
            raise ValueError(
                "included, deferred, and rejected revision lineage refs must be disjoint"
            )
        _ensure_no_forbidden_refs(
            [
                self.matrix_revision_registration_ref,
                self.matrix_inclusion_request_ref,
                self.matrix_amendment_plan_ref,
                self.matrix_case_delta_manifest_ref,
                self.matrix_inclusion_decision_ref,
                self.target_matrix_ref,
                self.registered_matrix_revision_ref,
            ],
            field_name="matrix_revision_registration_refs",
        )
        _ensure_no_soft_or_forbidden_language(
            self.limitation_note,
            field_name="limitation_note",
        )
        return self


class ProgrambenchLocalMatrixRevisionReadinessSummary(_MatrixInclusionBase):
    schema_id: Literal[
        PROGRAMBENCH_LOCAL_MATRIX_REVISION_READINESS_SUMMARY_SCHEMA
    ] = Field(alias="schema")
    matrix_revision_readiness_summary_ref: str
    matrix_revision_registration_ref: str
    registered_matrix_revision_ref: str
    included_case_count: int = Field(ge=0)
    deferred_case_count: int = Field(ge=0)
    rejected_case_count: int = Field(ge=0)
    included_case_lineage_refs: list[str] = Field(default_factory=list)
    carried_blocker_refs: list[str] = Field(default_factory=list)
    carried_warning_refs: list[str] = Field(default_factory=list)
    revision_readiness_posture: Literal[
        "ready_for_later_local_matrix_review",
        "open_with_deferred_or_rejected_membership",
        "blocked_by_carried_blockers",
    ]
    inventory_count_posture: Literal[
        "local_membership_inventory_only_not_result_count"
    ]
    matrix_denominator_posture: Literal[
        "local_matrix_denominator_only_not_benchmark_denominator"
    ]
    representativeness_posture: Literal["not_representative_benchmark_sample"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_revision_readiness(
        self,
    ) -> "ProgrambenchLocalMatrixRevisionReadinessSummary":
        _ensure_sorted_unique_allow_empty(
            self.included_case_lineage_refs,
            field_name="included_case_lineage_refs",
        )
        _ensure_sorted_unique_allow_empty(
            self.carried_blocker_refs,
            field_name="carried_blocker_refs",
        )
        _ensure_sorted_unique_allow_empty(
            self.carried_warning_refs,
            field_name="carried_warning_refs",
        )
        _ensure_no_forbidden_refs(
            self.included_case_lineage_refs
            + self.carried_blocker_refs
            + self.carried_warning_refs,
            field_name="revision_readiness_refs",
        )
        _ensure_no_forbidden_refs(
            [
                self.matrix_revision_readiness_summary_ref,
                self.matrix_revision_registration_ref,
                self.registered_matrix_revision_ref,
            ],
            field_name="revision_readiness_top_level_refs",
        )
        if self.revision_readiness_posture == "ready_for_later_local_matrix_review":
            if self.carried_blocker_refs:
                raise ValueError("ready matrix revision summary cannot carry blockers")
            if self.deferred_case_count or self.rejected_case_count:
                raise ValueError(
                    "ready matrix revision summary cannot carry deferred or rejected counts"
                )
        elif self.revision_readiness_posture == "blocked_by_carried_blockers":
            if not self.carried_blocker_refs:
                raise ValueError("blocked readiness requires carried blockers")
        elif not (self.deferred_case_count or self.rejected_case_count):
            raise ValueError(
                "open revision readiness requires deferred or rejected membership"
            )
        _ensure_no_soft_or_forbidden_language(
            self.limitation_note,
            field_name="limitation_note",
        )
        return self


class ProgrambenchLocalMatrixPostInclusionHandoff(_MatrixInclusionBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_MATRIX_POST_INCLUSION_HANDOFF_SCHEMA] = (
        Field(alias="schema")
    )
    matrix_post_inclusion_handoff_ref: str
    matrix_revision_registration_ref: str
    registered_matrix_revision_ref: str
    handoff_pressure_rows: list[
        ProgrambenchLocalMatrixPostInclusionHandoffPressureRow
    ] = Field(min_length=1)
    handoff_pressure_kind: Literal[
        "future_local_matrix_result_projection_review",
        "future_local_batch_execution_governance_review",
        "future_case_expansion_review",
        "future_official_participation_governance_review",
        "future_benchmark_result_governance_review",
        "future_family_only",
    ]
    handoff_non_selection_posture: Literal[
        "pressure_only_no_family_or_execution_selection"
    ]
    batch_execution_authority_posture: Literal[
        "no_batch_execution_authority_granted_by_pb_matrix_inclusion_0c"
    ]
    result_projection_authority_posture: Literal[
        "no_result_projection_authority_granted_by_pb_matrix_inclusion_0c"
    ]
    benchmark_score_authority_posture: Literal[
        "no_benchmark_score_authority_granted_by_pb_matrix_inclusion_0c"
    ]
    baseline_comparison_authority_posture: Literal[
        "no_baseline_comparison_authority_granted_by_pb_matrix_inclusion_0c"
    ]
    model_ranking_authority_posture: Literal[
        "no_model_ranking_authority_granted_by_pb_matrix_inclusion_0c"
    ]
    future_family_selection_posture: Literal[
        "no_future_family_selection_authority_granted_by_pb_matrix_inclusion_0c"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_post_inclusion_handoff(
        self,
    ) -> "ProgrambenchLocalMatrixPostInclusionHandoff":
        row_refs = [row.handoff_pressure_ref for row in self.handoff_pressure_rows]
        _ensure_sorted_unique(row_refs, field_name="handoff_pressure_rows")
        row_kinds = {row.handoff_pressure_kind for row in self.handoff_pressure_rows}
        if self.handoff_pressure_kind not in row_kinds:
            raise ValueError("handoff pressure kind must be represented by a row")
        _ensure_no_forbidden_refs(
            [
                self.matrix_post_inclusion_handoff_ref,
                self.matrix_revision_registration_ref,
                self.registered_matrix_revision_ref,
            ],
            field_name="post_inclusion_handoff_refs",
        )
        _ensure_no_soft_or_forbidden_language(
            self.limitation_note,
            field_name="limitation_note",
        )
        return self


class ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment(_MatrixInclusionBase):
    schema_id: Literal[
        PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    ] = Field(alias="schema")
    matrix_inclusion_family_closeout_ref: str
    closed_family_ref: Literal["PB-MATRIX-INCLUSION-0"]
    closed_slice_refs: list[str]
    shipped_record_shapes: list[str]
    matrix_inclusion_request_refs: list[str]
    candidate_intake_refs: list[str]
    eligibility_review_refs: list[str]
    control_contract_refs: list[str]
    guardrail_refs: list[str]
    amendment_plan_refs: list[str]
    case_delta_manifest_refs: list[str]
    comparability_delta_review_refs: list[str]
    contamination_delta_review_refs: list[str]
    inclusion_decision_refs: list[str]
    revision_registration_refs: list[str]
    revision_readiness_summary_refs: list[str]
    post_inclusion_handoff_refs: list[str]
    official_programbench_posture: Literal[
        "no_official_programbench_authority_granted_by_pb_matrix_inclusion_0c"
    ]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    baseline_comparison_posture: Literal["no_baseline_comparison_authority"]
    model_ranking_posture: Literal["no_model_ranking_authority"]
    future_family_authority_posture: Literal[
        "no_future_family_selection_authority_granted_by_pb_matrix_inclusion_0c"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_family_closeout(
        self,
    ) -> "ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment":
        expected_slices = [
            "PB-MATRIX-INCLUSION-0-A",
            "PB-MATRIX-INCLUSION-0-B",
            "PB-MATRIX-INCLUSION-0-C",
        ]
        _ensure_non_empty_trimmed(
            self.closed_slice_refs,
            field_name="closed_slice_refs",
        )
        if len(self.closed_slice_refs) != len(set(self.closed_slice_refs)):
            raise ValueError("closed_slice_refs must not contain duplicates")
        if sorted(self.closed_slice_refs) != expected_slices:
            raise ValueError("matrix inclusion closeout must close A, B, and C slices")
        expected_shapes = sorted(PB_MATRIX_INCLUSION_0_ARTIFACT_KINDS)
        if self.shipped_record_shapes != expected_shapes:
            raise ValueError(
                "matrix inclusion closeout shipped shapes must cover A, B, and C"
            )
        for field_name in (
            "matrix_inclusion_request_refs",
            "candidate_intake_refs",
            "eligibility_review_refs",
            "control_contract_refs",
            "guardrail_refs",
            "amendment_plan_refs",
            "case_delta_manifest_refs",
            "comparability_delta_review_refs",
            "contamination_delta_review_refs",
            "inclusion_decision_refs",
            "revision_registration_refs",
            "revision_readiness_summary_refs",
            "post_inclusion_handoff_refs",
        ):
            values = getattr(self, field_name)
            _ensure_sorted_unique(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        _ensure_no_forbidden_refs(
            [self.matrix_inclusion_family_closeout_ref],
            field_name="matrix_inclusion_family_closeout_ref",
        )
        _ensure_no_soft_or_forbidden_language(
            self.limitation_note,
            field_name="limitation_note",
        )
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


def validate_pb_matrix_inclusion_0b_bundle(
    *,
    inclusion_request: ProgrambenchLocalMatrixInclusionRequest,
    candidate_intake: ProgrambenchLocalMatrixCandidateIntake,
    eligibility_review: ProgrambenchLocalMatrixInclusionEligibilityReview,
    control_contract: ProgrambenchLocalMatrixInclusionControlContract,
    non_authority_guardrail: ProgrambenchLocalMatrixInclusionNonAuthorityGuardrail,
    amendment_plan: ProgrambenchLocalMatrixAmendmentPlan,
    case_delta_manifest: ProgrambenchLocalMatrixCaseDeltaManifest,
    comparability_delta_review: ProgrambenchLocalMatrixComparabilityDeltaReview,
    contamination_delta_review: ProgrambenchLocalMatrixContaminationDeltaReview,
    inclusion_decision_record: ProgrambenchLocalMatrixInclusionDecisionRecord,
) -> None:
    """Validate the PB-MATRIX-INCLUSION-0-B local accounting chain."""

    if not eligibility_review.eligible_case_lineage_refs:
        raise ValueError("PB-MATRIX-INCLUSION-0-B requires released A-eligible refs")
    if eligibility_review.eligibility_status != (
        "eligible_for_later_matrix_amendment_review"
    ):
        raise ValueError("PB-MATRIX-INCLUSION-0-B cannot consume non-eligible A review")
    if non_authority_guardrail.matrix_amendment_deferred_posture != (
        "matrix_amendment_deferred_to_pb_matrix_inclusion_0b"
    ):
        raise ValueError("A guardrail must defer amendment planning to B")

    if amendment_plan.matrix_inclusion_request_ref != (
        inclusion_request.matrix_inclusion_request_ref
    ):
        raise ValueError("amendment plan must reference released A request")
    if amendment_plan.matrix_inclusion_control_contract_ref != (
        control_contract.matrix_inclusion_control_contract_ref
    ):
        raise ValueError("amendment plan must reference released A control contract")
    if amendment_plan.target_matrix_ref != inclusion_request.base_matrix_ref:
        raise ValueError("amendment plan must preserve target matrix ref")
    if amendment_plan.target_matrix_revision_candidate_ref != (
        inclusion_request.target_matrix_revision_candidate_ref
    ):
        raise ValueError("amendment plan must preserve target revision candidate ref")

    planned_by_kind = {
        "added_to_revision_candidate": set(amendment_plan.planned_added_case_lineage_refs),
        "deferred_from_revision_candidate": set(
            amendment_plan.planned_deferred_case_lineage_refs
        ),
        "rejected_from_revision_candidate": set(
            amendment_plan.planned_rejected_case_lineage_refs
        ),
    }
    planned_refs = set().union(*planned_by_kind.values())
    eligible_refs = set(eligibility_review.eligible_case_lineage_refs)
    if planned_refs != eligible_refs:
        raise ValueError(
            "amendment plan must account for every A-eligible candidate exactly once"
        )

    if case_delta_manifest.matrix_amendment_plan_ref != (
        amendment_plan.matrix_amendment_plan_ref
    ):
        raise ValueError("case delta manifest must reference amendment plan")
    candidate_rows = {
        row.candidate_case_lineage_ref: row for row in candidate_intake.candidate_case_rows
    }
    manifest_refs = {row.case_lineage_ref for row in case_delta_manifest.case_delta_rows}
    if manifest_refs != planned_refs:
        raise ValueError("case delta manifest must match planned lineage refs")
    for row in case_delta_manifest.case_delta_rows:
        if row.case_lineage_ref not in candidate_rows:
            raise ValueError("case delta rows must bind to released A candidate rows")
        candidate_row = candidate_rows[row.case_lineage_ref]
        if row.case_lineage_hash != candidate_row.case_lineage_hash:
            raise ValueError("case delta row lineage hash must match A candidate row")
        if row.prior_matrix_membership_status != (
            candidate_row.prior_matrix_membership_status
        ):
            raise ValueError("case delta row must preserve prior membership status")
        if row.dedupe_status != candidate_row.dedupe_status:
            raise ValueError("case delta row must preserve A dedupe status")
        if row.case_lineage_ref not in planned_by_kind[row.case_delta_kind]:
            raise ValueError("case delta kind must match amendment plan membership sets")

    if comparability_delta_review.matrix_amendment_plan_ref != (
        amendment_plan.matrix_amendment_plan_ref
    ):
        raise ValueError("comparability review must reference amendment plan")
    if comparability_delta_review.matrix_case_delta_manifest_ref != (
        case_delta_manifest.matrix_case_delta_manifest_ref
    ):
        raise ValueError("comparability review must reference case delta manifest")
    continuity_pairs = (
        (
            control_contract.worker_profile_continuity_posture,
            comparability_delta_review.worker_profile_delta_posture,
        ),
        (
            control_contract.model_profile_continuity_posture,
            comparability_delta_review.model_profile_delta_posture,
        ),
        (
            control_contract.tool_policy_continuity_posture,
            comparability_delta_review.tool_policy_delta_posture,
        ),
        (
            control_contract.probe_basis_continuity_posture,
            comparability_delta_review.probe_basis_delta_posture,
        ),
        (
            control_contract.sandbox_write_scope_continuity_posture,
            comparability_delta_review.sandbox_write_scope_delta_posture,
        ),
        (
            control_contract.source_visibility_continuity_posture,
            comparability_delta_review.source_visibility_delta_posture,
        ),
    )
    for control_posture, review_posture in continuity_pairs:
        expected = (
            "unchanged"
            if control_posture == "unchanged"
            else "changed_non_comparable_local_accounting_only"
        )
        if review_posture != expected:
            raise ValueError("comparability review must mirror A control continuity")

    if contamination_delta_review.matrix_amendment_plan_ref != (
        amendment_plan.matrix_amendment_plan_ref
    ):
        raise ValueError("contamination review must reference amendment plan")
    if contamination_delta_review.matrix_case_delta_manifest_ref != (
        case_delta_manifest.matrix_case_delta_manifest_ref
    ):
        raise ValueError("contamination review must reference case delta manifest")
    contamination_refs = {
        row.case_lineage_ref for row in contamination_delta_review.contamination_delta_rows
    }
    if contamination_refs != planned_refs:
        raise ValueError("contamination delta rows must cover planned lineage refs")

    if inclusion_decision_record.matrix_amendment_plan_ref != (
        amendment_plan.matrix_amendment_plan_ref
    ):
        raise ValueError("inclusion decision must reference amendment plan")
    if inclusion_decision_record.matrix_case_delta_manifest_ref != (
        case_delta_manifest.matrix_case_delta_manifest_ref
    ):
        raise ValueError("inclusion decision must reference case delta manifest")
    if inclusion_decision_record.matrix_comparability_delta_review_ref != (
        comparability_delta_review.matrix_comparability_delta_review_ref
    ):
        raise ValueError("inclusion decision must reference comparability review")
    if inclusion_decision_record.matrix_contamination_delta_review_ref != (
        contamination_delta_review.matrix_contamination_delta_review_ref
    ):
        raise ValueError("inclusion decision must reference contamination review")
    if contamination_delta_review.contamination_transfer_status != "clean":
        if inclusion_decision_record.included_case_lineage_refs:
            raise ValueError("inclusion decision cannot include contaminated transfers")
    decision_sets = {
        "included": set(inclusion_decision_record.included_case_lineage_refs),
        "deferred": set(inclusion_decision_record.deferred_case_lineage_refs),
        "rejected": set(inclusion_decision_record.rejected_case_lineage_refs),
    }
    if decision_sets["included"] != set(amendment_plan.planned_added_case_lineage_refs):
        raise ValueError("included decision refs must match planned added refs")
    if decision_sets["deferred"] != set(amendment_plan.planned_deferred_case_lineage_refs):
        raise ValueError("deferred decision refs must match planned deferred refs")
    if decision_sets["rejected"] != set(amendment_plan.planned_rejected_case_lineage_refs):
        raise ValueError("rejected decision refs must match planned rejected refs")
    delta_reason_by_lineage = {
        row.case_lineage_ref: row.delta_reason for row in case_delta_manifest.case_delta_rows
    }
    decision_basis_by_lineage = {
        row.case_lineage_ref: row.decision_basis_kind
        for row in inclusion_decision_record.decision_basis_rows
    }
    if decision_basis_by_lineage != delta_reason_by_lineage:
        raise ValueError("decision basis kinds must match case delta reasons")


def validate_pb_matrix_inclusion_0c_bundle(
    *,
    inclusion_request: ProgrambenchLocalMatrixInclusionRequest,
    candidate_intake: ProgrambenchLocalMatrixCandidateIntake,
    eligibility_review: ProgrambenchLocalMatrixInclusionEligibilityReview,
    control_contract: ProgrambenchLocalMatrixInclusionControlContract,
    non_authority_guardrail: ProgrambenchLocalMatrixInclusionNonAuthorityGuardrail,
    amendment_plan: ProgrambenchLocalMatrixAmendmentPlan,
    case_delta_manifest: ProgrambenchLocalMatrixCaseDeltaManifest,
    comparability_delta_review: ProgrambenchLocalMatrixComparabilityDeltaReview,
    contamination_delta_review: ProgrambenchLocalMatrixContaminationDeltaReview,
    inclusion_decision_record: ProgrambenchLocalMatrixInclusionDecisionRecord,
    revision_registration: ProgrambenchLocalMatrixRevisionRegistration,
    revision_readiness_summary: ProgrambenchLocalMatrixRevisionReadinessSummary,
    post_inclusion_handoff: ProgrambenchLocalMatrixPostInclusionHandoff,
    family_closeout: ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment,
) -> None:
    """Validate the PB-MATRIX-INCLUSION-0-C revision registration chain."""

    validate_pb_matrix_inclusion_0b_bundle(
        inclusion_request=inclusion_request,
        candidate_intake=candidate_intake,
        eligibility_review=eligibility_review,
        control_contract=control_contract,
        non_authority_guardrail=non_authority_guardrail,
        amendment_plan=amendment_plan,
        case_delta_manifest=case_delta_manifest,
        comparability_delta_review=comparability_delta_review,
        contamination_delta_review=contamination_delta_review,
        inclusion_decision_record=inclusion_decision_record,
    )

    if revision_registration.matrix_inclusion_request_ref != (
        inclusion_request.matrix_inclusion_request_ref
    ):
        raise ValueError("revision registration must reference A request")
    if revision_registration.matrix_amendment_plan_ref != (
        amendment_plan.matrix_amendment_plan_ref
    ):
        raise ValueError("revision registration must reference B amendment plan")
    if revision_registration.matrix_case_delta_manifest_ref != (
        case_delta_manifest.matrix_case_delta_manifest_ref
    ):
        raise ValueError("revision registration must reference B case delta manifest")
    if revision_registration.matrix_inclusion_decision_ref != (
        inclusion_decision_record.matrix_inclusion_decision_ref
    ):
        raise ValueError("revision registration must reference B inclusion decision")
    if revision_registration.target_matrix_ref != inclusion_request.base_matrix_ref:
        raise ValueError("revision registration must preserve target matrix ref")
    if revision_registration.base_matrix_revision_hash != (
        inclusion_request.base_matrix_revision_hash
    ):
        raise ValueError("revision registration must bind the base matrix revision hash")
    if revision_registration.matrix_amendment_plan_hash != _model_hash(amendment_plan):
        raise ValueError("revision registration must bind the amendment plan hash")
    if revision_registration.case_delta_manifest_hash != (
        case_delta_manifest.delta_manifest_hash
    ):
        raise ValueError("revision registration must bind the case delta manifest hash")
    if revision_registration.comparability_delta_review_hash != (
        comparability_delta_review.comparability_delta_hash
    ):
        raise ValueError(
            "revision registration must bind the comparability delta review hash"
        )
    if revision_registration.contamination_delta_review_hash != _model_hash(
        contamination_delta_review
    ):
        raise ValueError(
            "revision registration must bind the contamination delta review hash"
        )
    if revision_registration.inclusion_decision_hash != _model_hash(
        inclusion_decision_record
    ):
        raise ValueError("revision registration must bind the inclusion decision hash")

    if set(revision_registration.included_case_lineage_refs) != set(
        inclusion_decision_record.included_case_lineage_refs
    ):
        raise ValueError("revision included membership must match B decision")
    if set(revision_registration.deferred_case_lineage_refs) != set(
        inclusion_decision_record.deferred_case_lineage_refs
    ):
        raise ValueError("revision deferred membership must match B decision")
    if set(revision_registration.rejected_case_lineage_refs) != set(
        inclusion_decision_record.rejected_case_lineage_refs
    ):
        raise ValueError("revision rejected membership must match B decision")

    if revision_readiness_summary.matrix_revision_registration_ref != (
        revision_registration.matrix_revision_registration_ref
    ):
        raise ValueError("readiness summary must reference revision registration")
    if revision_readiness_summary.registered_matrix_revision_ref != (
        revision_registration.registered_matrix_revision_ref
    ):
        raise ValueError("readiness summary must reference registered matrix revision")
    if revision_readiness_summary.included_case_count != len(
        revision_registration.included_case_lineage_refs
    ):
        raise ValueError("readiness included count must match revision registration")
    if revision_readiness_summary.deferred_case_count != len(
        revision_registration.deferred_case_lineage_refs
    ):
        raise ValueError("readiness deferred count must match revision registration")
    if revision_readiness_summary.rejected_case_count != len(
        revision_registration.rejected_case_lineage_refs
    ):
        raise ValueError("readiness rejected count must match revision registration")
    if set(revision_readiness_summary.included_case_lineage_refs) != set(
        revision_registration.included_case_lineage_refs
    ):
        raise ValueError("readiness included lineage refs must match registration")
    if (
        revision_readiness_summary.inventory_count_posture
        != "local_membership_inventory_only_not_result_count"
    ):
        raise ValueError("readiness counts must remain inventory-only")
    if (
        revision_readiness_summary.matrix_denominator_posture
        != "local_matrix_denominator_only_not_benchmark_denominator"
    ):
        raise ValueError("readiness denominator cannot become a benchmark denominator")
    if revision_readiness_summary.benchmark_truth_posture != "not_benchmark_truth":
        raise ValueError("readiness summary cannot claim benchmark truth")

    if post_inclusion_handoff.matrix_revision_registration_ref != (
        revision_registration.matrix_revision_registration_ref
    ):
        raise ValueError("post-inclusion handoff must reference revision registration")
    if post_inclusion_handoff.registered_matrix_revision_ref != (
        revision_registration.registered_matrix_revision_ref
    ):
        raise ValueError("post-inclusion handoff must reference registered revision")
    if (
        post_inclusion_handoff.batch_execution_authority_posture
        != "no_batch_execution_authority_granted_by_pb_matrix_inclusion_0c"
    ):
        raise ValueError("post-inclusion handoff cannot grant batch execution")
    if (
        post_inclusion_handoff.result_projection_authority_posture
        != "no_result_projection_authority_granted_by_pb_matrix_inclusion_0c"
    ):
        raise ValueError("post-inclusion handoff cannot grant result projection")
    if (
        post_inclusion_handoff.future_family_selection_posture
        != "no_future_family_selection_authority_granted_by_pb_matrix_inclusion_0c"
    ):
        raise ValueError("post-inclusion handoff cannot select a future family")

    if family_closeout.matrix_inclusion_request_refs != [
        inclusion_request.matrix_inclusion_request_ref
    ]:
        raise ValueError("family closeout must reference the released A request")
    if family_closeout.candidate_intake_refs != [
        candidate_intake.matrix_candidate_intake_ref
    ]:
        raise ValueError("family closeout must reference candidate intake")
    if family_closeout.eligibility_review_refs != [
        eligibility_review.matrix_inclusion_eligibility_review_ref
    ]:
        raise ValueError("family closeout must reference eligibility review")
    if family_closeout.control_contract_refs != [
        control_contract.matrix_inclusion_control_contract_ref
    ]:
        raise ValueError("family closeout must reference control contract")
    if family_closeout.guardrail_refs != [
        non_authority_guardrail.matrix_inclusion_guardrail_ref
    ]:
        raise ValueError("family closeout must reference non-authority guardrail")
    if family_closeout.amendment_plan_refs != [
        amendment_plan.matrix_amendment_plan_ref
    ]:
        raise ValueError("family closeout must reference amendment plan")
    if family_closeout.case_delta_manifest_refs != [
        case_delta_manifest.matrix_case_delta_manifest_ref
    ]:
        raise ValueError("family closeout must reference case delta manifest")
    if family_closeout.comparability_delta_review_refs != [
        comparability_delta_review.matrix_comparability_delta_review_ref
    ]:
        raise ValueError("family closeout must reference comparability review")
    if family_closeout.contamination_delta_review_refs != [
        contamination_delta_review.matrix_contamination_delta_review_ref
    ]:
        raise ValueError("family closeout must reference contamination review")
    if family_closeout.inclusion_decision_refs != [
        inclusion_decision_record.matrix_inclusion_decision_ref
    ]:
        raise ValueError("family closeout must reference inclusion decision")
    if family_closeout.revision_registration_refs != [
        revision_registration.matrix_revision_registration_ref
    ]:
        raise ValueError("family closeout must reference revision registration")
    if family_closeout.revision_readiness_summary_refs != [
        revision_readiness_summary.matrix_revision_readiness_summary_ref
    ]:
        raise ValueError("family closeout must reference revision readiness summary")
    if family_closeout.post_inclusion_handoff_refs != [
        post_inclusion_handoff.matrix_post_inclusion_handoff_ref
    ]:
        raise ValueError("family closeout must reference post-inclusion handoff")
    if family_closeout.future_family_authority_posture != (
        "no_future_family_selection_authority_granted_by_pb_matrix_inclusion_0c"
    ):
        raise ValueError("family closeout cannot grant future-family authority")
