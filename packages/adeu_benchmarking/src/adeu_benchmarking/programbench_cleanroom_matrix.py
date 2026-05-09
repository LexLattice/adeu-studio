from __future__ import annotations

import re
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .programbench_cleanroom_retry import ProgrambenchLocalRetryFamilyCloseoutAlignment
from .programbench_cleanroom_trial import ProgrambenchLocalTrialFamilyCloseoutAlignment

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

PROGRAMBENCH_LOCAL_CASE_MATRIX_REQUEST_SCHEMA = "programbench_local_case_matrix_request@1"
PROGRAMBENCH_LOCAL_CASE_INCLUSION_MANIFEST_SCHEMA = "programbench_local_case_inclusion_manifest@1"
PROGRAMBENCH_LOCAL_CASE_LINEAGE_ELIGIBILITY_REVIEW_SCHEMA = (
    "programbench_local_case_lineage_eligibility_review@1"
)
PROGRAMBENCH_LOCAL_CASE_MATRIX_CONTROL_CONTRACT_SCHEMA = (
    "programbench_local_case_matrix_control_contract@1"
)
PROGRAMBENCH_LOCAL_CASE_MATRIX_NON_AUTHORITY_GUARDRAIL_SCHEMA = (
    "programbench_local_case_matrix_non_authority_guardrail@1"
)

PROGRAMBENCH_LOCAL_CASE_MATRIX_RESULT_PROJECTION_SCHEMA = (
    "programbench_local_case_matrix_result_projection@1"
)
PROGRAMBENCH_LOCAL_CASE_MATRIX_OBSERVATION_LEDGER_SCHEMA = (
    "programbench_local_case_matrix_observation_ledger@1"
)
PROGRAMBENCH_LOCAL_CASE_MATRIX_COVERAGE_REGISTER_SCHEMA = (
    "programbench_local_case_matrix_coverage_register@1"
)
PROGRAMBENCH_LOCAL_CASE_MATRIX_CONTAMINATION_REGISTER_SCHEMA = (
    "programbench_local_case_matrix_contamination_register@1"
)
PROGRAMBENCH_LOCAL_CASE_MATRIX_SUMMARY_SCHEMA = "programbench_local_case_matrix_summary@1"
PROGRAMBENCH_LOCAL_CASE_MATRIX_HANDOFF_SCHEMA = "programbench_local_case_matrix_handoff@1"
PROGRAMBENCH_LOCAL_CASE_MATRIX_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "programbench_local_case_matrix_family_closeout_alignment@1"
)

PB_MATRIX_0A_ARTIFACT_KINDS = {
    PROGRAMBENCH_LOCAL_CASE_MATRIX_REQUEST_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_INCLUSION_MANIFEST_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_LINEAGE_ELIGIBILITY_REVIEW_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_MATRIX_CONTROL_CONTRACT_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_MATRIX_NON_AUTHORITY_GUARDRAIL_SCHEMA,
}
PB_MATRIX_0B_ARTIFACT_KINDS = {
    PROGRAMBENCH_LOCAL_CASE_MATRIX_RESULT_PROJECTION_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_MATRIX_OBSERVATION_LEDGER_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_MATRIX_COVERAGE_REGISTER_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_MATRIX_CONTAMINATION_REGISTER_SCHEMA,
}
PB_MATRIX_0C_ARTIFACT_KINDS = {
    PROGRAMBENCH_LOCAL_CASE_MATRIX_SUMMARY_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_MATRIX_HANDOFF_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_MATRIX_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
}
PB_MATRIX_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS = (
    PB_MATRIX_0B_ARTIFACT_KINDS | PB_MATRIX_0C_ARTIFACT_KINDS
)
PB_MATRIX_0B_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS = PB_MATRIX_0C_ARTIFACT_KINDS

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
    "beats baseline",
    "benchmark score",
    "leaderboard-like",
    "model wins",
    "official-like score",
    "pass rate",
    "representative benchmark subset",
    "solve rate",
    "success rate",
)


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
        raise ValueError(f"{field_name} contains forbidden matrix evidence refs: {leaked}")


def _ensure_no_soft_scoring_language(value: str, *, field_name: str) -> None:
    lowered = value.lower()
    leaked = [marker for marker in _SOFT_SCORING_LANGUAGE_MARKERS if marker in lowered]
    if leaked:
        raise ValueError(
            f"{field_name} contains benchmark-like scoring or ranking language: {leaked}"
        )


def _ensure_refs_resolve(
    values: list[str],
    allowed_refs: set[str],
    *,
    field_name: str,
) -> None:
    unknown = sorted(set(values) - allowed_refs)
    if unknown:
        raise ValueError(f"{field_name} contains refs outside released matrix basis: {unknown}")


class _MatrixBase(BaseModel):
    model_config = MODEL_CONFIG


class ProgrambenchLocalCaseMatrixSelectionRationaleRow(_MatrixBase):
    selection_rationale_ref: str
    rationale_kind: Literal[
        "local_coverage_probe",
        "local_regression_tracking",
        "local_research_inventory",
        "local_smoke_coverage",
    ]
    selected_case_refs: list[str] = Field(min_length=1)
    rationale_scope_posture: Literal["local_matrix_selection_only_not_representative"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_rationale(self) -> "ProgrambenchLocalCaseMatrixSelectionRationaleRow":
        _ensure_sorted_unique(self.selected_case_refs, field_name="selected_case_refs")
        _ensure_no_forbidden_refs(self.selected_case_refs, field_name="selected_case_refs")
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseMatrixCandidateRow(_MatrixBase):
    case_ref: str
    case_lineage_kind: Literal["trial_only", "trial_with_retry_settlement"]
    trial_lineage_ref: str
    retry_lineage_ref: str | None = None
    adapter_case_packet_ref: str
    workbench_ref: str
    attempt_ref: str
    trial_ref: str
    retry_settlement_ref: str | None = None
    case_visibility_boundary_hash: str
    case_cleanroom_boundary_hash: str
    case_result_source_posture: Literal[
        "local_released_result_only",
        "no_result_projection_by_pb_matrix_0a",
        "official_evaluator_derived",
        "support_only",
    ]
    case_contamination_posture: Literal[
        "clean",
        "contaminated",
        "hidden_or_forbidden_derived",
        "postmortem_only",
    ]
    case_origin_posture: Literal[
        "released_local_cleanroom_lineage",
        "support_only",
        "unreleased",
    ]
    inclusion_decision: Literal["blocked", "deferred", "included", "support_only"]
    inclusion_reason: str

    @model_validator(mode="after")
    def _validate_candidate(self) -> "ProgrambenchLocalCaseMatrixCandidateRow":
        _ensure_hash(
            self.case_visibility_boundary_hash,
            field_name="case_visibility_boundary_hash",
        )
        _ensure_hash(
            self.case_cleanroom_boundary_hash,
            field_name="case_cleanroom_boundary_hash",
        )
        _ensure_no_forbidden_refs(
            [
                self.case_ref,
                self.trial_lineage_ref,
                self.adapter_case_packet_ref,
                self.workbench_ref,
                self.attempt_ref,
                self.trial_ref,
            ],
            field_name="matrix_case_candidate_row refs",
        )
        optional_refs = [
            ref for ref in (self.retry_lineage_ref, self.retry_settlement_ref) if ref is not None
        ]
        _ensure_no_forbidden_refs(optional_refs, field_name="matrix_case_candidate_row refs")
        _ensure_no_soft_scoring_language(self.inclusion_reason, field_name="inclusion_reason")
        if self.case_lineage_kind == "trial_with_retry_settlement":
            if not (self.retry_lineage_ref and self.retry_settlement_ref):
                raise ValueError("retry-settlement candidates require retry lineage and settlement")
        elif self.retry_lineage_ref or self.retry_settlement_ref:
            raise ValueError("trial-only candidates cannot carry retry lineage or settlement")
        if self.inclusion_decision == "included":
            if self.case_origin_posture != "released_local_cleanroom_lineage":
                raise ValueError("included matrix cases require released local cleanroom lineage")
            if self.case_contamination_posture != "clean":
                raise ValueError("included matrix cases require clean contamination posture")
            if self.case_result_source_posture != "local_released_result_only":
                raise ValueError(
                    "included matrix cases require released local result source posture"
                )
        return self


class ProgrambenchLocalCaseMatrixEligibilityRow(_MatrixBase):
    eligibility_row_ref: str
    case_ref: str
    eligibility_posture: Literal[
        "blocked_by_contamination",
        "blocked_by_forbidden_source",
        "blocked_by_missing_lineage",
        "blocked_by_official_evaluator_source",
        "blocked_by_support_only",
        "deferred",
        "eligible_for_local_matrix_inclusion",
    ]
    lineage_release_refs: list[str] = Field(default_factory=list)
    blocker_refs: list[str] = Field(default_factory=list)
    warning_refs: list[str] = Field(default_factory=list)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_eligibility_row(self) -> "ProgrambenchLocalCaseMatrixEligibilityRow":
        _ensure_no_forbidden_refs([self.case_ref], field_name="case_ref")
        for field_name in ("lineage_release_refs", "blocker_refs", "warning_refs"):
            values = getattr(self, field_name)
            _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        if self.eligibility_posture == "eligible_for_local_matrix_inclusion":
            if not self.lineage_release_refs:
                raise ValueError("eligible matrix cases require lineage release refs")
            if self.blocker_refs:
                raise ValueError("eligible matrix cases cannot carry blockers")
        elif not self.blocker_refs and self.eligibility_posture != "deferred":
            raise ValueError("blocked matrix cases require blocker refs")
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseMatrixAllowedActionRow(_MatrixBase):
    allowed_action_ref: str
    action_kind: Literal[
        "case_inclusion_review",
        "lineage_eligibility_review",
        "matrix_control_accounting",
        "non_authority_guardrail_review",
    ]
    action_scope_posture: Literal["allowed_for_pb_matrix_0a_review_only"]
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_allowed_action(self) -> "ProgrambenchLocalCaseMatrixAllowedActionRow":
        _ensure_sorted_unique(self.source_refs, field_name="allowed action source_refs")
        _ensure_no_forbidden_refs(self.source_refs, field_name="allowed action source_refs")
        return self


class ProgrambenchLocalCaseMatrixForbiddenActionRow(_MatrixBase):
    forbidden_action_ref: str
    action_kind: Literal[
        "batch_command_execution",
        "benchmark_scoring",
        "candidate_materialization",
        "decompilation",
        "docker_socket_access",
        "external_repo_lookup",
        "hidden_test_access",
        "host_secret_access",
        "internet_lookup",
        "matrix_result_projection",
        "model_ranking",
        "official_evaluator_access",
        "official_submission",
        "second_retry_authority",
        "source_lookup",
        "widen_write_scope",
    ]
    forbiddance_posture: Literal["forbidden_by_pb_matrix_0a"]
    limitation_note: str


class ProgrambenchLocalCaseMatrixForbiddenAuthorityRow(_MatrixBase):
    forbidden_authority_ref: str
    authority_kind: Literal[
        "batch_execution",
        "benchmark_score",
        "benchmark_truth",
        "candidate_materialization",
        "contamination_register",
        "coverage_register",
        "future_family_selection",
        "hidden_test_inference",
        "matrix_handoff",
        "matrix_observation_ledger",
        "matrix_summary",
        "model_ranking",
        "official_programbench_participation",
        "official_submission",
        "per_case_result_projection",
        "retry_chain",
        "second_retry",
    ]
    forbiddance_posture: Literal["forbidden_by_pb_matrix_0a"]
    limitation_note: str


class ProgrambenchLocalCaseMatrixRequest(_MatrixBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_MATRIX_REQUEST_SCHEMA] = Field(alias="schema")
    case_matrix_ref: str
    matrix_request_ref: str
    matrix_horizon: Literal[
        "local_coverage_probe_matrix",
        "local_regression_matrix",
        "local_research_matrix",
        "local_smoke_matrix",
        "not_representative_benchmark_sample",
    ]
    matrix_max_case_count: int = Field(ge=1)
    matrix_selection_rationale_refs: list[str] = Field(min_length=1)
    matrix_case_candidate_refs: list[str] = Field(min_length=1)
    case_inclusion_manifest_ref: str
    case_lineage_eligibility_review_ref: str
    matrix_control_contract_ref: str
    requested_case_count: int = Field(ge=1)
    official_benchmark_authority_posture: Literal[
        "no_official_programbench_authority_granted_by_pb_matrix_0a"
    ]
    model_ranking_posture: Literal["no_model_ranking_claimed_by_pb_matrix_0a"]
    batch_execution_authority_posture: Literal[
        "no_batch_execution_authority_granted_by_pb_matrix_0a"
    ]
    future_family_selection_posture: Literal["no_future_family_selected_by_pb_matrix_0a"]
    representativeness_posture: Literal["not_representative_benchmark_sample"]
    aggregate_count_posture: Literal[
        "coverage_accounting_only",
        "local_case_posture_count_only",
        "local_inventory_count_only",
        "not_benchmark_score",
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_request(self) -> "ProgrambenchLocalCaseMatrixRequest":
        _ensure_sorted_unique(
            self.matrix_selection_rationale_refs,
            field_name="matrix_selection_rationale_refs",
        )
        _ensure_sorted_unique(
            self.matrix_case_candidate_refs,
            field_name="matrix_case_candidate_refs",
        )
        _ensure_no_forbidden_refs(
            self.matrix_case_candidate_refs,
            field_name="matrix_case_candidate_refs",
        )
        if self.requested_case_count > self.matrix_max_case_count:
            raise ValueError("requested_case_count cannot exceed matrix_max_case_count")
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseInclusionManifest(_MatrixBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_INCLUSION_MANIFEST_SCHEMA] = Field(alias="schema")
    case_inclusion_manifest_ref: str
    case_matrix_ref: str
    case_candidate_rows: list[ProgrambenchLocalCaseMatrixCandidateRow] = Field(min_length=1)
    matrix_selection_rationale_rows: list[ProgrambenchLocalCaseMatrixSelectionRationaleRow] = Field(
        min_length=1
    )
    included_case_refs: list[str] = Field(min_length=1)
    blocked_case_refs: list[str] = Field(default_factory=list)
    deferred_case_refs: list[str] = Field(default_factory=list)
    support_only_case_refs: list[str] = Field(default_factory=list)
    released_case_lineage_refs: list[str] = Field(min_length=1)
    case_origin_posture: Literal["released_local_cleanroom_lineage_only"]
    case_visibility_posture: Literal["released_cleanroom_boundary_only"]
    case_result_source_posture: Literal["released_local_results_only_no_projection"]
    hidden_or_forbidden_exposure_posture: Literal[
        "hidden_and_forbidden_sources_not_exposed_or_summarized"
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_manifest(self) -> "ProgrambenchLocalCaseInclusionManifest":
        row_refs = [row.case_ref for row in self.case_candidate_rows]
        _ensure_sorted_unique(row_refs, field_name="case_candidate_rows")
        rationale_refs = [
            row.selection_rationale_ref for row in self.matrix_selection_rationale_rows
        ]
        _ensure_sorted_unique(
            rationale_refs,
            field_name="matrix_selection_rationale_rows",
        )
        for field_name in (
            "included_case_refs",
            "blocked_case_refs",
            "deferred_case_refs",
            "support_only_case_refs",
            "released_case_lineage_refs",
        ):
            values = getattr(self, field_name)
            if field_name in {"included_case_refs", "released_case_lineage_refs"}:
                _ensure_sorted_unique(values, field_name=field_name)
            else:
                _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        all_case_refs = set(row_refs)
        decision_refs = {
            "blocked": set(self.blocked_case_refs),
            "deferred": set(self.deferred_case_refs),
            "included": set(self.included_case_refs),
            "support_only": set(self.support_only_case_refs),
        }
        unknown = sorted(set().union(*decision_refs.values()) - all_case_refs)
        if unknown:
            raise ValueError(f"case decision refs must resolve to candidate rows: {unknown}")
        overlaps = sorted(
            ref for ref in all_case_refs if sum(ref in refs for refs in decision_refs.values()) > 1
        )
        if overlaps:
            raise ValueError(f"case decision refs must not overlap: {overlaps}")
        for decision, refs in decision_refs.items():
            row_decision_refs = {
                row.case_ref
                for row in self.case_candidate_rows
                if row.inclusion_decision == decision
            }
            if refs != row_decision_refs:
                raise ValueError(f"{decision} case refs must match candidate row decisions")
        selected_by_rationale = set().union(
            *(row.selected_case_refs for row in self.matrix_selection_rationale_rows)
        )
        if not set(self.included_case_refs).issubset(selected_by_rationale):
            raise ValueError("included cases must be covered by selection rationale rows")
        release_candidates = {
            row.trial_lineage_ref
            for row in self.case_candidate_rows
            if row.case_ref in self.included_case_refs
        }
        release_candidates.update(
            row.retry_lineage_ref
            for row in self.case_candidate_rows
            if row.case_ref in self.included_case_refs and row.retry_lineage_ref
        )
        missing_release_refs = sorted(release_candidates - set(self.released_case_lineage_refs))
        if missing_release_refs:
            raise ValueError(
                "released_case_lineage_refs must include included case lineage refs: "
                f"{missing_release_refs}"
            )
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseLineageEligibilityReview(_MatrixBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_LINEAGE_ELIGIBILITY_REVIEW_SCHEMA] = Field(
        alias="schema"
    )
    case_lineage_eligibility_review_ref: str
    case_matrix_ref: str
    case_eligibility_rows: list[ProgrambenchLocalCaseMatrixEligibilityRow] = Field(min_length=1)
    eligible_case_refs: list[str] = Field(min_length=1)
    blocked_case_refs: list[str] = Field(default_factory=list)
    carried_blocker_refs: list[str] = Field(default_factory=list)
    carried_warning_refs: list[str] = Field(default_factory=list)
    released_family_closeout_refs: list[str] = Field(min_length=1)
    non_authority_guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_review(self) -> "ProgrambenchLocalCaseLineageEligibilityReview":
        row_refs = [row.eligibility_row_ref for row in self.case_eligibility_rows]
        _ensure_sorted_unique(row_refs, field_name="case_eligibility_rows")
        eligible_from_rows = {
            row.case_ref
            for row in self.case_eligibility_rows
            if row.eligibility_posture == "eligible_for_local_matrix_inclusion"
        }
        for field_name in (
            "eligible_case_refs",
            "blocked_case_refs",
            "carried_blocker_refs",
            "carried_warning_refs",
            "released_family_closeout_refs",
            "non_authority_guardrail_refs",
        ):
            values = getattr(self, field_name)
            if field_name in {
                "eligible_case_refs",
                "released_family_closeout_refs",
                "non_authority_guardrail_refs",
            }:
                _ensure_sorted_unique(values, field_name=field_name)
            else:
                _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        if set(self.eligible_case_refs) != eligible_from_rows:
            raise ValueError("eligible_case_refs must match eligible row case refs")
        if self.carried_blocker_refs:
            blocked_row_refs = {
                blocker for row in self.case_eligibility_rows for blocker in row.blocker_refs
            }
            unknown = sorted(set(self.carried_blocker_refs) - blocked_row_refs)
            if unknown:
                raise ValueError(
                    f"carried_blocker_refs must resolve to eligibility rows: {unknown}"
                )
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseMatrixControlContract(_MatrixBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_MATRIX_CONTROL_CONTRACT_SCHEMA] = Field(
        alias="schema"
    )
    matrix_control_contract_ref: str
    case_matrix_ref: str
    matrix_worker_profile_control_ref: str
    matrix_tool_policy_control_ref: str
    matrix_probe_basis_control_ref: str
    matrix_sandbox_policy_control_ref: str
    matrix_write_scope_control_ref: str
    matrix_visibility_control_ref: str
    worker_profile_refs: list[str] = Field(min_length=1)
    model_profile_refs: list[str] = Field(min_length=1)
    tool_policy_refs: list[str] = Field(min_length=1)
    probe_basis_refs: list[str] = Field(min_length=1)
    sandbox_policy_refs: list[str] = Field(min_length=1)
    write_scope_refs: list[str] = Field(min_length=1)
    matrix_non_ranking_posture: Literal["no_model_ranking_claimed_by_pb_matrix_0a"]
    matrix_comparability_posture: Literal[
        "single_profile_controls",
        "comparability_accounting_only_no_ranking",
    ]
    multi_profile_matrix_posture: Literal[
        "comparability_accounting_only_no_ranking",
        "single_profile_matrix",
    ]
    aggregate_count_posture: Literal[
        "coverage_accounting_only",
        "local_case_posture_count_only",
        "local_inventory_count_only",
        "not_benchmark_score",
    ]
    representativeness_posture: Literal["not_representative_benchmark_sample"]
    allowed_matrix_action_rows: list[ProgrambenchLocalCaseMatrixAllowedActionRow] = Field(
        min_length=1
    )
    forbidden_matrix_action_rows: list[ProgrambenchLocalCaseMatrixForbiddenActionRow] = Field(
        min_length=1
    )
    limitation_note: str

    @model_validator(mode="after")
    def _validate_control(self) -> "ProgrambenchLocalCaseMatrixControlContract":
        for field_name in (
            "worker_profile_refs",
            "model_profile_refs",
            "tool_policy_refs",
            "probe_basis_refs",
            "sandbox_policy_refs",
            "write_scope_refs",
        ):
            _ensure_sorted_unique(getattr(self, field_name), field_name=field_name)
            _ensure_no_forbidden_refs(getattr(self, field_name), field_name=field_name)
        single_profile = len(self.worker_profile_refs) == 1 and len(self.model_profile_refs) == 1
        single_controls = all(
            len(getattr(self, field_name)) == 1
            for field_name in (
                "tool_policy_refs",
                "probe_basis_refs",
                "sandbox_policy_refs",
                "write_scope_refs",
            )
        )
        if single_profile and single_controls:
            if self.multi_profile_matrix_posture != "single_profile_matrix":
                raise ValueError("single-profile matrices require single_profile_matrix posture")
            if self.matrix_comparability_posture != "single_profile_controls":
                raise ValueError("single-profile matrices require single_profile_controls posture")
        elif (
            self.multi_profile_matrix_posture != "comparability_accounting_only_no_ranking"
            or self.matrix_comparability_posture != "comparability_accounting_only_no_ranking"
        ):
            raise ValueError(
                "multi-profile or multi-control matrices require comparability-only posture"
            )
        allowed_refs = [row.allowed_action_ref for row in self.allowed_matrix_action_rows]
        _ensure_sorted_unique(allowed_refs, field_name="allowed_matrix_action_rows")
        forbidden_refs = [row.forbidden_action_ref for row in self.forbidden_matrix_action_rows]
        _ensure_sorted_unique(forbidden_refs, field_name="forbidden_matrix_action_rows")
        required_forbidden_actions = {
            "batch_command_execution",
            "benchmark_scoring",
            "candidate_materialization",
            "decompilation",
            "docker_socket_access",
            "external_repo_lookup",
            "hidden_test_access",
            "host_secret_access",
            "internet_lookup",
            "matrix_result_projection",
            "model_ranking",
            "official_evaluator_access",
            "official_submission",
            "second_retry_authority",
            "source_lookup",
            "widen_write_scope",
        }
        observed = {row.action_kind for row in self.forbidden_matrix_action_rows}
        if len(observed) != len(self.forbidden_matrix_action_rows):
            raise ValueError("forbidden_matrix_action_rows must not contain duplicate action kinds")
        missing = sorted(required_forbidden_actions - observed)
        if missing:
            raise ValueError(f"matrix control missing forbidden action kinds: {missing}")
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseMatrixNonAuthorityGuardrail(_MatrixBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_MATRIX_NON_AUTHORITY_GUARDRAIL_SCHEMA] = Field(
        alias="schema"
    )
    matrix_guardrail_ref: str
    case_matrix_refs: list[str] = Field(min_length=1)
    guardrail_source_refs: list[str] = Field(min_length=1)
    non_authority_rows: list[ProgrambenchLocalCaseMatrixForbiddenAuthorityRow] = Field(min_length=1)
    forbidden_future_artifact_kinds: list[str] = Field(min_length=1)
    official_programbench_posture: Literal[
        "no_official_programbench_authority_granted_by_pb_matrix_0a"
    ]
    hidden_test_posture: Literal["hidden_tests_not_visible_not_inference_evidence"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    model_ranking_posture: Literal["no_model_ranking_claimed_by_pb_matrix_0a"]
    batch_execution_posture: Literal["no_batch_execution_authority_granted_by_pb_matrix_0a"]
    second_retry_posture: Literal["no_second_retry_authority_granted_by_pb_matrix_0a"]
    future_family_posture: Literal["no_future_family_selected_by_pb_matrix_0a"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_guardrail(self) -> "ProgrambenchLocalCaseMatrixNonAuthorityGuardrail":
        _ensure_sorted_unique(self.case_matrix_refs, field_name="case_matrix_refs")
        _ensure_sorted_unique(self.guardrail_source_refs, field_name="guardrail_source_refs")
        row_refs = [row.forbidden_authority_ref for row in self.non_authority_rows]
        _ensure_sorted_unique(row_refs, field_name="non_authority_rows")
        required_authorities = {
            "batch_execution",
            "benchmark_score",
            "benchmark_truth",
            "candidate_materialization",
            "contamination_register",
            "coverage_register",
            "future_family_selection",
            "hidden_test_inference",
            "matrix_handoff",
            "matrix_observation_ledger",
            "matrix_summary",
            "model_ranking",
            "official_programbench_participation",
            "official_submission",
            "per_case_result_projection",
            "retry_chain",
            "second_retry",
        }
        observed = {row.authority_kind for row in self.non_authority_rows}
        if len(observed) != len(self.non_authority_rows):
            raise ValueError("non_authority_rows must not contain duplicate authority kinds")
        missing = sorted(required_authorities - observed)
        if missing:
            raise ValueError(f"matrix guardrail missing forbidden authorities: {missing}")
        _ensure_sorted_unique(
            self.forbidden_future_artifact_kinds,
            field_name="forbidden_future_artifact_kinds",
        )
        missing_future = sorted(
            PB_MATRIX_0A_REQUIRED_FORBIDDEN_FUTURE_ARTIFACT_KINDS
            - set(self.forbidden_future_artifact_kinds)
        )
        if missing_future:
            raise ValueError(f"matrix guardrail missing future artifact kinds: {missing_future}")
        current = sorted(PB_MATRIX_0A_ARTIFACT_KINDS & set(self.forbidden_future_artifact_kinds))
        if current:
            raise ValueError(f"matrix guardrail cannot forbid current A artifact kinds: {current}")
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseMatrixProjectionBasisRow(_MatrixBase):
    projection_basis_ref: str
    case_ref: str
    source_result_ref: str
    source_result_hash: str
    source_family_closeout_ref: str
    projection_rule_ref: str
    basis_kind: Literal[
        "released_local_retry_settlement",
        "released_local_trial_outcome",
        "projection_gap_basis",
    ]
    basis_scope_posture: Literal["local_matrix_projection_basis_only_not_new_truth"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_basis(self) -> "ProgrambenchLocalCaseMatrixProjectionBasisRow":
        _ensure_hash(self.source_result_hash, field_name="source_result_hash")
        _ensure_no_forbidden_refs(
            [
                self.case_ref,
                self.source_result_ref,
                self.source_family_closeout_ref,
                self.projection_rule_ref,
            ],
            field_name="projection_basis_row refs",
        )
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseMatrixProjectionCaseRow(_MatrixBase):
    projection_case_row_ref: str
    case_ref: str
    source_result_ref: str
    source_result_hash: str
    source_family_closeout_ref: str
    projection_rule_ref: str
    projection_basis_refs: list[str] = Field(min_length=1)
    projection_currentness: Literal[
        "current_projection",
        "projection_gap_declared",
    ]
    projected_result_posture: Literal[
        "local_case_blocked",
        "local_case_inconclusive",
        "local_case_remanded",
        "local_case_resolved",
        "projection_gap",
    ]
    projection_gap_ref: str | None = None
    projection_gap_reason: Literal[
        "not_applicable",
        "missing_current_result",
        "source_result_unreleased",
        "blocked_by_contamination",
    ]
    retry_remand_pressure_posture: Literal[
        "not_applicable",
        "unresolved_remand_pressure_preserved",
        "settled_remand_preserved",
    ]
    projection_is_not_new_truth_posture: Literal["derived_local_projection_not_new_truth"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_projection_case_row(self) -> "ProgrambenchLocalCaseMatrixProjectionCaseRow":
        _ensure_hash(self.source_result_hash, field_name="source_result_hash")
        _ensure_sorted_unique(self.projection_basis_refs, field_name="projection_basis_refs")
        _ensure_no_forbidden_refs(
            [
                self.case_ref,
                self.source_result_ref,
                self.source_family_closeout_ref,
                self.projection_rule_ref,
                *self.projection_basis_refs,
            ],
            field_name="projection_case_row refs",
        )
        if self.projection_currentness == "current_projection":
            if self.projected_result_posture == "projection_gap":
                raise ValueError("current projection rows cannot carry projection_gap posture")
            if self.projection_gap_ref is not None:
                raise ValueError("current projection rows cannot carry projection_gap_ref")
            if self.projection_gap_reason != "not_applicable":
                raise ValueError("current projection rows require not_applicable gap reason")
        else:
            if self.projected_result_posture != "projection_gap":
                raise ValueError("projection gaps require projection_gap result posture")
            if not self.projection_gap_ref:
                raise ValueError("projection gaps require projection_gap_ref")
            if self.projection_gap_reason == "not_applicable":
                raise ValueError("projection gaps require a concrete gap reason")
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseMatrixObservationRow(_MatrixBase):
    observation_ref: str
    case_ref: str
    source_projection_case_row_ref: str
    observation_kind: Literal[
        "local_blocker_observed",
        "local_gap_observed",
        "local_projection_observed",
        "local_remand_observed",
    ]
    observation_text: str
    observation_scope_posture: Literal["local_matrix_observation_only_not_ranking"]
    blocked_observation_reason: Literal[
        "not_applicable",
        "projection_gap",
        "contamination_blocked",
    ]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_observation_row(self) -> "ProgrambenchLocalCaseMatrixObservationRow":
        _ensure_no_forbidden_refs(
            [self.case_ref, self.source_projection_case_row_ref],
            field_name="observation_row refs",
        )
        _ensure_no_soft_scoring_language(self.observation_text, field_name="observation_text")
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        is_blocked_observation = self.observation_kind in {
            "local_blocker_observed",
            "local_gap_observed",
        }
        has_blocked_reason = self.blocked_observation_reason != "not_applicable"
        if is_blocked_observation and not has_blocked_reason:
            raise ValueError(f"{self.observation_kind} requires a blocked reason")
        if not is_blocked_observation and has_blocked_reason:
            raise ValueError(
                f"{self.observation_kind} cannot carry a blocked observation reason"
            )
        return self


class ProgrambenchLocalCaseMatrixCoverageRow(_MatrixBase):
    coverage_row_ref: str
    case_ref: str
    coverage_kind: Literal[
        "local_result_projection_coverage",
        "local_observation_coverage",
        "local_contamination_review_coverage",
    ]
    coverage_status: Literal["covered", "missing_local_coverage"]
    coverage_basis_refs: list[str] = Field(default_factory=list)
    coverage_scope_posture: Literal["local_matrix_coverage_only_not_hidden_test_coverage"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_coverage_row(self) -> "ProgrambenchLocalCaseMatrixCoverageRow":
        _ensure_sorted_unique_allow_empty(
            self.coverage_basis_refs,
            field_name="coverage_basis_refs",
        )
        _ensure_no_forbidden_refs(
            [self.case_ref, *self.coverage_basis_refs],
            field_name="coverage_row refs",
        )
        if self.coverage_status == "covered" and not self.coverage_basis_refs:
            raise ValueError("covered matrix cases require local coverage basis refs")
        if self.coverage_status == "missing_local_coverage" and self.coverage_basis_refs:
            raise ValueError("missing coverage rows cannot carry coverage basis refs")
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseMatrixContaminationRow(_MatrixBase):
    contamination_row_ref: str
    case_ref: str
    contamination_kind: Literal[
        "clean",
        "excluded_derived_summary",
        "forbidden_source_exposure",
        "hidden_test_exposure",
        "official_evaluator_exposure",
    ]
    contamination_posture: Literal["blocked", "clean"]
    redacted_detail_note: str
    contamination_redaction_policy: Literal["redacted_category_count_reason_only"]
    contamination_detail_posture: Literal["no_forbidden_names_paths_excerpts_or_summaries"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_contamination_row(self) -> "ProgrambenchLocalCaseMatrixContaminationRow":
        _ensure_no_forbidden_refs([self.case_ref], field_name="contamination_row refs")
        for field_name in ("redacted_detail_note", "limitation_note"):
            value = getattr(self, field_name)
            _ensure_no_soft_scoring_language(value, field_name=field_name)
            lowered = value.lower()
            leaked = [marker for marker in _FORBIDDEN_REF_MARKERS if marker in lowered]
            if leaked:
                raise ValueError(
                    f"{field_name} contains forbidden contamination detail markers: {leaked}"
                )
        if self.contamination_kind == "clean" and self.contamination_posture != "clean":
            raise ValueError("clean contamination rows require clean posture")
        if self.contamination_kind != "clean" and self.contamination_posture != "blocked":
            raise ValueError("non-clean contamination rows require blocked posture")
        return self


class ProgrambenchLocalCaseMatrixResultProjection(_MatrixBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_MATRIX_RESULT_PROJECTION_SCHEMA] = Field(
        alias="schema"
    )
    matrix_result_projection_ref: str
    case_matrix_ref: str
    matrix_request_ref: str
    case_inclusion_manifest_ref: str
    case_lineage_eligibility_review_ref: str
    matrix_control_contract_ref: str
    matrix_guardrail_ref: str
    projection_case_rows: list[ProgrambenchLocalCaseMatrixProjectionCaseRow] = Field(min_length=1)
    included_case_refs: list[str] = Field(min_length=1)
    source_trial_outcome_refs: list[str] = Field(default_factory=list)
    source_retry_outcome_refs: list[str] = Field(default_factory=list)
    source_retry_settlement_refs: list[str] = Field(default_factory=list)
    source_result_ref: str
    source_result_hash: str
    source_family_closeout_ref: str
    projection_rule_ref: str
    projection_basis_rows: list[ProgrambenchLocalCaseMatrixProjectionBasisRow] = Field(min_length=1)
    projection_currentness: Literal[
        "all_included_cases_current_or_gap_declared",
        "projection_gap_declared",
    ]
    projection_gap_reason: Literal[
        "not_applicable",
        "missing_current_result",
        "source_result_unreleased",
        "blocked_by_contamination",
    ]
    projection_is_not_new_truth_posture: Literal["derived_local_projection_not_new_truth"]
    projected_case_result_rows: list[str] = Field(min_length=1)
    projection_gap_refs: list[str] = Field(default_factory=list)
    projection_authority_posture: Literal["no_new_outcome_truth_created_by_pb_matrix_0b"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_projection(self) -> "ProgrambenchLocalCaseMatrixResultProjection":
        for field_name in (
            "included_case_refs",
            "source_trial_outcome_refs",
            "source_retry_outcome_refs",
            "source_retry_settlement_refs",
            "projected_case_result_rows",
            "projection_gap_refs",
        ):
            values = getattr(self, field_name)
            if field_name in {"included_case_refs", "projected_case_result_rows"}:
                _ensure_sorted_unique(values, field_name=field_name)
            else:
                _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        _ensure_hash(self.source_result_hash, field_name="source_result_hash")
        row_refs = [row.projection_case_row_ref for row in self.projection_case_rows]
        _ensure_sorted_unique(row_refs, field_name="projection_case_rows")
        basis_refs = [row.projection_basis_ref for row in self.projection_basis_rows]
        _ensure_sorted_unique(basis_refs, field_name="projection_basis_rows")
        row_case_refs = [row.case_ref for row in self.projection_case_rows]
        if sorted(row_case_refs) != self.included_case_refs:
            raise ValueError("projection rows must cover every included case exactly once")
        if self.projected_case_result_rows != row_refs:
            raise ValueError("projected_case_result_rows must match projection row refs")
        gap_refs = [
            row.projection_gap_ref
            for row in self.projection_case_rows
            if row.projection_gap_ref is not None
        ]
        if self.projection_gap_refs != gap_refs:
            raise ValueError("projection_gap_refs must match projection gap rows")
        if self.projection_gap_refs and self.projection_gap_reason == "not_applicable":
            raise ValueError("top-level projection gap reason must describe gap rows")
        if not self.projection_gap_refs and self.projection_gap_reason != "not_applicable":
            raise ValueError("top-level projection gap reason requires gap refs")
        basis_by_ref = {row.projection_basis_ref: row for row in self.projection_basis_rows}
        for row in self.projection_case_rows:
            _ensure_refs_resolve(
                row.projection_basis_refs,
                set(basis_by_ref),
                field_name="projection_case_row.projection_basis_refs",
            )
            for basis_ref in row.projection_basis_refs:
                if basis_by_ref[basis_ref].case_ref != row.case_ref:
                    raise ValueError("projection basis rows must match projection case refs")
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseMatrixObservationLedger(_MatrixBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_MATRIX_OBSERVATION_LEDGER_SCHEMA] = Field(
        alias="schema"
    )
    matrix_observation_ledger_ref: str
    case_matrix_ref: str
    observation_rows: list[ProgrambenchLocalCaseMatrixObservationRow] = Field(min_length=1)
    local_observation_refs: list[str] = Field(min_length=1)
    blocked_observation_refs: list[str] = Field(default_factory=list)
    non_ranking_posture: Literal["local_observations_only_no_model_ranking"]
    benchmark_truth_posture: Literal["not_benchmark_truth"]
    soft_scoring_language_posture: Literal["soft_scoring_language_rejected"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_observation_ledger(self) -> "ProgrambenchLocalCaseMatrixObservationLedger":
        row_refs = [row.observation_ref for row in self.observation_rows]
        _ensure_sorted_unique(row_refs, field_name="observation_rows")
        _ensure_sorted_unique(self.local_observation_refs, field_name="local_observation_refs")
        _ensure_sorted_unique_allow_empty(
            self.blocked_observation_refs,
            field_name="blocked_observation_refs",
        )
        local_from_rows = [
            row.observation_ref
            for row in self.observation_rows
            if row.blocked_observation_reason == "not_applicable"
        ]
        if self.local_observation_refs != local_from_rows:
            raise ValueError("local_observation_refs must match unblocked observation rows")
        blocked_from_rows = [
            row.observation_ref
            for row in self.observation_rows
            if row.blocked_observation_reason != "not_applicable"
        ]
        if self.blocked_observation_refs != blocked_from_rows:
            raise ValueError("blocked_observation_refs must match blocked observation rows")
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseMatrixCoverageRegister(_MatrixBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_MATRIX_COVERAGE_REGISTER_SCHEMA] = Field(
        alias="schema"
    )
    matrix_coverage_register_ref: str
    case_matrix_ref: str
    coverage_rows: list[ProgrambenchLocalCaseMatrixCoverageRow] = Field(min_length=1)
    covered_case_refs: list[str] = Field(default_factory=list)
    missing_coverage_case_refs: list[str] = Field(default_factory=list)
    local_coverage_basis_refs: list[str] = Field(min_length=1)
    coverage_denominator_posture: Literal["declared_local_matrix_cases_only"]
    coverage_basis_scope: Literal["local_probe_and_projection_basis_only"]
    hidden_test_coverage_exclusion_posture: Literal["hidden_tests_excluded_from_coverage"]
    hidden_test_coverage_posture: Literal["no_hidden_test_coverage_claimed"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_coverage_register(self) -> "ProgrambenchLocalCaseMatrixCoverageRegister":
        row_refs = [row.coverage_row_ref for row in self.coverage_rows]
        _ensure_sorted_unique(row_refs, field_name="coverage_rows")
        for field_name in (
            "covered_case_refs",
            "missing_coverage_case_refs",
            "local_coverage_basis_refs",
        ):
            values = getattr(self, field_name)
            if field_name == "local_coverage_basis_refs":
                _ensure_sorted_unique(values, field_name=field_name)
            else:
                _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        covered_from_rows = {
            row.case_ref for row in self.coverage_rows if row.coverage_status == "covered"
        }
        missing_from_rows = {
            row.case_ref
            for row in self.coverage_rows
            if row.coverage_status == "missing_local_coverage"
        }
        if set(self.covered_case_refs) != covered_from_rows:
            raise ValueError("covered_case_refs must match covered coverage rows")
        if set(self.missing_coverage_case_refs) != missing_from_rows:
            raise ValueError("missing_coverage_case_refs must match missing coverage rows")
        basis_from_rows = {
            basis_ref for row in self.coverage_rows for basis_ref in row.coverage_basis_refs
        }
        if set(self.local_coverage_basis_refs) != basis_from_rows:
            raise ValueError("local_coverage_basis_refs must match coverage row basis refs")
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


class ProgrambenchLocalCaseMatrixContaminationRegister(_MatrixBase):
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_MATRIX_CONTAMINATION_REGISTER_SCHEMA] = Field(
        alias="schema"
    )
    matrix_contamination_register_ref: str
    case_matrix_ref: str
    contamination_rows: list[ProgrambenchLocalCaseMatrixContaminationRow] = Field(min_length=1)
    clean_case_refs: list[str] = Field(default_factory=list)
    blocked_case_refs: list[str] = Field(default_factory=list)
    forbidden_exposure_refs: list[str] = Field(default_factory=list)
    excluded_derived_summary_refs: list[str] = Field(default_factory=list)
    contamination_redaction_policy: Literal["redacted_category_count_reason_only"]
    contamination_detail_posture: Literal["no_forbidden_names_paths_excerpts_or_summaries"]
    contamination_status: Literal["blocked", "clean"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_contamination_register(
        self,
    ) -> "ProgrambenchLocalCaseMatrixContaminationRegister":
        row_refs = [row.contamination_row_ref for row in self.contamination_rows]
        _ensure_sorted_unique(row_refs, field_name="contamination_rows")
        for field_name in (
            "clean_case_refs",
            "blocked_case_refs",
            "forbidden_exposure_refs",
            "excluded_derived_summary_refs",
        ):
            values = getattr(self, field_name)
            _ensure_sorted_unique_allow_empty(values, field_name=field_name)
            _ensure_no_forbidden_refs(values, field_name=field_name)
        clean_from_rows = {
            row.case_ref for row in self.contamination_rows if row.contamination_posture == "clean"
        }
        blocked_from_rows = {
            row.case_ref
            for row in self.contamination_rows
            if row.contamination_posture == "blocked"
        }
        if set(self.clean_case_refs) != clean_from_rows:
            raise ValueError("clean_case_refs must match clean contamination rows")
        if set(self.blocked_case_refs) != blocked_from_rows:
            raise ValueError("blocked_case_refs must match blocked contamination rows")
        if self.contamination_status == "clean" and (
            self.blocked_case_refs
            or self.forbidden_exposure_refs
            or self.excluded_derived_summary_refs
        ):
            raise ValueError("clean contamination register cannot carry blocked/exposure refs")
        if self.contamination_status == "blocked" and not self.blocked_case_refs:
            raise ValueError("blocked contamination register requires blocked case refs")
        _ensure_no_soft_scoring_language(self.limitation_note, field_name="limitation_note")
        return self


def validate_pb_matrix_0a_case_matrix_bundle(
    *,
    trial_family_closeout: ProgrambenchLocalTrialFamilyCloseoutAlignment,
    retry_family_closeout: ProgrambenchLocalRetryFamilyCloseoutAlignment | None,
    matrix_request: ProgrambenchLocalCaseMatrixRequest,
    inclusion_manifest: ProgrambenchLocalCaseInclusionManifest,
    lineage_eligibility_review: ProgrambenchLocalCaseLineageEligibilityReview,
    matrix_control_contract: ProgrambenchLocalCaseMatrixControlContract,
    matrix_guardrail: ProgrambenchLocalCaseMatrixNonAuthorityGuardrail,
) -> None:
    if trial_family_closeout.closed_family_ref != "PB-TRIAL-0":
        raise ValueError("matrix inclusion requires released PB-TRIAL-0 closeout")
    if (
        retry_family_closeout is not None
        and retry_family_closeout.family_closeout_posture != "pb_retry_0_closed_local_retry_only"
    ):
        raise ValueError("retry-settlement matrix inclusion requires released PB-RETRY-0 closeout")

    if inclusion_manifest.case_matrix_ref != matrix_request.case_matrix_ref:
        raise ValueError("inclusion manifest must reference matrix request case_matrix_ref")
    if matrix_request.case_inclusion_manifest_ref != (
        inclusion_manifest.case_inclusion_manifest_ref
    ):
        raise ValueError("matrix request must reference inclusion manifest")
    if lineage_eligibility_review.case_matrix_ref != matrix_request.case_matrix_ref:
        raise ValueError("lineage eligibility review must reference matrix request")
    if matrix_request.case_lineage_eligibility_review_ref != (
        lineage_eligibility_review.case_lineage_eligibility_review_ref
    ):
        raise ValueError("matrix request must reference lineage eligibility review")
    if matrix_control_contract.case_matrix_ref != matrix_request.case_matrix_ref:
        raise ValueError("matrix control contract must reference matrix request")
    if matrix_request.matrix_control_contract_ref != (
        matrix_control_contract.matrix_control_contract_ref
    ):
        raise ValueError("matrix request must reference matrix control contract")
    if matrix_request.case_matrix_ref not in matrix_guardrail.case_matrix_refs:
        raise ValueError("matrix guardrail must reference matrix request")

    if matrix_request.matrix_case_candidate_refs != [
        row.case_ref for row in inclusion_manifest.case_candidate_rows
    ]:
        raise ValueError("matrix request candidate refs must match inclusion manifest rows")
    if matrix_request.matrix_selection_rationale_refs != [
        row.selection_rationale_ref for row in inclusion_manifest.matrix_selection_rationale_rows
    ]:
        raise ValueError("matrix request rationale refs must match manifest rationale rows")
    if matrix_request.requested_case_count != len(inclusion_manifest.included_case_refs):
        raise ValueError("requested case count must equal included case count")
    if matrix_request.requested_case_count > matrix_request.matrix_max_case_count:
        raise ValueError("included case count cannot exceed matrix max case count")
    if matrix_request.aggregate_count_posture != matrix_control_contract.aggregate_count_posture:
        raise ValueError("aggregate count posture must match matrix control contract")
    if matrix_request.representativeness_posture != (
        matrix_control_contract.representativeness_posture
    ):
        raise ValueError("representativeness posture must match matrix control contract")

    included = set(inclusion_manifest.included_case_refs)
    eligible = set(lineage_eligibility_review.eligible_case_refs)
    if included != eligible:
        raise ValueError("included cases must match eligible case refs")
    candidate_refs = {row.case_ref for row in inclusion_manifest.case_candidate_rows}
    eligibility_case_refs = {
        row.case_ref for row in lineage_eligibility_review.case_eligibility_rows
    }
    if candidate_refs != eligibility_case_refs:
        missing = sorted(candidate_refs - eligibility_case_refs)
        extra = sorted(eligibility_case_refs - candidate_refs)
        raise ValueError(
            "lineage eligibility rows must cover every matrix case candidate; "
            f"missing={missing}, extra={extra}"
        )

    trial_closeout_refs = set(trial_family_closeout.trial_docket_refs)
    retry_settlement_refs = (
        set(retry_family_closeout.retry_remand_settlement_refs)
        if retry_family_closeout is not None
        else set()
    )
    for row in inclusion_manifest.case_candidate_rows:
        if row.case_ref not in included:
            continue
        if row.trial_ref not in trial_closeout_refs:
            raise ValueError("included matrix case must resolve to released trial lineage")
        if row.case_lineage_kind == "trial_with_retry_settlement":
            if retry_family_closeout is None:
                raise ValueError("retry-settlement matrix case requires PB-RETRY-0 closeout")
            if row.retry_settlement_ref not in retry_settlement_refs:
                raise ValueError(
                    "included retry matrix case must resolve to released retry settlement"
                )
    if matrix_guardrail.matrix_guardrail_ref not in (
        lineage_eligibility_review.non_authority_guardrail_refs
    ):
        raise ValueError("lineage eligibility review must release matrix guardrail")
    if matrix_request.official_benchmark_authority_posture != (
        "no_official_programbench_authority_granted_by_pb_matrix_0a"
    ):
        raise ValueError("matrix request must deny official benchmark authority")
    if matrix_guardrail.benchmark_truth_posture != "not_benchmark_truth":
        raise ValueError("matrix guardrail must deny benchmark truth")


def validate_pb_matrix_0b_projection_bundle(
    *,
    matrix_request: ProgrambenchLocalCaseMatrixRequest,
    inclusion_manifest: ProgrambenchLocalCaseInclusionManifest,
    lineage_eligibility_review: ProgrambenchLocalCaseLineageEligibilityReview,
    matrix_control_contract: ProgrambenchLocalCaseMatrixControlContract,
    matrix_guardrail: ProgrambenchLocalCaseMatrixNonAuthorityGuardrail,
    result_projection: ProgrambenchLocalCaseMatrixResultProjection,
    observation_ledger: ProgrambenchLocalCaseMatrixObservationLedger,
    coverage_register: ProgrambenchLocalCaseMatrixCoverageRegister,
    contamination_register: ProgrambenchLocalCaseMatrixContaminationRegister,
) -> None:
    if result_projection.case_matrix_ref != matrix_request.case_matrix_ref:
        raise ValueError("result projection must reference matrix request")
    if result_projection.matrix_request_ref != matrix_request.matrix_request_ref:
        raise ValueError("result projection must reference released A request")
    if result_projection.case_inclusion_manifest_ref != (
        inclusion_manifest.case_inclusion_manifest_ref
    ):
        raise ValueError("result projection must reference released A inclusion manifest")
    if result_projection.case_lineage_eligibility_review_ref != (
        lineage_eligibility_review.case_lineage_eligibility_review_ref
    ):
        raise ValueError("result projection must reference released A eligibility review")
    if result_projection.matrix_control_contract_ref != (
        matrix_control_contract.matrix_control_contract_ref
    ):
        raise ValueError("result projection must reference released A control contract")
    if result_projection.matrix_guardrail_ref != matrix_guardrail.matrix_guardrail_ref:
        raise ValueError("result projection must reference released A guardrail")
    for artifact in (observation_ledger, coverage_register, contamination_register):
        if artifact.case_matrix_ref != matrix_request.case_matrix_ref:
            raise ValueError("PB-MATRIX-0-B artifacts must share one case_matrix_ref")

    included = set(inclusion_manifest.included_case_refs)
    if set(result_projection.included_case_refs) != included:
        raise ValueError("result projection included cases must match A included cases")
    if set(lineage_eligibility_review.eligible_case_refs) != included:
        raise ValueError("B projection requires released eligible A cases")
    projection_case_refs = {row.case_ref for row in result_projection.projection_case_rows}
    if projection_case_refs != included:
        raise ValueError("result projection rows must cover all A-included cases")
    if result_projection.projection_authority_posture != (
        "no_new_outcome_truth_created_by_pb_matrix_0b"
    ):
        raise ValueError("result projection cannot create new outcome truth")

    a_candidate_by_case = {row.case_ref: row for row in inclusion_manifest.case_candidate_rows}
    for projection_row in result_projection.projection_case_rows:
        candidate = a_candidate_by_case[projection_row.case_ref]
        if candidate.case_lineage_kind == "trial_with_retry_settlement":
            if projection_row.source_result_ref != candidate.retry_settlement_ref:
                raise ValueError(
                    "retry-settlement matrix projections must match A-admitted settlement"
                )
            if (
                projection_row.source_result_ref
                not in result_projection.source_retry_settlement_refs
            ):
                raise ValueError(
                    "retry-settlement matrix projections must cite retry settlement refs"
                )
            if projection_row.retry_remand_pressure_posture == "not_applicable":
                raise ValueError(
                    "retry-settlement matrix projections must preserve remand pressure"
                )
        else:
            if projection_row.source_result_ref not in result_projection.source_trial_outcome_refs:
                raise ValueError("trial-only matrix projections must cite trial outcome refs")
            if projection_row.retry_remand_pressure_posture != "not_applicable":
                raise ValueError("trial-only matrix projections cannot carry retry remand posture")

    projection_row_refs = {
        row.projection_case_row_ref for row in result_projection.projection_case_rows
    }
    observation_case_refs = {row.case_ref for row in observation_ledger.observation_rows}
    if observation_case_refs - included:
        raise ValueError("observation rows may reference only A-included cases")
    _ensure_refs_resolve(
        [row.source_projection_case_row_ref for row in observation_ledger.observation_rows],
        projection_row_refs,
        field_name="observation source projection refs",
    )

    coverage_case_refs = {row.case_ref for row in coverage_register.coverage_rows}
    if coverage_case_refs != included:
        raise ValueError("coverage register rows must cover all A-included cases")
    if coverage_register.hidden_test_coverage_posture != "no_hidden_test_coverage_claimed":
        raise ValueError("coverage register cannot claim hidden-test coverage")
    if coverage_register.coverage_denominator_posture != "declared_local_matrix_cases_only":
        raise ValueError("coverage denominator must be local matrix cases only")

    contamination_case_refs = {row.case_ref for row in contamination_register.contamination_rows}
    if contamination_case_refs != included:
        raise ValueError("contamination register rows must cover all A-included cases")
    if contamination_register.contamination_status != "clean":
        raise ValueError("PB-MATRIX-0-B reference bundle requires clean contamination status")

    if matrix_control_contract.matrix_non_ranking_posture != (
        "no_model_ranking_claimed_by_pb_matrix_0a"
    ):
        raise ValueError("B requires A non-ranking controls")
    if matrix_guardrail.batch_execution_posture != (
        "no_batch_execution_authority_granted_by_pb_matrix_0a"
    ):
        raise ValueError("B requires A batch-execution denial")
