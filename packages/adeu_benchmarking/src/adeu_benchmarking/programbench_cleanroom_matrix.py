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

PROGRAMBENCH_LOCAL_CASE_MATRIX_REQUEST_SCHEMA = (
    "programbench_local_case_matrix_request@1"
)
PROGRAMBENCH_LOCAL_CASE_INCLUSION_MANIFEST_SCHEMA = (
    "programbench_local_case_inclusion_manifest@1"
)
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
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_MATRIX_REQUEST_SCHEMA] = Field(
        alias="schema"
    )
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
    schema_id: Literal[PROGRAMBENCH_LOCAL_CASE_INCLUSION_MANIFEST_SCHEMA] = Field(
        alias="schema"
    )
    case_inclusion_manifest_ref: str
    case_matrix_ref: str
    case_candidate_rows: list[ProgrambenchLocalCaseMatrixCandidateRow] = Field(
        min_length=1
    )
    matrix_selection_rationale_rows: list[
        ProgrambenchLocalCaseMatrixSelectionRationaleRow
    ] = Field(min_length=1)
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
            ref
            for ref in all_case_refs
            if sum(ref in refs for refs in decision_refs.values()) > 1
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
    schema_id: Literal[
        PROGRAMBENCH_LOCAL_CASE_LINEAGE_ELIGIBILITY_REVIEW_SCHEMA
    ] = Field(alias="schema")
    case_lineage_eligibility_review_ref: str
    case_matrix_ref: str
    case_eligibility_rows: list[ProgrambenchLocalCaseMatrixEligibilityRow] = Field(
        min_length=1
    )
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
                blocker
                for row in self.case_eligibility_rows
                for blocker in row.blocker_refs
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
    forbidden_matrix_action_rows: list[
        ProgrambenchLocalCaseMatrixForbiddenActionRow
    ] = Field(min_length=1)
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
        elif self.multi_profile_matrix_posture != "comparability_accounting_only_no_ranking":
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
    non_authority_rows: list[ProgrambenchLocalCaseMatrixForbiddenAuthorityRow] = Field(
        min_length=1
    )
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

    if sorted(matrix_request.matrix_case_candidate_refs) != [
        row.case_ref for row in inclusion_manifest.case_candidate_rows
    ]:
        raise ValueError("matrix request candidate refs must match inclusion manifest rows")
    if sorted(matrix_request.matrix_selection_rationale_refs) != [
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
                raise ValueError(
                    "retry-settlement matrix case requires PB-RETRY-0 closeout"
                )
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
