from __future__ import annotations

import re
from pathlib import Path
from typing import Literal

from pydantic import Field, model_validator

from .arc_series_cartography import (
    SourceStatus,
    _CartographyBase,
    _non_empty,
    _repo_ref,
    _sorted_unique,
    _sorted_unique_by_ref,
)
from .candidate_review_classification import _surface_id
from .recursive_candidate_intake import (
    CandidateAuthorityLayer,
    CandidateSourceKind,
    CandidateSourcePresencePosture,
    OdeuLane,
)

REPO_EXTERNAL_BRANCH_REVIEW_REQUEST_SCHEMA = "repo_external_branch_review_request@1"
REPO_EXTERNAL_BRANCH_SOURCE_INDEX_SCHEMA = "repo_external_branch_source_index@1"
REPO_EXTERNAL_BRANCH_NON_ACTIVATION_GUARDRAIL_SCHEMA = (
    "repo_external_branch_non_activation_guardrail@1"
)
REPO_EXTERNAL_DATA_BOUNDARY_SCHEMA = "repo_external_data_boundary@1"
REPO_EXTERNAL_TOOL_BOUNDARY_SCHEMA = "repo_external_tool_boundary@1"
REPO_EXTERNAL_SUBMISSION_AUTHORITY_REVIEW_SCHEMA = "repo_external_submission_authority_review@1"
REPO_EXTERNAL_RESULT_PROVENANCE_CONTRACT_SCHEMA = "repo_external_result_provenance_contract@1"
REPO_EXTERNAL_BRANCH_EXCEPTION_REGISTER_SCHEMA = "repo_external_branch_exception_register@1"

ExternalBranchSourceRole = Literal[
    "v79_controlled_execution_summary_source",
    "v79_post_controlled_execution_review_handoff_source",
    "v79_family_closeout_source",
    "v79_combined_dogfood_context",
    "post_v74_roadmap_context",
    "v43_branch_posture_source",
    "v43_branch_posture_absence_marker",
    "external_objective_source",
    "support_process_context",
    "absence_marker",
]
ExternalBranchPostureCurrentness = Literal[
    "current_branch_posture",
    "historical_branch_planning_context",
    "explicit_absence_marker",
    "stale_or_superseded",
    "unknown_needs_review",
]
ExternalObjectiveKind = Literal[
    "arc_contest_participation_review",
    "external_benchmark_review",
    "external_corpus_ingestion_review",
    "external_tool_endpoint_review",
    "product_externalization_review",
    "external_result_claim_review",
    "future_family_only",
]
ExternalBranchReviewPosture = Literal[
    "request_recorded_objective_only",
    "eligible_for_external_branch_review",
    "blocked_by_missing_source",
    "blocked_by_missing_v43_branch_posture",
    "blocked_by_missing_external_objective",
    "blocked_by_product_authority_gap",
    "blocked_by_runtime_authority_gap",
    "future_family_only",
    "rejected_out_of_scope",
]
ExternalBranchRequestedHorizon = Literal[
    "data_boundary_required_later",
    "tool_boundary_required_later",
    "submission_authority_required_later",
    "not_selected_in_v80a",
    "blocked_by_missing_v43_branch_posture",
    "blocked_by_missing_authority",
    "future_family_only",
]
ExternalBranchRequirementPosture = Literal[
    "required_for_later_review",
    "not_selected_in_v80a",
    "not_applicable",
    "blocked_by_missing_v43_branch_posture",
    "blocked_by_missing_authority",
    "future_family_only",
]
ExternalActivationPosture = Literal[
    "no_external_branch_activation_performed_by_v80",
    "external_activation_requires_later_family",
    "external_activation_forbidden_by_this_family",
]
ExternalSubmissionPosture = Literal[
    "no_external_submission_performed_by_v80",
    "submission_requires_later_family",
    "submission_forbidden_by_this_family",
]
ExternalToolInvocationPosture = Literal[
    "no_external_tool_invocation_performed_by_v80",
    "external_tool_invocation_requires_later_family",
    "external_tool_invocation_forbidden_by_this_family",
]
ExternalBranchExecutionPosture = Literal[
    "no_execution_performed_by_v80",
    "execution_requires_later_family",
    "execution_forbidden_by_this_family",
]
ExternalForbiddenAction = Literal[
    "activate_external_branch",
    "enter_v43_contest",
    "submit_externally",
    "invoke_external_tool_for_effect",
    "mutate_external_endpoint",
    "transfer_external_data",
    "claim_external_result_truth",
    "run_command",
    "invoke_tool_for_effect",
    "assign_worker",
    "dispatch_worker",
    "open_pr",
    "commit",
    "merge",
    "release",
]
ExternalForbiddenDownstreamAuthority = Literal[
    "external_branch_activation",
    "v43_contest_participation",
    "external_submission",
    "external_tool_invocation",
    "external_result_truth",
    "product_authorization",
    "released_truth",
    "benchmark_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
    "v81_selection",
]
ExternalDataKind = Literal[
    "contest_prompt_metadata",
    "external_objective_metadata",
    "external_result_metadata",
    "product_externalization_context",
    "no_external_data_selected",
]
ExternalAllowedDataReviewAction = Literal[
    "describe_data_boundary",
    "inspect_source_metadata",
    "record_absence_posture",
    "request_later_data_authority_review",
    "preserve_data_gap",
]
ExternalForbiddenDataAction = Literal[
    "ingest_external_data",
    "export_repo_data",
    "transfer_data",
    "mutate_external_dataset",
    "upload_submission_payload",
]
ExternalDataTransferPosture = Literal[
    "no_external_data_transfer_performed_by_v80",
    "data_transfer_requires_later_family",
    "data_transfer_forbidden_by_this_family",
]
ExternalDataBoundaryPosture = Literal[
    "data_boundary_complete_for_review_only",
    "data_boundary_blocked_by_missing_v43_branch_posture",
    "data_boundary_blocked_by_missing_authority",
    "data_boundary_future_family_only",
]
ExternalEndpointRefPosture = Literal[
    "endpoint_identifier_only",
    "endpoint_access_requires_later_authority",
    "endpoint_access_forbidden_by_this_family",
    "endpoint_absent_or_unknown",
]
ExternalAllowedToolReviewAction = Literal[
    "describe_tool_boundary",
    "inspect_tool_metadata",
    "record_endpoint_identifier",
    "request_later_tool_authority_review",
    "preserve_tool_gap",
]
ExternalForbiddenToolAction = Literal[
    "invoke_external_tool",
    "mutate_external_endpoint",
    "submit_payload",
    "download_external_result",
    "transfer_data",
]
ExternalToolBoundaryPosture = Literal[
    "tool_boundary_complete_for_review_only",
    "tool_boundary_blocked_by_missing_v43_branch_posture",
    "tool_boundary_blocked_by_missing_authority",
    "tool_boundary_future_family_only",
]
ExternalSubmissionAuthorityPosture = Literal[
    "submission_authority_complete_for_review_only",
    "submission_authority_blocked_by_missing_v43_branch_posture",
    "submission_authority_blocked_by_missing_authority",
    "submission_authority_future_family_only",
]
ExternalResultTruthPosture = Literal[
    "external_result_truth_not_claimed",
    "result_truth_requires_later_review",
    "result_truth_forbidden_by_this_family",
]
ExternalWithdrawalPosture = Literal[
    "withdrawal_requirement_recorded_only",
    "withdrawal_requires_later_authority",
    "withdrawal_not_applicable",
    "withdrawal_action_forbidden_by_this_family",
]
ExternalBranchExceptionKind = Literal[
    "missing_v43_branch_posture",
    "missing_external_data_boundary",
    "missing_external_tool_boundary",
    "missing_submission_authority",
    "missing_result_provenance",
    "missing_withdrawal_requirement",
    "product_authority_gap",
    "runtime_authority_gap",
    "release_authority_gap",
    "endpoint_access_authority_gap",
    "historical_v43_as_current_authority",
    "local_command_output_as_external_result_evidence",
    "unknown_needs_review",
]
ExternalBranchExceptionPosture = Literal[
    "blocking",
    "warning_only",
    "carried_forward",
    "not_applicable",
    "future_family_only",
]
ExternalBranchRequiredNextSurface = Literal[
    "v80c_external_branch_readiness_summary",
    "future_product_review",
    "future_runtime_review",
    "future_external_branch_authority_review",
    "future_family_review",
    "none",
]

_V79_ELIGIBILITY_SOURCE_ROLES = {
    "v79_controlled_execution_summary_source",
    "v79_post_controlled_execution_review_handoff_source",
    "v79_family_closeout_source",
}
_CONTEXT_SOURCE_ROLES = {
    "v79_combined_dogfood_context",
    "post_v74_roadmap_context",
    "support_process_context",
}
_ABSENCE_SOURCE_ROLES = {"v43_branch_posture_absence_marker", "absence_marker"}
_FORBIDDEN_EXTERNAL_ACTIONS = {
    "activate_external_branch",
    "enter_v43_contest",
    "submit_externally",
    "invoke_external_tool_for_effect",
    "mutate_external_endpoint",
    "transfer_external_data",
    "claim_external_result_truth",
    "run_command",
    "invoke_tool_for_effect",
    "assign_worker",
    "dispatch_worker",
    "open_pr",
    "commit",
    "merge",
    "release",
}
_FORBIDDEN_DOWNSTREAM_AUTHORITIES = {
    "external_branch_activation",
    "v43_contest_participation",
    "external_submission",
    "external_tool_invocation",
    "external_result_truth",
    "product_authorization",
    "released_truth",
    "benchmark_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
    "v81_selection",
}
_FORBIDDEN_DATA_ACTIONS = {
    "ingest_external_data",
    "export_repo_data",
    "transfer_data",
    "mutate_external_dataset",
    "upload_submission_payload",
}
_FORBIDDEN_TOOL_ACTIONS = {
    "invoke_external_tool",
    "mutate_external_endpoint",
    "submit_payload",
    "download_external_result",
    "transfer_data",
}


def _reject_glob_ref(value: str, *, field_name: str) -> str:
    if any(marker in value for marker in ("*", "?", "[")):
        raise ValueError(f"{field_name} may not contain glob target boundaries")
    return value


def _source_path(path: str) -> str:
    _repo_ref(path, field_name="source_ref")
    return path


def _require_terms(value: str, *, field_name: str, terms: tuple[str, ...]) -> str:
    lowered = value.lower()
    missing = [term for term in terms if term not in lowered]
    if missing:
        raise ValueError(f"{field_name} must mention {', '.join(missing)}")
    return value


def _reject_v80_action_claim(value: str, *, field_name: str) -> str:
    lowered = value.lower()
    forbidden_patterns = [
        r"external branch (?:is |was |has been |gets |got )?activated",
        r"activate external branch",
        r"v43 contest (?:is |was |has been |gets |got )?entered",
        r"enter v43 contest",
        r"external submission (?:is |was |has been |gets |got )?made",
        r"submit externally",
        r"external tool (?:is |was |has been |gets |got )?invoked",
        r"invoke external tool",
        r"external endpoint (?:is |was |has been |gets |got )?mutated",
        r"external data (?:is |was |has been |gets |got )?transferred",
        r"external result truth",
        r"command (?:is |was |has been |gets |got )?executed",
        r"run command",
        r"tool (?:is |was |has been |gets |got )?invoked",
        r"dispatch worker",
        r"product (?:is |was |has been |gets |got )?authorized",
        r"release now",
        r"v81 (?:is |was |has been |gets |got )?selected",
    ]
    negation_markers = ("no ", "not ", "without ", "forbidden ", "non-")
    for pattern in forbidden_patterns:
        match = re.search(pattern, lowered)
        if match is None:
            continue
        prefix = lowered[max(0, match.start() - 24) : match.start()]
        if not any(marker in prefix for marker in negation_markers):
            raise ValueError(f"{field_name} may not carry external branch activation")
    return value


class RepoExternalBranchSourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    external_branch_source_role: ExternalBranchSourceRole
    source_horizon: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_external_branch_source_row(self) -> RepoExternalBranchSourceRow:
        _repo_ref(self.source_ref, field_name="source_ref")
        _non_empty(self.source_horizon, field_name="source_horizon")
        _reject_v80_action_claim(self.limitation_note, field_name="limitation_note")
        if (
            self.external_branch_source_role not in _ABSENCE_SOURCE_ROLES
            and self.source_presence_posture != "present"
        ):
            raise ValueError("non-absence external branch source rows must be present")
        if (
            self.external_branch_source_role in _ABSENCE_SOURCE_ROLES
            and self.source_presence_posture == "present"
        ):
            raise ValueError("absence-marker external branch rows must not be present sources")
        if (
            self.external_branch_source_role in _CONTEXT_SOURCE_ROLES
            and self.authority_layer == "lock"
            and self.source_kind == "support_doc"
        ):
            raise ValueError("support context may not be marked as lock authority")
        return self


class RepoExternalBranchSourceIndex(_CartographyBase):
    schema: Literal["repo_external_branch_source_index@1"] = (
        REPO_EXTERNAL_BRANCH_SOURCE_INDEX_SCHEMA
    )
    external_branch_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    source_rows: list[RepoExternalBranchSourceRow] = Field(min_length=1)
    external_branch_source_summary: str

    @model_validator(mode="after")
    def _validate_external_branch_source_index(self) -> RepoExternalBranchSourceIndex:
        object.__setattr__(
            self,
            "source_rows",
            _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows"),
        )
        _non_empty(self.review_id, field_name="review_id")
        _non_empty(self.snapshot_id, field_name="snapshot_id")
        _non_empty(self.source_set_id, field_name="source_set_id")
        _require_terms(
            self.external_branch_source_summary,
            field_name="external_branch_source_summary",
            terms=("eligibility", "context", "no external activation"),
        )
        expected_id = _surface_id(
            "repo_external_branch_source_index",
            self.schema,
            self.model_dump(mode="json"),
            "external_branch_source_index_id",
        )
        if self.external_branch_source_index_id != expected_id:
            raise ValueError("external_branch_source_index_id does not match canonical hash")
        return self


class RepoExternalBranchReviewRequestRow(_CartographyBase):
    external_branch_review_request_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    v79_summary_refs: list[str] = Field(default_factory=list)
    v79_handoff_refs: list[str] = Field(default_factory=list)
    v79_closeout_refs: list[str] = Field(default_factory=list)
    branch_family_ref: str
    branch_posture_currentness: ExternalBranchPostureCurrentness
    external_objective_kind: ExternalObjectiveKind
    branch_review_posture: ExternalBranchReviewPosture
    requested_data_boundary_horizon: ExternalBranchRequestedHorizon
    requested_tool_boundary_horizon: ExternalBranchRequestedHorizon
    requested_submission_authority_horizon: ExternalBranchRequestedHorizon
    required_result_provenance_posture: ExternalBranchRequirementPosture
    required_withdrawal_posture: ExternalBranchRequirementPosture
    required_authority_refs: list[str] = Field(default_factory=list)
    guardrail_refs: list[str] = Field(min_length=1)
    external_activation_posture: ExternalActivationPosture
    external_submission_posture: ExternalSubmissionPosture
    external_tool_invocation_posture: ExternalToolInvocationPosture
    execution_posture: ExternalBranchExecutionPosture
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_external_branch_review_request_row(
        self,
    ) -> RepoExternalBranchReviewRequestRow:
        _non_empty(
            self.external_branch_review_request_ref,
            field_name="external_branch_review_request_ref",
        )
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        _non_empty(self.branch_family_ref, field_name="branch_family_ref")
        for field_name in (
            "source_refs",
            "v79_summary_refs",
            "v79_handoff_refs",
            "v79_closeout_refs",
            "required_authority_refs",
            "guardrail_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "odeu_lanes",
            _sorted_unique(self.odeu_lanes, field_name="odeu_lanes"),
        )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        if self.external_activation_posture != "no_external_branch_activation_performed_by_v80":
            raise ValueError("V80-A request rows must not activate external branches")
        if self.external_submission_posture != "no_external_submission_performed_by_v80":
            raise ValueError("V80-A request rows must not submit externally")
        if self.external_tool_invocation_posture != "no_external_tool_invocation_performed_by_v80":
            raise ValueError("V80-A request rows must not invoke external tools")
        if self.execution_posture != "no_execution_performed_by_v80":
            raise ValueError("V80-A request rows must not perform execution")
        _reject_v80_action_claim(self.limitation_note, field_name="limitation_note")
        if self.branch_review_posture == "eligible_for_external_branch_review":
            if self.branch_posture_currentness != "current_branch_posture":
                raise ValueError("eligible external branch review requires current branch posture")
            if (
                not self.v79_summary_refs
                and not self.v79_handoff_refs
                and not self.v79_closeout_refs
            ):
                raise ValueError("eligible external branch review requests require V79-C refs")
            if not any("v43" in ref.lower() or "external" in ref for ref in self.source_refs):
                raise ValueError("eligible external branch review requests require branch source")
            expected_horizons = {
                "requested_data_boundary_horizon": "data_boundary_required_later",
                "requested_tool_boundary_horizon": "tool_boundary_required_later",
                "requested_submission_authority_horizon": ("submission_authority_required_later"),
            }
            for field_name, expected_value in expected_horizons.items():
                if getattr(self, field_name) != expected_value:
                    raise ValueError(
                        f"eligible external branch review requests require {field_name} "
                        f"to be {expected_value}"
                    )
        if self.branch_review_posture == "request_recorded_objective_only":
            if self.branch_posture_currentness == "current_branch_posture":
                raise ValueError("objective-only rows must not claim current branch posture")
        if self.external_objective_kind == "product_externalization_review":
            if self.branch_review_posture not in {
                "blocked_by_product_authority_gap",
                "future_family_only",
                "rejected_out_of_scope",
            }:
                raise ValueError("product pressure must remain blocked in V80-A")
            if not any("product" in ref for ref in self.required_authority_refs):
                raise ValueError("product pressure requires product authority blocker")
        return self


class RepoExternalBranchReviewRequest(_CartographyBase):
    schema: Literal["repo_external_branch_review_request@1"] = (
        REPO_EXTERNAL_BRANCH_REVIEW_REQUEST_SCHEMA
    )
    external_branch_review_request_id: str
    external_branch_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    request_rows: list[RepoExternalBranchReviewRequestRow] = Field(min_length=1)
    external_branch_boundary_summary: str

    @model_validator(mode="after")
    def _validate_external_branch_review_request(self) -> RepoExternalBranchReviewRequest:
        object.__setattr__(
            self,
            "request_rows",
            _sorted_unique_by_ref(
                self.request_rows,
                attr="external_branch_review_request_ref",
                field_name="request_rows",
            ),
        )
        _require_terms(
            self.external_branch_boundary_summary,
            field_name="external_branch_boundary_summary",
            terms=("review", "no external activation", "no external submission", "no release"),
        )
        expected_id = _surface_id(
            "repo_external_branch_review_request",
            self.schema,
            self.model_dump(mode="json"),
            "external_branch_review_request_id",
        )
        if self.external_branch_review_request_id != expected_id:
            raise ValueError("external_branch_review_request_id does not match canonical hash")
        return self


class RepoExternalBranchNonActivationGuardrailRow(_CartographyBase):
    guardrail_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    external_branch_review_request_refs: list[str] = Field(min_length=1)
    forbidden_external_actions: list[ExternalForbiddenAction] = Field(min_length=1)
    forbidden_downstream_authority: list[ExternalForbiddenDownstreamAuthority] = Field(min_length=1)
    guardrail_posture: Literal["non_activation_guardrail_active"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_external_branch_guardrail_row(
        self,
    ) -> RepoExternalBranchNonActivationGuardrailRow:
        _non_empty(self.guardrail_ref, field_name="guardrail_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "external_branch_review_request_refs",
            "forbidden_external_actions",
            "forbidden_downstream_authority",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        missing_actions = _FORBIDDEN_EXTERNAL_ACTIONS.difference(self.forbidden_external_actions)
        if missing_actions:
            raise ValueError("external branch guardrail omits forbidden external actions")
        missing_authority = _FORBIDDEN_DOWNSTREAM_AUTHORITIES.difference(
            self.forbidden_downstream_authority
        )
        if missing_authority:
            raise ValueError("external branch guardrail omits forbidden downstream authority")
        _reject_v80_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("no external activation", "no external submission", "no release"),
        )
        return self


class RepoExternalBranchNonActivationGuardrail(_CartographyBase):
    schema: Literal["repo_external_branch_non_activation_guardrail@1"] = (
        REPO_EXTERNAL_BRANCH_NON_ACTIVATION_GUARDRAIL_SCHEMA
    )
    external_branch_non_activation_guardrail_id: str
    external_branch_review_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    guardrail_rows: list[RepoExternalBranchNonActivationGuardrailRow] = Field(min_length=1)
    non_activation_summary: str

    @model_validator(mode="after")
    def _validate_external_branch_guardrail(
        self,
    ) -> RepoExternalBranchNonActivationGuardrail:
        object.__setattr__(
            self,
            "guardrail_rows",
            _sorted_unique_by_ref(
                self.guardrail_rows,
                attr="guardrail_ref",
                field_name="guardrail_rows",
            ),
        )
        _require_terms(
            self.non_activation_summary,
            field_name="non_activation_summary",
            terms=("no external activation", "no external submission", "no release"),
        )
        expected_id = _surface_id(
            "repo_external_branch_non_activation_guardrail",
            self.schema,
            self.model_dump(mode="json"),
            "external_branch_non_activation_guardrail_id",
        )
        if self.external_branch_non_activation_guardrail_id != expected_id:
            raise ValueError(
                "external_branch_non_activation_guardrail_id does not match canonical hash"
            )
        return self


def derive_v80a_repo_external_branch_source_index(
    *, repo_root: Path | None = None
) -> RepoExternalBranchSourceIndex:
    _ = repo_root
    payload = {
        "schema": REPO_EXTERNAL_BRANCH_SOURCE_INDEX_SCHEMA,
        "external_branch_source_index_id": "",
        "review_id": "review:v80a:external-branch-review",
        "snapshot_id": "vNext+223-controlled-execution-review-closeout",
        "source_set_id": "source-set:v80a:released-v79c-external-branch-pressure",
        "source_rows": [
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus223/"
                    "repo_controlled_execution_review_summary_v223_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "external_branch_source_role": "v79_controlled_execution_summary_source",
                "source_horizon": "Released V79-C controlled execution review summary rows.",
                "limitation_note": (
                    "Eligibility context for external branch review only; no external activation."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus223/"
                    "repo_post_controlled_execution_review_handoff_v223_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "external_branch_source_role": (
                    "v79_post_controlled_execution_review_handoff_source"
                ),
                "source_horizon": "Released V79-C post-controlled-execution handoff rows.",
                "limitation_note": (
                    "Eligibility context for external branch review only; no external activation."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus223/"
                    "repo_controlled_execution_review_family_closeout_alignment_v223_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "external_branch_source_role": "v79_family_closeout_source",
                "source_horizon": "Released V79 family closeout alignment rows.",
                "limitation_note": (
                    "Family closeout context for review boundary only; no external activation."
                ),
            },
            {
                "source_ref": _source_path(
                    "docs/support/arc_series_mapping/"
                    "V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_"
                    "COMBINED_DOGFOOD_TEST_v0.json"
                ),
                "source_kind": "support_doc",
                "authority_layer": "support",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "external_branch_source_role": "v79_combined_dogfood_context",
                "source_horizon": "Combined V68-V79 dogfood context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; "
                    "no external activation."
                ),
            },
            {
                "source_ref": _source_path("docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md"),
                "source_kind": "planning_doc",
                "authority_layer": "planning",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "external_branch_source_role": "post_v74_roadmap_context",
                "source_horizon": "Post-V74 multi-arc roadmap context.",
                "limitation_note": (
                    "Roadmap context only and not sufficient for eligibility; "
                    "no external activation."
                ),
            },
            {
                "source_ref": _source_path("docs/DRAFT_NEXT_ARC_OPTIONS_v43.md"),
                "source_kind": "planning_doc",
                "authority_layer": "planning",
                "source_status": "available_but_not_integrated",
                "source_presence_posture": "present",
                "external_branch_source_role": "support_process_context",
                "source_horizon": "Historical V43 branch planning context.",
                "limitation_note": (
                    "Historical context only; not current branch posture and "
                    "no external activation."
                ),
            },
            {
                "source_ref": "external-branch-posture:v43:current:absent",
                "source_kind": "external_artifact",
                "authority_layer": "support",
                "source_status": "review_pending_input",
                "source_presence_posture": "external_unavailable",
                "external_branch_source_role": "v43_branch_posture_absence_marker",
                "source_horizon": "Current V43 external branch posture is absent.",
                "limitation_note": ("Explicit absence marker only; no external activation."),
            },
        ],
        "external_branch_source_summary": (
            "External branch source rows separate eligibility from context with "
            "no external activation and no prose memory."
        ),
    }
    payload["source_rows"] = sorted(payload["source_rows"], key=lambda row: row["source_ref"])
    payload["external_branch_source_index_id"] = _surface_id(
        "repo_external_branch_source_index",
        REPO_EXTERNAL_BRANCH_SOURCE_INDEX_SCHEMA,
        payload,
        "external_branch_source_index_id",
    )
    return RepoExternalBranchSourceIndex.model_validate(payload)


def derive_v80a_repo_external_branch_review_request(
    *,
    repo_root: Path | None = None,
    external_branch_source_index: RepoExternalBranchSourceIndex | None = None,
) -> RepoExternalBranchReviewRequest:
    _ = repo_root
    source_index = external_branch_source_index or derive_v80a_repo_external_branch_source_index()
    source_refs = [row.source_ref for row in source_index.source_rows]
    self_candidate = "candidate:internal:self_evidencing_workflow_type_emergence"
    product_candidate = "candidate:internal:typed_adjudication_product_wedge"
    payload = {
        "schema": REPO_EXTERNAL_BRANCH_REVIEW_REQUEST_SCHEMA,
        "external_branch_review_request_id": "",
        "external_branch_source_index_id": source_index.external_branch_source_index_id,
        "review_id": source_index.review_id,
        "snapshot_id": source_index.snapshot_id,
        "source_set_id": source_index.source_set_id,
        "request_rows": [
            {
                "external_branch_review_request_ref": (
                    "external-branch-review:v80a:self-evidencing:v43-blocked"
                ),
                "candidate_ref": self_candidate,
                "source_refs": sorted(source_refs),
                "v79_summary_refs": [
                    "controlled-execution-summary:v79c:self-evidencing:review-package"
                ],
                "v79_handoff_refs": ["handoff:v79c:self-evidencing:future-execution-trial-review"],
                "v79_closeout_refs": [
                    "repo_controlled_execution_review_family_closeout_alignment_c529594bf82f3e0b681d8cbc"
                ],
                "branch_family_ref": "V43",
                "branch_posture_currentness": "explicit_absence_marker",
                "external_objective_kind": "arc_contest_participation_review",
                "branch_review_posture": "blocked_by_missing_v43_branch_posture",
                "requested_data_boundary_horizon": "blocked_by_missing_v43_branch_posture",
                "requested_tool_boundary_horizon": "blocked_by_missing_v43_branch_posture",
                "requested_submission_authority_horizon": ("blocked_by_missing_v43_branch_posture"),
                "required_result_provenance_posture": ("blocked_by_missing_v43_branch_posture"),
                "required_withdrawal_posture": "blocked_by_missing_v43_branch_posture",
                "required_authority_refs": ["external-branch-posture:v43:current:absent"],
                "guardrail_refs": ["guardrail:v80a:self-evidencing:non-activation"],
                "external_activation_posture": ("no_external_branch_activation_performed_by_v80"),
                "external_submission_posture": "no_external_submission_performed_by_v80",
                "external_tool_invocation_posture": (
                    "no_external_tool_invocation_performed_by_v80"
                ),
                "execution_posture": "no_execution_performed_by_v80",
                "odeu_lanes": ["deontic", "epistemic", "utility"],
                "limitation_note": (
                    "External branch review is blocked by missing current V43 "
                    "posture with no external activation, no external submission, "
                    "and no release."
                ),
            },
            {
                "external_branch_review_request_ref": (
                    "external-branch-review:v80a:product-wedge:out-of-scope"
                ),
                "candidate_ref": product_candidate,
                "source_refs": sorted(source_refs),
                "v79_summary_refs": ["controlled-execution-summary:v79c:product-wedge:blocked"],
                "v79_handoff_refs": ["handoff:v79c:product-wedge:future-product-review"],
                "v79_closeout_refs": [
                    "repo_controlled_execution_review_family_closeout_alignment_c529594bf82f3e0b681d8cbc"
                ],
                "branch_family_ref": "V80",
                "branch_posture_currentness": "explicit_absence_marker",
                "external_objective_kind": "product_externalization_review",
                "branch_review_posture": "blocked_by_product_authority_gap",
                "requested_data_boundary_horizon": "future_family_only",
                "requested_tool_boundary_horizon": "future_family_only",
                "requested_submission_authority_horizon": "future_family_only",
                "required_result_provenance_posture": "future_family_only",
                "required_withdrawal_posture": "not_applicable",
                "required_authority_refs": ["authority:v78a:product-wedge:product-review"],
                "guardrail_refs": ["guardrail:v80a:product-wedge:non-activation"],
                "external_activation_posture": ("no_external_branch_activation_performed_by_v80"),
                "external_submission_posture": "no_external_submission_performed_by_v80",
                "external_tool_invocation_posture": (
                    "no_external_tool_invocation_performed_by_v80"
                ),
                "execution_posture": "no_execution_performed_by_v80",
                "odeu_lanes": ["deontic", "utility"],
                "limitation_note": (
                    "Product pressure remains blocked by product authority with "
                    "no external activation, no external submission, and no release."
                ),
            },
        ],
        "external_branch_boundary_summary": (
            "External branch review request is review only: no external activation, "
            "no external submission, no external tool invocation, and no release."
        ),
    }
    payload["request_rows"] = sorted(
        payload["request_rows"],
        key=lambda row: row["external_branch_review_request_ref"],
    )
    payload["external_branch_review_request_id"] = _surface_id(
        "repo_external_branch_review_request",
        REPO_EXTERNAL_BRANCH_REVIEW_REQUEST_SCHEMA,
        payload,
        "external_branch_review_request_id",
    )
    return RepoExternalBranchReviewRequest.model_validate(payload)


def derive_v80a_repo_external_branch_non_activation_guardrail(
    *,
    repo_root: Path | None = None,
    external_branch_review_request: RepoExternalBranchReviewRequest | None = None,
) -> RepoExternalBranchNonActivationGuardrail:
    _ = repo_root
    request = external_branch_review_request or derive_v80a_repo_external_branch_review_request()
    grouped_rows: dict[str, dict[str, object]] = {}
    for request_row in request.request_rows:
        for guardrail_ref in request_row.guardrail_refs:
            existing = grouped_rows.setdefault(
                guardrail_ref,
                {
                    "guardrail_ref": guardrail_ref,
                    "candidate_ref": request_row.candidate_ref,
                    "source_refs": [],
                    "external_branch_review_request_refs": [],
                    "forbidden_external_actions": sorted(_FORBIDDEN_EXTERNAL_ACTIONS),
                    "forbidden_downstream_authority": sorted(_FORBIDDEN_DOWNSTREAM_AUTHORITIES),
                    "guardrail_posture": "non_activation_guardrail_active",
                    "limitation_note": (
                        "This V80-A row is review only: no external activation, "
                        "no external submission, no external tool invocation, "
                        "no product authorization, and no release."
                    ),
                },
            )
            if existing["candidate_ref"] != request_row.candidate_ref:
                raise ValueError("external branch guardrail cannot merge candidates")
            existing["external_branch_review_request_refs"] = sorted(
                {
                    *existing["external_branch_review_request_refs"],
                    request_row.external_branch_review_request_ref,
                }
            )
            existing["source_refs"] = sorted({*existing["source_refs"], *request_row.source_refs})
    payload = {
        "schema": REPO_EXTERNAL_BRANCH_NON_ACTIVATION_GUARDRAIL_SCHEMA,
        "external_branch_non_activation_guardrail_id": "",
        "external_branch_review_request_id": request.external_branch_review_request_id,
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "guardrail_rows": sorted(grouped_rows.values(), key=lambda row: row["guardrail_ref"]),
        "non_activation_summary": (
            "External branch non-activation guardrails preserve review only: "
            "no external activation, no external submission, and no release."
        ),
    }
    payload["external_branch_non_activation_guardrail_id"] = _surface_id(
        "repo_external_branch_non_activation_guardrail",
        REPO_EXTERNAL_BRANCH_NON_ACTIVATION_GUARDRAIL_SCHEMA,
        payload,
        "external_branch_non_activation_guardrail_id",
    )
    return RepoExternalBranchNonActivationGuardrail.model_validate(payload)


def validate_v80a_external_branch_review_bundle(
    *,
    external_branch_source_index: RepoExternalBranchSourceIndex,
    external_branch_review_request: RepoExternalBranchReviewRequest,
    external_branch_non_activation_guardrail: RepoExternalBranchNonActivationGuardrail,
) -> None:
    if (
        external_branch_review_request.external_branch_source_index_id
        != external_branch_source_index.external_branch_source_index_id
    ):
        raise ValueError("external branch request must reference the source index")
    if (
        external_branch_review_request.review_id,
        external_branch_review_request.snapshot_id,
        external_branch_review_request.source_set_id,
    ) != (
        external_branch_source_index.review_id,
        external_branch_source_index.snapshot_id,
        external_branch_source_index.source_set_id,
    ):
        raise ValueError("external branch request provenance must match source index")
    if (
        external_branch_non_activation_guardrail.external_branch_review_request_id
        != external_branch_review_request.external_branch_review_request_id
    ):
        raise ValueError("external branch guardrail must reference the request surface")

    source_roles = {
        row.source_ref: row.external_branch_source_role
        for row in external_branch_source_index.source_rows
    }
    known_sources = set(source_roles)
    request_rows = {
        row.external_branch_review_request_ref: row
        for row in external_branch_review_request.request_rows
    }
    guardrail_rows = {}
    for row in external_branch_non_activation_guardrail.guardrail_rows:
        guardrail_rows[row.guardrail_ref] = row
    for request_row in external_branch_review_request.request_rows:
        if any(source_ref not in known_sources for source_ref in request_row.source_refs):
            raise ValueError("external branch request source refs must be known")
        roles = {source_roles[source_ref] for source_ref in request_row.source_refs}
        if request_row.branch_review_posture == "eligible_for_external_branch_review":
            if not roles.intersection(_V79_ELIGIBILITY_SOURCE_ROLES):
                raise ValueError("eligible external branch requests require released V79-C sources")
            if "v43_branch_posture_source" not in roles:
                raise ValueError("eligible external branch requests require current V43 posture")
            if "external_objective_source" in roles and len(roles) == 1:
                raise ValueError("external objective source alone cannot create eligibility")
        if (
            request_row.branch_review_posture == "request_recorded_objective_only"
            and "v43_branch_posture_source" in roles
        ):
            raise ValueError("objective-only request rows must not cite current branch posture")
        if request_row.v79_summary_refs and "v79_controlled_execution_summary_source" not in roles:
            raise ValueError("V79-C summary refs require a controlled-execution summary source")
        if (
            request_row.v79_handoff_refs
            and "v79_post_controlled_execution_review_handoff_source" not in roles
        ):
            raise ValueError("V79-C handoff refs require a post-review handoff source")
        if request_row.v79_closeout_refs and "v79_family_closeout_source" not in roles:
            raise ValueError("V79-C closeout refs require a family closeout source")
        if any(guardrail_ref not in guardrail_rows for guardrail_ref in request_row.guardrail_refs):
            raise ValueError("external branch request guardrail refs must be known")
        for guardrail_ref in request_row.guardrail_refs:
            guardrail_row = guardrail_rows[guardrail_ref]
            if guardrail_row.candidate_ref != request_row.candidate_ref:
                raise ValueError("external branch guardrails must match candidate")
            if (
                request_row.external_branch_review_request_ref
                not in guardrail_row.external_branch_review_request_refs
            ):
                raise ValueError("external branch guardrails must reference request rows")
    for guardrail_row in external_branch_non_activation_guardrail.guardrail_rows:
        if any(source_ref not in known_sources for source_ref in guardrail_row.source_refs):
            raise ValueError("external branch guardrail source refs must be known")
        if any(
            ref not in request_rows for ref in guardrail_row.external_branch_review_request_refs
        ):
            raise ValueError("guardrail external branch request refs must be known")
        for ref in guardrail_row.external_branch_review_request_refs:
            if request_rows[ref].candidate_ref != guardrail_row.candidate_ref:
                raise ValueError("guardrail request refs must match candidate")


def derive_v80a_external_branch_review_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoExternalBranchSourceIndex,
    RepoExternalBranchReviewRequest,
    RepoExternalBranchNonActivationGuardrail,
]:
    source_index = derive_v80a_repo_external_branch_source_index(repo_root=repo_root)
    request = derive_v80a_repo_external_branch_review_request(
        repo_root=repo_root,
        external_branch_source_index=source_index,
    )
    guardrail = derive_v80a_repo_external_branch_non_activation_guardrail(
        repo_root=repo_root,
        external_branch_review_request=request,
    )
    validate_v80a_external_branch_review_bundle(
        external_branch_source_index=source_index,
        external_branch_review_request=request,
        external_branch_non_activation_guardrail=guardrail,
    )
    return source_index, request, guardrail


class RepoExternalDataBoundaryRow(_CartographyBase):
    data_boundary_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    external_branch_review_request_refs: list[str] = Field(min_length=1)
    non_activation_guardrail_refs: list[str] = Field(min_length=1)
    external_data_kind: ExternalDataKind
    data_source_refs: list[str] = Field(default_factory=list)
    allowed_data_review_actions: list[ExternalAllowedDataReviewAction] = Field(min_length=1)
    forbidden_data_actions: list[ExternalForbiddenDataAction] = Field(min_length=1)
    data_transfer_posture: ExternalDataTransferPosture
    data_boundary_posture: ExternalDataBoundaryPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_external_data_boundary_row(self) -> RepoExternalDataBoundaryRow:
        _non_empty(self.data_boundary_ref, field_name="data_boundary_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "external_branch_review_request_refs",
            "non_activation_guardrail_refs",
            "data_source_refs",
            "allowed_data_review_actions",
            "forbidden_data_actions",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        for data_source_ref in self.data_source_refs:
            _non_empty(data_source_ref, field_name="data_source_refs")
            _reject_glob_ref(data_source_ref, field_name="data_source_refs")
        missing = _FORBIDDEN_DATA_ACTIONS.difference(self.forbidden_data_actions)
        if missing:
            raise ValueError("external data boundary omits forbidden data actions")
        if self.data_transfer_posture != "no_external_data_transfer_performed_by_v80":
            raise ValueError("V80-B data boundaries must not transfer external data")
        if (
            self.data_boundary_posture == "data_boundary_complete_for_review_only"
            and not self.data_source_refs
        ):
            raise ValueError("complete data boundaries require source-bound data refs")
        _reject_v80_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("review only", "no external data transfer", "no external activation"),
        )
        return self


class RepoExternalDataBoundary(_CartographyBase):
    schema: Literal["repo_external_data_boundary@1"] = REPO_EXTERNAL_DATA_BOUNDARY_SCHEMA
    external_data_boundary_id: str
    external_branch_review_request_id: str
    external_branch_source_index_id: str
    external_branch_non_activation_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    data_boundary_rows: list[RepoExternalDataBoundaryRow] = Field(min_length=1)
    data_boundary_summary: str

    @model_validator(mode="after")
    def _validate_external_data_boundary(self) -> RepoExternalDataBoundary:
        object.__setattr__(
            self,
            "data_boundary_rows",
            _sorted_unique_by_ref(
                self.data_boundary_rows,
                attr="data_boundary_ref",
                field_name="data_boundary_rows",
            ),
        )
        _require_terms(
            self.data_boundary_summary,
            field_name="data_boundary_summary",
            terms=("review only", "no external data transfer", "no external activation"),
        )
        expected_id = _surface_id(
            "repo_external_data_boundary",
            self.schema,
            self.model_dump(mode="json"),
            "external_data_boundary_id",
        )
        if self.external_data_boundary_id != expected_id:
            raise ValueError("external_data_boundary_id does not match canonical hash")
        return self


class RepoExternalToolBoundaryRow(_CartographyBase):
    external_tool_boundary_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    external_branch_review_request_refs: list[str] = Field(min_length=1)
    non_activation_guardrail_refs: list[str] = Field(min_length=1)
    tool_id: str
    tool_target_refs: list[str] = Field(default_factory=list)
    tool_endpoint_refs: list[str] = Field(default_factory=list)
    endpoint_ref_posture: ExternalEndpointRefPosture
    allowed_tool_review_actions: list[ExternalAllowedToolReviewAction] = Field(min_length=1)
    forbidden_tool_actions: list[ExternalForbiddenToolAction] = Field(min_length=1)
    external_tool_invocation_posture: ExternalToolInvocationPosture
    tool_boundary_posture: ExternalToolBoundaryPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_external_tool_boundary_row(self) -> RepoExternalToolBoundaryRow:
        _non_empty(self.external_tool_boundary_ref, field_name="external_tool_boundary_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        _non_empty(self.tool_id, field_name="tool_id")
        for field_name in (
            "source_refs",
            "external_branch_review_request_refs",
            "non_activation_guardrail_refs",
            "tool_target_refs",
            "tool_endpoint_refs",
            "allowed_tool_review_actions",
            "forbidden_tool_actions",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        for target_ref in self.tool_target_refs:
            _non_empty(target_ref, field_name="tool_target_refs")
            _reject_glob_ref(target_ref, field_name="tool_target_refs")
        for endpoint_ref in self.tool_endpoint_refs:
            _non_empty(endpoint_ref, field_name="tool_endpoint_refs")
            _reject_glob_ref(endpoint_ref, field_name="tool_endpoint_refs")
        missing = _FORBIDDEN_TOOL_ACTIONS.difference(self.forbidden_tool_actions)
        if missing:
            raise ValueError("external tool boundary omits forbidden tool actions")
        if self.external_tool_invocation_posture != "no_external_tool_invocation_performed_by_v80":
            raise ValueError("V80-B tool boundaries must not invoke external tools")
        if self.endpoint_ref_posture != "endpoint_identifier_only":
            raise ValueError("external endpoint refs must remain identifier-only in V80-B")
        if (
            self.tool_boundary_posture == "tool_boundary_complete_for_review_only"
            and not self.tool_endpoint_refs
        ):
            raise ValueError("complete external tool boundaries require endpoint identifiers")
        _reject_v80_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("review only", "no external tool invocation", "no external activation"),
        )
        return self


class RepoExternalToolBoundary(_CartographyBase):
    schema: Literal["repo_external_tool_boundary@1"] = REPO_EXTERNAL_TOOL_BOUNDARY_SCHEMA
    external_tool_boundary_id: str
    external_branch_review_request_id: str
    external_branch_source_index_id: str
    external_branch_non_activation_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    tool_boundary_rows: list[RepoExternalToolBoundaryRow] = Field(min_length=1)
    tool_boundary_summary: str

    @model_validator(mode="after")
    def _validate_external_tool_boundary(self) -> RepoExternalToolBoundary:
        object.__setattr__(
            self,
            "tool_boundary_rows",
            _sorted_unique_by_ref(
                self.tool_boundary_rows,
                attr="external_tool_boundary_ref",
                field_name="tool_boundary_rows",
            ),
        )
        _require_terms(
            self.tool_boundary_summary,
            field_name="tool_boundary_summary",
            terms=("review only", "no external tool invocation", "no external activation"),
        )
        expected_id = _surface_id(
            "repo_external_tool_boundary",
            self.schema,
            self.model_dump(mode="json"),
            "external_tool_boundary_id",
        )
        if self.external_tool_boundary_id != expected_id:
            raise ValueError("external_tool_boundary_id does not match canonical hash")
        return self


class RepoExternalSubmissionAuthorityReviewRow(_CartographyBase):
    submission_authority_review_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    external_branch_review_request_refs: list[str] = Field(min_length=1)
    data_boundary_refs: list[str] = Field(min_length=1)
    external_tool_boundary_refs: list[str] = Field(min_length=1)
    authority_refs: list[str] = Field(min_length=1)
    submission_target_refs: list[str] = Field(default_factory=list)
    submission_authority_posture: ExternalSubmissionAuthorityPosture
    external_submission_posture: ExternalSubmissionPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_submission_authority_review_row(
        self,
    ) -> RepoExternalSubmissionAuthorityReviewRow:
        _non_empty(
            self.submission_authority_review_ref,
            field_name="submission_authority_review_ref",
        )
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "external_branch_review_request_refs",
            "data_boundary_refs",
            "external_tool_boundary_refs",
            "authority_refs",
            "submission_target_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        for target_ref in self.submission_target_refs:
            _non_empty(target_ref, field_name="submission_target_refs")
            _reject_glob_ref(target_ref, field_name="submission_target_refs")
        if self.external_submission_posture != "no_external_submission_performed_by_v80":
            raise ValueError("V80-B submission authority review must not submit externally")
        if (
            self.submission_authority_posture == "submission_authority_complete_for_review_only"
            and not self.submission_target_refs
        ):
            raise ValueError("complete submission authority review requires target refs")
        _reject_v80_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("review only", "no external submission", "no external activation"),
        )
        return self


class RepoExternalSubmissionAuthorityReview(_CartographyBase):
    schema: Literal["repo_external_submission_authority_review@1"] = (
        REPO_EXTERNAL_SUBMISSION_AUTHORITY_REVIEW_SCHEMA
    )
    external_submission_authority_review_id: str
    external_branch_review_request_id: str
    external_branch_source_index_id: str
    external_branch_non_activation_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    submission_authority_review_rows: list[RepoExternalSubmissionAuthorityReviewRow] = Field(
        min_length=1
    )
    submission_authority_summary: str

    @model_validator(mode="after")
    def _validate_submission_authority_review(self) -> RepoExternalSubmissionAuthorityReview:
        object.__setattr__(
            self,
            "submission_authority_review_rows",
            _sorted_unique_by_ref(
                self.submission_authority_review_rows,
                attr="submission_authority_review_ref",
                field_name="submission_authority_review_rows",
            ),
        )
        _require_terms(
            self.submission_authority_summary,
            field_name="submission_authority_summary",
            terms=("review only", "no external submission", "no external activation"),
        )
        expected_id = _surface_id(
            "repo_external_submission_authority_review",
            self.schema,
            self.model_dump(mode="json"),
            "external_submission_authority_review_id",
        )
        if self.external_submission_authority_review_id != expected_id:
            raise ValueError(
                "external_submission_authority_review_id does not match canonical hash"
            )
        return self


class RepoExternalResultProvenanceContractRow(_CartographyBase):
    result_provenance_contract_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    external_branch_review_request_refs: list[str] = Field(min_length=1)
    data_boundary_refs: list[str] = Field(min_length=1)
    external_tool_boundary_refs: list[str] = Field(min_length=1)
    submission_authority_review_refs: list[str] = Field(min_length=1)
    expected_result_source_refs: list[str] = Field(default_factory=list)
    result_capture_requirement_refs: list[str] = Field(min_length=1)
    withdrawal_requirement_refs: list[str] = Field(default_factory=list)
    result_truth_posture: ExternalResultTruthPosture
    withdrawal_posture: ExternalWithdrawalPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_result_provenance_contract_row(
        self,
    ) -> RepoExternalResultProvenanceContractRow:
        _non_empty(
            self.result_provenance_contract_ref,
            field_name="result_provenance_contract_ref",
        )
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "external_branch_review_request_refs",
            "data_boundary_refs",
            "external_tool_boundary_refs",
            "submission_authority_review_refs",
            "expected_result_source_refs",
            "result_capture_requirement_refs",
            "withdrawal_requirement_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        for result_ref in self.expected_result_source_refs:
            _non_empty(result_ref, field_name="expected_result_source_refs")
            _reject_glob_ref(result_ref, field_name="expected_result_source_refs")
        if self.result_truth_posture != "external_result_truth_not_claimed":
            raise ValueError("V80-B result provenance must not claim external result truth")
        lowered_note = self.limitation_note.lower()
        if (
            "withdrawal action" in lowered_note
            and "no withdrawal action" not in lowered_note
            and "forbidden" not in lowered_note
        ):
            raise ValueError("withdrawal requirement cannot become withdrawal action")
        if (
            self.withdrawal_posture != "withdrawal_action_forbidden_by_this_family"
            and "withdrawal" in lowered_note
            and "requirement" not in lowered_note
        ):
            raise ValueError("withdrawal posture must remain a requirement, not action")
        _reject_v80_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("review only", "no external result truth", "no external activation"),
        )
        return self


class RepoExternalResultProvenanceContract(_CartographyBase):
    schema: Literal["repo_external_result_provenance_contract@1"] = (
        REPO_EXTERNAL_RESULT_PROVENANCE_CONTRACT_SCHEMA
    )
    external_result_provenance_contract_id: str
    external_branch_review_request_id: str
    external_branch_source_index_id: str
    external_branch_non_activation_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    result_provenance_contract_rows: list[RepoExternalResultProvenanceContractRow] = Field(
        min_length=1
    )
    result_provenance_summary: str

    @model_validator(mode="after")
    def _validate_result_provenance_contract(self) -> RepoExternalResultProvenanceContract:
        object.__setattr__(
            self,
            "result_provenance_contract_rows",
            _sorted_unique_by_ref(
                self.result_provenance_contract_rows,
                attr="result_provenance_contract_ref",
                field_name="result_provenance_contract_rows",
            ),
        )
        _require_terms(
            self.result_provenance_summary,
            field_name="result_provenance_summary",
            terms=("review only", "no external result truth", "no external activation"),
        )
        expected_id = _surface_id(
            "repo_external_result_provenance_contract",
            self.schema,
            self.model_dump(mode="json"),
            "external_result_provenance_contract_id",
        )
        if self.external_result_provenance_contract_id != expected_id:
            raise ValueError("external_result_provenance_contract_id does not match canonical hash")
        return self


class RepoExternalBranchExceptionRow(_CartographyBase):
    exception_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    external_branch_review_request_refs: list[str] = Field(min_length=1)
    exception_kind: ExternalBranchExceptionKind
    exception_posture: ExternalBranchExceptionPosture
    blocking_surface_refs: list[str] = Field(default_factory=list)
    required_next_surface: ExternalBranchRequiredNextSurface
    limitation_note: str

    @model_validator(mode="after")
    def _validate_external_branch_exception_row(self) -> RepoExternalBranchExceptionRow:
        _non_empty(self.exception_ref, field_name="exception_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "external_branch_review_request_refs",
            "blocking_surface_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        if self.exception_posture == "blocking" and not self.blocking_surface_refs:
            raise ValueError("blocking external branch exceptions require blockers")
        if self.exception_kind == "local_command_output_as_external_result_evidence":
            raise ValueError("local command output cannot be external result evidence")
        if self.exception_kind == "historical_v43_as_current_authority":
            raise ValueError("historical V43 context cannot be current external authority")
        if self.exception_kind in {"product_authority_gap", "runtime_authority_gap"}:
            if self.exception_posture not in {"blocking", "future_family_only"}:
                raise ValueError("product/runtime exceptions must remain blocked or deferred")
        if "resolved" in self.limitation_note.lower():
            raise ValueError("external branch exceptions cannot be resolved by prose")
        _reject_v80_action_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoExternalBranchExceptionRegister(_CartographyBase):
    schema: Literal["repo_external_branch_exception_register@1"] = (
        REPO_EXTERNAL_BRANCH_EXCEPTION_REGISTER_SCHEMA
    )
    external_branch_exception_register_id: str
    external_branch_review_request_id: str
    external_branch_source_index_id: str
    external_branch_non_activation_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    exception_rows: list[RepoExternalBranchExceptionRow] = Field(min_length=1)
    exception_summary: str

    @model_validator(mode="after")
    def _validate_external_branch_exception_register(
        self,
    ) -> RepoExternalBranchExceptionRegister:
        object.__setattr__(
            self,
            "exception_rows",
            _sorted_unique_by_ref(
                self.exception_rows,
                attr="exception_ref",
                field_name="exception_rows",
            ),
        )
        _require_terms(
            self.exception_summary,
            field_name="exception_summary",
            terms=("review only", "blocking", "no external activation"),
        )
        expected_id = _surface_id(
            "repo_external_branch_exception_register",
            self.schema,
            self.model_dump(mode="json"),
            "external_branch_exception_register_id",
        )
        if self.external_branch_exception_register_id != expected_id:
            raise ValueError("external_branch_exception_register_id does not match canonical hash")
        return self


def _v80b_v80a_request_rows(
    request: RepoExternalBranchReviewRequest,
) -> dict[str, RepoExternalBranchReviewRequestRow]:
    return {row.external_branch_review_request_ref: row for row in request.request_rows}


def _v80b_shared_ids(
    *,
    request: RepoExternalBranchReviewRequest,
    source_index: RepoExternalBranchSourceIndex,
    guardrail: RepoExternalBranchNonActivationGuardrail,
) -> dict[str, str]:
    guardrail_id = guardrail.external_branch_non_activation_guardrail_id
    return {
        "external_branch_review_request_id": request.external_branch_review_request_id,
        "external_branch_source_index_id": source_index.external_branch_source_index_id,
        "external_branch_non_activation_guardrail_id": guardrail_id,
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
    }


def derive_v80b_repo_external_data_boundary(
    *,
    repo_root: Path | None = None,
    external_branch_source_index: RepoExternalBranchSourceIndex | None = None,
    external_branch_review_request: RepoExternalBranchReviewRequest | None = None,
    external_branch_non_activation_guardrail: RepoExternalBranchNonActivationGuardrail
    | None = None,
) -> RepoExternalDataBoundary:
    _ = repo_root
    source_index, request, guardrail = (
        (
            external_branch_source_index,
            external_branch_review_request,
            external_branch_non_activation_guardrail,
        )
        if (
            external_branch_source_index is not None
            and external_branch_review_request is not None
            and external_branch_non_activation_guardrail is not None
        )
        else derive_v80a_external_branch_review_bundle()
    )
    source_refs = [row.source_ref for row in source_index.source_rows]
    rows_by_request = _v80b_v80a_request_rows(request)
    self_request = rows_by_request["external-branch-review:v80a:self-evidencing:v43-blocked"]
    product_request = rows_by_request["external-branch-review:v80a:product-wedge:out-of-scope"]
    payload = {
        "schema": REPO_EXTERNAL_DATA_BOUNDARY_SCHEMA,
        "external_data_boundary_id": "",
        **_v80b_shared_ids(request=request, source_index=source_index, guardrail=guardrail),
        "data_boundary_rows": [
            {
                "data_boundary_ref": "external-data-boundary:v80b:self-evidencing:v43-blocked",
                "candidate_ref": self_request.candidate_ref,
                "source_refs": source_refs,
                "external_branch_review_request_refs": [
                    self_request.external_branch_review_request_ref
                ],
                "non_activation_guardrail_refs": self_request.guardrail_refs,
                "external_data_kind": "contest_prompt_metadata",
                "data_source_refs": ["external-objective:v43:contest-metadata:placeholder"],
                "allowed_data_review_actions": [
                    "describe_data_boundary",
                    "record_absence_posture",
                    "request_later_data_authority_review",
                ],
                "forbidden_data_actions": sorted(_FORBIDDEN_DATA_ACTIONS),
                "data_transfer_posture": "no_external_data_transfer_performed_by_v80",
                "data_boundary_posture": "data_boundary_blocked_by_missing_v43_branch_posture",
                "limitation_note": (
                    "External data boundary is review only with no external data "
                    "transfer and no external activation."
                ),
            },
            {
                "data_boundary_ref": "external-data-boundary:v80b:product-wedge:blocked",
                "candidate_ref": product_request.candidate_ref,
                "source_refs": source_refs,
                "external_branch_review_request_refs": [
                    product_request.external_branch_review_request_ref
                ],
                "non_activation_guardrail_refs": product_request.guardrail_refs,
                "external_data_kind": "product_externalization_context",
                "data_source_refs": [],
                "allowed_data_review_actions": ["preserve_data_gap"],
                "forbidden_data_actions": sorted(_FORBIDDEN_DATA_ACTIONS),
                "data_transfer_posture": "no_external_data_transfer_performed_by_v80",
                "data_boundary_posture": "data_boundary_future_family_only",
                "limitation_note": (
                    "Product externalization data pressure is review only with no "
                    "external data transfer and no external activation."
                ),
            },
        ],
        "data_boundary_summary": (
            "External data boundaries are review only with no external data transfer "
            "and no external activation."
        ),
    }
    payload["data_boundary_rows"] = sorted(
        payload["data_boundary_rows"],
        key=lambda row: row["data_boundary_ref"],
    )
    payload["external_data_boundary_id"] = _surface_id(
        "repo_external_data_boundary",
        REPO_EXTERNAL_DATA_BOUNDARY_SCHEMA,
        payload,
        "external_data_boundary_id",
    )
    return RepoExternalDataBoundary.model_validate(payload)


def derive_v80b_repo_external_tool_boundary(
    *,
    repo_root: Path | None = None,
    external_branch_source_index: RepoExternalBranchSourceIndex | None = None,
    external_branch_review_request: RepoExternalBranchReviewRequest | None = None,
    external_branch_non_activation_guardrail: RepoExternalBranchNonActivationGuardrail
    | None = None,
) -> RepoExternalToolBoundary:
    _ = repo_root
    source_index, request, guardrail = (
        (
            external_branch_source_index,
            external_branch_review_request,
            external_branch_non_activation_guardrail,
        )
        if (
            external_branch_source_index is not None
            and external_branch_review_request is not None
            and external_branch_non_activation_guardrail is not None
        )
        else derive_v80a_external_branch_review_bundle()
    )
    source_refs = [row.source_ref for row in source_index.source_rows]
    rows_by_request = _v80b_v80a_request_rows(request)
    self_request = rows_by_request["external-branch-review:v80a:self-evidencing:v43-blocked"]
    payload = {
        "schema": REPO_EXTERNAL_TOOL_BOUNDARY_SCHEMA,
        "external_tool_boundary_id": "",
        **_v80b_shared_ids(request=request, source_index=source_index, guardrail=guardrail),
        "tool_boundary_rows": [
            {
                "external_tool_boundary_ref": (
                    "external-tool-boundary:v80b:self-evidencing:v43-blocked"
                ),
                "candidate_ref": self_request.candidate_ref,
                "source_refs": source_refs,
                "external_branch_review_request_refs": [
                    self_request.external_branch_review_request_ref
                ],
                "non_activation_guardrail_refs": self_request.guardrail_refs,
                "tool_id": "external-v43-submission-endpoint",
                "tool_target_refs": ["external-target:v43:submission-review-placeholder"],
                "tool_endpoint_refs": ["external-endpoint:v43:submission-api:identifier-only"],
                "endpoint_ref_posture": "endpoint_identifier_only",
                "allowed_tool_review_actions": [
                    "describe_tool_boundary",
                    "record_endpoint_identifier",
                    "request_later_tool_authority_review",
                ],
                "forbidden_tool_actions": sorted(_FORBIDDEN_TOOL_ACTIONS),
                "external_tool_invocation_posture": (
                    "no_external_tool_invocation_performed_by_v80"
                ),
                "tool_boundary_posture": "tool_boundary_blocked_by_missing_v43_branch_posture",
                "limitation_note": (
                    "External tool boundary is review only with no external tool "
                    "invocation and no external activation."
                ),
            }
        ],
        "tool_boundary_summary": (
            "External tool boundaries are review only with no external tool invocation "
            "and no external activation."
        ),
    }
    payload["external_tool_boundary_id"] = _surface_id(
        "repo_external_tool_boundary",
        REPO_EXTERNAL_TOOL_BOUNDARY_SCHEMA,
        payload,
        "external_tool_boundary_id",
    )
    return RepoExternalToolBoundary.model_validate(payload)


def derive_v80b_repo_external_submission_authority_review(
    *,
    repo_root: Path | None = None,
    external_branch_source_index: RepoExternalBranchSourceIndex | None = None,
    external_branch_review_request: RepoExternalBranchReviewRequest | None = None,
    external_branch_non_activation_guardrail: RepoExternalBranchNonActivationGuardrail
    | None = None,
    external_data_boundary: RepoExternalDataBoundary | None = None,
    external_tool_boundary: RepoExternalToolBoundary | None = None,
) -> RepoExternalSubmissionAuthorityReview:
    _ = repo_root
    source_index, request, guardrail = (
        (
            external_branch_source_index,
            external_branch_review_request,
            external_branch_non_activation_guardrail,
        )
        if (
            external_branch_source_index is not None
            and external_branch_review_request is not None
            and external_branch_non_activation_guardrail is not None
        )
        else derive_v80a_external_branch_review_bundle()
    )
    data_boundary = external_data_boundary or derive_v80b_repo_external_data_boundary(
        external_branch_source_index=source_index,
        external_branch_review_request=request,
        external_branch_non_activation_guardrail=guardrail,
    )
    tool_boundary = external_tool_boundary or derive_v80b_repo_external_tool_boundary(
        external_branch_source_index=source_index,
        external_branch_review_request=request,
        external_branch_non_activation_guardrail=guardrail,
    )
    source_refs = [row.source_ref for row in source_index.source_rows]
    rows_by_request = _v80b_v80a_request_rows(request)
    self_request = rows_by_request["external-branch-review:v80a:self-evidencing:v43-blocked"]
    payload = {
        "schema": REPO_EXTERNAL_SUBMISSION_AUTHORITY_REVIEW_SCHEMA,
        "external_submission_authority_review_id": "",
        **_v80b_shared_ids(request=request, source_index=source_index, guardrail=guardrail),
        "submission_authority_review_rows": [
            {
                "submission_authority_review_ref": (
                    "external-submission-authority:v80b:self-evidencing:v43-blocked"
                ),
                "candidate_ref": self_request.candidate_ref,
                "source_refs": source_refs,
                "external_branch_review_request_refs": [
                    self_request.external_branch_review_request_ref
                ],
                "data_boundary_refs": ["external-data-boundary:v80b:self-evidencing:v43-blocked"],
                "external_tool_boundary_refs": [
                    "external-tool-boundary:v80b:self-evidencing:v43-blocked"
                ],
                "authority_refs": ["external-branch-posture:v43:current:absent"],
                "submission_target_refs": ["external-submission:v43:target-placeholder"],
                "submission_authority_posture": (
                    "submission_authority_blocked_by_missing_v43_branch_posture"
                ),
                "external_submission_posture": "no_external_submission_performed_by_v80",
                "limitation_note": (
                    "Submission authority review is review only with no external "
                    "submission and no external activation."
                ),
            }
        ],
        "submission_authority_summary": (
            "External submission authority review is review only with no external "
            "submission and no external activation."
        ),
    }
    _ = data_boundary, tool_boundary
    payload["external_submission_authority_review_id"] = _surface_id(
        "repo_external_submission_authority_review",
        REPO_EXTERNAL_SUBMISSION_AUTHORITY_REVIEW_SCHEMA,
        payload,
        "external_submission_authority_review_id",
    )
    return RepoExternalSubmissionAuthorityReview.model_validate(payload)


def derive_v80b_repo_external_result_provenance_contract(
    *,
    repo_root: Path | None = None,
    external_branch_source_index: RepoExternalBranchSourceIndex | None = None,
    external_branch_review_request: RepoExternalBranchReviewRequest | None = None,
    external_branch_non_activation_guardrail: RepoExternalBranchNonActivationGuardrail
    | None = None,
    external_data_boundary: RepoExternalDataBoundary | None = None,
    external_tool_boundary: RepoExternalToolBoundary | None = None,
    external_submission_authority_review: RepoExternalSubmissionAuthorityReview | None = None,
) -> RepoExternalResultProvenanceContract:
    _ = repo_root
    source_index, request, guardrail = (
        (
            external_branch_source_index,
            external_branch_review_request,
            external_branch_non_activation_guardrail,
        )
        if (
            external_branch_source_index is not None
            and external_branch_review_request is not None
            and external_branch_non_activation_guardrail is not None
        )
        else derive_v80a_external_branch_review_bundle()
    )
    data_boundary = external_data_boundary or derive_v80b_repo_external_data_boundary(
        external_branch_source_index=source_index,
        external_branch_review_request=request,
        external_branch_non_activation_guardrail=guardrail,
    )
    tool_boundary = external_tool_boundary or derive_v80b_repo_external_tool_boundary(
        external_branch_source_index=source_index,
        external_branch_review_request=request,
        external_branch_non_activation_guardrail=guardrail,
    )
    submission_authority = external_submission_authority_review or (
        derive_v80b_repo_external_submission_authority_review(
            external_branch_source_index=source_index,
            external_branch_review_request=request,
            external_branch_non_activation_guardrail=guardrail,
            external_data_boundary=data_boundary,
            external_tool_boundary=tool_boundary,
        )
    )
    source_refs = [row.source_ref for row in source_index.source_rows]
    rows_by_request = _v80b_v80a_request_rows(request)
    self_request = rows_by_request["external-branch-review:v80a:self-evidencing:v43-blocked"]
    payload = {
        "schema": REPO_EXTERNAL_RESULT_PROVENANCE_CONTRACT_SCHEMA,
        "external_result_provenance_contract_id": "",
        **_v80b_shared_ids(request=request, source_index=source_index, guardrail=guardrail),
        "result_provenance_contract_rows": [
            {
                "result_provenance_contract_ref": (
                    "external-result-provenance:v80b:self-evidencing:v43-blocked"
                ),
                "candidate_ref": self_request.candidate_ref,
                "source_refs": source_refs,
                "external_branch_review_request_refs": [
                    self_request.external_branch_review_request_ref
                ],
                "data_boundary_refs": ["external-data-boundary:v80b:self-evidencing:v43-blocked"],
                "external_tool_boundary_refs": [
                    "external-tool-boundary:v80b:self-evidencing:v43-blocked"
                ],
                "submission_authority_review_refs": [
                    "external-submission-authority:v80b:self-evidencing:v43-blocked"
                ],
                "expected_result_source_refs": ["external-result:v43:result-capture-placeholder"],
                "result_capture_requirement_refs": [
                    "result-capture:v80b:self-evidencing:required-later"
                ],
                "withdrawal_requirement_refs": ["withdrawal:v80b:self-evidencing:required-later"],
                "result_truth_posture": "external_result_truth_not_claimed",
                "withdrawal_posture": "withdrawal_requires_later_authority",
                "limitation_note": (
                    "Result provenance is review only with no external result truth, "
                    "withdrawal requirement only, and no external activation."
                ),
            }
        ],
        "result_provenance_summary": (
            "External result provenance is review only with no external result truth "
            "and no external activation."
        ),
    }
    _ = submission_authority
    payload["external_result_provenance_contract_id"] = _surface_id(
        "repo_external_result_provenance_contract",
        REPO_EXTERNAL_RESULT_PROVENANCE_CONTRACT_SCHEMA,
        payload,
        "external_result_provenance_contract_id",
    )
    return RepoExternalResultProvenanceContract.model_validate(payload)


def derive_v80b_repo_external_branch_exception_register(
    *,
    repo_root: Path | None = None,
    external_branch_source_index: RepoExternalBranchSourceIndex | None = None,
    external_branch_review_request: RepoExternalBranchReviewRequest | None = None,
    external_branch_non_activation_guardrail: RepoExternalBranchNonActivationGuardrail
    | None = None,
) -> RepoExternalBranchExceptionRegister:
    _ = repo_root
    source_index, request, guardrail = (
        (
            external_branch_source_index,
            external_branch_review_request,
            external_branch_non_activation_guardrail,
        )
        if (
            external_branch_source_index is not None
            and external_branch_review_request is not None
            and external_branch_non_activation_guardrail is not None
        )
        else derive_v80a_external_branch_review_bundle()
    )
    source_refs = [row.source_ref for row in source_index.source_rows]
    rows_by_request = _v80b_v80a_request_rows(request)
    self_request = rows_by_request["external-branch-review:v80a:self-evidencing:v43-blocked"]
    product_request = rows_by_request["external-branch-review:v80a:product-wedge:out-of-scope"]
    payload = {
        "schema": REPO_EXTERNAL_BRANCH_EXCEPTION_REGISTER_SCHEMA,
        "external_branch_exception_register_id": "",
        **_v80b_shared_ids(request=request, source_index=source_index, guardrail=guardrail),
        "exception_rows": [
            {
                "exception_ref": "external-exception:v80b:self-evidencing:missing-v43",
                "candidate_ref": self_request.candidate_ref,
                "source_refs": source_refs,
                "external_branch_review_request_refs": [
                    self_request.external_branch_review_request_ref
                ],
                "exception_kind": "missing_v43_branch_posture",
                "exception_posture": "blocking",
                "blocking_surface_refs": ["external-branch-posture:v43:current:absent"],
                "required_next_surface": "future_external_branch_authority_review",
                "limitation_note": (
                    "Missing current V43 posture remains blocking for review only "
                    "with no external activation."
                ),
            },
            {
                "exception_ref": "external-exception:v80b:product-wedge:authority-gap",
                "candidate_ref": product_request.candidate_ref,
                "source_refs": source_refs,
                "external_branch_review_request_refs": [
                    product_request.external_branch_review_request_ref
                ],
                "exception_kind": "product_authority_gap",
                "exception_posture": "blocking",
                "blocking_surface_refs": ["authority:v78a:product-wedge:product-review"],
                "required_next_surface": "future_product_review",
                "limitation_note": (
                    "Product authority gap remains blocking for review only with "
                    "no external activation."
                ),
            },
        ],
        "exception_summary": (
            "External branch exceptions are review only, blocking where required, "
            "with no external activation."
        ),
    }
    payload["exception_rows"] = sorted(
        payload["exception_rows"],
        key=lambda row: row["exception_ref"],
    )
    payload["external_branch_exception_register_id"] = _surface_id(
        "repo_external_branch_exception_register",
        REPO_EXTERNAL_BRANCH_EXCEPTION_REGISTER_SCHEMA,
        payload,
        "external_branch_exception_register_id",
    )
    return RepoExternalBranchExceptionRegister.model_validate(payload)


def validate_v80b_external_branch_boundary_bundle(
    *,
    external_branch_source_index: RepoExternalBranchSourceIndex,
    external_branch_review_request: RepoExternalBranchReviewRequest,
    external_branch_non_activation_guardrail: RepoExternalBranchNonActivationGuardrail,
    external_data_boundary: RepoExternalDataBoundary,
    external_tool_boundary: RepoExternalToolBoundary,
    external_submission_authority_review: RepoExternalSubmissionAuthorityReview,
    external_result_provenance_contract: RepoExternalResultProvenanceContract,
    external_branch_exception_register: RepoExternalBranchExceptionRegister,
) -> None:
    validate_v80a_external_branch_review_bundle(
        external_branch_source_index=external_branch_source_index,
        external_branch_review_request=external_branch_review_request,
        external_branch_non_activation_guardrail=external_branch_non_activation_guardrail,
    )
    surface_ids = (
        external_branch_review_request.external_branch_review_request_id,
        external_branch_source_index.external_branch_source_index_id,
        external_branch_non_activation_guardrail.external_branch_non_activation_guardrail_id,
    )
    for surface in (
        external_data_boundary,
        external_tool_boundary,
        external_submission_authority_review,
        external_result_provenance_contract,
        external_branch_exception_register,
    ):
        if (
            surface.external_branch_review_request_id,
            surface.external_branch_source_index_id,
            surface.external_branch_non_activation_guardrail_id,
        ) != surface_ids:
            raise ValueError("V80-B surfaces must reference released V80-A surfaces")
        if (
            surface.review_id,
            surface.snapshot_id,
            surface.source_set_id,
        ) != (
            external_branch_review_request.review_id,
            external_branch_review_request.snapshot_id,
            external_branch_review_request.source_set_id,
        ):
            raise ValueError("V80-B surface provenance must match V80-A request")

    known_sources = {row.source_ref for row in external_branch_source_index.source_rows}
    request_rows = {
        row.external_branch_review_request_ref: row
        for row in external_branch_review_request.request_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row for row in external_branch_non_activation_guardrail.guardrail_rows
    }
    data_rows = {row.data_boundary_ref: row for row in external_data_boundary.data_boundary_rows}
    tool_rows = {
        row.external_tool_boundary_ref: row for row in external_tool_boundary.tool_boundary_rows
    }
    submission_rows = {
        row.submission_authority_review_ref: row
        for row in external_submission_authority_review.submission_authority_review_rows
    }

    def _check_sources(source_refs: list[str], *, label: str) -> None:
        if any(source_ref not in known_sources for source_ref in source_refs):
            raise ValueError(f"{label} source refs must be known")

    def _check_request_refs(
        refs: list[str],
        *,
        candidate_ref: str,
        label: str,
    ) -> None:
        if not refs:
            raise ValueError(f"{label} request refs must be non-empty")
        if any(ref not in request_rows for ref in refs):
            raise ValueError(f"{label} request refs must be known")
        for ref in refs:
            if request_rows[ref].candidate_ref != candidate_ref:
                raise ValueError(f"{label} request refs must match candidate")

    def _check_guardrail_refs(
        refs: list[str],
        *,
        candidate_ref: str,
        label: str,
    ) -> None:
        if any(ref not in guardrail_rows for ref in refs):
            raise ValueError(f"{label} guardrail refs must be known")
        for ref in refs:
            if guardrail_rows[ref].candidate_ref != candidate_ref:
                raise ValueError(f"{label} guardrail refs must match candidate")

    for row in external_data_boundary.data_boundary_rows:
        _check_sources(row.source_refs, label="external data boundary")
        _check_request_refs(
            row.external_branch_review_request_refs,
            candidate_ref=row.candidate_ref,
            label="external data boundary",
        )
        _check_guardrail_refs(
            row.non_activation_guardrail_refs,
            candidate_ref=row.candidate_ref,
            label="external data boundary",
        )
    for row in external_tool_boundary.tool_boundary_rows:
        _check_sources(row.source_refs, label="external tool boundary")
        _check_request_refs(
            row.external_branch_review_request_refs,
            candidate_ref=row.candidate_ref,
            label="external tool boundary",
        )
        _check_guardrail_refs(
            row.non_activation_guardrail_refs,
            candidate_ref=row.candidate_ref,
            label="external tool boundary",
        )
    for row in external_submission_authority_review.submission_authority_review_rows:
        _check_sources(row.source_refs, label="external submission authority review")
        _check_request_refs(
            row.external_branch_review_request_refs,
            candidate_ref=row.candidate_ref,
            label="external submission authority review",
        )
        if any(ref not in data_rows for ref in row.data_boundary_refs):
            raise ValueError("submission authority data boundary refs must be known")
        if any(ref not in tool_rows for ref in row.external_tool_boundary_refs):
            raise ValueError("submission authority tool boundary refs must be known")
        for ref in row.data_boundary_refs:
            if data_rows[ref].candidate_ref != row.candidate_ref:
                raise ValueError("submission authority data boundary refs must match candidate")
        for ref in row.external_tool_boundary_refs:
            if tool_rows[ref].candidate_ref != row.candidate_ref:
                raise ValueError("submission authority tool boundary refs must match candidate")
    for row in external_result_provenance_contract.result_provenance_contract_rows:
        _check_sources(row.source_refs, label="external result provenance")
        _check_request_refs(
            row.external_branch_review_request_refs,
            candidate_ref=row.candidate_ref,
            label="external result provenance",
        )
        if any(ref not in data_rows for ref in row.data_boundary_refs):
            raise ValueError("result provenance data boundary refs must be known")
        if any(ref not in tool_rows for ref in row.external_tool_boundary_refs):
            raise ValueError("result provenance tool boundary refs must be known")
        if any(ref not in submission_rows for ref in row.submission_authority_review_refs):
            raise ValueError("result provenance submission authority refs must be known")
        for ref in row.data_boundary_refs:
            if data_rows[ref].candidate_ref != row.candidate_ref:
                raise ValueError("result provenance data boundary refs must match candidate")
        for ref in row.external_tool_boundary_refs:
            if tool_rows[ref].candidate_ref != row.candidate_ref:
                raise ValueError("result provenance tool boundary refs must match candidate")
        for ref in row.submission_authority_review_refs:
            if submission_rows[ref].candidate_ref != row.candidate_ref:
                raise ValueError("result provenance submission authority refs must match candidate")
    for row in external_branch_exception_register.exception_rows:
        _check_sources(row.source_refs, label="external branch exception")
        _check_request_refs(
            row.external_branch_review_request_refs,
            candidate_ref=row.candidate_ref,
            label="external branch exception",
        )


def derive_v80b_external_branch_boundary_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoExternalBranchSourceIndex,
    RepoExternalBranchReviewRequest,
    RepoExternalBranchNonActivationGuardrail,
    RepoExternalDataBoundary,
    RepoExternalToolBoundary,
    RepoExternalSubmissionAuthorityReview,
    RepoExternalResultProvenanceContract,
    RepoExternalBranchExceptionRegister,
]:
    source_index, request, guardrail = derive_v80a_external_branch_review_bundle(
        repo_root=repo_root
    )
    data_boundary = derive_v80b_repo_external_data_boundary(
        repo_root=repo_root,
        external_branch_source_index=source_index,
        external_branch_review_request=request,
        external_branch_non_activation_guardrail=guardrail,
    )
    tool_boundary = derive_v80b_repo_external_tool_boundary(
        repo_root=repo_root,
        external_branch_source_index=source_index,
        external_branch_review_request=request,
        external_branch_non_activation_guardrail=guardrail,
    )
    submission_authority = derive_v80b_repo_external_submission_authority_review(
        repo_root=repo_root,
        external_branch_source_index=source_index,
        external_branch_review_request=request,
        external_branch_non_activation_guardrail=guardrail,
        external_data_boundary=data_boundary,
        external_tool_boundary=tool_boundary,
    )
    result_provenance = derive_v80b_repo_external_result_provenance_contract(
        repo_root=repo_root,
        external_branch_source_index=source_index,
        external_branch_review_request=request,
        external_branch_non_activation_guardrail=guardrail,
        external_data_boundary=data_boundary,
        external_tool_boundary=tool_boundary,
        external_submission_authority_review=submission_authority,
    )
    exception_register = derive_v80b_repo_external_branch_exception_register(
        repo_root=repo_root,
        external_branch_source_index=source_index,
        external_branch_review_request=request,
        external_branch_non_activation_guardrail=guardrail,
    )
    validate_v80b_external_branch_boundary_bundle(
        external_branch_source_index=source_index,
        external_branch_review_request=request,
        external_branch_non_activation_guardrail=guardrail,
        external_data_boundary=data_boundary,
        external_tool_boundary=tool_boundary,
        external_submission_authority_review=submission_authority,
        external_result_provenance_contract=result_provenance,
        external_branch_exception_register=exception_register,
    )
    return (
        source_index,
        request,
        guardrail,
        data_boundary,
        tool_boundary,
        submission_authority,
        result_provenance,
        exception_register,
    )
