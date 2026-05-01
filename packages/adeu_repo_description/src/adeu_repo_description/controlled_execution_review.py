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

REPO_CONTROLLED_EXECUTION_REVIEW_REQUEST_SCHEMA = (
    "repo_controlled_execution_review_request@1"
)
REPO_CONTROLLED_EXECUTION_SOURCE_INDEX_SCHEMA = "repo_controlled_execution_source_index@1"
REPO_CONTROLLED_EXECUTION_NON_EXECUTION_GUARDRAIL_SCHEMA = (
    "repo_controlled_execution_non_execution_guardrail@1"
)

ControlledExecutionSourceRole = Literal[
    "v78_readiness_summary_source",
    "v78_pre_execution_authority_review_handoff_source",
    "v78_family_closeout_source",
    "v78_authority_decision_context",
    "v78_tool_permission_context",
    "v78_command_scope_context",
    "v78_exception_context",
    "combined_dogfood_context",
    "support_process_context",
    "absence_marker",
]
ControlledExecutionReviewPosture = Literal[
    "eligible_for_controlled_execution_review",
    "blocked_by_missing_source",
    "blocked_by_missing_authority",
    "blocked_by_product_authority_gap",
    "blocked_by_external_branch_gap",
    "blocked_by_unbounded_target",
    "blocked_by_missing_effect_monitoring",
    "blocked_by_missing_telemetry",
    "blocked_by_missing_rollback",
    "future_family_only",
    "rejected_out_of_scope",
]
RequestedExecutionReviewHorizon = Literal[
    "bounded_command_run_plan_review",
    "bounded_tool_invocation_plan_review",
    "bounded_repo_script_run_plan_review",
    "future_product_review",
    "future_external_branch_review",
    "future_family_review",
]
RequestedRunPlanHorizon = Literal[
    "bounded_run_plan_required_later",
    "run_plan_not_selected_in_v79a",
    "run_plan_blocked_by_missing_source",
    "run_plan_blocked_by_missing_authority",
    "future_family_only",
]
RequestedToolInvocationHorizon = Literal[
    "bounded_tool_invocation_plan_required_later",
    "tool_invocation_plan_not_selected_in_v79a",
    "tool_invocation_plan_blocked_by_missing_source",
    "tool_invocation_plan_blocked_by_missing_authority",
    "future_family_only",
]
ControlledExecutionRequirementPosture = Literal[
    "required_for_later_review",
    "not_selected_in_v79a",
    "not_applicable",
    "blocked_by_missing_source",
    "blocked_by_missing_authority",
    "future_family_only",
]
ControlledExecutionActionPosture = Literal[
    "no_controlled_execution_performed_by_v79",
    "controlled_execution_requires_later_family",
    "controlled_execution_forbidden_by_this_family",
]
ControlledExecutionExecutionPosture = Literal[
    "no_execution_performed_by_v79",
    "execution_requires_later_family",
    "execution_forbidden_by_this_family",
]
ControlledExecutionToolInvocationPosture = Literal[
    "no_tool_invocation_performed_by_v79",
    "tool_invocation_requires_later_family",
    "tool_invocation_forbidden_by_this_family",
]
ControlledExecutionForbiddenAction = Literal[
    "run_command",
    "invoke_tool_for_effect",
    "mutate_target",
    "accept_effect",
    "observe_telemetry_as_success",
    "verify_rollback",
    "assign_worker",
    "dispatch_worker",
    "open_pr",
    "commit",
    "merge",
    "release",
    "external_submission",
]
ControlledExecutionForbiddenDownstreamAuthority = Literal[
    "product_authorization",
    "external_branch_activation",
    "released_truth",
    "benchmark_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
    "v80_selection",
]

_ELIGIBILITY_SOURCE_ROLES = {
    "v78_readiness_summary_source",
    "v78_pre_execution_authority_review_handoff_source",
}
_CONTEXT_SOURCE_ROLES = {
    "v78_authority_decision_context",
    "v78_tool_permission_context",
    "v78_command_scope_context",
    "v78_exception_context",
    "combined_dogfood_context",
    "support_process_context",
}
_FORBIDDEN_EXECUTION_ACTIONS = {
    "run_command",
    "invoke_tool_for_effect",
    "mutate_target",
    "accept_effect",
    "observe_telemetry_as_success",
    "verify_rollback",
    "assign_worker",
    "dispatch_worker",
    "open_pr",
    "commit",
    "merge",
    "release",
    "external_submission",
}
_FORBIDDEN_DOWNSTREAM_AUTHORITIES = {
    "product_authorization",
    "external_branch_activation",
    "released_truth",
    "benchmark_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
    "v80_selection",
}


def _reject_v79_action_claim(value: str, *, field_name: str) -> str:
    lowered = value.lower()
    forbidden_patterns = [
        r"controlled execution (?:is |was |has been |gets |got )?performed",
        r"command (?:is |was |has been |gets |got )?executed",
        r"run command",
        r"tool (?:is |was |has been |gets |got )?invoked",
        r"invoke tool",
        r"target (?:is |was |has been |gets |got )?mutated",
        r"effect (?:is |was |has been |gets |got )?accepted",
        r"telemetry (?:is |was |has been |gets |got )?observed",
        r"rollback (?:is |was |has been |gets |got )?verified",
        r"assign worker",
        r"dispatch worker",
        r"open pr",
        r"commit now",
        r"merge now",
        r"release now",
        r"product (?:is |was |has been |gets |got )?authorized",
        r"external branch (?:is |was |has been |gets |got )?activated",
        r"benchmark truth",
        r"model (?:is |was |has been |gets |got )?selected",
        r"v80 (?:is |was |has been |gets |got )?selected",
    ]
    negation_markers = ("no ", "not ", "without ", "forbidden ", "non-")
    for pattern in forbidden_patterns:
        match = re.search(pattern, lowered)
        if match is None:
            continue
        prefix = lowered[max(0, match.start() - 24) : match.start()]
        if not any(marker in prefix for marker in negation_markers):
            raise ValueError(f"{field_name} may not carry controlled execution action")
    return value


def _require_terms(value: str, *, field_name: str, terms: tuple[str, ...]) -> str:
    lowered = value.lower()
    missing = [term for term in terms if term not in lowered]
    if missing:
        raise ValueError(f"{field_name} must mention {', '.join(missing)}")
    return value


def _source_path(path: str) -> str:
    _repo_ref(path, field_name="source_ref")
    return path


def _reject_glob_ref(value: str, *, field_name: str) -> str:
    if any(marker in value for marker in ("*", "?", "[")):
        raise ValueError(f"{field_name} may not contain glob target boundaries")
    return value


class RepoControlledExecutionSourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    controlled_execution_source_role: ControlledExecutionSourceRole
    source_horizon: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_controlled_execution_source_row(self) -> RepoControlledExecutionSourceRow:
        _repo_ref(self.source_ref, field_name="source_ref")
        _non_empty(self.source_horizon, field_name="source_horizon")
        _reject_v79_action_claim(self.limitation_note, field_name="limitation_note")
        if (
            self.controlled_execution_source_role != "absence_marker"
            and self.source_presence_posture != "present"
        ):
            raise ValueError("non-absence controlled execution source rows must be present")
        if (
            self.controlled_execution_source_role == "absence_marker"
            and self.source_presence_posture == "present"
        ):
            raise ValueError("absence-marker controlled execution rows must not be present sources")
        if (
            self.controlled_execution_source_role in _CONTEXT_SOURCE_ROLES
            and self.authority_layer == "lock"
            and self.source_kind == "support_doc"
        ):
            raise ValueError("support context may not be marked as lock authority")
        return self


class RepoControlledExecutionSourceIndex(_CartographyBase):
    schema: Literal["repo_controlled_execution_source_index@1"] = (
        REPO_CONTROLLED_EXECUTION_SOURCE_INDEX_SCHEMA
    )
    controlled_execution_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    source_rows: list[RepoControlledExecutionSourceRow] = Field(min_length=1)
    controlled_execution_source_summary: str

    @model_validator(mode="after")
    def _validate_controlled_execution_source_index(self) -> RepoControlledExecutionSourceIndex:
        object.__setattr__(
            self,
            "source_rows",
            _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows"),
        )
        _non_empty(self.review_id, field_name="review_id")
        _non_empty(self.snapshot_id, field_name="snapshot_id")
        _non_empty(self.source_set_id, field_name="source_set_id")
        _require_terms(
            self.controlled_execution_source_summary,
            field_name="controlled_execution_source_summary",
            terms=("eligibility", "context", "no execution"),
        )
        expected_id = _surface_id(
            "repo_controlled_execution_source_index",
            self.schema,
            self.model_dump(mode="json"),
            "controlled_execution_source_index_id",
        )
        if self.controlled_execution_source_index_id != expected_id:
            raise ValueError("controlled_execution_source_index_id does not match canonical hash")
        return self


class RepoControlledExecutionReviewRequestRow(_CartographyBase):
    execution_review_request_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    v78_summary_refs: list[str] = Field(default_factory=list)
    v78_handoff_refs: list[str] = Field(default_factory=list)
    v78_closeout_refs: list[str] = Field(default_factory=list)
    requested_execution_review_horizon: RequestedExecutionReviewHorizon
    execution_review_posture: ControlledExecutionReviewPosture
    requested_run_plan_horizon: RequestedRunPlanHorizon
    requested_tool_invocation_horizon: RequestedToolInvocationHorizon
    required_effect_monitoring_posture: ControlledExecutionRequirementPosture
    required_telemetry_posture: ControlledExecutionRequirementPosture
    required_rollback_posture: ControlledExecutionRequirementPosture
    required_operator_confirmation_posture: ControlledExecutionRequirementPosture
    required_authority_refs: list[str] = Field(default_factory=list)
    target_boundary_refs: list[str] = Field(default_factory=list)
    guardrail_refs: list[str] = Field(min_length=1)
    controlled_execution_action_posture: ControlledExecutionActionPosture
    execution_posture: ControlledExecutionExecutionPosture
    tool_invocation_posture: ControlledExecutionToolInvocationPosture
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_controlled_execution_review_request_row(
        self,
    ) -> RepoControlledExecutionReviewRequestRow:
        _non_empty(self.execution_review_request_ref, field_name="execution_review_request_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "v78_summary_refs",
            "v78_handoff_refs",
            "v78_closeout_refs",
            "required_authority_refs",
            "target_boundary_refs",
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
        for target_ref in self.target_boundary_refs:
            _reject_glob_ref(target_ref, field_name="target_boundary_refs")
            _repo_ref(target_ref, field_name="target_boundary_refs")
        if self.controlled_execution_action_posture != "no_controlled_execution_performed_by_v79":
            raise ValueError("V79-A request rows must not perform controlled execution")
        if self.execution_posture != "no_execution_performed_by_v79":
            raise ValueError("V79-A request rows must not perform execution")
        if self.tool_invocation_posture != "no_tool_invocation_performed_by_v79":
            raise ValueError("V79-A request rows must not invoke tools")
        _reject_v79_action_claim(self.limitation_note, field_name="limitation_note")
        if self.execution_review_posture == "eligible_for_controlled_execution_review":
            if self.requested_execution_review_horizon in {
                "future_product_review",
                "future_external_branch_review",
            }:
                raise ValueError("product/external pressure is not execution-review-ready")
            if not self.v78_summary_refs and not self.v78_handoff_refs:
                raise ValueError("eligible execution review requests require V78-C refs")
            if not self.required_authority_refs:
                raise ValueError("eligible execution review requests require authority refs")
            for field_name in (
                "required_effect_monitoring_posture",
                "required_telemetry_posture",
                "required_rollback_posture",
                "required_operator_confirmation_posture",
            ):
                if getattr(self, field_name) != "required_for_later_review":
                    raise ValueError("eligible execution review requests require later safeguards")
        if self.requested_execution_review_horizon == "future_product_review":
            if self.execution_review_posture not in {
                "blocked_by_product_authority_gap",
                "future_family_only",
                "rejected_out_of_scope",
            }:
                raise ValueError("product pressure must remain product-blocked in V79-A")
            if not any("product" in ref for ref in self.required_authority_refs):
                raise ValueError("product pressure requires product authority blocker")
        if self.requested_execution_review_horizon == "future_external_branch_review":
            if self.execution_review_posture not in {
                "blocked_by_external_branch_gap",
                "future_family_only",
                "rejected_out_of_scope",
            }:
                raise ValueError("external branch pressure must remain blocked in V79-A")
            has_external_authority = any(
                "external" in ref or "v43" in ref.lower()
                for ref in self.required_authority_refs
            )
            if not has_external_authority:
                raise ValueError("external branch pressure requires external authority blocker")
        return self


class RepoControlledExecutionReviewRequest(_CartographyBase):
    schema: Literal["repo_controlled_execution_review_request@1"] = (
        REPO_CONTROLLED_EXECUTION_REVIEW_REQUEST_SCHEMA
    )
    controlled_execution_review_request_id: str
    controlled_execution_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    request_rows: list[RepoControlledExecutionReviewRequestRow] = Field(min_length=1)
    controlled_execution_boundary_summary: str

    @model_validator(mode="after")
    def _validate_controlled_execution_review_request(
        self,
    ) -> RepoControlledExecutionReviewRequest:
        object.__setattr__(
            self,
            "request_rows",
            _sorted_unique_by_ref(
                self.request_rows,
                attr="execution_review_request_ref",
                field_name="request_rows",
            ),
        )
        _require_terms(
            self.controlled_execution_boundary_summary,
            field_name="controlled_execution_boundary_summary",
            terms=("review", "no execution", "no tool invocation", "no release"),
        )
        expected_id = _surface_id(
            "repo_controlled_execution_review_request",
            self.schema,
            self.model_dump(mode="json"),
            "controlled_execution_review_request_id",
        )
        if self.controlled_execution_review_request_id != expected_id:
            raise ValueError(
                "controlled_execution_review_request_id does not match canonical hash"
            )
        return self


class RepoControlledExecutionNonExecutionGuardrailRow(_CartographyBase):
    guardrail_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    execution_review_request_refs: list[str] = Field(min_length=1)
    forbidden_execution_actions: list[ControlledExecutionForbiddenAction] = Field(min_length=1)
    forbidden_downstream_authority: list[ControlledExecutionForbiddenDownstreamAuthority] = Field(
        min_length=1
    )
    guardrail_posture: Literal["non_execution_guardrail_active"]
    limitation_note: str

    @model_validator(mode="after")
    def _validate_controlled_execution_guardrail_row(
        self,
    ) -> RepoControlledExecutionNonExecutionGuardrailRow:
        _non_empty(self.guardrail_ref, field_name="guardrail_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "execution_review_request_refs",
            "forbidden_execution_actions",
            "forbidden_downstream_authority",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        missing_actions = _FORBIDDEN_EXECUTION_ACTIONS.difference(
            self.forbidden_execution_actions
        )
        if missing_actions:
            raise ValueError("controlled execution guardrail omits forbidden execution actions")
        missing_authority = _FORBIDDEN_DOWNSTREAM_AUTHORITIES.difference(
            self.forbidden_downstream_authority
        )
        if missing_authority:
            raise ValueError("controlled execution guardrail omits forbidden downstream authority")
        _reject_v79_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("no controlled execution", "no execution", "no tool invocation", "no release"),
        )
        return self


class RepoControlledExecutionNonExecutionGuardrail(_CartographyBase):
    schema: Literal["repo_controlled_execution_non_execution_guardrail@1"] = (
        REPO_CONTROLLED_EXECUTION_NON_EXECUTION_GUARDRAIL_SCHEMA
    )
    controlled_execution_non_execution_guardrail_id: str
    controlled_execution_review_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    guardrail_rows: list[RepoControlledExecutionNonExecutionGuardrailRow] = Field(min_length=1)
    non_execution_summary: str

    @model_validator(mode="after")
    def _validate_controlled_execution_guardrail(
        self,
    ) -> RepoControlledExecutionNonExecutionGuardrail:
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
            self.non_execution_summary,
            field_name="non_execution_summary",
            terms=("no controlled execution", "no execution", "no tool invocation", "no release"),
        )
        expected_id = _surface_id(
            "repo_controlled_execution_non_execution_guardrail",
            self.schema,
            self.model_dump(mode="json"),
            "controlled_execution_non_execution_guardrail_id",
        )
        if self.controlled_execution_non_execution_guardrail_id != expected_id:
            raise ValueError(
                "controlled_execution_non_execution_guardrail_id does not match canonical hash"
            )
        return self


def derive_v79a_repo_controlled_execution_source_index(
    *, repo_root: Path | None = None
) -> RepoControlledExecutionSourceIndex:
    _ = repo_root
    payload = {
        "schema": REPO_CONTROLLED_EXECUTION_SOURCE_INDEX_SCHEMA,
        "controlled_execution_source_index_id": "",
        "review_id": "review:v79a:controlled-execution-review",
        "snapshot_id": "vNext+220-runtime-authority-closeout",
        "source_set_id": "source-set:v79a:released-v78c-controlled-execution-pressure",
        "source_rows": [
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus220/"
                    "repo_runtime_authority_readiness_summary_v220_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": "v78_readiness_summary_source",
                "source_horizon": "Released V78-C runtime authority readiness summary rows.",
                "limitation_note": (
                    "Eligibility source for controlled execution review only; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus220/"
                    "repo_pre_execution_authority_review_handoff_v220_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": (
                    "v78_pre_execution_authority_review_handoff_source"
                ),
                "source_horizon": "Released V78-C pre-execution-authority-review handoff rows.",
                "limitation_note": (
                    "Eligibility source for controlled execution review only; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus220/"
                    "repo_runtime_execution_authority_family_closeout_alignment_v220_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": "v78_family_closeout_source",
                "source_horizon": "Released V78 family closeout alignment rows.",
                "limitation_note": "Family closeout source for review boundary only; no execution.",
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus219/"
                    "repo_runtime_execution_authority_decision_v219_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": "v78_authority_decision_context",
                "source_horizon": "Released V78-B authority decision context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus219/"
                    "repo_tool_use_permission_envelope_v219_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": "v78_tool_permission_context",
                "source_horizon": "Released V78-B tool-use permission context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; "
                    "no tool invocation."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus219/"
                    "repo_command_scope_authorization_boundary_v219_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": "v78_command_scope_context",
                "source_horizon": "Released V78-B command-scope context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus219/"
                    "repo_runtime_authority_exception_register_v219_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": "v78_exception_context",
                "source_horizon": "Released V78-B exception context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "docs/support/arc_series_mapping/"
                    "V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_COMBINED_DOGFOOD_TEST_v0.json"
                ),
                "source_kind": "support_doc",
                "authority_layer": "support",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": "combined_dogfood_context",
                "source_horizon": "Combined V68-V78 dogfood context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path("docs/LOCKED_CONTINUATION_vNEXT_PLUS221.md"),
                "source_kind": "planning_doc",
                "authority_layer": "lock",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "controlled_execution_source_role": "support_process_context",
                "source_horizon": "Active V79-A starter lock context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
        ],
        "controlled_execution_source_summary": (
            "Controlled execution source rows separate eligibility from context "
            "with no execution and no prose memory."
        ),
    }
    payload["source_rows"] = sorted(payload["source_rows"], key=lambda row: row["source_ref"])
    payload["controlled_execution_source_index_id"] = _surface_id(
        "repo_controlled_execution_source_index",
        REPO_CONTROLLED_EXECUTION_SOURCE_INDEX_SCHEMA,
        payload,
        "controlled_execution_source_index_id",
    )
    return RepoControlledExecutionSourceIndex.model_validate(payload)


def derive_v79a_repo_controlled_execution_review_request(
    *,
    repo_root: Path | None = None,
    controlled_execution_source_index: RepoControlledExecutionSourceIndex | None = None,
) -> RepoControlledExecutionReviewRequest:
    _ = repo_root
    source_index = (
        controlled_execution_source_index or derive_v79a_repo_controlled_execution_source_index()
    )
    source_refs = [row.source_ref for row in source_index.source_rows]
    self_candidate = "candidate:internal:self_evidencing_workflow_type_emergence"
    product_candidate = "candidate:internal:typed_adjudication_product_wedge"
    payload = {
        "schema": REPO_CONTROLLED_EXECUTION_REVIEW_REQUEST_SCHEMA,
        "controlled_execution_review_request_id": "",
        "controlled_execution_source_index_id": (
            source_index.controlled_execution_source_index_id
        ),
        "review_id": source_index.review_id,
        "snapshot_id": source_index.snapshot_id,
        "source_set_id": source_index.source_set_id,
        "request_rows": [
            {
                "execution_review_request_ref": (
                    "execution-review:v79a:self-evidencing:controlled-execution"
                ),
                "candidate_ref": self_candidate,
                "source_refs": sorted(source_refs),
                "v78_summary_refs": [
                    "runtime-authority-summary:v78c:self-evidencing:later-execution-review"
                ],
                "v78_handoff_refs": [
                    "handoff:v78c:self-evidencing:later-execution-review"
                ],
                "v78_closeout_refs": [
                    "repo_runtime_execution_authority_family_closeout_alignment_120526ecd5ba85ec60335490"
                ],
                "requested_execution_review_horizon": "bounded_repo_script_run_plan_review",
                "execution_review_posture": "eligible_for_controlled_execution_review",
                "requested_run_plan_horizon": "bounded_run_plan_required_later",
                "requested_tool_invocation_horizon": (
                    "bounded_tool_invocation_plan_required_later"
                ),
                "required_effect_monitoring_posture": "required_for_later_review",
                "required_telemetry_posture": "required_for_later_review",
                "required_rollback_posture": "required_for_later_review",
                "required_operator_confirmation_posture": "required_for_later_review",
                "required_authority_refs": [
                    "authority:v78a:self-evidencing:runtime-review",
                    "authority:v78a:self-evidencing:tool-use-review",
                ],
                "target_boundary_refs": [
                    "packages/adeu_repo_description/src/adeu_repo_description/"
                    "controlled_execution_review.py"
                ],
                "guardrail_refs": ["guardrail:v79a:self-evidencing:non-execution"],
                "controlled_execution_action_posture": (
                    "no_controlled_execution_performed_by_v79"
                ),
                "execution_posture": "no_execution_performed_by_v79",
                "tool_invocation_posture": "no_tool_invocation_performed_by_v79",
                "odeu_lanes": ["deontic", "epistemic", "utility"],
                "limitation_note": (
                    "Eligible for controlled execution review only with no controlled "
                    "execution, no execution, no tool invocation, and no release."
                ),
            },
            {
                "execution_review_request_ref": "execution-review:v79a:product-wedge:blocked",
                "candidate_ref": product_candidate,
                "source_refs": sorted(source_refs),
                "v78_summary_refs": [
                    "runtime-authority-summary:v78c:product-wedge:future-family-only"
                ],
                "v78_handoff_refs": ["handoff:v78c:product-wedge:future-family-only"],
                "v78_closeout_refs": [
                    "repo_runtime_execution_authority_family_closeout_alignment_120526ecd5ba85ec60335490"
                ],
                "requested_execution_review_horizon": "future_product_review",
                "execution_review_posture": "blocked_by_product_authority_gap",
                "requested_run_plan_horizon": "future_family_only",
                "requested_tool_invocation_horizon": "future_family_only",
                "required_effect_monitoring_posture": "not_applicable",
                "required_telemetry_posture": "not_applicable",
                "required_rollback_posture": "not_applicable",
                "required_operator_confirmation_posture": "future_family_only",
                "required_authority_refs": ["authority:v78a:product-wedge:product-review"],
                "target_boundary_refs": [],
                "guardrail_refs": ["guardrail:v79a:product-wedge:non-execution"],
                "controlled_execution_action_posture": (
                    "no_controlled_execution_performed_by_v79"
                ),
                "execution_posture": "no_execution_performed_by_v79",
                "tool_invocation_posture": "no_tool_invocation_performed_by_v79",
                "odeu_lanes": ["deontic", "utility"],
                "limitation_note": (
                    "Product pressure remains blocked by later product authority with "
                    "no controlled execution, no execution, no tool invocation, and no release."
                ),
            },
        ],
        "controlled_execution_boundary_summary": (
            "Controlled execution review request is review only: no execution, "
            "no tool invocation, no product authorization, and no release."
        ),
    }
    payload["request_rows"] = sorted(
        payload["request_rows"],
        key=lambda row: row["execution_review_request_ref"],
    )
    payload["controlled_execution_review_request_id"] = _surface_id(
        "repo_controlled_execution_review_request",
        REPO_CONTROLLED_EXECUTION_REVIEW_REQUEST_SCHEMA,
        payload,
        "controlled_execution_review_request_id",
    )
    return RepoControlledExecutionReviewRequest.model_validate(payload)


def derive_v79a_repo_controlled_execution_non_execution_guardrail(
    *,
    repo_root: Path | None = None,
    controlled_execution_review_request: RepoControlledExecutionReviewRequest | None = None,
) -> RepoControlledExecutionNonExecutionGuardrail:
    _ = repo_root
    request = (
        controlled_execution_review_request
        or derive_v79a_repo_controlled_execution_review_request()
    )
    grouped_rows: dict[str, dict[str, object]] = {}
    for request_row in request.request_rows:
        for guardrail_ref in request_row.guardrail_refs:
            existing = grouped_rows.setdefault(
                guardrail_ref,
                {
                    "guardrail_ref": guardrail_ref,
                    "candidate_ref": request_row.candidate_ref,
                    "source_refs": [],
                    "execution_review_request_refs": [],
                    "forbidden_execution_actions": sorted(_FORBIDDEN_EXECUTION_ACTIONS),
                    "forbidden_downstream_authority": sorted(
                        _FORBIDDEN_DOWNSTREAM_AUTHORITIES
                    ),
                    "guardrail_posture": "non_execution_guardrail_active",
                    "limitation_note": (
                        "This V79-A row is review only: no controlled execution, "
                        "no execution, no tool invocation, no product authorization, "
                        "no external branch activation, and no release."
                    ),
                },
            )
            if existing["candidate_ref"] != request_row.candidate_ref:
                raise ValueError("controlled execution guardrail cannot merge candidates")
            existing["execution_review_request_refs"] = sorted(
                {
                    *existing["execution_review_request_refs"],
                    request_row.execution_review_request_ref,
                }
            )
            existing["source_refs"] = sorted({*existing["source_refs"], *request_row.source_refs})
    payload = {
        "schema": REPO_CONTROLLED_EXECUTION_NON_EXECUTION_GUARDRAIL_SCHEMA,
        "controlled_execution_non_execution_guardrail_id": "",
        "controlled_execution_review_request_id": (
            request.controlled_execution_review_request_id
        ),
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "guardrail_rows": sorted(grouped_rows.values(), key=lambda row: row["guardrail_ref"]),
        "non_execution_summary": (
            "Controlled execution non-execution guardrails preserve review only: "
            "no controlled execution, no execution, no tool invocation, and no release."
        ),
    }
    payload["controlled_execution_non_execution_guardrail_id"] = _surface_id(
        "repo_controlled_execution_non_execution_guardrail",
        REPO_CONTROLLED_EXECUTION_NON_EXECUTION_GUARDRAIL_SCHEMA,
        payload,
        "controlled_execution_non_execution_guardrail_id",
    )
    return RepoControlledExecutionNonExecutionGuardrail.model_validate(payload)


def validate_v79a_controlled_execution_review_bundle(
    *,
    controlled_execution_source_index: RepoControlledExecutionSourceIndex,
    controlled_execution_review_request: RepoControlledExecutionReviewRequest,
    controlled_execution_non_execution_guardrail: RepoControlledExecutionNonExecutionGuardrail,
) -> None:
    if (
        controlled_execution_review_request.controlled_execution_source_index_id
        != controlled_execution_source_index.controlled_execution_source_index_id
    ):
        raise ValueError("controlled execution request must reference the source index")
    if (
        controlled_execution_review_request.review_id,
        controlled_execution_review_request.snapshot_id,
        controlled_execution_review_request.source_set_id,
    ) != (
        controlled_execution_source_index.review_id,
        controlled_execution_source_index.snapshot_id,
        controlled_execution_source_index.source_set_id,
    ):
        raise ValueError("controlled execution request provenance must match source index")
    if (
        controlled_execution_non_execution_guardrail.controlled_execution_review_request_id
        != controlled_execution_review_request.controlled_execution_review_request_id
    ):
        raise ValueError("controlled execution guardrail must reference the request surface")
    if (
        controlled_execution_non_execution_guardrail.review_id,
        controlled_execution_non_execution_guardrail.snapshot_id,
        controlled_execution_non_execution_guardrail.source_set_id,
    ) != (
        controlled_execution_review_request.review_id,
        controlled_execution_review_request.snapshot_id,
        controlled_execution_review_request.source_set_id,
    ):
        raise ValueError("controlled execution guardrail provenance must match request")

    source_roles = {
        row.source_ref: row.controlled_execution_source_role
        for row in controlled_execution_source_index.source_rows
    }
    known_sources = set(source_roles)
    request_rows = {
        row.execution_review_request_ref: row
        for row in controlled_execution_review_request.request_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row
        for row in controlled_execution_non_execution_guardrail.guardrail_rows
    }
    for request_row in controlled_execution_review_request.request_rows:
        if any(source_ref not in known_sources for source_ref in request_row.source_refs):
            raise ValueError("controlled execution request source refs must be known")
        roles = {source_roles[source_ref] for source_ref in request_row.source_refs}
        if request_row.execution_review_posture == "eligible_for_controlled_execution_review":
            if not roles.intersection(_ELIGIBILITY_SOURCE_ROLES):
                raise ValueError(
                    "eligible controlled execution requests require released V78-C sources"
                )
        if any(guardrail_ref not in guardrail_rows for guardrail_ref in request_row.guardrail_refs):
            raise ValueError("controlled execution request guardrail refs must be known")
        for guardrail_ref in request_row.guardrail_refs:
            guardrail_row = guardrail_rows[guardrail_ref]
            if guardrail_row.candidate_ref != request_row.candidate_ref:
                raise ValueError("controlled execution guardrails must match candidate")
            if (
                request_row.execution_review_request_ref
                not in guardrail_row.execution_review_request_refs
            ):
                raise ValueError("controlled execution guardrails must reference request rows")

    for guardrail_row in controlled_execution_non_execution_guardrail.guardrail_rows:
        if any(source_ref not in known_sources for source_ref in guardrail_row.source_refs):
            raise ValueError("controlled execution guardrail source refs must be known")
        if any(ref not in request_rows for ref in guardrail_row.execution_review_request_refs):
            raise ValueError("guardrail execution review request refs must be known")
        for ref in guardrail_row.execution_review_request_refs:
            if request_rows[ref].candidate_ref != guardrail_row.candidate_ref:
                raise ValueError("guardrail request refs must match candidate")


def derive_v79a_controlled_execution_review_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoControlledExecutionSourceIndex,
    RepoControlledExecutionReviewRequest,
    RepoControlledExecutionNonExecutionGuardrail,
]:
    source_index = derive_v79a_repo_controlled_execution_source_index(repo_root=repo_root)
    request = derive_v79a_repo_controlled_execution_review_request(
        repo_root=repo_root,
        controlled_execution_source_index=source_index,
    )
    guardrail = derive_v79a_repo_controlled_execution_non_execution_guardrail(
        repo_root=repo_root,
        controlled_execution_review_request=request,
    )
    validate_v79a_controlled_execution_review_bundle(
        controlled_execution_source_index=source_index,
        controlled_execution_review_request=request,
        controlled_execution_non_execution_guardrail=guardrail,
    )
    return source_index, request, guardrail
