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

REPO_RUNTIME_EXECUTION_AUTHORITY_REQUEST_SCHEMA = (
    "repo_runtime_execution_authority_request@1"
)
REPO_RUNTIME_AUTHORITY_SOURCE_INDEX_SCHEMA = "repo_runtime_authority_source_index@1"
REPO_RUNTIME_AUTHORITY_NON_ACTION_GUARDRAIL_SCHEMA = (
    "repo_runtime_authority_non_action_guardrail@1"
)

RuntimeAuthoritySourceRole = Literal[
    "v77_authority_posture_source",
    "v77_runtime_summary_source",
    "v77_post_runtime_permission_review_handoff_source",
    "v77_family_closeout_source",
    "v77_command_preflight_context",
    "v77_effect_envelope_context",
    "v77_telemetry_requirement_context",
    "v77_rollback_contract_context",
    "combined_dogfood_source",
    "support_context",
    "absence_marker",
]
RuntimeExecutionAuthorityRequestPosture = Literal[
    "eligible_for_runtime_execution_authority_review",
    "blocked_by_missing_source",
    "blocked_by_missing_authority_source",
    "blocked_by_product_authority_gap",
    "blocked_by_external_branch_gap",
    "blocked_by_unbounded_command_scope",
    "blocked_by_missing_telemetry_requirement",
    "blocked_by_missing_rollback_requirement",
    "future_family_only",
    "rejected_out_of_scope",
]
RequestedRuntimeAuthorityHorizon = Literal[
    "bounded_command_execution_review",
    "bounded_tool_invocation_review",
    "bounded_repo_script_execution_review",
    "bounded_api_call_execution_review",
    "telemetry_observation_review",
    "rollback_execution_review",
    "future_product_runtime_review",
    "future_external_branch_runtime_review",
    "future_family_review",
]
RuntimeExecutionAuthorityKind = Literal[
    "maintainer_authority",
    "policy_authority",
    "runtime_execution_review_authority",
    "tool_use_review_authority",
    "product_authorization",
    "external_branch_activation",
    "release_authority",
    "recursive_policy_authority",
]
RuntimeAuthorityGapPosture = Literal[
    "authority_gap_present",
    "authority_checked_absent",
    "authority_not_applicable",
    "unknown_needs_review",
]
RuntimeAuthorityExecutionPosture = Literal[
    "no_execution_performed_by_v78",
    "execution_requires_later_family",
    "execution_forbidden_by_this_family",
]
RuntimeAuthorityToolInvocationPosture = Literal[
    "no_tool_invocation_performed_by_v78",
    "tool_invocation_requires_later_family",
    "tool_invocation_forbidden_by_this_family",
]
RuntimeAuthorityForbiddenAction = Literal[
    "run_command",
    "invoke_tool_for_effect",
    "assign_worker",
    "dispatch_worker",
    "open_pr",
    "commit",
    "merge",
    "release",
    "external_submission",
]
RuntimeAuthorityForbiddenDownstreamAuthority = Literal[
    "product_authorization",
    "external_branch_activation",
    "released_truth",
    "benchmark_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
]

_ELIGIBILITY_SOURCE_ROLES = {
    "v77_authority_posture_source",
    "v77_runtime_summary_source",
    "v77_post_runtime_permission_review_handoff_source",
    "v77_family_closeout_source",
}
_CONTEXT_SOURCE_ROLES = {
    "v77_command_preflight_context",
    "v77_effect_envelope_context",
    "v77_telemetry_requirement_context",
    "v77_rollback_contract_context",
    "combined_dogfood_source",
    "support_context",
}
_FORBIDDEN_RUNTIME_ACTIONS = {
    "run_command",
    "invoke_tool_for_effect",
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
}


def _reject_v78_action_claim(value: str, *, field_name: str) -> str:
    lowered = value.lower()
    forbidden_patterns = [
        r"command (?:is |was |has been |gets |got )?executed",
        r"execution (?:is |was |has been |gets |got )?authorized",
        r"run command",
        r"command output proves",
        r"tool (?:is |was |has been |gets |got )?invoked",
        r"invoke tool",
        r"assign worker",
        r"dispatch worker",
        r"open pr",
        r"commit now",
        r"merge now",
        r"release now",
        r"product (?:is |was |has been |gets |got )?authorized",
        r"external branch (?:is |was |has been |gets |got )?activated",
        r"external submission",
        r"benchmark truth",
        r"model (?:is |was |has been |gets |got )?selected",
        r"policy (?:is |was |has been |gets |got )?amended",
    ]
    negation_markers = ("no ", "not ", "without ", "forbidden ", "non-")
    for pattern in forbidden_patterns:
        match = re.search(pattern, lowered)
        if match is None:
            continue
        prefix = lowered[max(0, match.start() - 18) : match.start()]
        if not any(marker in prefix for marker in negation_markers):
            raise ValueError(f"{field_name} may not carry runtime action or authority")
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


class RepoRuntimeAuthoritySourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    runtime_authority_source_role: RuntimeAuthoritySourceRole
    source_horizon: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_authority_source_row(self) -> RepoRuntimeAuthoritySourceRow:
        _repo_ref(self.source_ref, field_name="source_ref")
        _non_empty(self.source_horizon, field_name="source_horizon")
        _reject_v78_action_claim(self.limitation_note, field_name="limitation_note")
        if (
            self.runtime_authority_source_role != "absence_marker"
            and self.source_presence_posture != "present"
        ):
            raise ValueError("non-absence runtime authority source rows must be present")
        if (
            self.runtime_authority_source_role == "absence_marker"
            and self.source_presence_posture == "present"
        ):
            raise ValueError("absence-marker runtime authority rows must not be present sources")
        if (
            self.runtime_authority_source_role in _CONTEXT_SOURCE_ROLES
            and self.authority_layer == "lock"
            and self.source_kind == "support_doc"
        ):
            raise ValueError("support context may not be marked as lock authority")
        return self


class RepoRuntimeAuthoritySourceIndex(_CartographyBase):
    schema: Literal["repo_runtime_authority_source_index@1"] = (
        REPO_RUNTIME_AUTHORITY_SOURCE_INDEX_SCHEMA
    )
    runtime_authority_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    source_rows: list[RepoRuntimeAuthoritySourceRow] = Field(min_length=1)
    runtime_authority_source_summary: str

    @model_validator(mode="after")
    def _validate_runtime_authority_source_index(self) -> RepoRuntimeAuthoritySourceIndex:
        object.__setattr__(
            self,
            "source_rows",
            _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows"),
        )
        _non_empty(self.review_id, field_name="review_id")
        _non_empty(self.snapshot_id, field_name="snapshot_id")
        _non_empty(self.source_set_id, field_name="source_set_id")
        _require_terms(
            self.runtime_authority_source_summary,
            field_name="runtime_authority_source_summary",
            terms=("eligibility", "context", "no prose memory", "no execution"),
        )
        expected_id = _surface_id(
            "repo_runtime_authority_source_index",
            self.schema,
            self.model_dump(mode="json"),
            "runtime_authority_source_index_id",
        )
        if self.runtime_authority_source_index_id != expected_id:
            raise ValueError("runtime_authority_source_index_id does not match canonical hash")
        return self


class RepoRuntimeAuthorityRequirementRow(_CartographyBase):
    authority_requirement_ref: str
    candidate_ref: str
    authority_kind: RuntimeExecutionAuthorityKind
    required_for_horizon: RequestedRuntimeAuthorityHorizon
    source_refs: list[str] = Field(min_length=1)
    source_presence_posture: CandidateSourcePresencePosture
    authority_gap_posture: RuntimeAuthorityGapPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_authority_requirement_row(
        self,
    ) -> RepoRuntimeAuthorityRequirementRow:
        _non_empty(self.authority_requirement_ref, field_name="authority_requirement_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        object.__setattr__(
            self,
            "source_refs",
            _sorted_unique(self.source_refs, field_name="source_refs"),
        )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        _reject_v78_action_claim(self.limitation_note, field_name="limitation_note")
        if (
            self.source_presence_posture != "present"
            and self.authority_gap_posture != "unknown_needs_review"
        ):
            raise ValueError("missing authority requirement sources must remain unknown")
        return self


class RepoRuntimeExecutionAuthorityRequestRow(_CartographyBase):
    authority_request_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    v77_authority_posture_refs: list[str] = Field(default_factory=list)
    v77_summary_refs: list[str] = Field(default_factory=list)
    v77_handoff_refs: list[str] = Field(default_factory=list)
    v77_closeout_refs: list[str] = Field(default_factory=list)
    requested_authority_horizon: RequestedRuntimeAuthorityHorizon
    authority_request_posture: RuntimeExecutionAuthorityRequestPosture
    requested_tool_use_refs: list[str] = Field(default_factory=list)
    requested_command_scope_refs: list[str] = Field(default_factory=list)
    required_authority_source_refs: list[str] = Field(default_factory=list)
    authority_requirement_rows: list[RepoRuntimeAuthorityRequirementRow] = Field(
        default_factory=list
    )
    target_boundary_refs: list[str] = Field(default_factory=list)
    telemetry_requirement_refs: list[str] = Field(default_factory=list)
    rollback_requirement_refs: list[str] = Field(default_factory=list)
    guardrail_refs: list[str] = Field(min_length=1)
    execution_posture: RuntimeAuthorityExecutionPosture
    tool_invocation_posture: RuntimeAuthorityToolInvocationPosture
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_execution_authority_request_row(
        self,
    ) -> RepoRuntimeExecutionAuthorityRequestRow:
        _non_empty(self.authority_request_ref, field_name="authority_request_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "v77_authority_posture_refs",
            "v77_summary_refs",
            "v77_handoff_refs",
            "v77_closeout_refs",
            "requested_tool_use_refs",
            "requested_command_scope_refs",
            "required_authority_source_refs",
            "target_boundary_refs",
            "telemetry_requirement_refs",
            "rollback_requirement_refs",
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
        object.__setattr__(
            self,
            "authority_requirement_rows",
            _sorted_unique_by_ref(
                self.authority_requirement_rows,
                attr="authority_requirement_ref",
                field_name="authority_requirement_rows",
            ),
        )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        for target_ref in self.target_boundary_refs:
            _reject_glob_ref(target_ref, field_name="target_boundary_refs")
            _repo_ref(target_ref, field_name="target_boundary_refs")
        if self.execution_posture != "no_execution_performed_by_v78":
            raise ValueError("V78-A request rows must not perform execution")
        if self.tool_invocation_posture != "no_tool_invocation_performed_by_v78":
            raise ValueError("V78-A request rows must not invoke tools")
        if self.required_authority_source_refs and not self.authority_requirement_rows:
            raise ValueError("required authority source refs must resolve to row-shaped records")
        row_refs = {row.authority_requirement_ref for row in self.authority_requirement_rows}
        if set(self.required_authority_source_refs) != row_refs:
            raise ValueError("required authority source refs must match authority rows")
        for row in self.authority_requirement_rows:
            if row.candidate_ref != self.candidate_ref:
                raise ValueError("authority requirement rows must match request candidate")
        _reject_v78_action_claim(self.limitation_note, field_name="limitation_note")
        if self.authority_request_posture == "eligible_for_runtime_execution_authority_review":
            if self.requested_authority_horizon in {
                "future_product_runtime_review",
                "future_external_branch_runtime_review",
            }:
                raise ValueError("product/external pressure is not runtime-authority-ready")
            if not self.v77_authority_posture_refs:
                raise ValueError("eligible authority requests require V77 authority refs")
            if not self.v77_summary_refs:
                raise ValueError("eligible authority requests require V77 summary refs")
            if not self.v77_handoff_refs:
                raise ValueError("eligible authority requests require V77 handoff refs")
            if not self.v77_closeout_refs:
                raise ValueError("eligible authority requests require V77 closeout refs")
            authority_kinds = {row.authority_kind for row in self.authority_requirement_rows}
            if "runtime_execution_review_authority" not in authority_kinds:
                raise ValueError("eligible authority requests require runtime review authority")
            if "tool_use_review_authority" not in authority_kinds:
                raise ValueError("eligible authority requests require tool-use review authority")
        if self.requested_authority_horizon == "future_product_runtime_review":
            if self.authority_request_posture not in {
                "blocked_by_product_authority_gap",
                "future_family_only",
                "rejected_out_of_scope",
            }:
                raise ValueError("product pressure must remain product-blocked in V78-A")
            if not any(
                row.authority_kind == "product_authorization"
                for row in self.authority_requirement_rows
            ):
                raise ValueError("product pressure requires product authority blocker")
        if self.requested_authority_horizon == "future_external_branch_runtime_review":
            if self.authority_request_posture not in {
                "blocked_by_external_branch_gap",
                "future_family_only",
                "rejected_out_of_scope",
            }:
                raise ValueError("external branch pressure must remain blocked in V78-A")
            if not any(
                row.authority_kind == "external_branch_activation"
                for row in self.authority_requirement_rows
            ):
                raise ValueError("external branch pressure requires external authority blocker")
        if self.requested_command_scope_refs:
            raise ValueError("V78-A must not emit command-scope authorization refs")
        return self


class RepoRuntimeExecutionAuthorityRequest(_CartographyBase):
    schema: Literal["repo_runtime_execution_authority_request@1"] = (
        REPO_RUNTIME_EXECUTION_AUTHORITY_REQUEST_SCHEMA
    )
    runtime_execution_authority_request_id: str
    runtime_authority_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    request_rows: list[RepoRuntimeExecutionAuthorityRequestRow] = Field(min_length=1)
    runtime_authority_boundary_summary: str

    @model_validator(mode="after")
    def _validate_runtime_execution_authority_request(
        self,
    ) -> RepoRuntimeExecutionAuthorityRequest:
        object.__setattr__(
            self,
            "request_rows",
            _sorted_unique_by_ref(
                self.request_rows,
                attr="authority_request_ref",
                field_name="request_rows",
            ),
        )
        _require_terms(
            self.runtime_authority_boundary_summary,
            field_name="runtime_authority_boundary_summary",
            terms=("request", "no execution", "no tool invocation", "no release"),
        )
        expected_id = _surface_id(
            "repo_runtime_execution_authority_request",
            self.schema,
            self.model_dump(mode="json"),
            "runtime_execution_authority_request_id",
        )
        if self.runtime_execution_authority_request_id != expected_id:
            raise ValueError(
                "runtime_execution_authority_request_id does not match canonical hash"
            )
        return self


class RepoRuntimeAuthorityNonActionGuardrailRow(_CartographyBase):
    guardrail_ref: str
    candidate_ref: str
    authority_request_refs: list[str] = Field(min_length=1)
    forbidden_runtime_actions: list[RuntimeAuthorityForbiddenAction] = Field(min_length=1)
    forbidden_downstream_authority: list[RuntimeAuthorityForbiddenDownstreamAuthority] = Field(
        min_length=1
    )
    execution_posture: RuntimeAuthorityExecutionPosture
    tool_invocation_posture: RuntimeAuthorityToolInvocationPosture
    authority_gap_refs: list[str] = Field(default_factory=list)
    source_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_runtime_authority_guardrail_row(
        self,
    ) -> RepoRuntimeAuthorityNonActionGuardrailRow:
        _non_empty(self.guardrail_ref, field_name="guardrail_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "authority_request_refs",
            "forbidden_runtime_actions",
            "forbidden_downstream_authority",
            "authority_gap_refs",
            "source_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        missing_actions = _FORBIDDEN_RUNTIME_ACTIONS.difference(
            self.forbidden_runtime_actions
        )
        if missing_actions:
            raise ValueError("runtime authority guardrail omits forbidden runtime actions")
        missing_authority = _FORBIDDEN_DOWNSTREAM_AUTHORITIES.difference(
            self.forbidden_downstream_authority
        )
        if missing_authority:
            raise ValueError("runtime authority guardrail omits forbidden downstream authority")
        if self.execution_posture != "no_execution_performed_by_v78":
            raise ValueError("runtime authority guardrails must preserve no-execution posture")
        if self.tool_invocation_posture != "no_tool_invocation_performed_by_v78":
            raise ValueError("runtime authority guardrails may not invoke tools")
        _reject_v78_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("no execution", "no tool invocation", "no release"),
        )
        return self


class RepoRuntimeAuthorityNonActionGuardrail(_CartographyBase):
    schema: Literal["repo_runtime_authority_non_action_guardrail@1"] = (
        REPO_RUNTIME_AUTHORITY_NON_ACTION_GUARDRAIL_SCHEMA
    )
    runtime_authority_non_action_guardrail_id: str
    runtime_execution_authority_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    guardrail_rows: list[RepoRuntimeAuthorityNonActionGuardrailRow] = Field(min_length=1)
    non_action_summary: str

    @model_validator(mode="after")
    def _validate_runtime_authority_guardrail(
        self,
    ) -> RepoRuntimeAuthorityNonActionGuardrail:
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
            self.non_action_summary,
            field_name="non_action_summary",
            terms=("no execution", "no tool invocation", "no release"),
        )
        expected_id = _surface_id(
            "repo_runtime_authority_non_action_guardrail",
            self.schema,
            self.model_dump(mode="json"),
            "runtime_authority_non_action_guardrail_id",
        )
        if self.runtime_authority_non_action_guardrail_id != expected_id:
            raise ValueError(
                "runtime_authority_non_action_guardrail_id does not match canonical hash"
            )
        return self


def derive_v78a_repo_runtime_authority_source_index(
    *, repo_root: Path | None = None
) -> RepoRuntimeAuthoritySourceIndex:
    _ = repo_root
    payload = {
        "schema": REPO_RUNTIME_AUTHORITY_SOURCE_INDEX_SCHEMA,
        "runtime_authority_source_index_id": "",
        "review_id": "review:v78a:runtime-execution-authority-request",
        "snapshot_id": "vNext+217-closed-on-main",
        "source_set_id": "source-set:v78a:released-v77c-runtime-authority-pressure",
        "source_rows": [
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus217/"
                    "repo_runtime_permission_authority_posture_v217_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "v77_authority_posture_source",
                "source_horizon": "Released V77-C runtime authority posture rows.",
                "limitation_note": (
                    "Eligibility source for authority request review only; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus217/"
                    "repo_runtime_permission_review_summary_v217_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "v77_runtime_summary_source",
                "source_horizon": "Released V77-C runtime review summary rows.",
                "limitation_note": (
                    "Eligibility source for authority request review only; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus217/"
                    "repo_post_runtime_permission_review_handoff_v217_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": (
                    "v77_post_runtime_permission_review_handoff_source"
                ),
                "source_horizon": (
                    "Released V77-C post-runtime-permission-review handoff rows."
                ),
                "limitation_note": (
                    "Eligibility source for authority request review only; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus217/"
                    "repo_runtime_permission_family_closeout_alignment_v217_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "v77_family_closeout_source",
                "source_horizon": "Released V77 family closeout alignment rows.",
                "limitation_note": "Eligibility source for family boundary only; no execution.",
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus216/"
                    "repo_command_preflight_contract_v216_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "v77_command_preflight_context",
                "source_horizon": "Released V77-B command preflight context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus216/"
                    "repo_action_effect_envelope_v216_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "v77_effect_envelope_context",
                "source_horizon": "Released V77-B action-effect envelope context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus216/"
                    "repo_runtime_telemetry_requirement_v216_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "v77_telemetry_requirement_context",
                "source_horizon": "Released V77-B telemetry requirement context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus216/"
                    "repo_runtime_rollback_contract_v216_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "v77_rollback_contract_context",
                "source_horizon": "Released V77-B rollback contract context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path(
                    "docs/support/arc_series_mapping/"
                    "V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_COMBINED_DOGFOOD_TEST_v0.json"
                ),
                "source_kind": "support_doc",
                "authority_layer": "support",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "combined_dogfood_source",
                "source_horizon": "Combined V68-V77 dogfood context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
            {
                "source_ref": _source_path("docs/LOCKED_CONTINUATION_vNEXT_PLUS218.md"),
                "source_kind": "planning_doc",
                "authority_layer": "lock",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "runtime_authority_source_role": "support_context",
                "source_horizon": "Active V78-A starter lock context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; no execution."
                ),
            },
        ],
        "runtime_authority_source_summary": (
            "Runtime authority source rows separate eligibility from context with "
            "no prose memory and no execution."
        ),
    }
    payload["source_rows"] = sorted(payload["source_rows"], key=lambda row: row["source_ref"])
    payload["runtime_authority_source_index_id"] = _surface_id(
        "repo_runtime_authority_source_index",
        REPO_RUNTIME_AUTHORITY_SOURCE_INDEX_SCHEMA,
        payload,
        "runtime_authority_source_index_id",
    )
    return RepoRuntimeAuthoritySourceIndex.model_validate(payload)


def _runtime_authority_requirement_rows_for_candidate(
    candidate_ref: str,
) -> list[RepoRuntimeAuthorityRequirementRow]:
    if candidate_ref == "candidate:internal:self_evidencing_workflow_type_emergence":
        rows = [
            {
                "authority_requirement_ref": "authority:v78a:self-evidencing:runtime-review",
                "candidate_ref": candidate_ref,
                "authority_kind": "runtime_execution_review_authority",
                "required_for_horizon": "bounded_repo_script_execution_review",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus217/"
                    "repo_runtime_permission_authority_posture_v217_reference.json",
                    "docs/LOCKED_CONTINUATION_vNEXT_PLUS218.md",
                ],
                "source_presence_posture": "present",
                "authority_gap_posture": "authority_gap_present",
                "limitation_note": (
                    "Runtime execution review authority remains required; no execution."
                ),
            },
            {
                "authority_requirement_ref": "authority:v78a:self-evidencing:tool-use-review",
                "candidate_ref": candidate_ref,
                "authority_kind": "tool_use_review_authority",
                "required_for_horizon": "bounded_tool_invocation_review",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus217/"
                    "repo_runtime_permission_authority_posture_v217_reference.json",
                    "docs/LOCKED_CONTINUATION_vNEXT_PLUS218.md",
                ],
                "source_presence_posture": "present",
                "authority_gap_posture": "authority_gap_present",
                "limitation_note": (
                    "Tool-use review authority remains required; no tool invocation."
                ),
            },
        ]
    elif candidate_ref == "candidate:internal:typed_adjudication_product_wedge":
        rows = [
            {
                "authority_requirement_ref": "authority:v78a:product-wedge:product-review",
                "candidate_ref": candidate_ref,
                "authority_kind": "product_authorization",
                "required_for_horizon": "future_product_runtime_review",
                "source_refs": [
                    "apps/api/fixtures/repo_description/vnext_plus217/"
                    "repo_runtime_permission_authority_posture_v217_reference.json",
                    "docs/LOCKED_CONTINUATION_vNEXT_PLUS218.md",
                ],
                "source_presence_posture": "present",
                "authority_gap_posture": "authority_gap_present",
                "limitation_note": "Product authorization remains required before product review.",
            }
        ]
    elif candidate_ref == "candidate:conditional:v43_external_branch":
        rows = [
            {
                "authority_requirement_ref": "authority:v78a:v43:external-branch",
                "candidate_ref": candidate_ref,
                "authority_kind": "external_branch_activation",
                "required_for_horizon": "future_external_branch_runtime_review",
                "source_refs": ["docs/LOCKED_CONTINUATION_vNEXT_PLUS218.md"],
                "source_presence_posture": "present",
                "authority_gap_posture": "authority_gap_present",
                "limitation_note": "External branch activation remains required before review.",
            }
        ]
    else:
        rows = []
    return [RepoRuntimeAuthorityRequirementRow.model_validate(row) for row in rows]


def derive_v78a_repo_runtime_execution_authority_request(
    *,
    repo_root: Path | None = None,
    runtime_authority_source_index: RepoRuntimeAuthoritySourceIndex | None = None,
) -> RepoRuntimeExecutionAuthorityRequest:
    _ = repo_root
    source_index = (
        runtime_authority_source_index
        or derive_v78a_repo_runtime_authority_source_index()
    )
    eligibility_sources = [
        row.source_ref
        for row in source_index.source_rows
        if row.runtime_authority_source_role in _ELIGIBILITY_SOURCE_ROLES
    ]
    context_sources = [
        row.source_ref
        for row in source_index.source_rows
        if row.runtime_authority_source_role in _CONTEXT_SOURCE_ROLES
    ]
    self_candidate = "candidate:internal:self_evidencing_workflow_type_emergence"
    product_candidate = "candidate:internal:typed_adjudication_product_wedge"
    self_authority_rows = _runtime_authority_requirement_rows_for_candidate(self_candidate)
    product_authority_rows = _runtime_authority_requirement_rows_for_candidate(product_candidate)
    payload = {
        "schema": REPO_RUNTIME_EXECUTION_AUTHORITY_REQUEST_SCHEMA,
        "runtime_execution_authority_request_id": "",
        "runtime_authority_source_index_id": source_index.runtime_authority_source_index_id,
        "review_id": source_index.review_id,
        "snapshot_id": source_index.snapshot_id,
        "source_set_id": source_index.source_set_id,
        "request_rows": [
            {
                "authority_request_ref": (
                    "authority-request:v78a:self-evidencing:runtime-execution-review"
                ),
                "candidate_ref": self_candidate,
                "source_refs": sorted([*eligibility_sources, *context_sources]),
                "v77_authority_posture_refs": [
                    "authority-posture:v77c:self-evidencing:runtime-execution",
                    "authority-posture:v77c:self-evidencing:tool-use",
                ],
                "v77_summary_refs": ["runtime-summary:v77c:self-evidencing:preflight"],
                "v77_handoff_refs": ["handoff:v77c:self-evidencing:preflight"],
                "v77_closeout_refs": [
                    "repo_runtime_permission_family_closeout_alignment_836d6f0ac44683ea0914ef7e"
                ],
                "requested_authority_horizon": "bounded_repo_script_execution_review",
                "authority_request_posture": "eligible_for_runtime_execution_authority_review",
                "requested_tool_use_refs": ["tool-use-request:v78a:self-evidencing:review-only"],
                "requested_command_scope_refs": [],
                "required_authority_source_refs": [
                    row.authority_requirement_ref for row in self_authority_rows
                ],
                "authority_requirement_rows": [
                    row.model_dump(mode="json") for row in self_authority_rows
                ],
                "target_boundary_refs": [
                    "packages/adeu_repo_description/src/adeu_repo_description/"
                    "runtime_execution_authority.py"
                ],
                "telemetry_requirement_refs": ["telemetry:v77b:self-evidencing:required"],
                "rollback_requirement_refs": ["rollback:v77b:self-evidencing:required"],
                "guardrail_refs": ["guardrail:v78a:self-evidencing:non-action"],
                "execution_posture": "no_execution_performed_by_v78",
                "tool_invocation_posture": "no_tool_invocation_performed_by_v78",
                "odeu_lanes": ["deontic", "epistemic", "utility"],
                "limitation_note": (
                    "Eligible for runtime execution authority request review only with "
                    "no execution, no tool invocation, and no release."
                ),
            },
            {
                "authority_request_ref": "authority-request:v78a:product-wedge:blocked",
                "candidate_ref": product_candidate,
                "source_refs": sorted([*eligibility_sources, *context_sources]),
                "v77_authority_posture_refs": [
                    "authority-posture:v77c:product-wedge:product-review"
                ],
                "v77_summary_refs": ["runtime-summary:v77c:product-wedge:blocked"],
                "v77_handoff_refs": ["handoff:v77c:product-wedge:blocked"],
                "v77_closeout_refs": [
                    "repo_runtime_permission_family_closeout_alignment_836d6f0ac44683ea0914ef7e"
                ],
                "requested_authority_horizon": "future_product_runtime_review",
                "authority_request_posture": "blocked_by_product_authority_gap",
                "requested_tool_use_refs": [],
                "requested_command_scope_refs": [],
                "required_authority_source_refs": [
                    row.authority_requirement_ref for row in product_authority_rows
                ],
                "authority_requirement_rows": [
                    row.model_dump(mode="json") for row in product_authority_rows
                ],
                "target_boundary_refs": [],
                "telemetry_requirement_refs": [],
                "rollback_requirement_refs": [],
                "guardrail_refs": ["guardrail:v78a:product-wedge:non-action"],
                "execution_posture": "no_execution_performed_by_v78",
                "tool_invocation_posture": "no_tool_invocation_performed_by_v78",
                "odeu_lanes": ["deontic", "utility"],
                "limitation_note": (
                    "Product pressure remains blocked by later product authority with "
                    "no execution, no tool invocation, and no release."
                ),
            },
        ],
        "runtime_authority_boundary_summary": (
            "Runtime execution authority request is request only: no execution, "
            "no tool invocation, no product authorization, and no release."
        ),
    }
    payload["request_rows"] = sorted(
        payload["request_rows"],
        key=lambda row: row["authority_request_ref"],
    )
    payload["runtime_execution_authority_request_id"] = _surface_id(
        "repo_runtime_execution_authority_request",
        REPO_RUNTIME_EXECUTION_AUTHORITY_REQUEST_SCHEMA,
        payload,
        "runtime_execution_authority_request_id",
    )
    return RepoRuntimeExecutionAuthorityRequest.model_validate(payload)


def derive_v78a_repo_runtime_authority_non_action_guardrail(
    *,
    repo_root: Path | None = None,
    runtime_execution_authority_request: RepoRuntimeExecutionAuthorityRequest | None = None,
) -> RepoRuntimeAuthorityNonActionGuardrail:
    _ = repo_root
    request = (
        runtime_execution_authority_request
        or derive_v78a_repo_runtime_execution_authority_request()
    )
    grouped_rows: dict[str, dict[str, object]] = {}
    for request_row in request.request_rows:
        for guardrail_ref in request_row.guardrail_refs:
            existing = grouped_rows.setdefault(
                guardrail_ref,
                {
                    "guardrail_ref": guardrail_ref,
                    "candidate_ref": request_row.candidate_ref,
                    "authority_request_refs": [],
                    "forbidden_runtime_actions": sorted(_FORBIDDEN_RUNTIME_ACTIONS),
                    "forbidden_downstream_authority": sorted(
                        _FORBIDDEN_DOWNSTREAM_AUTHORITIES
                    ),
                    "execution_posture": "no_execution_performed_by_v78",
                    "tool_invocation_posture": "no_tool_invocation_performed_by_v78",
                    "authority_gap_refs": [],
                    "source_refs": [],
                    "limitation_note": (
                        "This V78-A row is request only: no execution, no tool invocation, "
                        "no product authorization, no external branch activation, and no release."
                    ),
                },
            )
            if existing["candidate_ref"] != request_row.candidate_ref:
                raise ValueError("runtime authority guardrail derivation cannot merge candidates")
            existing["authority_request_refs"] = sorted(
                {
                    *existing["authority_request_refs"],
                    request_row.authority_request_ref,
                }
            )
            existing["authority_gap_refs"] = sorted(
                {
                    *existing["authority_gap_refs"],
                    *request_row.required_authority_source_refs,
                }
            )
            existing["source_refs"] = sorted(
                {*existing["source_refs"], *request_row.source_refs}
            )
    payload = {
        "schema": REPO_RUNTIME_AUTHORITY_NON_ACTION_GUARDRAIL_SCHEMA,
        "runtime_authority_non_action_guardrail_id": "",
        "runtime_execution_authority_request_id": (
            request.runtime_execution_authority_request_id
        ),
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "guardrail_rows": sorted(
            grouped_rows.values(),
            key=lambda row: row["guardrail_ref"],
        ),
        "non_action_summary": (
            "Runtime authority non-action guardrails preserve request only: "
            "no execution, no tool invocation, no product authorization, and no release."
        ),
    }
    payload["runtime_authority_non_action_guardrail_id"] = _surface_id(
        "repo_runtime_authority_non_action_guardrail",
        REPO_RUNTIME_AUTHORITY_NON_ACTION_GUARDRAIL_SCHEMA,
        payload,
        "runtime_authority_non_action_guardrail_id",
    )
    return RepoRuntimeAuthorityNonActionGuardrail.model_validate(payload)


def validate_v78a_runtime_execution_authority_bundle(
    *,
    runtime_authority_source_index: RepoRuntimeAuthoritySourceIndex,
    runtime_execution_authority_request: RepoRuntimeExecutionAuthorityRequest,
    runtime_authority_non_action_guardrail: RepoRuntimeAuthorityNonActionGuardrail,
) -> None:
    if (
        runtime_execution_authority_request.runtime_authority_source_index_id
        != runtime_authority_source_index.runtime_authority_source_index_id
    ):
        raise ValueError("runtime authority request must reference the source index")
    if (
        runtime_execution_authority_request.review_id,
        runtime_execution_authority_request.snapshot_id,
        runtime_execution_authority_request.source_set_id,
    ) != (
        runtime_authority_source_index.review_id,
        runtime_authority_source_index.snapshot_id,
        runtime_authority_source_index.source_set_id,
    ):
        raise ValueError("runtime authority request provenance must match source index")
    if (
        runtime_authority_non_action_guardrail.runtime_execution_authority_request_id
        != runtime_execution_authority_request.runtime_execution_authority_request_id
    ):
        raise ValueError("runtime authority guardrail must reference the request surface")
    if (
        runtime_authority_non_action_guardrail.review_id,
        runtime_authority_non_action_guardrail.snapshot_id,
        runtime_authority_non_action_guardrail.source_set_id,
    ) != (
        runtime_execution_authority_request.review_id,
        runtime_execution_authority_request.snapshot_id,
        runtime_execution_authority_request.source_set_id,
    ):
        raise ValueError("runtime authority guardrail provenance must match request")

    source_roles = {
        row.source_ref: row.runtime_authority_source_role
        for row in runtime_authority_source_index.source_rows
    }
    known_sources = set(source_roles)
    request_rows = {
        row.authority_request_ref: row
        for row in runtime_execution_authority_request.request_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row
        for row in runtime_authority_non_action_guardrail.guardrail_rows
    }
    for request_row in runtime_execution_authority_request.request_rows:
        if any(source_ref not in known_sources for source_ref in request_row.source_refs):
            raise ValueError("runtime authority request source refs must be known")
        roles = {source_roles[source_ref] for source_ref in request_row.source_refs}
        if (
            request_row.authority_request_posture
            == "eligible_for_runtime_execution_authority_review"
        ):
            if not _ELIGIBILITY_SOURCE_ROLES.issubset(roles):
                raise ValueError(
                    "eligible runtime authority requests require released V77-C sources"
                )
        for requirement_row in request_row.authority_requirement_rows:
            if any(source_ref not in known_sources for source_ref in requirement_row.source_refs):
                raise ValueError("runtime authority requirement source refs must be known")
        if any(
            guardrail_ref not in guardrail_rows
            for guardrail_ref in request_row.guardrail_refs
        ):
            raise ValueError("runtime authority request guardrail refs must be known")
        for guardrail_ref in request_row.guardrail_refs:
            guardrail_row = guardrail_rows[guardrail_ref]
            if guardrail_row.candidate_ref != request_row.candidate_ref:
                raise ValueError("runtime authority guardrails must match candidate")
            if request_row.authority_request_ref not in guardrail_row.authority_request_refs:
                raise ValueError("runtime authority guardrails must reference request rows")
            if set(request_row.required_authority_source_refs) - set(
                guardrail_row.authority_gap_refs
            ):
                raise ValueError("runtime authority guardrails must carry authority gap refs")

    for guardrail_row in runtime_authority_non_action_guardrail.guardrail_rows:
        if any(source_ref not in known_sources for source_ref in guardrail_row.source_refs):
            raise ValueError("runtime authority guardrail source refs must be known")
        if any(ref not in request_rows for ref in guardrail_row.authority_request_refs):
            raise ValueError("guardrail authority request refs must be known")
        for ref in guardrail_row.authority_request_refs:
            if request_rows[ref].candidate_ref != guardrail_row.candidate_ref:
                raise ValueError("guardrail authority refs must match candidate")


def derive_v78a_runtime_execution_authority_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoRuntimeAuthoritySourceIndex,
    RepoRuntimeExecutionAuthorityRequest,
    RepoRuntimeAuthorityNonActionGuardrail,
]:
    source_index = derive_v78a_repo_runtime_authority_source_index(repo_root=repo_root)
    request = derive_v78a_repo_runtime_execution_authority_request(
        repo_root=repo_root,
        runtime_authority_source_index=source_index,
    )
    guardrail = derive_v78a_repo_runtime_authority_non_action_guardrail(
        repo_root=repo_root,
        runtime_execution_authority_request=request,
    )
    validate_v78a_runtime_execution_authority_bundle(
        runtime_authority_source_index=source_index,
        runtime_execution_authority_request=request,
        runtime_authority_non_action_guardrail=guardrail,
    )
    return source_index, request, guardrail
