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

REPO_CROSS_CORPUS_GOVERNANCE_REQUEST_SCHEMA = "repo_cross_corpus_governance_request@1"
REPO_CROSS_CORPUS_SOURCE_INDEX_SCHEMA = "repo_cross_corpus_source_index@1"
REPO_CROSS_CORPUS_NON_INGESTION_GUARDRAIL_SCHEMA = (
    "repo_cross_corpus_non_ingestion_guardrail@1"
)

CrossCorpusSourceRole = Literal[
    "v80_summary_source",
    "v80_handoff_source",
    "v80_closeout_source",
    "concrete_repo_local_corpus_source",
    "concrete_imported_corpus_source",
    "concrete_benchmark_result_source",
    "concrete_customer_corpus_source",
    "concrete_paper_design_repo_bundle_source",
    "synthetic_corpus_descriptor_source",
    "explicit_corpus_absence_marker",
    "explicit_authority_absence_marker",
    "dogfood_context",
    "roadmap_context",
    "support_process_context",
    "absence_marker",
]
CorpusHorizonKind = Literal[
    "repo_local_corpus_governance",
    "imported_corpus_governance",
    "benchmark_result_governance",
    "customer_corpus_governance",
    "paper_design_repo_bundle_governance",
    "synthetic_descriptor_governance",
    "corpus_absence_review",
    "product_pressure_out_of_scope",
]
CorpusSourceCurrentness = Literal[
    "current_concrete_source",
    "explicit_absence_marker",
    "historical_context_only",
    "stale_or_superseded",
    "unknown_needs_review",
]
CorpusReviewPosture = Literal[
    "request_recorded_boundary_only",
    "request_recorded_absence_only",
    "eligible_for_cross_corpus_governance_review",
    "blocked_by_missing_source",
    "blocked_by_missing_corpus_source",
    "blocked_by_missing_corpus_boundary",
    "blocked_by_missing_provenance",
    "blocked_by_missing_authority",
    "blocked_by_missing_privacy_authority",
    "blocked_by_missing_license_or_consent",
    "blocked_by_missing_customer_data_authority",
    "blocked_by_missing_connector_authority",
    "blocked_by_benchmark_truth_guardrail",
    "blocked_by_product_authority_gap",
    "blocked_by_external_branch_authority_gap",
    "future_family_only",
    "rejected_out_of_scope",
]
CorpusRequestedHorizon = Literal[
    "corpus_boundary_required_later",
    "provenance_required_later",
    "not_selected_in_v81a",
    "blocked_by_missing_corpus_source",
    "blocked_by_missing_authority",
    "future_family_only",
]
CorpusRequirementPosture = Literal[
    "required_for_later_review",
    "not_selected_in_v81a",
    "not_applicable",
    "blocked_by_missing_corpus_source",
    "blocked_by_missing_authority",
    "blocked_by_missing_privacy_authority",
    "blocked_by_missing_license_or_consent",
    "blocked_by_missing_customer_data_authority",
    "blocked_by_missing_connector_authority",
    "blocked_by_product_authority_gap",
    "future_family_only",
]
CorpusIngestionPosture = Literal[
    "no_corpus_ingestion_performed_by_v81",
    "corpus_ingestion_requires_later_family",
    "corpus_ingestion_forbidden_by_this_family",
]
ConnectorActivationPosture = Literal[
    "no_connector_activation_performed_by_v81",
    "connector_activation_requires_later_family",
    "connector_activation_forbidden_by_this_family",
]
ExternalEndpointAccessPosture = Literal[
    "no_endpoint_access_performed_by_v81",
    "endpoint_access_requires_later_family",
    "endpoint_access_forbidden_by_this_family",
]
AdjudicationExecutionPosture = Literal[
    "no_cross_corpus_adjudication_performed_by_v81",
    "cross_corpus_adjudication_requires_later_family",
    "cross_corpus_adjudication_forbidden_by_this_family",
]
ForbiddenCorpusDataAction = Literal[
    "ingest_corpus",
    "import_external_data",
    "export_repo_data_to_external_corpus",
    "handle_customer_data",
    "transfer_corpus_data",
    "persist_imported_corpus_content",
    "run_cross_corpus_adjudication",
]
ForbiddenConnectorAction = Literal[
    "activate_connector",
    "access_endpoint",
    "mutate_endpoint",
    "fetch_external_corpus",
    "upload_customer_data",
    "invoke_external_tool_for_corpus",
]
ForbiddenCrossCorpusDownstreamAuthority = Literal[
    "corpus_ingestion",
    "external_data_import",
    "customer_data_handling",
    "connector_activation",
    "endpoint_access",
    "cross_corpus_adjudication_execution",
    "product_authorization",
    "release_authority",
    "benchmark_truth",
    "imported_result_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
    "v82_selection",
]
NonIngestionPosture = Literal["non_ingestion_guardrail_active"]
NonConnectorPosture = Literal["non_connector_guardrail_active"]

_V80_ELIGIBILITY_SOURCE_ROLES = {
    "v80_summary_source",
    "v80_handoff_source",
    "v80_closeout_source",
}
_CONCRETE_CORPUS_SOURCE_ROLES = {
    "concrete_repo_local_corpus_source",
    "concrete_imported_corpus_source",
    "concrete_benchmark_result_source",
    "concrete_customer_corpus_source",
    "concrete_paper_design_repo_bundle_source",
    "synthetic_corpus_descriptor_source",
}
_CONTEXT_SOURCE_ROLES = {
    "dogfood_context",
    "roadmap_context",
    "support_process_context",
}
_ABSENCE_SOURCE_ROLES = {
    "explicit_corpus_absence_marker",
    "explicit_authority_absence_marker",
    "absence_marker",
}
_FORBIDDEN_DATA_ACTIONS = {
    "ingest_corpus",
    "import_external_data",
    "export_repo_data_to_external_corpus",
    "handle_customer_data",
    "transfer_corpus_data",
    "persist_imported_corpus_content",
    "run_cross_corpus_adjudication",
}
_FORBIDDEN_CONNECTOR_ACTIONS = {
    "activate_connector",
    "access_endpoint",
    "mutate_endpoint",
    "fetch_external_corpus",
    "upload_customer_data",
    "invoke_external_tool_for_corpus",
}
_FORBIDDEN_DOWNSTREAM_AUTHORITIES = {
    "corpus_ingestion",
    "external_data_import",
    "customer_data_handling",
    "connector_activation",
    "endpoint_access",
    "cross_corpus_adjudication_execution",
    "product_authorization",
    "release_authority",
    "benchmark_truth",
    "imported_result_truth",
    "model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
    "v82_selection",
}


def _source_path(path: str) -> str:
    _repo_ref(path, field_name="source_ref")
    return path


def _require_terms(value: str, *, field_name: str, terms: tuple[str, ...]) -> str:
    lowered = value.lower()
    missing = [term for term in terms if term not in lowered]
    if missing:
        raise ValueError(f"{field_name} must mention {', '.join(missing)}")
    return value


def _reject_v81_action_claim(value: str, *, field_name: str) -> str:
    lowered = value.lower()
    forbidden_patterns = [
        r"corpus (?:is |was |has been |gets |got )?ingested",
        r"ingest corpus",
        r"customer data (?:is |was |has been |gets |got )?handled",
        r"connector (?:is |was |has been |gets |got )?activated",
        r"activate connector",
        r"endpoint (?:is |was |has been |gets |got )?accessed",
        r"access endpoint",
        r"cross-corpus adjudication (?:is |was |has been |gets |got )?executed",
        r"benchmark truth",
        r"imported result truth",
        r"product (?:is |was |has been |gets |got )?authorized",
        r"release now",
        r"v82 (?:is |was |has been |gets |got )?selected",
    ]
    negation_markers = ("no ", "not ", "without ", "forbidden ", "non-")
    for pattern in forbidden_patterns:
        match = re.search(pattern, lowered)
        if match is None:
            continue
        prefix = lowered[max(0, match.start() - 24) : match.start()]
        if not any(marker in prefix for marker in negation_markers):
            raise ValueError(f"{field_name} may not carry cross-corpus action authority")
    return value


class RepoCrossCorpusSourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    cross_corpus_source_role: CrossCorpusSourceRole
    source_horizon: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_cross_corpus_source_row(self) -> RepoCrossCorpusSourceRow:
        _repo_ref(self.source_ref, field_name="source_ref")
        _non_empty(self.source_horizon, field_name="source_horizon")
        _reject_v81_action_claim(self.limitation_note, field_name="limitation_note")
        if (
            self.cross_corpus_source_role not in _ABSENCE_SOURCE_ROLES
            and self.source_presence_posture != "present"
        ):
            raise ValueError("non-absence cross-corpus source rows must be present")
        if (
            self.cross_corpus_source_role in _ABSENCE_SOURCE_ROLES
            and self.source_presence_posture == "present"
        ):
            raise ValueError("absence-marker cross-corpus rows must not be present sources")
        if (
            self.cross_corpus_source_role in _CONTEXT_SOURCE_ROLES
            and self.authority_layer == "lock"
            and self.source_kind in {"support_doc", "planning_doc"}
        ):
            raise ValueError("context source rows may not be marked as lock authority")
        return self


class RepoCrossCorpusSourceIndex(_CartographyBase):
    schema: Literal["repo_cross_corpus_source_index@1"] = (
        REPO_CROSS_CORPUS_SOURCE_INDEX_SCHEMA
    )
    cross_corpus_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    source_rows: list[RepoCrossCorpusSourceRow] = Field(min_length=1)
    cross_corpus_source_summary: str

    @model_validator(mode="after")
    def _validate_cross_corpus_source_index(self) -> RepoCrossCorpusSourceIndex:
        object.__setattr__(
            self,
            "source_rows",
            _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows"),
        )
        _non_empty(self.review_id, field_name="review_id")
        _non_empty(self.snapshot_id, field_name="snapshot_id")
        _non_empty(self.source_set_id, field_name="source_set_id")
        _require_terms(
            self.cross_corpus_source_summary,
            field_name="cross_corpus_source_summary",
            terms=("eligibility", "absence", "no corpus ingestion"),
        )
        expected_id = _surface_id(
            "repo_cross_corpus_source_index",
            self.schema,
            self.model_dump(mode="json"),
            "cross_corpus_source_index_id",
        )
        if self.cross_corpus_source_index_id != expected_id:
            raise ValueError("cross_corpus_source_index_id does not match canonical hash")
        return self


class RepoCrossCorpusGovernanceRequestRow(_CartographyBase):
    cross_corpus_governance_request_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    v80_summary_refs: list[str] = Field(default_factory=list)
    v80_handoff_refs: list[str] = Field(default_factory=list)
    v80_closeout_refs: list[str] = Field(default_factory=list)
    corpus_family_ref: str
    corpus_horizon_kind: CorpusHorizonKind
    corpus_source_currentness: CorpusSourceCurrentness
    corpus_review_posture: CorpusReviewPosture
    requested_boundary_horizon: CorpusRequestedHorizon
    requested_provenance_horizon: CorpusRequestedHorizon
    required_authority_posture: CorpusRequirementPosture
    required_privacy_posture: CorpusRequirementPosture
    required_license_posture: CorpusRequirementPosture
    required_connector_posture: CorpusRequirementPosture
    guardrail_refs: list[str] = Field(min_length=1)
    corpus_ingestion_posture: CorpusIngestionPosture
    connector_activation_posture: ConnectorActivationPosture
    external_endpoint_access_posture: ExternalEndpointAccessPosture
    adjudication_execution_posture: AdjudicationExecutionPosture
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_cross_corpus_request_row(self) -> RepoCrossCorpusGovernanceRequestRow:
        _non_empty(
            self.cross_corpus_governance_request_ref,
            field_name="cross_corpus_governance_request_ref",
        )
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        _non_empty(self.corpus_family_ref, field_name="corpus_family_ref")
        for field_name in (
            "source_refs",
            "v80_summary_refs",
            "v80_handoff_refs",
            "v80_closeout_refs",
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
        if self.corpus_ingestion_posture != "no_corpus_ingestion_performed_by_v81":
            raise ValueError("V81-A request rows must not ingest corpora")
        if self.connector_activation_posture != "no_connector_activation_performed_by_v81":
            raise ValueError("V81-A request rows must not activate connectors")
        if self.external_endpoint_access_posture != "no_endpoint_access_performed_by_v81":
            raise ValueError("V81-A request rows must not access endpoints")
        if (
            self.adjudication_execution_posture
            != "no_cross_corpus_adjudication_performed_by_v81"
        ):
            raise ValueError("V81-A request rows must not execute cross-corpus adjudication")
        _reject_v81_action_claim(self.limitation_note, field_name="limitation_note")
        if self.corpus_review_posture == "eligible_for_cross_corpus_governance_review":
            if self.corpus_source_currentness != "current_concrete_source":
                raise ValueError(
                    "eligible cross-corpus governance requests require current corpus source"
                )
            if (
                not self.v80_summary_refs
                and not self.v80_handoff_refs
                and not self.v80_closeout_refs
            ):
                raise ValueError("eligible cross-corpus governance requests require V80-C refs")
        if self.corpus_review_posture == "request_recorded_absence_only":
            if self.corpus_source_currentness != "explicit_absence_marker":
                raise ValueError("absence-only requests require explicit source absence")
        if self.corpus_horizon_kind == "customer_corpus_governance":
            blocked_values = {"not_selected_in_v81a", "not_applicable"}
            if (
                self.required_privacy_posture in blocked_values
                or self.required_license_posture in blocked_values
                or self.required_authority_posture in blocked_values
            ):
                raise ValueError("customer corpus rows require privacy, license, and authority")
        if self.corpus_horizon_kind == "benchmark_result_governance":
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("no benchmark truth",),
            )
        if (
            "product" in self.candidate_ref
            or self.corpus_horizon_kind == "product_pressure_out_of_scope"
        ):
            if self.corpus_review_posture not in {
                "blocked_by_product_authority_gap",
                "future_family_only",
                "rejected_out_of_scope",
            }:
                raise ValueError("product pressure must remain blocked in V81-A")
            if self.required_authority_posture != "blocked_by_product_authority_gap":
                raise ValueError("product pressure requires product authority blocker")
        return self


class RepoCrossCorpusGovernanceRequest(_CartographyBase):
    schema: Literal["repo_cross_corpus_governance_request@1"] = (
        REPO_CROSS_CORPUS_GOVERNANCE_REQUEST_SCHEMA
    )
    cross_corpus_governance_request_id: str
    cross_corpus_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    request_rows: list[RepoCrossCorpusGovernanceRequestRow] = Field(min_length=1)
    cross_corpus_governance_summary: str

    @model_validator(mode="after")
    def _validate_cross_corpus_request(self) -> RepoCrossCorpusGovernanceRequest:
        object.__setattr__(
            self,
            "request_rows",
            _sorted_unique_by_ref(
                self.request_rows,
                attr="cross_corpus_governance_request_ref",
                field_name="request_rows",
            ),
        )
        _require_terms(
            self.cross_corpus_governance_summary,
            field_name="cross_corpus_governance_summary",
            terms=("review", "no corpus ingestion", "no connector activation", "no release"),
        )
        expected_id = _surface_id(
            "repo_cross_corpus_governance_request",
            self.schema,
            self.model_dump(mode="json"),
            "cross_corpus_governance_request_id",
        )
        if self.cross_corpus_governance_request_id != expected_id:
            raise ValueError("cross_corpus_governance_request_id does not match canonical hash")
        return self


class RepoCrossCorpusNonIngestionGuardrailRow(_CartographyBase):
    guardrail_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    cross_corpus_governance_request_refs: list[str] = Field(min_length=1)
    forbidden_data_actions: list[ForbiddenCorpusDataAction] = Field(min_length=1)
    forbidden_connector_actions: list[ForbiddenConnectorAction] = Field(min_length=1)
    forbidden_downstream_authority: list[ForbiddenCrossCorpusDownstreamAuthority] = Field(
        min_length=1
    )
    required_later_authority_refs: list[str] = Field(default_factory=list)
    non_ingestion_posture: NonIngestionPosture
    non_connector_posture: NonConnectorPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_cross_corpus_guardrail_row(self) -> RepoCrossCorpusNonIngestionGuardrailRow:
        _non_empty(self.guardrail_ref, field_name="guardrail_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "cross_corpus_governance_request_refs",
            "forbidden_data_actions",
            "forbidden_connector_actions",
            "forbidden_downstream_authority",
            "required_later_authority_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        missing_data_actions = _FORBIDDEN_DATA_ACTIONS.difference(self.forbidden_data_actions)
        if missing_data_actions:
            raise ValueError("cross-corpus guardrail omits forbidden data actions")
        missing_connector_actions = _FORBIDDEN_CONNECTOR_ACTIONS.difference(
            self.forbidden_connector_actions
        )
        if missing_connector_actions:
            raise ValueError("cross-corpus guardrail omits forbidden connector actions")
        missing_authority = _FORBIDDEN_DOWNSTREAM_AUTHORITIES.difference(
            self.forbidden_downstream_authority
        )
        if missing_authority:
            raise ValueError("cross-corpus guardrail omits forbidden downstream authority")
        _reject_v81_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("no corpus ingestion", "no connector activation", "no release"),
        )
        return self


class RepoCrossCorpusNonIngestionGuardrail(_CartographyBase):
    schema: Literal["repo_cross_corpus_non_ingestion_guardrail@1"] = (
        REPO_CROSS_CORPUS_NON_INGESTION_GUARDRAIL_SCHEMA
    )
    cross_corpus_non_ingestion_guardrail_id: str
    cross_corpus_governance_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    guardrail_rows: list[RepoCrossCorpusNonIngestionGuardrailRow] = Field(min_length=1)
    non_ingestion_summary: str

    @model_validator(mode="after")
    def _validate_cross_corpus_guardrail(self) -> RepoCrossCorpusNonIngestionGuardrail:
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
            self.non_ingestion_summary,
            field_name="non_ingestion_summary",
            terms=("no corpus ingestion", "no connector activation", "no release"),
        )
        expected_id = _surface_id(
            "repo_cross_corpus_non_ingestion_guardrail",
            self.schema,
            self.model_dump(mode="json"),
            "cross_corpus_non_ingestion_guardrail_id",
        )
        if self.cross_corpus_non_ingestion_guardrail_id != expected_id:
            raise ValueError(
                "cross_corpus_non_ingestion_guardrail_id does not match canonical hash"
            )
        return self


def derive_v81a_repo_cross_corpus_source_index(
    *, repo_root: Path | None = None
) -> RepoCrossCorpusSourceIndex:
    _ = repo_root
    payload = {
        "schema": REPO_CROSS_CORPUS_SOURCE_INDEX_SCHEMA,
        "cross_corpus_source_index_id": "",
        "review_id": "review:v81a:cross-corpus-governance",
        "snapshot_id": "vNext+226-external-branch-review-closeout",
        "source_set_id": "source-set:v81a:released-v80c-cross-corpus-pressure",
        "source_rows": [
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus226/"
                    "repo_external_branch_readiness_summary_v226_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "cross_corpus_source_role": "v80_summary_source",
                "source_horizon": "Released V80-C external branch readiness summary rows.",
                "limitation_note": (
                    "Eligibility substrate for cross-corpus review only; "
                    "no corpus ingestion."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus226/"
                    "repo_post_external_branch_review_handoff_v226_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "cross_corpus_source_role": "v80_handoff_source",
                "source_horizon": "Released V80-C post-external-branch-review handoff rows.",
                "limitation_note": (
                    "Handoff substrate for cross-corpus review only; "
                    "no corpus ingestion."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus226/"
                    "repo_external_branch_review_family_closeout_alignment_v226_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "cross_corpus_source_role": "v80_closeout_source",
                "source_horizon": "Released V80 family closeout alignment rows.",
                "limitation_note": (
                    "Family closeout context for review boundary only; "
                    "no corpus ingestion."
                ),
            },
            {
                "source_ref": _source_path(
                    "docs/support/arc_series_mapping/"
                    "V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_"
                    "COMBINED_DOGFOOD_TEST_v0.json"
                ),
                "source_kind": "support_doc",
                "authority_layer": "support",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "cross_corpus_source_role": "dogfood_context",
                "source_horizon": "Combined V68-V80 dogfood context.",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; "
                    "no corpus ingestion."
                ),
            },
            {
                "source_ref": _source_path("docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md"),
                "source_kind": "planning_doc",
                "authority_layer": "planning",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "cross_corpus_source_role": "roadmap_context",
                "source_horizon": "Post-V74 multi-arc roadmap context.",
                "limitation_note": (
                    "Roadmap context only and not sufficient for eligibility; "
                    "no corpus ingestion."
                ),
            },
            {
                "source_ref": "corpus-source:cross-corpus:current:absent",
                "source_kind": "external_artifact",
                "authority_layer": "support",
                "source_status": "review_pending_input",
                "source_presence_posture": "external_unavailable",
                "cross_corpus_source_role": "explicit_corpus_absence_marker",
                "source_horizon": "Current concrete cross-corpus source is absent.",
                "limitation_note": "Explicit absence marker only; no corpus ingestion.",
            },
            {
                "source_ref": "corpus-authority:customer-data:current:absent",
                "source_kind": "external_artifact",
                "authority_layer": "support",
                "source_status": "review_pending_input",
                "source_presence_posture": "external_unavailable",
                "cross_corpus_source_role": "explicit_authority_absence_marker",
                "source_horizon": "Customer data authority source is absent.",
                "limitation_note": "Explicit authority absence marker only; no corpus ingestion.",
            },
        ],
        "cross_corpus_source_summary": (
            "Cross-corpus source rows separate eligibility from absence and context "
            "with no corpus ingestion and no prose memory."
        ),
    }
    payload["source_rows"] = sorted(payload["source_rows"], key=lambda row: row["source_ref"])
    payload["cross_corpus_source_index_id"] = _surface_id(
        "repo_cross_corpus_source_index",
        REPO_CROSS_CORPUS_SOURCE_INDEX_SCHEMA,
        payload,
        "cross_corpus_source_index_id",
    )
    return RepoCrossCorpusSourceIndex.model_validate(payload)


def derive_v81a_repo_cross_corpus_governance_request(
    *,
    repo_root: Path | None = None,
    cross_corpus_source_index: RepoCrossCorpusSourceIndex | None = None,
) -> RepoCrossCorpusGovernanceRequest:
    _ = repo_root
    source_index = cross_corpus_source_index or derive_v81a_repo_cross_corpus_source_index()
    source_refs = [row.source_ref for row in source_index.source_rows]
    self_candidate = "candidate:internal:self_evidencing_workflow_type_emergence"
    product_candidate = "candidate:internal:typed_adjudication_product_wedge"
    payload = {
        "schema": REPO_CROSS_CORPUS_GOVERNANCE_REQUEST_SCHEMA,
        "cross_corpus_governance_request_id": "",
        "cross_corpus_source_index_id": source_index.cross_corpus_source_index_id,
        "review_id": source_index.review_id,
        "snapshot_id": source_index.snapshot_id,
        "source_set_id": source_index.source_set_id,
        "request_rows": [
            {
                "cross_corpus_governance_request_ref": (
                    "cross-corpus-governance:v81a:self-evidencing:source-absent"
                ),
                "candidate_ref": self_candidate,
                "source_refs": sorted(source_refs),
                "v80_summary_refs": [
                    "external-branch-summary:v80c:self-evidencing:v43-blocked"
                ],
                "v80_handoff_refs": [
                    "handoff:v80c:self-evidencing:external-authority-review"
                ],
                "v80_closeout_refs": [
                    "repo_external_branch_review_family_closeout_alignment_c0595828b382b50633052039"
                ],
                "corpus_family_ref": "cross-corpus:absent:self-evidencing",
                "corpus_horizon_kind": "corpus_absence_review",
                "corpus_source_currentness": "explicit_absence_marker",
                "corpus_review_posture": "blocked_by_missing_corpus_source",
                "requested_boundary_horizon": "blocked_by_missing_corpus_source",
                "requested_provenance_horizon": "blocked_by_missing_corpus_source",
                "required_authority_posture": "blocked_by_missing_authority",
                "required_privacy_posture": "blocked_by_missing_corpus_source",
                "required_license_posture": "blocked_by_missing_corpus_source",
                "required_connector_posture": "blocked_by_missing_corpus_source",
                "guardrail_refs": ["guardrail:v81a:self-evidencing:non-ingestion"],
                "corpus_ingestion_posture": "no_corpus_ingestion_performed_by_v81",
                "connector_activation_posture": "no_connector_activation_performed_by_v81",
                "external_endpoint_access_posture": "no_endpoint_access_performed_by_v81",
                "adjudication_execution_posture": (
                    "no_cross_corpus_adjudication_performed_by_v81"
                ),
                "odeu_lanes": ["deontic", "epistemic", "utility"],
                "limitation_note": (
                    "Cross-corpus governance review is blocked by missing corpus source "
                    "with no corpus ingestion, no connector activation, no endpoint access, "
                    "no cross-corpus adjudication, and no release."
                ),
            },
            {
                "cross_corpus_governance_request_ref": (
                    "cross-corpus-governance:v81a:product-wedge:product-blocked"
                ),
                "candidate_ref": product_candidate,
                "source_refs": sorted(source_refs),
                "v80_summary_refs": ["external-branch-summary:v80c:product-wedge:blocked"],
                "v80_handoff_refs": ["handoff:v80c:product-wedge:future-product-review"],
                "v80_closeout_refs": [
                    "repo_external_branch_review_family_closeout_alignment_c0595828b382b50633052039"
                ],
                "corpus_family_ref": "cross-corpus:product-pressure:typed-adjudication",
                "corpus_horizon_kind": "product_pressure_out_of_scope",
                "corpus_source_currentness": "explicit_absence_marker",
                "corpus_review_posture": "blocked_by_product_authority_gap",
                "requested_boundary_horizon": "future_family_only",
                "requested_provenance_horizon": "future_family_only",
                "required_authority_posture": "blocked_by_product_authority_gap",
                "required_privacy_posture": "not_applicable",
                "required_license_posture": "not_applicable",
                "required_connector_posture": "not_applicable",
                "guardrail_refs": ["guardrail:v81a:product-wedge:non-ingestion"],
                "corpus_ingestion_posture": "no_corpus_ingestion_performed_by_v81",
                "connector_activation_posture": "no_connector_activation_performed_by_v81",
                "external_endpoint_access_posture": "no_endpoint_access_performed_by_v81",
                "adjudication_execution_posture": (
                    "no_cross_corpus_adjudication_performed_by_v81"
                ),
                "odeu_lanes": ["deontic", "utility"],
                "limitation_note": (
                    "Product-pressure cross-corpus row remains product blocked with "
                    "no corpus ingestion, no connector activation, no endpoint access, "
                    "no cross-corpus adjudication, and no release."
                ),
            },
        ],
        "cross_corpus_governance_summary": (
            "Cross-corpus governance requests are review only: no corpus ingestion, "
            "no connector activation, no endpoint access, no cross-corpus adjudication, "
            "and no release."
        ),
    }
    payload["request_rows"] = sorted(
        payload["request_rows"],
        key=lambda row: row["cross_corpus_governance_request_ref"],
    )
    payload["cross_corpus_governance_request_id"] = _surface_id(
        "repo_cross_corpus_governance_request",
        REPO_CROSS_CORPUS_GOVERNANCE_REQUEST_SCHEMA,
        payload,
        "cross_corpus_governance_request_id",
    )
    return RepoCrossCorpusGovernanceRequest.model_validate(payload)


def derive_v81a_repo_cross_corpus_non_ingestion_guardrail(
    *,
    repo_root: Path | None = None,
    cross_corpus_governance_request: RepoCrossCorpusGovernanceRequest | None = None,
) -> RepoCrossCorpusNonIngestionGuardrail:
    _ = repo_root
    request = cross_corpus_governance_request or derive_v81a_repo_cross_corpus_governance_request()
    grouped_rows: dict[str, dict[str, object]] = {}
    for request_row in request.request_rows:
        for guardrail_ref in request_row.guardrail_refs:
            existing = grouped_rows.setdefault(
                guardrail_ref,
                {
                    "guardrail_ref": guardrail_ref,
                    "candidate_ref": request_row.candidate_ref,
                    "source_refs": [],
                    "cross_corpus_governance_request_refs": [],
                    "forbidden_data_actions": sorted(_FORBIDDEN_DATA_ACTIONS),
                    "forbidden_connector_actions": sorted(_FORBIDDEN_CONNECTOR_ACTIONS),
                    "forbidden_downstream_authority": sorted(_FORBIDDEN_DOWNSTREAM_AUTHORITIES),
                    "required_later_authority_refs": [],
                    "non_ingestion_posture": "non_ingestion_guardrail_active",
                    "non_connector_posture": "non_connector_guardrail_active",
                    "limitation_note": (
                        "This V81-A row is review only: no corpus ingestion, "
                        "no connector activation, no endpoint access, "
                        "no cross-corpus adjudication, no product authorization, "
                        "and no release."
                    ),
                },
            )
            if existing["candidate_ref"] != request_row.candidate_ref:
                raise ValueError("cross-corpus guardrail cannot merge candidates")
            existing["cross_corpus_governance_request_refs"] = sorted(
                {
                    *existing["cross_corpus_governance_request_refs"],
                    request_row.cross_corpus_governance_request_ref,
                }
            )
            existing["source_refs"] = sorted({*existing["source_refs"], *request_row.source_refs})
            if "product" in request_row.candidate_ref:
                existing["required_later_authority_refs"] = sorted(
                    {
                        *existing["required_later_authority_refs"],
                        "authority:v78a:product-wedge:product-review",
                    }
                )
            if request_row.corpus_review_posture in {
                "blocked_by_missing_corpus_source",
                "request_recorded_absence_only",
            }:
                existing["required_later_authority_refs"] = sorted(
                    {
                        *existing["required_later_authority_refs"],
                        "corpus-source:cross-corpus:current:absent",
                    }
                )
    payload = {
        "schema": REPO_CROSS_CORPUS_NON_INGESTION_GUARDRAIL_SCHEMA,
        "cross_corpus_non_ingestion_guardrail_id": "",
        "cross_corpus_governance_request_id": request.cross_corpus_governance_request_id,
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "guardrail_rows": sorted(grouped_rows.values(), key=lambda row: row["guardrail_ref"]),
        "non_ingestion_summary": (
            "Cross-corpus non-ingestion guardrails preserve review only: "
            "no corpus ingestion, no connector activation, no endpoint access, "
            "and no release."
        ),
    }
    payload["cross_corpus_non_ingestion_guardrail_id"] = _surface_id(
        "repo_cross_corpus_non_ingestion_guardrail",
        REPO_CROSS_CORPUS_NON_INGESTION_GUARDRAIL_SCHEMA,
        payload,
        "cross_corpus_non_ingestion_guardrail_id",
    )
    return RepoCrossCorpusNonIngestionGuardrail.model_validate(payload)


def validate_v81a_cross_corpus_governance_bundle(
    *,
    cross_corpus_source_index: RepoCrossCorpusSourceIndex,
    cross_corpus_governance_request: RepoCrossCorpusGovernanceRequest,
    cross_corpus_non_ingestion_guardrail: RepoCrossCorpusNonIngestionGuardrail,
) -> None:
    if (
        cross_corpus_governance_request.cross_corpus_source_index_id
        != cross_corpus_source_index.cross_corpus_source_index_id
    ):
        raise ValueError("cross-corpus request must reference the source index")
    if (
        cross_corpus_governance_request.review_id,
        cross_corpus_governance_request.snapshot_id,
        cross_corpus_governance_request.source_set_id,
    ) != (
        cross_corpus_source_index.review_id,
        cross_corpus_source_index.snapshot_id,
        cross_corpus_source_index.source_set_id,
    ):
        raise ValueError("cross-corpus request provenance must match source index")
    if (
        cross_corpus_non_ingestion_guardrail.cross_corpus_governance_request_id
        != cross_corpus_governance_request.cross_corpus_governance_request_id
    ):
        raise ValueError("cross-corpus guardrail must reference the request surface")

    source_roles = {
        row.source_ref: row.cross_corpus_source_role
        for row in cross_corpus_source_index.source_rows
    }
    known_sources = set(source_roles)
    request_rows = {
        row.cross_corpus_governance_request_ref: row
        for row in cross_corpus_governance_request.request_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row for row in cross_corpus_non_ingestion_guardrail.guardrail_rows
    }
    for request_row in cross_corpus_governance_request.request_rows:
        if any(source_ref not in known_sources for source_ref in request_row.source_refs):
            raise ValueError("cross-corpus request source refs must be known")
        roles = {source_roles[source_ref] for source_ref in request_row.source_refs}
        if request_row.corpus_review_posture == "eligible_for_cross_corpus_governance_review":
            if not roles.intersection(_V80_ELIGIBILITY_SOURCE_ROLES):
                raise ValueError("eligible cross-corpus requests require released V80-C sources")
            if not roles.intersection(_CONCRETE_CORPUS_SOURCE_ROLES):
                raise ValueError("eligible cross-corpus requests require concrete corpus source")
            if request_row.corpus_source_currentness != "current_concrete_source":
                raise ValueError("eligible cross-corpus requests require current corpus source")
            if roles.issubset(_CONTEXT_SOURCE_ROLES):
                raise ValueError("context-only sources cannot create cross-corpus eligibility")
        if not roles.intersection(_CONCRETE_CORPUS_SOURCE_ROLES) and roles.intersection(
            _ABSENCE_SOURCE_ROLES
        ):
            if request_row.corpus_review_posture not in {
                "request_recorded_absence_only",
                "blocked_by_missing_corpus_source",
                "blocked_by_product_authority_gap",
                "future_family_only",
                "rejected_out_of_scope",
            }:
                raise ValueError("absence-only sources cannot create cross-corpus readiness")
        if request_row.v80_summary_refs and "v80_summary_source" not in roles:
            raise ValueError("V80-C summary refs require a V80 summary source")
        if request_row.v80_handoff_refs and "v80_handoff_source" not in roles:
            raise ValueError("V80-C handoff refs require a V80 handoff source")
        if request_row.v80_closeout_refs and "v80_closeout_source" not in roles:
            raise ValueError("V80-C closeout refs require a V80 closeout source")
        if any(guardrail_ref not in guardrail_rows for guardrail_ref in request_row.guardrail_refs):
            raise ValueError("cross-corpus request guardrail refs must be known")
        for guardrail_ref in request_row.guardrail_refs:
            guardrail_row = guardrail_rows[guardrail_ref]
            if guardrail_row.candidate_ref != request_row.candidate_ref:
                raise ValueError("cross-corpus guardrails must match candidate")
            if (
                request_row.cross_corpus_governance_request_ref
                not in guardrail_row.cross_corpus_governance_request_refs
            ):
                raise ValueError("cross-corpus guardrails must reference request rows")
    for guardrail_row in cross_corpus_non_ingestion_guardrail.guardrail_rows:
        if any(source_ref not in known_sources for source_ref in guardrail_row.source_refs):
            raise ValueError("cross-corpus guardrail source refs must be known")
        if any(
            ref not in request_rows for ref in guardrail_row.cross_corpus_governance_request_refs
        ):
            raise ValueError("guardrail cross-corpus request refs must be known")
        for ref in guardrail_row.cross_corpus_governance_request_refs:
            if request_rows[ref].candidate_ref != guardrail_row.candidate_ref:
                raise ValueError("guardrail request refs must match candidate")


def derive_v81a_cross_corpus_governance_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoCrossCorpusSourceIndex,
    RepoCrossCorpusGovernanceRequest,
    RepoCrossCorpusNonIngestionGuardrail,
]:
    source_index = derive_v81a_repo_cross_corpus_source_index(repo_root=repo_root)
    request = derive_v81a_repo_cross_corpus_governance_request(
        repo_root=repo_root,
        cross_corpus_source_index=source_index,
    )
    guardrail = derive_v81a_repo_cross_corpus_non_ingestion_guardrail(
        repo_root=repo_root,
        cross_corpus_governance_request=request,
    )
    validate_v81a_cross_corpus_governance_bundle(
        cross_corpus_source_index=source_index,
        cross_corpus_governance_request=request,
        cross_corpus_non_ingestion_guardrail=guardrail,
    )
    return source_index, request, guardrail
