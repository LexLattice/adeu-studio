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
REPO_CORPUS_BOUNDARY_CONTRACT_SCHEMA = "repo_corpus_boundary_contract@1"
REPO_IMPORTED_SUBSTRATE_PROVENANCE_REGISTER_SCHEMA = (
    "repo_imported_substrate_provenance_register@1"
)
REPO_CROSS_CORPUS_AUTHORITY_GAP_REGISTER_SCHEMA = (
    "repo_cross_corpus_authority_gap_register@1"
)
REPO_CROSS_CORPUS_EXCEPTION_REGISTER_SCHEMA = "repo_cross_corpus_exception_register@1"
REPO_CROSS_CORPUS_GOVERNANCE_SUMMARY_SCHEMA = "repo_cross_corpus_governance_summary@1"
REPO_POST_CROSS_CORPUS_REVIEW_HANDOFF_SCHEMA = "repo_post_cross_corpus_review_handoff@1"
REPO_CROSS_CORPUS_GOVERNANCE_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "repo_cross_corpus_governance_family_closeout_alignment@1"
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
CorpusBoundaryResolutionKind = Literal[
    "concrete_repo_file_ref",
    "concrete_external_source_ref",
    "bounded_public_corpus_descriptor",
    "bounded_customer_corpus_descriptor",
    "benchmark_result_descriptor",
    "paper_design_repo_bundle_descriptor",
    "synthetic_corpus_descriptor",
    "no_corpus_boundary",
]
AllowedCorpusReviewAction = Literal[
    "describe_corpus_boundary",
    "inspect_source_metadata",
    "record_absence_posture",
    "request_later_privacy_review",
    "request_later_license_review",
    "request_later_connector_review",
    "preserve_corpus_gap",
]
PrivacyClearancePosture = Literal[
    "clearance_not_present",
    "clearance_requires_later_authority",
    "clearance_not_applicable",
    "clearance_explicitly_absent",
]
LicenseOrConsentPosture = Literal[
    "license_not_present",
    "license_requires_later_authority",
    "consent_requires_later_authority",
    "not_applicable",
    "explicitly_absent",
]
CustomerDataHandlingPosture = Literal[
    "no_customer_data_handling_performed_by_v81",
    "customer_data_handling_requires_later_authority",
    "customer_data_handling_forbidden_by_this_family",
]
DataHandlingPosture = Literal[
    "no_data_handling_performed_by_v81",
    "data_handling_requires_later_authority",
    "data_handling_forbidden_by_this_family",
]
CorpusTransferPosture = Literal[
    "no_corpus_transfer_performed_by_v81",
    "corpus_transfer_requires_later_authority",
    "corpus_transfer_forbidden_by_this_family",
]
SubstrateKind = Literal[
    "repo_local_descriptor",
    "imported_corpus_descriptor",
    "benchmark_result_descriptor",
    "customer_corpus_descriptor",
    "paper_design_repo_bundle_descriptor",
    "synthetic_corpus_descriptor",
    "source_absence_marker",
]
CapturePosture = Literal[
    "descriptor_recorded_only",
    "source_metadata_recorded_only",
    "provenance_requires_later_review",
    "corpus_content_not_captured",
    "capture_not_applicable",
]
ProvenanceStatus = Literal[
    "source_present_unverified_truth",
    "source_absent",
    "source_stale_or_incomplete",
    "provenance_requires_later_review",
    "not_applicable",
]
TruthStatusForbidden = Literal[
    "corpus_truth_not_claimed",
    "truth_requires_later_review",
    "truth_forbidden_by_this_family",
]
BenchmarkTruthPosture = Literal[
    "benchmark_truth_not_claimed",
    "benchmark_truth_requires_later_review",
    "benchmark_truth_forbidden_by_this_family",
]
CrossCorpusAuthorityKind = Literal[
    "maintainer_authority",
    "privacy_authority",
    "license_or_consent_authority",
    "customer_data_authority",
    "connector_authority",
    "benchmark_result_authority",
    "product_authorization",
    "external_branch_activation",
    "release_authority",
    "recursive_policy_authority",
]
CrossCorpusAuthorityGapPosture = Literal[
    "authority_missing",
    "authority_requires_later_review",
    "authority_not_applicable",
    "authority_future_family_only",
    "authority_rejected_out_of_scope",
]
CrossCorpusRequiredBeforeSurface = Literal[
    "v81c_cross_corpus_governance_summary",
    "future_corpus_ingestion_review",
    "future_connector_authority_review",
    "future_cross_corpus_adjudication_review",
    "future_product_review",
    "future_external_branch_review",
    "future_release_review",
    "future_family_review",
    "none",
]
CrossCorpusExceptionKind = Literal[
    "missing_corpus_source",
    "stale_or_historical_corpus_source",
    "missing_corpus_boundary",
    "missing_imported_provenance",
    "privacy_authority_gap",
    "license_or_consent_gap",
    "customer_data_authority_gap",
    "connector_authority_gap",
    "benchmark_truth_guardrail_gap",
    "product_authority_gap",
    "external_branch_authority_gap",
    "release_authority_gap",
    "unknown_needs_review",
]
CrossCorpusBlockingPosture = Literal[
    "blocking",
    "warning_only",
    "carried_forward",
    "not_applicable",
    "future_family_only",
]
CrossCorpusVisibilityPosture = Literal[
    "visible_to_later_review",
    "visible_warning_only",
    "visible_blocking",
    "not_applicable",
]
CrossCorpusRequiredNextSurface = Literal[
    "v81c_cross_corpus_governance_summary",
    "future_corpus_ingestion_review",
    "future_connector_authority_review",
    "future_cross_corpus_adjudication_review",
    "future_product_review",
    "future_external_branch_review",
    "future_release_review",
    "future_family_review",
    "none",
]
CrossCorpusSummaryPosture = Literal[
    "cross_corpus_review_ready_with_no_blockers",
    "cross_corpus_review_ready_with_nonblocking_warnings",
    "blocked_by_missing_corpus_source",
    "blocked_by_missing_boundary",
    "blocked_by_missing_provenance",
    "blocked_by_missing_authority",
    "blocked_by_missing_privacy_authority",
    "blocked_by_missing_license_or_consent",
    "blocked_by_missing_customer_data_authority",
    "blocked_by_missing_connector_authority",
    "blocked_by_product_authority_gap",
    "blocked_by_external_branch_authority_gap",
    "future_family_only",
    "rejected_out_of_scope",
]
CrossCorpusReadyBasisPosture = Literal[
    "ready_no_blockers",
    "ready_with_nonblocking_warnings",
    "not_ready_blockers_remain",
    "authority_review_requested_for_blockers",
    "future_family_only",
    "rejected_out_of_scope",
]
ProductAuthorizationPosture = Literal[
    "no_product_authorization_performed_by_v81",
    "product_authorization_requires_later_family",
    "product_authorization_forbidden_by_this_family",
]
ReleaseAuthorityPosture = Literal[
    "no_release_authority_performed_by_v81",
    "release_authority_requires_later_family",
    "release_authority_forbidden_by_this_family",
]
PostCrossCorpusReviewHandoffTarget = Literal[
    "future_corpus_ingestion_review",
    "future_connector_authority_review",
    "future_cross_corpus_adjudication_review",
    "future_product_review",
    "future_external_branch_review",
    "future_benchmark_review",
    "future_graph_memory_review",
    "future_family_review",
    "deferred_no_selection",
]
PostCrossCorpusReviewHandoffSubjectHorizon = Literal[
    "corpus_boundary_review_package",
    "imported_substrate_provenance_review",
    "privacy_or_license_authority_gap",
    "connector_authority_gap",
    "benchmark_result_review",
    "product_authority_gap",
    "external_branch_authority_gap",
    "graph_memory_pressure",
]
PostCrossCorpusReviewHandoffAuthorityHorizon = Literal[
    "corpus_ingestion_authority_review",
    "connector_authority_review",
    "cross_corpus_adjudication_review",
    "benchmark_truth_guardrail_review",
    "product_authority_review",
    "external_branch_authority_review",
    "graph_memory_review",
]
PostCrossCorpusReviewHandoffPosture = Literal[
    "ready_for_later_review",
    "ready_with_nonblocking_warnings",
    "blocked_by_carried_exceptions",
    "authority_review_requested_for_blockers",
    "future_family_only",
    "rejected_out_of_scope",
    "deferred_no_selection",
]
CrossCorpusClosedSlice = Literal["V81-A", "V81-B", "V81-C"]
CrossCorpusConsumedFamily = Literal[
    "V68",
    "V69",
    "V70",
    "V71",
    "V72",
    "V73",
    "V74",
    "V75",
    "V76",
    "V77",
    "V78",
    "V79",
    "V80",
    "V81",
]
CrossCorpusShippedRecordShape = Literal[
    "repo_cross_corpus_governance_request@1",
    "repo_cross_corpus_source_index@1",
    "repo_cross_corpus_non_ingestion_guardrail@1",
    "repo_corpus_boundary_contract@1",
    "repo_imported_substrate_provenance_register@1",
    "repo_cross_corpus_authority_gap_register@1",
    "repo_cross_corpus_exception_register@1",
    "repo_cross_corpus_governance_summary@1",
    "repo_post_cross_corpus_review_handoff@1",
    "repo_cross_corpus_governance_family_closeout_alignment@1",
]
CrossCorpusUnselectedFutureSurface = Literal[
    "corpus_ingestion",
    "customer_data_handling",
    "connector_activation",
    "endpoint_access",
    "cross_corpus_adjudication_execution",
    "product_authorization",
    "release",
    "benchmark_truth",
    "imported_result_truth",
    "global_model_selection",
    "living_memory_authority",
    "recursive_policy_amendment",
    "v82_selection",
]

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
_CUSTOMER_BOUNDARY_RESOLUTION_KINDS = {"bounded_customer_corpus_descriptor"}
_NON_PUBLIC_BOUNDARY_RESOLUTION_KINDS = {
    "bounded_customer_corpus_descriptor",
    "concrete_external_source_ref",
}
_PRODUCT_EXTERNAL_AUTHORITY_KINDS = {
    "product_authorization",
    "external_branch_activation",
    "release_authority",
}
_SUMMARY_READY_POSTURES = {
    "cross_corpus_review_ready_with_no_blockers",
    "cross_corpus_review_ready_with_nonblocking_warnings",
}
_SUMMARY_BLOCKED_POSTURES = {
    "blocked_by_missing_corpus_source",
    "blocked_by_missing_boundary",
    "blocked_by_missing_provenance",
    "blocked_by_missing_authority",
    "blocked_by_missing_privacy_authority",
    "blocked_by_missing_license_or_consent",
    "blocked_by_missing_customer_data_authority",
    "blocked_by_missing_connector_authority",
    "blocked_by_product_authority_gap",
    "blocked_by_external_branch_authority_gap",
}
_HANDOFF_TARGET_AUTHORITY_TERMS = {
    "future_corpus_ingestion_review": ("privacy", "license"),
    "future_connector_authority_review": ("connector",),
    "future_cross_corpus_adjudication_review": ("benchmark",),
    "future_product_review": ("product",),
    "future_external_branch_review": ("external",),
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
        r"corpus truth",
        r"benchmark truth",
        r"imported result truth",
        r"graph[- ]memory (?:is |was |has been |gets |got )?created",
        r"graph[- ]memory authority (?:is |was |has been |gets |got )?(?:created|granted)",
        r"living[- ]memory authority (?:is |was |has been |gets |got )?(?:created|granted)",
        r"authority (?:is |was |has been |gets |got )?granted",
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


class RepoCorpusBoundaryContractRow(_CartographyBase):
    boundary_contract_ref: str
    candidate_ref: str
    request_refs: list[str] = Field(min_length=1)
    source_refs: list[str] = Field(min_length=1)
    guardrail_refs: list[str] = Field(min_length=1)
    corpus_horizon_kind: CorpusHorizonKind
    corpus_scope_refs: list[str] = Field(default_factory=list)
    boundary_resolution_kind: CorpusBoundaryResolutionKind
    allowed_corpus_review_actions: list[AllowedCorpusReviewAction] = Field(min_length=1)
    forbidden_corpus_actions: list[ForbiddenCorpusDataAction] = Field(min_length=1)
    privacy_clearance_posture: PrivacyClearancePosture
    license_or_consent_posture: LicenseOrConsentPosture
    customer_data_handling_posture: CustomerDataHandlingPosture
    data_handling_posture: DataHandlingPosture
    corpus_transfer_posture: CorpusTransferPosture
    connector_activation_posture: ConnectorActivationPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_corpus_boundary_contract_row(self) -> RepoCorpusBoundaryContractRow:
        _non_empty(self.boundary_contract_ref, field_name="boundary_contract_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "request_refs",
            "source_refs",
            "guardrail_refs",
            "corpus_scope_refs",
            "allowed_corpus_review_actions",
            "forbidden_corpus_actions",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        for scope_ref in self.corpus_scope_refs:
            _non_empty(scope_ref, field_name="corpus_scope_refs")
        missing = _FORBIDDEN_DATA_ACTIONS.difference(self.forbidden_corpus_actions)
        if missing:
            raise ValueError("corpus boundary contract omits forbidden corpus actions")
        if self.data_handling_posture != "no_data_handling_performed_by_v81":
            raise ValueError("V81-B boundary contracts must not handle corpus data")
        if self.corpus_transfer_posture != "no_corpus_transfer_performed_by_v81":
            raise ValueError("V81-B boundary contracts must not transfer corpus data")
        if self.connector_activation_posture != "no_connector_activation_performed_by_v81":
            raise ValueError("V81-B boundary contracts must not activate connectors")
        if (
            self.boundary_resolution_kind != "no_corpus_boundary"
            and not self.corpus_scope_refs
        ):
            raise ValueError("corpus boundary contracts require source-bound scope refs")
        if self.boundary_resolution_kind in _NON_PUBLIC_BOUNDARY_RESOLUTION_KINDS:
            if self.privacy_clearance_posture == "clearance_not_applicable":
                raise ValueError("non-public corpus boundaries require privacy posture")
            if self.license_or_consent_posture == "not_applicable":
                raise ValueError("non-public corpus boundaries require license or consent posture")
        if self.boundary_resolution_kind in _CUSTOMER_BOUNDARY_RESOLUTION_KINDS:
            if (
                self.customer_data_handling_posture
                == "no_customer_data_handling_performed_by_v81"
            ):
                raise ValueError("customer corpus boundaries require customer-data blocker")
        _reject_v81_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("review only", "no corpus ingestion", "no connector activation"),
        )
        return self


class RepoCorpusBoundaryContract(_CartographyBase):
    schema: Literal["repo_corpus_boundary_contract@1"] = REPO_CORPUS_BOUNDARY_CONTRACT_SCHEMA
    corpus_boundary_contract_id: str
    cross_corpus_governance_request_id: str
    cross_corpus_source_index_id: str
    cross_corpus_non_ingestion_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    boundary_contract_rows: list[RepoCorpusBoundaryContractRow] = Field(min_length=1)
    boundary_contract_summary: str

    @model_validator(mode="after")
    def _validate_corpus_boundary_contract(self) -> RepoCorpusBoundaryContract:
        object.__setattr__(
            self,
            "boundary_contract_rows",
            _sorted_unique_by_ref(
                self.boundary_contract_rows,
                attr="boundary_contract_ref",
                field_name="boundary_contract_rows",
            ),
        )
        _require_terms(
            self.boundary_contract_summary,
            field_name="boundary_contract_summary",
            terms=("review only", "no corpus ingestion", "no connector activation"),
        )
        expected_id = _surface_id(
            "repo_corpus_boundary_contract",
            self.schema,
            self.model_dump(mode="json"),
            "corpus_boundary_contract_id",
        )
        if self.corpus_boundary_contract_id != expected_id:
            raise ValueError("corpus_boundary_contract_id does not match canonical hash")
        return self


class RepoImportedSubstrateProvenanceRow(_CartographyBase):
    provenance_ref: str
    candidate_ref: str
    request_refs: list[str] = Field(min_length=1)
    source_refs: list[str] = Field(min_length=1)
    boundary_contract_refs: list[str] = Field(min_length=1)
    substrate_kind: SubstrateKind
    capture_posture: CapturePosture
    provenance_status: ProvenanceStatus
    truth_status_forbidden: TruthStatusForbidden
    benchmark_truth_posture: BenchmarkTruthPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_imported_substrate_provenance_row(
        self,
    ) -> RepoImportedSubstrateProvenanceRow:
        _non_empty(self.provenance_ref, field_name="provenance_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in ("request_refs", "source_refs", "boundary_contract_refs"):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        if self.capture_posture not in {
            "descriptor_recorded_only",
            "source_metadata_recorded_only",
            "provenance_requires_later_review",
            "corpus_content_not_captured",
            "capture_not_applicable",
        }:
            raise ValueError("provenance capture posture must not capture corpus content")
        if self.truth_status_forbidden != "corpus_truth_not_claimed":
            raise ValueError("V81-B provenance rows must not claim corpus truth")
        if self.benchmark_truth_posture != "benchmark_truth_not_claimed":
            raise ValueError("V81-B provenance rows must not claim benchmark truth")
        _reject_v81_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("review only", "no corpus truth", "no benchmark truth"),
        )
        return self


class RepoImportedSubstrateProvenanceRegister(_CartographyBase):
    schema: Literal["repo_imported_substrate_provenance_register@1"] = (
        REPO_IMPORTED_SUBSTRATE_PROVENANCE_REGISTER_SCHEMA
    )
    imported_substrate_provenance_register_id: str
    cross_corpus_governance_request_id: str
    cross_corpus_source_index_id: str
    cross_corpus_non_ingestion_guardrail_id: str
    corpus_boundary_contract_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    provenance_rows: list[RepoImportedSubstrateProvenanceRow] = Field(min_length=1)
    provenance_summary: str

    @model_validator(mode="after")
    def _validate_imported_substrate_provenance_register(
        self,
    ) -> RepoImportedSubstrateProvenanceRegister:
        object.__setattr__(
            self,
            "provenance_rows",
            _sorted_unique_by_ref(
                self.provenance_rows,
                attr="provenance_ref",
                field_name="provenance_rows",
            ),
        )
        _require_terms(
            self.provenance_summary,
            field_name="provenance_summary",
            terms=("review only", "no corpus truth", "no benchmark truth"),
        )
        expected_id = _surface_id(
            "repo_imported_substrate_provenance_register",
            self.schema,
            self.model_dump(mode="json"),
            "imported_substrate_provenance_register_id",
        )
        if self.imported_substrate_provenance_register_id != expected_id:
            raise ValueError(
                "imported_substrate_provenance_register_id does not match canonical hash"
            )
        return self


class RepoCrossCorpusAuthorityGapRow(_CartographyBase):
    authority_gap_ref: str
    candidate_ref: str
    request_refs: list[str] = Field(min_length=1)
    source_refs: list[str] = Field(min_length=1)
    boundary_contract_refs: list[str] = Field(default_factory=list)
    provenance_refs: list[str] = Field(default_factory=list)
    authority_kind: CrossCorpusAuthorityKind
    authority_gap_posture: CrossCorpusAuthorityGapPosture
    required_before_surface: CrossCorpusRequiredBeforeSurface
    source_presence_posture: CandidateSourcePresencePosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_cross_corpus_authority_gap_row(self) -> RepoCrossCorpusAuthorityGapRow:
        _non_empty(self.authority_gap_ref, field_name="authority_gap_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "request_refs",
            "source_refs",
            "boundary_contract_refs",
            "provenance_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        if (
            self.authority_kind in _PRODUCT_EXTERNAL_AUTHORITY_KINDS
            and self.authority_gap_posture
            not in {
                "authority_missing",
                "authority_requires_later_review",
                "authority_future_family_only",
            }
        ):
            raise ValueError("product/external/release authority gaps must remain blocked")
        _reject_v81_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("review only", "authority gap", "no authority granted"),
        )
        return self


class RepoCrossCorpusAuthorityGapRegister(_CartographyBase):
    schema: Literal["repo_cross_corpus_authority_gap_register@1"] = (
        REPO_CROSS_CORPUS_AUTHORITY_GAP_REGISTER_SCHEMA
    )
    cross_corpus_authority_gap_register_id: str
    cross_corpus_governance_request_id: str
    cross_corpus_source_index_id: str
    cross_corpus_non_ingestion_guardrail_id: str
    corpus_boundary_contract_id: str
    imported_substrate_provenance_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    authority_gap_rows: list[RepoCrossCorpusAuthorityGapRow] = Field(min_length=1)
    authority_gap_summary: str

    @model_validator(mode="after")
    def _validate_cross_corpus_authority_gap_register(
        self,
    ) -> RepoCrossCorpusAuthorityGapRegister:
        object.__setattr__(
            self,
            "authority_gap_rows",
            _sorted_unique_by_ref(
                self.authority_gap_rows,
                attr="authority_gap_ref",
                field_name="authority_gap_rows",
            ),
        )
        _require_terms(
            self.authority_gap_summary,
            field_name="authority_gap_summary",
            terms=("review only", "authority gap", "no authority granted"),
        )
        expected_id = _surface_id(
            "repo_cross_corpus_authority_gap_register",
            self.schema,
            self.model_dump(mode="json"),
            "cross_corpus_authority_gap_register_id",
        )
        if self.cross_corpus_authority_gap_register_id != expected_id:
            raise ValueError(
                "cross_corpus_authority_gap_register_id does not match canonical hash"
            )
        return self


class RepoCrossCorpusExceptionRow(_CartographyBase):
    exception_ref: str
    candidate_ref: str
    request_refs: list[str] = Field(min_length=1)
    boundary_contract_refs: list[str] = Field(default_factory=list)
    provenance_refs: list[str] = Field(default_factory=list)
    authority_gap_refs: list[str] = Field(default_factory=list)
    exception_kind: CrossCorpusExceptionKind
    blocking_posture: CrossCorpusBlockingPosture
    visibility_posture: CrossCorpusVisibilityPosture
    required_next_surface: CrossCorpusRequiredNextSurface
    limitation_note: str

    @model_validator(mode="after")
    def _validate_cross_corpus_exception_row(self) -> RepoCrossCorpusExceptionRow:
        _non_empty(self.exception_ref, field_name="exception_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "request_refs",
            "boundary_contract_refs",
            "provenance_refs",
            "authority_gap_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if self.blocking_posture == "blocking" and not (
            self.boundary_contract_refs or self.provenance_refs or self.authority_gap_refs
        ):
            raise ValueError("blocking cross-corpus exceptions require blocker refs")
        lowered_note = self.limitation_note.lower()
        if "resolved by prose" in lowered_note or "prose resolved" in lowered_note:
            raise ValueError("cross-corpus exceptions cannot be resolved by prose")
        if self.exception_kind in {
            "product_authority_gap",
            "external_branch_authority_gap",
            "release_authority_gap",
        }:
            if self.blocking_posture not in {"blocking", "future_family_only"}:
                raise ValueError("product/external/release exceptions must remain blocked")
        _reject_v81_action_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoCrossCorpusExceptionRegister(_CartographyBase):
    schema: Literal["repo_cross_corpus_exception_register@1"] = (
        REPO_CROSS_CORPUS_EXCEPTION_REGISTER_SCHEMA
    )
    cross_corpus_exception_register_id: str
    cross_corpus_governance_request_id: str
    cross_corpus_source_index_id: str
    cross_corpus_non_ingestion_guardrail_id: str
    corpus_boundary_contract_id: str
    imported_substrate_provenance_register_id: str
    cross_corpus_authority_gap_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    exception_rows: list[RepoCrossCorpusExceptionRow] = Field(min_length=1)
    exception_summary: str

    @model_validator(mode="after")
    def _validate_cross_corpus_exception_register(self) -> RepoCrossCorpusExceptionRegister:
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
            terms=("review only", "blocking", "no corpus ingestion"),
        )
        expected_id = _surface_id(
            "repo_cross_corpus_exception_register",
            self.schema,
            self.model_dump(mode="json"),
            "cross_corpus_exception_register_id",
        )
        if self.cross_corpus_exception_register_id != expected_id:
            raise ValueError("cross_corpus_exception_register_id does not match canonical hash")
        return self


class RepoCrossCorpusGovernanceSummaryRow(_CartographyBase):
    cross_corpus_summary_ref: str
    candidate_ref: str
    request_refs: list[str] = Field(min_length=1)
    boundary_contract_refs: list[str] = Field(default_factory=list)
    provenance_refs: list[str] = Field(default_factory=list)
    authority_gap_refs: list[str] = Field(default_factory=list)
    exception_refs: list[str] = Field(default_factory=list)
    carried_blocker_refs: list[str] = Field(default_factory=list)
    carried_warning_refs: list[str] = Field(default_factory=list)
    summary_posture: CrossCorpusSummaryPosture
    ready_basis_posture: CrossCorpusReadyBasisPosture
    corpus_ingestion_posture: CorpusIngestionPosture
    connector_activation_posture: ConnectorActivationPosture
    endpoint_access_posture: ExternalEndpointAccessPosture
    adjudication_execution_posture: AdjudicationExecutionPosture
    product_authorization_posture: ProductAuthorizationPosture
    release_authority_posture: ReleaseAuthorityPosture
    guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_cross_corpus_governance_summary_row(
        self,
    ) -> RepoCrossCorpusGovernanceSummaryRow:
        _non_empty(self.cross_corpus_summary_ref, field_name="cross_corpus_summary_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "request_refs",
            "boundary_contract_refs",
            "provenance_refs",
            "authority_gap_refs",
            "exception_refs",
            "carried_blocker_refs",
            "carried_warning_refs",
            "guardrail_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if self.corpus_ingestion_posture != "no_corpus_ingestion_performed_by_v81":
            raise ValueError("V81-C summaries must not ingest corpora")
        if self.connector_activation_posture != "no_connector_activation_performed_by_v81":
            raise ValueError("V81-C summaries must not activate connectors")
        if self.endpoint_access_posture != "no_endpoint_access_performed_by_v81":
            raise ValueError("V81-C summaries must not access endpoints")
        if (
            self.adjudication_execution_posture
            != "no_cross_corpus_adjudication_performed_by_v81"
        ):
            raise ValueError("V81-C summaries must not execute cross-corpus adjudication")
        if self.product_authorization_posture != "no_product_authorization_performed_by_v81":
            raise ValueError("V81-C summaries must not authorize products")
        if self.release_authority_posture != "no_release_authority_performed_by_v81":
            raise ValueError("V81-C summaries must not grant release authority")
        if self.summary_posture == "cross_corpus_review_ready_with_no_blockers":
            if self.ready_basis_posture != "ready_no_blockers":
                raise ValueError("ready cross-corpus summaries require ready_no_blockers")
            if self.exception_refs or self.carried_blocker_refs or self.carried_warning_refs:
                raise ValueError("ready cross-corpus summaries cannot carry exceptions")
        if self.summary_posture == "cross_corpus_review_ready_with_nonblocking_warnings":
            if self.ready_basis_posture != "ready_with_nonblocking_warnings":
                raise ValueError("warning-ready cross-corpus summaries require warning basis")
            if self.carried_blocker_refs:
                raise ValueError("warning-ready summaries cannot carry blockers")
            if not self.carried_warning_refs:
                raise ValueError("warning-ready summaries must carry warnings")
        if self.summary_posture in _SUMMARY_READY_POSTURES:
            for field_name in (
                "boundary_contract_refs",
                "provenance_refs",
                "authority_gap_refs",
            ):
                if not getattr(self, field_name):
                    raise ValueError("ready cross-corpus summaries require released refs")
        if self.summary_posture in _SUMMARY_BLOCKED_POSTURES:
            if self.ready_basis_posture not in {
                "not_ready_blockers_remain",
                "authority_review_requested_for_blockers",
            }:
                raise ValueError("blocked cross-corpus summaries must preserve blocker basis")
            if not self.carried_blocker_refs:
                raise ValueError("blocked cross-corpus summaries must carry blockers")
        if self.summary_posture == "future_family_only" and (
            self.ready_basis_posture != "future_family_only"
        ):
            raise ValueError("future-family cross-corpus summaries require future basis")
        if self.summary_posture == "rejected_out_of_scope" and (
            self.ready_basis_posture != "rejected_out_of_scope"
        ):
            raise ValueError("rejected cross-corpus summaries require rejected basis")
        if self.summary_posture == "blocked_by_product_authority_gap" and not any(
            "product" in ref for ref in self.authority_gap_refs
        ):
            raise ValueError("product-blocked summaries require product authority gap refs")
        _reject_v81_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("review", "no corpus ingestion", "no connector activation"),
        )
        return self


class RepoCrossCorpusGovernanceSummary(_CartographyBase):
    schema: Literal["repo_cross_corpus_governance_summary@1"] = (
        REPO_CROSS_CORPUS_GOVERNANCE_SUMMARY_SCHEMA
    )
    cross_corpus_governance_summary_id: str
    cross_corpus_governance_request_id: str
    cross_corpus_source_index_id: str
    cross_corpus_non_ingestion_guardrail_id: str
    corpus_boundary_contract_id: str
    imported_substrate_provenance_register_id: str
    cross_corpus_authority_gap_register_id: str
    cross_corpus_exception_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    summary_rows: list[RepoCrossCorpusGovernanceSummaryRow] = Field(min_length=1)
    governance_summary: str

    @model_validator(mode="after")
    def _validate_cross_corpus_governance_summary(
        self,
    ) -> RepoCrossCorpusGovernanceSummary:
        object.__setattr__(
            self,
            "summary_rows",
            _sorted_unique_by_ref(
                self.summary_rows,
                attr="cross_corpus_summary_ref",
                field_name="summary_rows",
            ),
        )
        _require_terms(
            self.governance_summary,
            field_name="governance_summary",
            terms=("review", "no corpus ingestion", "no connector activation", "no release"),
        )
        expected_id = _surface_id(
            "repo_cross_corpus_governance_summary",
            self.schema,
            self.model_dump(mode="json"),
            "cross_corpus_governance_summary_id",
        )
        if self.cross_corpus_governance_summary_id != expected_id:
            raise ValueError("cross_corpus_governance_summary_id does not match canonical hash")
        return self


class RepoPostCrossCorpusReviewHandoffRow(_CartographyBase):
    handoff_ref: str
    candidate_ref: str
    summary_refs: list[str] = Field(min_length=1)
    boundary_contract_refs: list[str] = Field(default_factory=list)
    provenance_refs: list[str] = Field(default_factory=list)
    authority_gap_refs: list[str] = Field(default_factory=list)
    carried_exception_refs: list[str] = Field(default_factory=list)
    handoff_target: PostCrossCorpusReviewHandoffTarget
    handoff_subject_horizon: PostCrossCorpusReviewHandoffSubjectHorizon
    handoff_authority_horizon: PostCrossCorpusReviewHandoffAuthorityHorizon
    handoff_posture: PostCrossCorpusReviewHandoffPosture
    required_later_authority_refs: list[str] = Field(default_factory=list)
    corpus_ingestion_posture: CorpusIngestionPosture
    connector_activation_posture: ConnectorActivationPosture
    endpoint_access_posture: ExternalEndpointAccessPosture
    adjudication_execution_posture: AdjudicationExecutionPosture
    guardrail_refs: list[str] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_post_cross_corpus_review_handoff_row(
        self,
    ) -> RepoPostCrossCorpusReviewHandoffRow:
        _non_empty(self.handoff_ref, field_name="handoff_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "summary_refs",
            "boundary_contract_refs",
            "provenance_refs",
            "authority_gap_refs",
            "carried_exception_refs",
            "required_later_authority_refs",
            "guardrail_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if self.corpus_ingestion_posture != "no_corpus_ingestion_performed_by_v81":
            raise ValueError("V81-C handoffs must not ingest corpora")
        if self.connector_activation_posture != "no_connector_activation_performed_by_v81":
            raise ValueError("V81-C handoffs must not activate connectors")
        if self.endpoint_access_posture != "no_endpoint_access_performed_by_v81":
            raise ValueError("V81-C handoffs must not access endpoints")
        if (
            self.adjudication_execution_posture
            != "no_cross_corpus_adjudication_performed_by_v81"
        ):
            raise ValueError("V81-C handoffs must not execute cross-corpus adjudication")
        if self.handoff_posture == "ready_for_later_review" and self.carried_exception_refs:
            raise ValueError("ready handoffs cannot carry exceptions")
        if self.handoff_posture == "ready_with_nonblocking_warnings":
            if not self.carried_exception_refs:
                raise ValueError("warning-ready handoffs must carry warnings")
        if (
            self.handoff_posture == "blocked_by_carried_exceptions"
            and not self.carried_exception_refs
        ):
            raise ValueError("blocked handoffs must carry exceptions")
        authority_terms = _HANDOFF_TARGET_AUTHORITY_TERMS.get(self.handoff_target, ())
        for term in authority_terms:
            if not any(term in ref for ref in self.required_later_authority_refs):
                raise ValueError(f"{term} handoffs require authority refs")
        if self.handoff_target == "future_corpus_ingestion_review":
            for field_name in ("boundary_contract_refs", "provenance_refs", "authority_gap_refs"):
                if not getattr(self, field_name):
                    raise ValueError("corpus ingestion handoffs require released refs")
        if self.handoff_target == "future_cross_corpus_adjudication_review":
            if not self.provenance_refs or not self.authority_gap_refs:
                raise ValueError("adjudication handoffs require provenance and authority refs")
        _reject_v81_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("later review", "no corpus ingestion", "no connector activation"),
        )
        return self


class RepoPostCrossCorpusReviewHandoff(_CartographyBase):
    schema: Literal["repo_post_cross_corpus_review_handoff@1"] = (
        REPO_POST_CROSS_CORPUS_REVIEW_HANDOFF_SCHEMA
    )
    post_cross_corpus_review_handoff_id: str
    cross_corpus_governance_summary_id: str
    cross_corpus_governance_request_id: str
    cross_corpus_source_index_id: str
    cross_corpus_non_ingestion_guardrail_id: str
    corpus_boundary_contract_id: str
    imported_substrate_provenance_register_id: str
    cross_corpus_authority_gap_register_id: str
    cross_corpus_exception_register_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    handoff_rows: list[RepoPostCrossCorpusReviewHandoffRow] = Field(min_length=1)
    handoff_summary: str

    @model_validator(mode="after")
    def _validate_post_cross_corpus_review_handoff(
        self,
    ) -> RepoPostCrossCorpusReviewHandoff:
        object.__setattr__(
            self,
            "handoff_rows",
            _sorted_unique_by_ref(self.handoff_rows, attr="handoff_ref", field_name="handoff_rows"),
        )
        _require_terms(
            self.handoff_summary,
            field_name="handoff_summary",
            terms=("later review", "no corpus ingestion", "no connector activation", "no release"),
        )
        expected_id = _surface_id(
            "repo_post_cross_corpus_review_handoff",
            self.schema,
            self.model_dump(mode="json"),
            "post_cross_corpus_review_handoff_id",
        )
        if self.post_cross_corpus_review_handoff_id != expected_id:
            raise ValueError("post_cross_corpus_review_handoff_id does not match canonical hash")
        return self


class RepoCrossCorpusGovernanceFamilyCloseoutAlignment(_CartographyBase):
    schema: Literal["repo_cross_corpus_governance_family_closeout_alignment@1"] = (
        REPO_CROSS_CORPUS_GOVERNANCE_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    )
    cross_corpus_governance_family_closeout_alignment_id: str
    cross_corpus_governance_summary_id: str
    post_cross_corpus_review_handoff_id: str
    family: Literal["V81"]
    closed_by_arc: Literal["vNext+229"]
    closed_slice_ladder: list[CrossCorpusClosedSlice] = Field(min_length=3)
    shipped_record_shapes: list[CrossCorpusShippedRecordShape] = Field(min_length=1)
    consumed_source_families: list[CrossCorpusConsumedFamily] = Field(min_length=1)
    family_closed_on_main: Literal["closed_after_v81c_merge"]
    future_family_authority: Literal["next_selector_required"]
    unselected_future_surfaces: list[CrossCorpusUnselectedFutureSurface] = Field(min_length=1)
    cross_corpus_boundary: str
    limitation_note: str

    @model_validator(mode="after")
    def _validate_cross_corpus_governance_family_closeout_alignment(
        self,
    ) -> RepoCrossCorpusGovernanceFamilyCloseoutAlignment:
        for field_name in (
            "closed_slice_ladder",
            "shipped_record_shapes",
            "consumed_source_families",
            "unselected_future_surfaces",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if self.closed_slice_ladder != ["V81-A", "V81-B", "V81-C"]:
            raise ValueError("cross-corpus closeout must close V81-A/B/C")
        if "v82_selection" not in self.unselected_future_surfaces:
            raise ValueError("cross-corpus closeout must not select V82")
        _require_terms(
            self.cross_corpus_boundary,
            field_name="cross_corpus_boundary",
            terms=("no corpus ingestion", "no connector activation", "no v82 selection"),
        )
        _reject_v81_action_claim(self.cross_corpus_boundary, field_name="cross_corpus_boundary")
        _reject_v81_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("closed", "no corpus ingestion", "no connector activation", "no v82 selection"),
        )
        expected_id = _surface_id(
            "repo_cross_corpus_governance_family_closeout_alignment",
            self.schema,
            self.model_dump(mode="json"),
            "cross_corpus_governance_family_closeout_alignment_id",
        )
        if self.cross_corpus_governance_family_closeout_alignment_id != expected_id:
            raise ValueError(
                "cross_corpus_governance_family_closeout_alignment_id does not match canonical hash"
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
    if (
        cross_corpus_non_ingestion_guardrail.review_id,
        cross_corpus_non_ingestion_guardrail.snapshot_id,
        cross_corpus_non_ingestion_guardrail.source_set_id,
    ) != (
        cross_corpus_governance_request.review_id,
        cross_corpus_governance_request.snapshot_id,
        cross_corpus_governance_request.source_set_id,
    ):
        raise ValueError("cross-corpus guardrail provenance must match request")

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


def _v81b_v81a_request_rows(
    request: RepoCrossCorpusGovernanceRequest,
) -> dict[str, RepoCrossCorpusGovernanceRequestRow]:
    return {
        row.cross_corpus_governance_request_ref: row for row in request.request_rows
    }


def _v81b_shared_ids(
    *,
    request: RepoCrossCorpusGovernanceRequest,
    source_index: RepoCrossCorpusSourceIndex,
    guardrail: RepoCrossCorpusNonIngestionGuardrail,
) -> dict[str, str]:
    return {
        "cross_corpus_governance_request_id": request.cross_corpus_governance_request_id,
        "cross_corpus_source_index_id": source_index.cross_corpus_source_index_id,
        "cross_corpus_non_ingestion_guardrail_id": (
            guardrail.cross_corpus_non_ingestion_guardrail_id
        ),
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
    }


def _resolve_v81b_v81a_inputs(
    *,
    repo_root: Path | None = None,
    cross_corpus_source_index: RepoCrossCorpusSourceIndex | None = None,
    cross_corpus_governance_request: RepoCrossCorpusGovernanceRequest | None = None,
    cross_corpus_non_ingestion_guardrail: RepoCrossCorpusNonIngestionGuardrail | None = None,
) -> tuple[
    RepoCrossCorpusSourceIndex,
    RepoCrossCorpusGovernanceRequest,
    RepoCrossCorpusNonIngestionGuardrail,
]:
    provided = (
        cross_corpus_source_index,
        cross_corpus_governance_request,
        cross_corpus_non_ingestion_guardrail,
    )
    if all(item is None for item in provided):
        return derive_v81a_cross_corpus_governance_bundle(repo_root=repo_root)
    if any(item is None for item in provided):
        raise ValueError("V81-B derivation requires all V81-A inputs when any are supplied")
    assert cross_corpus_source_index is not None
    assert cross_corpus_governance_request is not None
    assert cross_corpus_non_ingestion_guardrail is not None
    validate_v81a_cross_corpus_governance_bundle(
        cross_corpus_source_index=cross_corpus_source_index,
        cross_corpus_governance_request=cross_corpus_governance_request,
        cross_corpus_non_ingestion_guardrail=cross_corpus_non_ingestion_guardrail,
    )
    return (
        cross_corpus_source_index,
        cross_corpus_governance_request,
        cross_corpus_non_ingestion_guardrail,
    )


def derive_v81b_repo_corpus_boundary_contract(
    *,
    repo_root: Path | None = None,
    cross_corpus_source_index: RepoCrossCorpusSourceIndex | None = None,
    cross_corpus_governance_request: RepoCrossCorpusGovernanceRequest | None = None,
    cross_corpus_non_ingestion_guardrail: RepoCrossCorpusNonIngestionGuardrail | None = None,
) -> RepoCorpusBoundaryContract:
    source_index, request, guardrail = _resolve_v81b_v81a_inputs(
        repo_root=repo_root,
        cross_corpus_source_index=cross_corpus_source_index,
        cross_corpus_governance_request=cross_corpus_governance_request,
        cross_corpus_non_ingestion_guardrail=cross_corpus_non_ingestion_guardrail,
    )
    source_refs = [row.source_ref for row in source_index.source_rows]
    rows_by_request = _v81b_v81a_request_rows(request)
    self_request = rows_by_request[
        "cross-corpus-governance:v81a:self-evidencing:source-absent"
    ]
    product_request = rows_by_request[
        "cross-corpus-governance:v81a:product-wedge:product-blocked"
    ]
    payload = {
        "schema": REPO_CORPUS_BOUNDARY_CONTRACT_SCHEMA,
        "corpus_boundary_contract_id": "",
        **_v81b_shared_ids(request=request, source_index=source_index, guardrail=guardrail),
        "boundary_contract_rows": [
            {
                "boundary_contract_ref": (
                    "corpus-boundary:v81b:self-evidencing:source-absent"
                ),
                "candidate_ref": self_request.candidate_ref,
                "request_refs": [self_request.cross_corpus_governance_request_ref],
                "source_refs": source_refs,
                "guardrail_refs": self_request.guardrail_refs,
                "corpus_horizon_kind": self_request.corpus_horizon_kind,
                "corpus_scope_refs": [],
                "boundary_resolution_kind": "no_corpus_boundary",
                "allowed_corpus_review_actions": [
                    "preserve_corpus_gap",
                    "record_absence_posture",
                ],
                "forbidden_corpus_actions": sorted(_FORBIDDEN_DATA_ACTIONS),
                "privacy_clearance_posture": "clearance_explicitly_absent",
                "license_or_consent_posture": "explicitly_absent",
                "customer_data_handling_posture": (
                    "customer_data_handling_forbidden_by_this_family"
                ),
                "data_handling_posture": "no_data_handling_performed_by_v81",
                "corpus_transfer_posture": "no_corpus_transfer_performed_by_v81",
                "connector_activation_posture": (
                    "no_connector_activation_performed_by_v81"
                ),
                "limitation_note": (
                    "Boundary contract is review only over explicit corpus absence "
                    "with no corpus ingestion, no connector activation, and no release."
                ),
            },
            {
                "boundary_contract_ref": "corpus-boundary:v81b:product-wedge:blocked",
                "candidate_ref": product_request.candidate_ref,
                "request_refs": [product_request.cross_corpus_governance_request_ref],
                "source_refs": source_refs,
                "guardrail_refs": product_request.guardrail_refs,
                "corpus_horizon_kind": product_request.corpus_horizon_kind,
                "corpus_scope_refs": [],
                "boundary_resolution_kind": "no_corpus_boundary",
                "allowed_corpus_review_actions": ["preserve_corpus_gap"],
                "forbidden_corpus_actions": sorted(_FORBIDDEN_DATA_ACTIONS),
                "privacy_clearance_posture": "clearance_not_applicable",
                "license_or_consent_posture": "not_applicable",
                "customer_data_handling_posture": (
                    "customer_data_handling_forbidden_by_this_family"
                ),
                "data_handling_posture": "no_data_handling_performed_by_v81",
                "corpus_transfer_posture": "no_corpus_transfer_performed_by_v81",
                "connector_activation_posture": (
                    "no_connector_activation_performed_by_v81"
                ),
                "limitation_note": (
                    "Product-pressure boundary is review only and remains authority "
                    "blocked with no corpus ingestion, no connector activation, "
                    "and no release."
                ),
            },
        ],
        "boundary_contract_summary": (
            "Corpus boundary contracts are review only with no corpus ingestion, "
            "no connector activation, and no release."
        ),
    }
    payload["boundary_contract_rows"] = sorted(
        payload["boundary_contract_rows"],
        key=lambda row: row["boundary_contract_ref"],
    )
    payload["corpus_boundary_contract_id"] = _surface_id(
        "repo_corpus_boundary_contract",
        REPO_CORPUS_BOUNDARY_CONTRACT_SCHEMA,
        payload,
        "corpus_boundary_contract_id",
    )
    return RepoCorpusBoundaryContract.model_validate(payload)


def derive_v81b_repo_imported_substrate_provenance_register(
    *,
    repo_root: Path | None = None,
    cross_corpus_source_index: RepoCrossCorpusSourceIndex | None = None,
    cross_corpus_governance_request: RepoCrossCorpusGovernanceRequest | None = None,
    cross_corpus_non_ingestion_guardrail: RepoCrossCorpusNonIngestionGuardrail | None = None,
    corpus_boundary_contract: RepoCorpusBoundaryContract | None = None,
) -> RepoImportedSubstrateProvenanceRegister:
    source_index, request, guardrail = _resolve_v81b_v81a_inputs(
        repo_root=repo_root,
        cross_corpus_source_index=cross_corpus_source_index,
        cross_corpus_governance_request=cross_corpus_governance_request,
        cross_corpus_non_ingestion_guardrail=cross_corpus_non_ingestion_guardrail,
    )
    boundary = corpus_boundary_contract or derive_v81b_repo_corpus_boundary_contract(
        cross_corpus_source_index=source_index,
        cross_corpus_governance_request=request,
        cross_corpus_non_ingestion_guardrail=guardrail,
    )
    source_refs = [row.source_ref for row in source_index.source_rows]
    rows_by_request = _v81b_v81a_request_rows(request)
    self_request = rows_by_request[
        "cross-corpus-governance:v81a:self-evidencing:source-absent"
    ]
    product_request = rows_by_request[
        "cross-corpus-governance:v81a:product-wedge:product-blocked"
    ]
    payload = {
        "schema": REPO_IMPORTED_SUBSTRATE_PROVENANCE_REGISTER_SCHEMA,
        "imported_substrate_provenance_register_id": "",
        **_v81b_shared_ids(request=request, source_index=source_index, guardrail=guardrail),
        "corpus_boundary_contract_id": boundary.corpus_boundary_contract_id,
        "provenance_rows": [
            {
                "provenance_ref": "corpus-provenance:v81b:self-evidencing:source-absent",
                "candidate_ref": self_request.candidate_ref,
                "request_refs": [self_request.cross_corpus_governance_request_ref],
                "source_refs": source_refs,
                "boundary_contract_refs": [
                    "corpus-boundary:v81b:self-evidencing:source-absent"
                ],
                "substrate_kind": "source_absence_marker",
                "capture_posture": "corpus_content_not_captured",
                "provenance_status": "source_absent",
                "truth_status_forbidden": "corpus_truth_not_claimed",
                "benchmark_truth_posture": "benchmark_truth_not_claimed",
                "limitation_note": (
                    "Provenance is review only for an absence marker with no corpus "
                    "truth, no benchmark truth, and no corpus ingestion."
                ),
            },
            {
                "provenance_ref": "corpus-provenance:v81b:product-wedge:blocked",
                "candidate_ref": product_request.candidate_ref,
                "request_refs": [product_request.cross_corpus_governance_request_ref],
                "source_refs": source_refs,
                "boundary_contract_refs": ["corpus-boundary:v81b:product-wedge:blocked"],
                "substrate_kind": "source_absence_marker",
                "capture_posture": "corpus_content_not_captured",
                "provenance_status": "source_absent",
                "truth_status_forbidden": "corpus_truth_not_claimed",
                "benchmark_truth_posture": "benchmark_truth_not_claimed",
                "limitation_note": (
                    "Product-pressure provenance is review only with no corpus truth, "
                    "no benchmark truth, and no corpus ingestion."
                ),
            },
        ],
        "provenance_summary": (
            "Imported-substrate provenance is review only with no corpus truth, "
            "no benchmark truth, and no corpus ingestion."
        ),
    }
    payload["provenance_rows"] = sorted(
        payload["provenance_rows"],
        key=lambda row: row["provenance_ref"],
    )
    payload["imported_substrate_provenance_register_id"] = _surface_id(
        "repo_imported_substrate_provenance_register",
        REPO_IMPORTED_SUBSTRATE_PROVENANCE_REGISTER_SCHEMA,
        payload,
        "imported_substrate_provenance_register_id",
    )
    return RepoImportedSubstrateProvenanceRegister.model_validate(payload)


def derive_v81b_repo_cross_corpus_authority_gap_register(
    *,
    repo_root: Path | None = None,
    cross_corpus_source_index: RepoCrossCorpusSourceIndex | None = None,
    cross_corpus_governance_request: RepoCrossCorpusGovernanceRequest | None = None,
    cross_corpus_non_ingestion_guardrail: RepoCrossCorpusNonIngestionGuardrail | None = None,
    corpus_boundary_contract: RepoCorpusBoundaryContract | None = None,
    imported_substrate_provenance_register: RepoImportedSubstrateProvenanceRegister
    | None = None,
) -> RepoCrossCorpusAuthorityGapRegister:
    source_index, request, guardrail = _resolve_v81b_v81a_inputs(
        repo_root=repo_root,
        cross_corpus_source_index=cross_corpus_source_index,
        cross_corpus_governance_request=cross_corpus_governance_request,
        cross_corpus_non_ingestion_guardrail=cross_corpus_non_ingestion_guardrail,
    )
    boundary = corpus_boundary_contract or derive_v81b_repo_corpus_boundary_contract(
        cross_corpus_source_index=source_index,
        cross_corpus_governance_request=request,
        cross_corpus_non_ingestion_guardrail=guardrail,
    )
    provenance = imported_substrate_provenance_register or (
        derive_v81b_repo_imported_substrate_provenance_register(
            cross_corpus_source_index=source_index,
            cross_corpus_governance_request=request,
            cross_corpus_non_ingestion_guardrail=guardrail,
            corpus_boundary_contract=boundary,
        )
    )
    source_refs = [row.source_ref for row in source_index.source_rows]
    rows_by_request = _v81b_v81a_request_rows(request)
    self_request = rows_by_request[
        "cross-corpus-governance:v81a:self-evidencing:source-absent"
    ]
    product_request = rows_by_request[
        "cross-corpus-governance:v81a:product-wedge:product-blocked"
    ]
    payload = {
        "schema": REPO_CROSS_CORPUS_AUTHORITY_GAP_REGISTER_SCHEMA,
        "cross_corpus_authority_gap_register_id": "",
        **_v81b_shared_ids(request=request, source_index=source_index, guardrail=guardrail),
        "corpus_boundary_contract_id": boundary.corpus_boundary_contract_id,
        "imported_substrate_provenance_register_id": (
            provenance.imported_substrate_provenance_register_id
        ),
        "authority_gap_rows": [
            {
                "authority_gap_ref": "corpus-authority-gap:v81b:self-evidencing:privacy",
                "candidate_ref": self_request.candidate_ref,
                "request_refs": [self_request.cross_corpus_governance_request_ref],
                "source_refs": source_refs,
                "boundary_contract_refs": [
                    "corpus-boundary:v81b:self-evidencing:source-absent"
                ],
                "provenance_refs": ["corpus-provenance:v81b:self-evidencing:source-absent"],
                "authority_kind": "privacy_authority",
                "authority_gap_posture": "authority_missing",
                "required_before_surface": "future_corpus_ingestion_review",
                "source_presence_posture": "external_unavailable",
                "limitation_note": (
                    "Privacy authority gap is review only; authority gap preserved "
                    "with no authority granted and no corpus ingestion."
                ),
            },
            {
                "authority_gap_ref": "corpus-authority-gap:v81b:self-evidencing:license",
                "candidate_ref": self_request.candidate_ref,
                "request_refs": [self_request.cross_corpus_governance_request_ref],
                "source_refs": source_refs,
                "boundary_contract_refs": [
                    "corpus-boundary:v81b:self-evidencing:source-absent"
                ],
                "provenance_refs": ["corpus-provenance:v81b:self-evidencing:source-absent"],
                "authority_kind": "license_or_consent_authority",
                "authority_gap_posture": "authority_missing",
                "required_before_surface": "future_corpus_ingestion_review",
                "source_presence_posture": "external_unavailable",
                "limitation_note": (
                    "License authority gap is review only; authority gap preserved "
                    "with no authority granted and no corpus ingestion."
                ),
            },
            {
                "authority_gap_ref": "corpus-authority-gap:v81b:self-evidencing:connector",
                "candidate_ref": self_request.candidate_ref,
                "request_refs": [self_request.cross_corpus_governance_request_ref],
                "source_refs": source_refs,
                "boundary_contract_refs": [
                    "corpus-boundary:v81b:self-evidencing:source-absent"
                ],
                "provenance_refs": ["corpus-provenance:v81b:self-evidencing:source-absent"],
                "authority_kind": "connector_authority",
                "authority_gap_posture": "authority_missing",
                "required_before_surface": "future_connector_authority_review",
                "source_presence_posture": "external_unavailable",
                "limitation_note": (
                    "Connector authority gap is review only; authority gap preserved "
                    "with no authority granted and no connector activation."
                ),
            },
            {
                "authority_gap_ref": "corpus-authority-gap:v81b:product-wedge:product",
                "candidate_ref": product_request.candidate_ref,
                "request_refs": [product_request.cross_corpus_governance_request_ref],
                "source_refs": source_refs,
                "boundary_contract_refs": ["corpus-boundary:v81b:product-wedge:blocked"],
                "provenance_refs": ["corpus-provenance:v81b:product-wedge:blocked"],
                "authority_kind": "product_authorization",
                "authority_gap_posture": "authority_future_family_only",
                "required_before_surface": "future_product_review",
                "source_presence_posture": "external_unavailable",
                "limitation_note": (
                    "Product authority gap is review only and future-family routed; "
                    "authority gap preserved with no authority granted and no release."
                ),
            },
            {
                "authority_gap_ref": (
                    "corpus-authority-gap:v81b:product-wedge:external-branch"
                ),
                "candidate_ref": product_request.candidate_ref,
                "request_refs": [product_request.cross_corpus_governance_request_ref],
                "source_refs": source_refs,
                "boundary_contract_refs": ["corpus-boundary:v81b:product-wedge:blocked"],
                "provenance_refs": ["corpus-provenance:v81b:product-wedge:blocked"],
                "authority_kind": "external_branch_activation",
                "authority_gap_posture": "authority_future_family_only",
                "required_before_surface": "future_external_branch_review",
                "source_presence_posture": "external_unavailable",
                "limitation_note": (
                    "External branch authority gap is review only and future-family "
                    "routed; authority gap preserved with no authority granted."
                ),
            },
        ],
        "authority_gap_summary": (
            "Cross-corpus authority gaps are review only with authority gap posture "
            "and no authority granted."
        ),
    }
    payload["authority_gap_rows"] = sorted(
        payload["authority_gap_rows"],
        key=lambda row: row["authority_gap_ref"],
    )
    payload["cross_corpus_authority_gap_register_id"] = _surface_id(
        "repo_cross_corpus_authority_gap_register",
        REPO_CROSS_CORPUS_AUTHORITY_GAP_REGISTER_SCHEMA,
        payload,
        "cross_corpus_authority_gap_register_id",
    )
    return RepoCrossCorpusAuthorityGapRegister.model_validate(payload)


def derive_v81b_repo_cross_corpus_exception_register(
    *,
    repo_root: Path | None = None,
    cross_corpus_source_index: RepoCrossCorpusSourceIndex | None = None,
    cross_corpus_governance_request: RepoCrossCorpusGovernanceRequest | None = None,
    cross_corpus_non_ingestion_guardrail: RepoCrossCorpusNonIngestionGuardrail | None = None,
    corpus_boundary_contract: RepoCorpusBoundaryContract | None = None,
    imported_substrate_provenance_register: RepoImportedSubstrateProvenanceRegister
    | None = None,
    cross_corpus_authority_gap_register: RepoCrossCorpusAuthorityGapRegister | None = None,
) -> RepoCrossCorpusExceptionRegister:
    source_index, request, guardrail = _resolve_v81b_v81a_inputs(
        repo_root=repo_root,
        cross_corpus_source_index=cross_corpus_source_index,
        cross_corpus_governance_request=cross_corpus_governance_request,
        cross_corpus_non_ingestion_guardrail=cross_corpus_non_ingestion_guardrail,
    )
    boundary = corpus_boundary_contract or derive_v81b_repo_corpus_boundary_contract(
        cross_corpus_source_index=source_index,
        cross_corpus_governance_request=request,
        cross_corpus_non_ingestion_guardrail=guardrail,
    )
    provenance = imported_substrate_provenance_register or (
        derive_v81b_repo_imported_substrate_provenance_register(
            cross_corpus_source_index=source_index,
            cross_corpus_governance_request=request,
            cross_corpus_non_ingestion_guardrail=guardrail,
            corpus_boundary_contract=boundary,
        )
    )
    authority_gap = cross_corpus_authority_gap_register or (
        derive_v81b_repo_cross_corpus_authority_gap_register(
            cross_corpus_source_index=source_index,
            cross_corpus_governance_request=request,
            cross_corpus_non_ingestion_guardrail=guardrail,
            corpus_boundary_contract=boundary,
            imported_substrate_provenance_register=provenance,
        )
    )
    rows_by_request = _v81b_v81a_request_rows(request)
    self_request = rows_by_request[
        "cross-corpus-governance:v81a:self-evidencing:source-absent"
    ]
    product_request = rows_by_request[
        "cross-corpus-governance:v81a:product-wedge:product-blocked"
    ]
    payload = {
        "schema": REPO_CROSS_CORPUS_EXCEPTION_REGISTER_SCHEMA,
        "cross_corpus_exception_register_id": "",
        **_v81b_shared_ids(request=request, source_index=source_index, guardrail=guardrail),
        "corpus_boundary_contract_id": boundary.corpus_boundary_contract_id,
        "imported_substrate_provenance_register_id": (
            provenance.imported_substrate_provenance_register_id
        ),
        "cross_corpus_authority_gap_register_id": (
            authority_gap.cross_corpus_authority_gap_register_id
        ),
        "exception_rows": [
            {
                "exception_ref": "corpus-exception:v81b:self-evidencing:missing-source",
                "candidate_ref": self_request.candidate_ref,
                "request_refs": [self_request.cross_corpus_governance_request_ref],
                "boundary_contract_refs": [
                    "corpus-boundary:v81b:self-evidencing:source-absent"
                ],
                "provenance_refs": ["corpus-provenance:v81b:self-evidencing:source-absent"],
                "authority_gap_refs": sorted([
                    "corpus-authority-gap:v81b:self-evidencing:privacy",
                    "corpus-authority-gap:v81b:self-evidencing:license",
                    "corpus-authority-gap:v81b:self-evidencing:connector",
                ]),
                "exception_kind": "missing_corpus_source",
                "blocking_posture": "blocking",
                "visibility_posture": "visible_blocking",
                "required_next_surface": "future_corpus_ingestion_review",
                "limitation_note": (
                    "Missing corpus source remains blocking for review only with "
                    "no corpus ingestion."
                ),
            },
            {
                "exception_ref": "corpus-exception:v81b:product-wedge:product-gap",
                "candidate_ref": product_request.candidate_ref,
                "request_refs": [product_request.cross_corpus_governance_request_ref],
                "boundary_contract_refs": ["corpus-boundary:v81b:product-wedge:blocked"],
                "provenance_refs": ["corpus-provenance:v81b:product-wedge:blocked"],
                "authority_gap_refs": sorted([
                    "corpus-authority-gap:v81b:product-wedge:product",
                    "corpus-authority-gap:v81b:product-wedge:external-branch",
                ]),
                "exception_kind": "product_authority_gap",
                "blocking_posture": "blocking",
                "visibility_posture": "visible_blocking",
                "required_next_surface": "future_product_review",
                "limitation_note": (
                    "Product authority gap remains blocking for review only with "
                    "no corpus ingestion and no release."
                ),
            },
        ],
        "exception_summary": (
            "Cross-corpus exceptions are review only, blocking where required, "
            "with no corpus ingestion."
        ),
    }
    payload["exception_rows"] = sorted(
        payload["exception_rows"],
        key=lambda row: row["exception_ref"],
    )
    payload["cross_corpus_exception_register_id"] = _surface_id(
        "repo_cross_corpus_exception_register",
        REPO_CROSS_CORPUS_EXCEPTION_REGISTER_SCHEMA,
        payload,
        "cross_corpus_exception_register_id",
    )
    return RepoCrossCorpusExceptionRegister.model_validate(payload)


def validate_v81b_cross_corpus_boundary_bundle(
    *,
    cross_corpus_source_index: RepoCrossCorpusSourceIndex,
    cross_corpus_governance_request: RepoCrossCorpusGovernanceRequest,
    cross_corpus_non_ingestion_guardrail: RepoCrossCorpusNonIngestionGuardrail,
    corpus_boundary_contract: RepoCorpusBoundaryContract,
    imported_substrate_provenance_register: RepoImportedSubstrateProvenanceRegister,
    cross_corpus_authority_gap_register: RepoCrossCorpusAuthorityGapRegister,
    cross_corpus_exception_register: RepoCrossCorpusExceptionRegister,
) -> None:
    validate_v81a_cross_corpus_governance_bundle(
        cross_corpus_source_index=cross_corpus_source_index,
        cross_corpus_governance_request=cross_corpus_governance_request,
        cross_corpus_non_ingestion_guardrail=cross_corpus_non_ingestion_guardrail,
    )
    surface_ids = (
        cross_corpus_governance_request.cross_corpus_governance_request_id,
        cross_corpus_source_index.cross_corpus_source_index_id,
        cross_corpus_non_ingestion_guardrail.cross_corpus_non_ingestion_guardrail_id,
    )
    for surface in (
        corpus_boundary_contract,
        imported_substrate_provenance_register,
        cross_corpus_authority_gap_register,
        cross_corpus_exception_register,
    ):
        if (
            surface.cross_corpus_governance_request_id,
            surface.cross_corpus_source_index_id,
            surface.cross_corpus_non_ingestion_guardrail_id,
        ) != surface_ids:
            raise ValueError("V81-B surfaces must reference released V81-A surfaces")
        if (
            surface.review_id,
            surface.snapshot_id,
            surface.source_set_id,
        ) != (
            cross_corpus_governance_request.review_id,
            cross_corpus_governance_request.snapshot_id,
            cross_corpus_governance_request.source_set_id,
        ):
            raise ValueError("V81-B surface provenance must match V81-A request")
    if (
        imported_substrate_provenance_register.corpus_boundary_contract_id
        != corpus_boundary_contract.corpus_boundary_contract_id
        or cross_corpus_authority_gap_register.corpus_boundary_contract_id
        != corpus_boundary_contract.corpus_boundary_contract_id
        or cross_corpus_exception_register.corpus_boundary_contract_id
        != corpus_boundary_contract.corpus_boundary_contract_id
    ):
        raise ValueError("V81-B downstream surfaces must reference boundary contract")
    if (
        cross_corpus_authority_gap_register.imported_substrate_provenance_register_id
        != imported_substrate_provenance_register.imported_substrate_provenance_register_id
        or cross_corpus_exception_register.imported_substrate_provenance_register_id
        != imported_substrate_provenance_register.imported_substrate_provenance_register_id
    ):
        raise ValueError("V81-B downstream surfaces must reference provenance register")
    if (
        cross_corpus_exception_register.cross_corpus_authority_gap_register_id
        != cross_corpus_authority_gap_register.cross_corpus_authority_gap_register_id
    ):
        raise ValueError("V81-B exceptions must reference authority gap register")

    known_sources = {row.source_ref for row in cross_corpus_source_index.source_rows}
    request_rows = {
        row.cross_corpus_governance_request_ref: row
        for row in cross_corpus_governance_request.request_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row for row in cross_corpus_non_ingestion_guardrail.guardrail_rows
    }
    boundary_rows = {
        row.boundary_contract_ref: row
        for row in corpus_boundary_contract.boundary_contract_rows
    }
    provenance_rows = {
        row.provenance_ref: row
        for row in imported_substrate_provenance_register.provenance_rows
    }
    authority_gap_rows = {
        row.authority_gap_ref: row
        for row in cross_corpus_authority_gap_register.authority_gap_rows
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

    for row in corpus_boundary_contract.boundary_contract_rows:
        _check_sources(row.source_refs, label="corpus boundary contract")
        _check_request_refs(
            row.request_refs,
            candidate_ref=row.candidate_ref,
            label="corpus boundary contract",
        )
        if any(ref not in guardrail_rows for ref in row.guardrail_refs):
            raise ValueError("corpus boundary guardrail refs must be known")
        for ref in row.guardrail_refs:
            if guardrail_rows[ref].candidate_ref != row.candidate_ref:
                raise ValueError("corpus boundary guardrail refs must match candidate")
    for row in imported_substrate_provenance_register.provenance_rows:
        _check_sources(row.source_refs, label="imported substrate provenance")
        _check_request_refs(
            row.request_refs,
            candidate_ref=row.candidate_ref,
            label="imported substrate provenance",
        )
        if any(ref not in boundary_rows for ref in row.boundary_contract_refs):
            raise ValueError("provenance boundary refs must be known")
        for ref in row.boundary_contract_refs:
            if boundary_rows[ref].candidate_ref != row.candidate_ref:
                raise ValueError("provenance boundary refs must match candidate")
    for row in cross_corpus_authority_gap_register.authority_gap_rows:
        _check_sources(row.source_refs, label="cross-corpus authority gap")
        _check_request_refs(
            row.request_refs,
            candidate_ref=row.candidate_ref,
            label="cross-corpus authority gap",
        )
        if any(ref not in boundary_rows for ref in row.boundary_contract_refs):
            raise ValueError("authority gap boundary refs must be known")
        if any(ref not in provenance_rows for ref in row.provenance_refs):
            raise ValueError("authority gap provenance refs must be known")
        for ref in row.boundary_contract_refs:
            if boundary_rows[ref].candidate_ref != row.candidate_ref:
                raise ValueError("authority gap boundary refs must match candidate")
        for ref in row.provenance_refs:
            if provenance_rows[ref].candidate_ref != row.candidate_ref:
                raise ValueError("authority gap provenance refs must match candidate")
    for row in cross_corpus_exception_register.exception_rows:
        _check_request_refs(
            row.request_refs,
            candidate_ref=row.candidate_ref,
            label="cross-corpus exception",
        )
        if any(ref not in boundary_rows for ref in row.boundary_contract_refs):
            raise ValueError("cross-corpus exception boundary refs must be known")
        if any(ref not in provenance_rows for ref in row.provenance_refs):
            raise ValueError("cross-corpus exception provenance refs must be known")
        if any(ref not in authority_gap_rows for ref in row.authority_gap_refs):
            raise ValueError("cross-corpus exception authority gap refs must be known")
        for ref in row.boundary_contract_refs:
            if boundary_rows[ref].candidate_ref != row.candidate_ref:
                raise ValueError("cross-corpus exception boundary refs must match candidate")
        for ref in row.provenance_refs:
            if provenance_rows[ref].candidate_ref != row.candidate_ref:
                raise ValueError("cross-corpus exception provenance refs must match candidate")
        for ref in row.authority_gap_refs:
            if authority_gap_rows[ref].candidate_ref != row.candidate_ref:
                raise ValueError("cross-corpus exception authority gap refs must match candidate")


def derive_v81b_cross_corpus_boundary_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoCrossCorpusSourceIndex,
    RepoCrossCorpusGovernanceRequest,
    RepoCrossCorpusNonIngestionGuardrail,
    RepoCorpusBoundaryContract,
    RepoImportedSubstrateProvenanceRegister,
    RepoCrossCorpusAuthorityGapRegister,
    RepoCrossCorpusExceptionRegister,
]:
    source_index, request, guardrail = derive_v81a_cross_corpus_governance_bundle(
        repo_root=repo_root
    )
    boundary = derive_v81b_repo_corpus_boundary_contract(
        repo_root=repo_root,
        cross_corpus_source_index=source_index,
        cross_corpus_governance_request=request,
        cross_corpus_non_ingestion_guardrail=guardrail,
    )
    provenance = derive_v81b_repo_imported_substrate_provenance_register(
        repo_root=repo_root,
        cross_corpus_source_index=source_index,
        cross_corpus_governance_request=request,
        cross_corpus_non_ingestion_guardrail=guardrail,
        corpus_boundary_contract=boundary,
    )
    authority_gap = derive_v81b_repo_cross_corpus_authority_gap_register(
        repo_root=repo_root,
        cross_corpus_source_index=source_index,
        cross_corpus_governance_request=request,
        cross_corpus_non_ingestion_guardrail=guardrail,
        corpus_boundary_contract=boundary,
        imported_substrate_provenance_register=provenance,
    )
    exception_register = derive_v81b_repo_cross_corpus_exception_register(
        repo_root=repo_root,
        cross_corpus_source_index=source_index,
        cross_corpus_governance_request=request,
        cross_corpus_non_ingestion_guardrail=guardrail,
        corpus_boundary_contract=boundary,
        imported_substrate_provenance_register=provenance,
        cross_corpus_authority_gap_register=authority_gap,
    )
    validate_v81b_cross_corpus_boundary_bundle(
        cross_corpus_source_index=source_index,
        cross_corpus_governance_request=request,
        cross_corpus_non_ingestion_guardrail=guardrail,
        corpus_boundary_contract=boundary,
        imported_substrate_provenance_register=provenance,
        cross_corpus_authority_gap_register=authority_gap,
        cross_corpus_exception_register=exception_register,
    )
    return (
        source_index,
        request,
        guardrail,
        boundary,
        provenance,
        authority_gap,
        exception_register,
    )


def derive_v81c_repo_cross_corpus_governance_summary(
    *,
    repo_root: Path | None = None,
    cross_corpus_source_index: RepoCrossCorpusSourceIndex | None = None,
    cross_corpus_governance_request: RepoCrossCorpusGovernanceRequest | None = None,
    cross_corpus_non_ingestion_guardrail: RepoCrossCorpusNonIngestionGuardrail | None = None,
    corpus_boundary_contract: RepoCorpusBoundaryContract | None = None,
    imported_substrate_provenance_register: RepoImportedSubstrateProvenanceRegister
    | None = None,
    cross_corpus_authority_gap_register: RepoCrossCorpusAuthorityGapRegister | None = None,
    cross_corpus_exception_register: RepoCrossCorpusExceptionRegister | None = None,
) -> RepoCrossCorpusGovernanceSummary:
    (
        source_index,
        request,
        guardrail,
        boundary,
        provenance,
        authority_gap,
        exception_register,
    ) = (
        derive_v81b_cross_corpus_boundary_bundle(repo_root=repo_root)
        if (
            cross_corpus_source_index is None
            and cross_corpus_governance_request is None
            and cross_corpus_non_ingestion_guardrail is None
            and corpus_boundary_contract is None
            and imported_substrate_provenance_register is None
            and cross_corpus_authority_gap_register is None
            and cross_corpus_exception_register is None
        )
        else (
            cross_corpus_source_index,
            cross_corpus_governance_request,
            cross_corpus_non_ingestion_guardrail,
            corpus_boundary_contract,
            imported_substrate_provenance_register,
            cross_corpus_authority_gap_register,
            cross_corpus_exception_register,
        )
    )
    if any(
        item is None
        for item in (
            source_index,
            request,
            guardrail,
            boundary,
            provenance,
            authority_gap,
            exception_register,
        )
    ):
        raise ValueError("V81-C derivation requires all V81-A/B inputs when any are supplied")
    assert source_index is not None
    assert request is not None
    assert guardrail is not None
    assert boundary is not None
    assert provenance is not None
    assert authority_gap is not None
    assert exception_register is not None
    validate_v81b_cross_corpus_boundary_bundle(
        cross_corpus_source_index=source_index,
        cross_corpus_governance_request=request,
        cross_corpus_non_ingestion_guardrail=guardrail,
        corpus_boundary_contract=boundary,
        imported_substrate_provenance_register=provenance,
        cross_corpus_authority_gap_register=authority_gap,
        cross_corpus_exception_register=exception_register,
    )
    boundary_rows = {row.candidate_ref: row for row in boundary.boundary_contract_rows}
    provenance_rows = {row.candidate_ref: row for row in provenance.provenance_rows}
    authority_gap_rows_by_candidate: dict[str, list[RepoCrossCorpusAuthorityGapRow]] = {}
    for row in authority_gap.authority_gap_rows:
        authority_gap_rows_by_candidate.setdefault(row.candidate_ref, []).append(row)
    exception_rows = {row.candidate_ref: row for row in exception_register.exception_rows}
    guardrail_rows = {row.candidate_ref: row for row in guardrail.guardrail_rows}
    summary_rows: list[dict[str, object]] = []
    for request_row in request.request_rows:
        candidate_ref = request_row.candidate_ref
        candidate_boundary = boundary_rows[candidate_ref]
        candidate_provenance = provenance_rows[candidate_ref]
        candidate_authority_gaps = authority_gap_rows_by_candidate[candidate_ref]
        candidate_exception = exception_rows[candidate_ref]
        if candidate_ref == "candidate:internal:typed_adjudication_product_wedge":
            summary_posture = "blocked_by_product_authority_gap"
            ready_basis_posture = "authority_review_requested_for_blockers"
            limitation_note = (
                "Product-pressure cross-corpus summary remains blocked for review with "
                "no corpus ingestion, no connector activation, and no release."
            )
        else:
            summary_posture = "blocked_by_missing_corpus_source"
            ready_basis_posture = "not_ready_blockers_remain"
            limitation_note = (
                "Cross-corpus summary preserves missing corpus-source blockers for review "
                "with no corpus ingestion, no connector activation, and no release."
            )
        summary_rows.append(
            {
                "cross_corpus_summary_ref": (
                    "cross-corpus-summary:v81c:"
                    f"{candidate_ref.removeprefix('candidate:internal:')}"
                ),
                "candidate_ref": candidate_ref,
                "request_refs": [request_row.cross_corpus_governance_request_ref],
                "boundary_contract_refs": [candidate_boundary.boundary_contract_ref],
                "provenance_refs": [candidate_provenance.provenance_ref],
                "authority_gap_refs": [
                    row.authority_gap_ref for row in candidate_authority_gaps
                ],
                "exception_refs": [candidate_exception.exception_ref],
                "carried_blocker_refs": [candidate_exception.exception_ref],
                "carried_warning_refs": [],
                "summary_posture": summary_posture,
                "ready_basis_posture": ready_basis_posture,
                "corpus_ingestion_posture": "no_corpus_ingestion_performed_by_v81",
                "connector_activation_posture": "no_connector_activation_performed_by_v81",
                "endpoint_access_posture": "no_endpoint_access_performed_by_v81",
                "adjudication_execution_posture": (
                    "no_cross_corpus_adjudication_performed_by_v81"
                ),
                "product_authorization_posture": (
                    "no_product_authorization_performed_by_v81"
                ),
                "release_authority_posture": "no_release_authority_performed_by_v81",
                "guardrail_refs": [guardrail_rows[candidate_ref].guardrail_ref],
                "limitation_note": limitation_note,
            }
        )
    payload = {
        "schema": REPO_CROSS_CORPUS_GOVERNANCE_SUMMARY_SCHEMA,
        "cross_corpus_governance_summary_id": "",
        "cross_corpus_governance_request_id": request.cross_corpus_governance_request_id,
        "cross_corpus_source_index_id": source_index.cross_corpus_source_index_id,
        "cross_corpus_non_ingestion_guardrail_id": (
            guardrail.cross_corpus_non_ingestion_guardrail_id
        ),
        "corpus_boundary_contract_id": boundary.corpus_boundary_contract_id,
        "imported_substrate_provenance_register_id": (
            provenance.imported_substrate_provenance_register_id
        ),
        "cross_corpus_authority_gap_register_id": (
            authority_gap.cross_corpus_authority_gap_register_id
        ),
        "cross_corpus_exception_register_id": (
            exception_register.cross_corpus_exception_register_id
        ),
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "summary_rows": sorted(
            summary_rows,
            key=lambda row: str(row["cross_corpus_summary_ref"]),
        ),
        "governance_summary": (
            "V81-C summarizes released cross-corpus review substrate with no corpus "
            "ingestion, no connector activation, no release, and no downstream authority."
        ),
    }
    payload["cross_corpus_governance_summary_id"] = _surface_id(
        "repo_cross_corpus_governance_summary",
        REPO_CROSS_CORPUS_GOVERNANCE_SUMMARY_SCHEMA,
        payload,
        "cross_corpus_governance_summary_id",
    )
    return RepoCrossCorpusGovernanceSummary.model_validate(payload)


def derive_v81c_repo_post_cross_corpus_review_handoff(
    *,
    repo_root: Path | None = None,
    cross_corpus_source_index: RepoCrossCorpusSourceIndex | None = None,
    cross_corpus_governance_request: RepoCrossCorpusGovernanceRequest | None = None,
    cross_corpus_non_ingestion_guardrail: RepoCrossCorpusNonIngestionGuardrail | None = None,
    corpus_boundary_contract: RepoCorpusBoundaryContract | None = None,
    imported_substrate_provenance_register: RepoImportedSubstrateProvenanceRegister
    | None = None,
    cross_corpus_authority_gap_register: RepoCrossCorpusAuthorityGapRegister | None = None,
    cross_corpus_exception_register: RepoCrossCorpusExceptionRegister | None = None,
    cross_corpus_governance_summary: RepoCrossCorpusGovernanceSummary | None = None,
) -> RepoPostCrossCorpusReviewHandoff:
    if cross_corpus_governance_summary is None:
        summary = derive_v81c_repo_cross_corpus_governance_summary(
            repo_root=repo_root,
            cross_corpus_source_index=cross_corpus_source_index,
            cross_corpus_governance_request=cross_corpus_governance_request,
            cross_corpus_non_ingestion_guardrail=cross_corpus_non_ingestion_guardrail,
            corpus_boundary_contract=corpus_boundary_contract,
            imported_substrate_provenance_register=imported_substrate_provenance_register,
            cross_corpus_authority_gap_register=cross_corpus_authority_gap_register,
            cross_corpus_exception_register=cross_corpus_exception_register,
        )
    else:
        summary = cross_corpus_governance_summary
    if (
        cross_corpus_source_index is None
        or cross_corpus_governance_request is None
        or cross_corpus_non_ingestion_guardrail is None
        or corpus_boundary_contract is None
        or imported_substrate_provenance_register is None
        or cross_corpus_authority_gap_register is None
        or cross_corpus_exception_register is None
    ):
        (
            source_index,
            request,
            guardrail,
            boundary,
            provenance,
            authority_gap,
            exception_register,
        ) = derive_v81b_cross_corpus_boundary_bundle(repo_root=repo_root)
    else:
        source_index = cross_corpus_source_index
        request = cross_corpus_governance_request
        guardrail = cross_corpus_non_ingestion_guardrail
        boundary = corpus_boundary_contract
        provenance = imported_substrate_provenance_register
        authority_gap = cross_corpus_authority_gap_register
        exception_register = cross_corpus_exception_register
    validate_v81b_cross_corpus_boundary_bundle(
        cross_corpus_source_index=source_index,
        cross_corpus_governance_request=request,
        cross_corpus_non_ingestion_guardrail=guardrail,
        corpus_boundary_contract=boundary,
        imported_substrate_provenance_register=provenance,
        cross_corpus_authority_gap_register=authority_gap,
        cross_corpus_exception_register=exception_register,
    )
    authority_gap_by_ref = {
        row.authority_gap_ref: row for row in authority_gap.authority_gap_rows
    }
    summary_rows = {row.candidate_ref: row for row in summary.summary_rows}
    handoff_rows: list[dict[str, object]] = []
    for candidate_ref, summary_row in summary_rows.items():
        if candidate_ref == "candidate:internal:typed_adjudication_product_wedge":
            target = "future_product_review"
            subject = "product_authority_gap"
            authority = "product_authority_review"
            required = [
                ref
                for ref in summary_row.authority_gap_refs
                if authority_gap_by_ref[ref].authority_kind == "product_authorization"
            ]
            note = (
                "Product cross-corpus pressure is handed off for later review with "
                "no corpus ingestion, no connector activation, and no product authorization."
            )
        else:
            target = "future_corpus_ingestion_review"
            subject = "corpus_boundary_review_package"
            authority = "corpus_ingestion_authority_review"
            required = [
                ref
                for ref in summary_row.authority_gap_refs
                if "privacy" in ref or "license" in ref
            ]
            note = (
                "Corpus-ingestion pressure is handed off for later review with "
                "no corpus ingestion, no connector activation, and no endpoint access."
            )
        handoff_rows.append(
            {
                "handoff_ref": (
                    "post-cross-corpus-handoff:v81c:"
                    f"{candidate_ref.removeprefix('candidate:internal:')}"
                ),
                "candidate_ref": candidate_ref,
                "summary_refs": [summary_row.cross_corpus_summary_ref],
                "boundary_contract_refs": summary_row.boundary_contract_refs,
                "provenance_refs": summary_row.provenance_refs,
                "authority_gap_refs": summary_row.authority_gap_refs,
                "carried_exception_refs": summary_row.carried_blocker_refs,
                "handoff_target": target,
                "handoff_subject_horizon": subject,
                "handoff_authority_horizon": authority,
                "handoff_posture": "blocked_by_carried_exceptions",
                "required_later_authority_refs": required,
                "corpus_ingestion_posture": "no_corpus_ingestion_performed_by_v81",
                "connector_activation_posture": "no_connector_activation_performed_by_v81",
                "endpoint_access_posture": "no_endpoint_access_performed_by_v81",
                "adjudication_execution_posture": (
                    "no_cross_corpus_adjudication_performed_by_v81"
                ),
                "guardrail_refs": summary_row.guardrail_refs,
                "limitation_note": note,
            }
        )
    payload = {
        "schema": REPO_POST_CROSS_CORPUS_REVIEW_HANDOFF_SCHEMA,
        "post_cross_corpus_review_handoff_id": "",
        "cross_corpus_governance_summary_id": summary.cross_corpus_governance_summary_id,
        "cross_corpus_governance_request_id": request.cross_corpus_governance_request_id,
        "cross_corpus_source_index_id": source_index.cross_corpus_source_index_id,
        "cross_corpus_non_ingestion_guardrail_id": (
            guardrail.cross_corpus_non_ingestion_guardrail_id
        ),
        "corpus_boundary_contract_id": boundary.corpus_boundary_contract_id,
        "imported_substrate_provenance_register_id": (
            provenance.imported_substrate_provenance_register_id
        ),
        "cross_corpus_authority_gap_register_id": (
            authority_gap.cross_corpus_authority_gap_register_id
        ),
        "cross_corpus_exception_register_id": (
            exception_register.cross_corpus_exception_register_id
        ),
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "handoff_rows": sorted(handoff_rows, key=lambda row: str(row["handoff_ref"])),
        "handoff_summary": (
            "V81-C handoffs request later review with no corpus ingestion, "
            "no connector activation, no release, and no later-family completion."
        ),
    }
    payload["post_cross_corpus_review_handoff_id"] = _surface_id(
        "repo_post_cross_corpus_review_handoff",
        REPO_POST_CROSS_CORPUS_REVIEW_HANDOFF_SCHEMA,
        payload,
        "post_cross_corpus_review_handoff_id",
    )
    return RepoPostCrossCorpusReviewHandoff.model_validate(payload)


def derive_v81c_repo_cross_corpus_governance_family_closeout_alignment(
    *,
    repo_root: Path | None = None,
    cross_corpus_governance_summary: RepoCrossCorpusGovernanceSummary | None = None,
    post_cross_corpus_review_handoff: RepoPostCrossCorpusReviewHandoff | None = None,
) -> RepoCrossCorpusGovernanceFamilyCloseoutAlignment:
    summary = cross_corpus_governance_summary or derive_v81c_repo_cross_corpus_governance_summary(
        repo_root=repo_root
    )
    handoff = post_cross_corpus_review_handoff or derive_v81c_repo_post_cross_corpus_review_handoff(
        repo_root=repo_root,
        cross_corpus_governance_summary=summary,
    )
    payload = {
        "schema": REPO_CROSS_CORPUS_GOVERNANCE_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        "cross_corpus_governance_family_closeout_alignment_id": "",
        "cross_corpus_governance_summary_id": summary.cross_corpus_governance_summary_id,
        "post_cross_corpus_review_handoff_id": handoff.post_cross_corpus_review_handoff_id,
        "family": "V81",
        "closed_by_arc": "vNext+229",
        "closed_slice_ladder": ["V81-A", "V81-B", "V81-C"],
        "shipped_record_shapes": sorted(
            [
                REPO_CROSS_CORPUS_GOVERNANCE_REQUEST_SCHEMA,
                REPO_CROSS_CORPUS_SOURCE_INDEX_SCHEMA,
                REPO_CROSS_CORPUS_NON_INGESTION_GUARDRAIL_SCHEMA,
                REPO_CORPUS_BOUNDARY_CONTRACT_SCHEMA,
                REPO_IMPORTED_SUBSTRATE_PROVENANCE_REGISTER_SCHEMA,
                REPO_CROSS_CORPUS_AUTHORITY_GAP_REGISTER_SCHEMA,
                REPO_CROSS_CORPUS_EXCEPTION_REGISTER_SCHEMA,
                REPO_CROSS_CORPUS_GOVERNANCE_SUMMARY_SCHEMA,
                REPO_POST_CROSS_CORPUS_REVIEW_HANDOFF_SCHEMA,
                REPO_CROSS_CORPUS_GOVERNANCE_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            ]
        ),
        "consumed_source_families": [
            "V68",
            "V69",
            "V70",
            "V71",
            "V72",
            "V73",
            "V74",
            "V75",
            "V76",
            "V77",
            "V78",
            "V79",
            "V80",
            "V81",
        ],
        "family_closed_on_main": "closed_after_v81c_merge",
        "future_family_authority": "next_selector_required",
        "unselected_future_surfaces": [
            "benchmark_truth",
            "connector_activation",
            "corpus_ingestion",
            "cross_corpus_adjudication_execution",
            "customer_data_handling",
            "endpoint_access",
            "global_model_selection",
            "imported_result_truth",
            "living_memory_authority",
            "product_authorization",
            "recursive_policy_amendment",
            "release",
            "v82_selection",
        ],
        "cross_corpus_boundary": (
            "V81 closes cross-corpus governance review with no corpus ingestion, "
            "no connector activation, no release, and no v82 selection."
        ),
        "limitation_note": (
            "V81 is closed as review only with no corpus ingestion, no connector "
            "activation, no v82 selection, and no downstream authority."
        ),
    }
    payload["cross_corpus_governance_family_closeout_alignment_id"] = _surface_id(
        "repo_cross_corpus_governance_family_closeout_alignment",
        REPO_CROSS_CORPUS_GOVERNANCE_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        payload,
        "cross_corpus_governance_family_closeout_alignment_id",
    )
    return RepoCrossCorpusGovernanceFamilyCloseoutAlignment.model_validate(payload)


def validate_v81c_cross_corpus_governance_closeout_bundle(
    *,
    cross_corpus_source_index: RepoCrossCorpusSourceIndex,
    cross_corpus_governance_request: RepoCrossCorpusGovernanceRequest,
    cross_corpus_non_ingestion_guardrail: RepoCrossCorpusNonIngestionGuardrail,
    corpus_boundary_contract: RepoCorpusBoundaryContract,
    imported_substrate_provenance_register: RepoImportedSubstrateProvenanceRegister,
    cross_corpus_authority_gap_register: RepoCrossCorpusAuthorityGapRegister,
    cross_corpus_exception_register: RepoCrossCorpusExceptionRegister,
    cross_corpus_governance_summary: RepoCrossCorpusGovernanceSummary,
    post_cross_corpus_review_handoff: RepoPostCrossCorpusReviewHandoff,
    cross_corpus_governance_family_closeout_alignment: (
        RepoCrossCorpusGovernanceFamilyCloseoutAlignment
    ),
) -> None:
    validate_v81b_cross_corpus_boundary_bundle(
        cross_corpus_source_index=cross_corpus_source_index,
        cross_corpus_governance_request=cross_corpus_governance_request,
        cross_corpus_non_ingestion_guardrail=cross_corpus_non_ingestion_guardrail,
        corpus_boundary_contract=corpus_boundary_contract,
        imported_substrate_provenance_register=imported_substrate_provenance_register,
        cross_corpus_authority_gap_register=cross_corpus_authority_gap_register,
        cross_corpus_exception_register=cross_corpus_exception_register,
    )
    expected_ids = (
        cross_corpus_governance_request.cross_corpus_governance_request_id,
        cross_corpus_source_index.cross_corpus_source_index_id,
        cross_corpus_non_ingestion_guardrail.cross_corpus_non_ingestion_guardrail_id,
        corpus_boundary_contract.corpus_boundary_contract_id,
        imported_substrate_provenance_register.imported_substrate_provenance_register_id,
        cross_corpus_authority_gap_register.cross_corpus_authority_gap_register_id,
        cross_corpus_exception_register.cross_corpus_exception_register_id,
    )
    if (
        cross_corpus_governance_summary.cross_corpus_governance_request_id,
        cross_corpus_governance_summary.cross_corpus_source_index_id,
        cross_corpus_governance_summary.cross_corpus_non_ingestion_guardrail_id,
        cross_corpus_governance_summary.corpus_boundary_contract_id,
        cross_corpus_governance_summary.imported_substrate_provenance_register_id,
        cross_corpus_governance_summary.cross_corpus_authority_gap_register_id,
        cross_corpus_governance_summary.cross_corpus_exception_register_id,
    ) != expected_ids:
        raise ValueError("V81-C summary must reference released V81-A/B surfaces")
    if (
        post_cross_corpus_review_handoff.cross_corpus_governance_summary_id
        != cross_corpus_governance_summary.cross_corpus_governance_summary_id
    ):
        raise ValueError("V81-C handoff must reference released summary surface")
    if (
        post_cross_corpus_review_handoff.cross_corpus_governance_request_id,
        post_cross_corpus_review_handoff.cross_corpus_source_index_id,
        post_cross_corpus_review_handoff.cross_corpus_non_ingestion_guardrail_id,
        post_cross_corpus_review_handoff.corpus_boundary_contract_id,
        post_cross_corpus_review_handoff.imported_substrate_provenance_register_id,
        post_cross_corpus_review_handoff.cross_corpus_authority_gap_register_id,
        post_cross_corpus_review_handoff.cross_corpus_exception_register_id,
    ) != expected_ids:
        raise ValueError("V81-C handoff must reference released V81-A/B surfaces")
    if (
        cross_corpus_governance_family_closeout_alignment.cross_corpus_governance_summary_id
        != cross_corpus_governance_summary.cross_corpus_governance_summary_id
        or cross_corpus_governance_family_closeout_alignment.post_cross_corpus_review_handoff_id
        != post_cross_corpus_review_handoff.post_cross_corpus_review_handoff_id
    ):
        raise ValueError("V81-C closeout must reference released summary and handoff")

    request_rows = {
        row.cross_corpus_governance_request_ref: row
        for row in cross_corpus_governance_request.request_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row for row in cross_corpus_non_ingestion_guardrail.guardrail_rows
    }
    boundary_rows = {
        row.boundary_contract_ref: row
        for row in corpus_boundary_contract.boundary_contract_rows
    }
    provenance_rows = {
        row.provenance_ref: row
        for row in imported_substrate_provenance_register.provenance_rows
    }
    authority_gap_rows = {
        row.authority_gap_ref: row
        for row in cross_corpus_authority_gap_register.authority_gap_rows
    }
    exception_rows = {
        row.exception_ref: row for row in cross_corpus_exception_register.exception_rows
    }
    summary_rows = {
        row.cross_corpus_summary_ref: row
        for row in cross_corpus_governance_summary.summary_rows
    }
    request_candidates = {row.candidate_ref for row in cross_corpus_governance_request.request_rows}
    summary_candidates = {row.candidate_ref for row in cross_corpus_governance_summary.summary_rows}
    handoff_candidates = {
        row.candidate_ref for row in post_cross_corpus_review_handoff.handoff_rows
    }
    if request_candidates != summary_candidates:
        raise ValueError("V81-C summary must cover all request candidates")
    if request_candidates != handoff_candidates:
        raise ValueError("V81-C handoff must cover all request candidates")

    def _require_known_refs(refs: list[str], known: set[str], message: str) -> None:
        if any(ref not in known for ref in refs):
            raise ValueError(message)

    def _require_candidate_refs(
        refs: list[str],
        rows_by_ref: dict[str, _CartographyBase],
        *,
        candidate_ref: str,
        message: str,
    ) -> None:
        for ref in refs:
            if rows_by_ref[ref].candidate_ref != candidate_ref:
                raise ValueError(message)

    for row in cross_corpus_governance_summary.summary_rows:
        _require_known_refs(
            row.request_refs,
            set(request_rows),
            "summary request refs must be known",
        )
        _require_known_refs(
            row.boundary_contract_refs,
            set(boundary_rows),
            "summary boundary refs must be known",
        )
        _require_known_refs(
            row.provenance_refs,
            set(provenance_rows),
            "summary provenance refs must be known",
        )
        _require_known_refs(
            row.authority_gap_refs,
            set(authority_gap_rows),
            "summary authority gap refs must be known",
        )
        _require_known_refs(
            row.exception_refs,
            set(exception_rows),
            "summary exception refs must be known",
        )
        _require_known_refs(
            row.carried_blocker_refs,
            set(exception_rows),
            "summary blocker refs must be known",
        )
        _require_known_refs(
            row.carried_warning_refs,
            set(exception_rows),
            "summary warning refs must be known",
        )
        _require_known_refs(
            row.guardrail_refs,
            set(guardrail_rows),
            "summary guardrail refs must be known",
        )
        _require_candidate_refs(
            row.request_refs,
            request_rows,
            candidate_ref=row.candidate_ref,
            message="summary request refs must match candidate",
        )
        _require_candidate_refs(
            row.boundary_contract_refs,
            boundary_rows,
            candidate_ref=row.candidate_ref,
            message="summary boundary refs must match candidate",
        )
        _require_candidate_refs(
            row.provenance_refs,
            provenance_rows,
            candidate_ref=row.candidate_ref,
            message="summary provenance refs must match candidate",
        )
        _require_candidate_refs(
            row.authority_gap_refs,
            authority_gap_rows,
            candidate_ref=row.candidate_ref,
            message="summary authority gap refs must match candidate",
        )
        _require_candidate_refs(
            row.exception_refs,
            exception_rows,
            candidate_ref=row.candidate_ref,
            message="summary exception refs must match candidate",
        )
        _require_candidate_refs(
            row.guardrail_refs,
            guardrail_rows,
            candidate_ref=row.candidate_ref,
            message="summary guardrail refs must match candidate",
        )
        blocking_refs = {
            ref for ref in row.exception_refs if exception_rows[ref].blocking_posture == "blocking"
        }
        if row.summary_posture in _SUMMARY_READY_POSTURES and blocking_refs:
            raise ValueError("ready cross-corpus summaries cannot hide blocking exceptions")
        if row.summary_posture == "cross_corpus_review_ready_with_nonblocking_warnings":
            warning_refs = {
                ref
                for ref in row.exception_refs
                if exception_rows[ref].blocking_posture == "warning_only"
            }
            if set(row.exception_refs) != warning_refs:
                raise ValueError("warning-ready summaries may carry warnings only")
        for ref in row.carried_blocker_refs:
            if exception_rows[ref].blocking_posture != "blocking":
                raise ValueError("carried blocker refs must point to blocking exceptions")
        for ref in row.carried_warning_refs:
            if exception_rows[ref].blocking_posture != "warning_only":
                raise ValueError("carried warning refs must point to warning exceptions")
        carried_exception_refs = set(row.carried_blocker_refs) | set(row.carried_warning_refs)
        if not carried_exception_refs.issubset(set(row.exception_refs)):
            raise ValueError("summary carried exception refs must be included in exception refs")
        _require_candidate_refs(
            row.carried_blocker_refs,
            exception_rows,
            candidate_ref=row.candidate_ref,
            message="summary carried blocker refs must match candidate",
        )
        _require_candidate_refs(
            row.carried_warning_refs,
            exception_rows,
            candidate_ref=row.candidate_ref,
            message="summary carried warning refs must match candidate",
        )

    for row in post_cross_corpus_review_handoff.handoff_rows:
        _require_known_refs(
            row.summary_refs,
            set(summary_rows),
            "handoff summary refs must be known",
        )
        _require_known_refs(
            row.boundary_contract_refs,
            set(boundary_rows),
            "handoff boundary refs must be known",
        )
        _require_known_refs(
            row.provenance_refs,
            set(provenance_rows),
            "handoff provenance refs must be known",
        )
        _require_known_refs(
            row.authority_gap_refs,
            set(authority_gap_rows),
            "handoff authority gap refs must be known",
        )
        _require_known_refs(
            row.required_later_authority_refs,
            set(authority_gap_rows),
            "handoff required authority refs must be known",
        )
        _require_known_refs(
            row.carried_exception_refs,
            set(exception_rows),
            "handoff exception refs must be known",
        )
        _require_known_refs(
            row.guardrail_refs,
            set(guardrail_rows),
            "handoff guardrail refs must be known",
        )
        _require_candidate_refs(
            row.summary_refs,
            summary_rows,
            candidate_ref=row.candidate_ref,
            message="handoff summary refs must match candidate",
        )
        _require_candidate_refs(
            row.boundary_contract_refs,
            boundary_rows,
            candidate_ref=row.candidate_ref,
            message="handoff boundary refs must match candidate",
        )
        _require_candidate_refs(
            row.provenance_refs,
            provenance_rows,
            candidate_ref=row.candidate_ref,
            message="handoff provenance refs must match candidate",
        )
        _require_candidate_refs(
            row.authority_gap_refs,
            authority_gap_rows,
            candidate_ref=row.candidate_ref,
            message="handoff authority gap refs must match candidate",
        )
        _require_candidate_refs(
            row.required_later_authority_refs,
            authority_gap_rows,
            candidate_ref=row.candidate_ref,
            message="handoff required authority refs must match candidate",
        )
        _require_candidate_refs(
            row.carried_exception_refs,
            exception_rows,
            candidate_ref=row.candidate_ref,
            message="handoff exception refs must match candidate",
        )
        if not set(row.required_later_authority_refs).issubset(set(row.authority_gap_refs)):
            raise ValueError(
                "handoff required authority refs must be carried authority gap refs"
            )
        _require_candidate_refs(
            row.guardrail_refs,
            guardrail_rows,
            candidate_ref=row.candidate_ref,
            message="handoff guardrail refs must match candidate",
        )
        blocking_refs = {
            ref
            for ref in row.carried_exception_refs
            if exception_rows[ref].blocking_posture == "blocking"
        }
        if blocking_refs and row.handoff_posture == "ready_for_later_review":
            raise ValueError("handoffs with blocking exceptions cannot be ready")
        if row.handoff_posture == "ready_with_nonblocking_warnings":
            warning_refs = {
                ref
                for ref in row.carried_exception_refs
                if exception_rows[ref].blocking_posture == "warning_only"
            }
            if set(row.carried_exception_refs) != warning_refs:
                raise ValueError("warning-ready handoffs may carry warnings only")

    if (
        "v82_selection"
        not in cross_corpus_governance_family_closeout_alignment.unselected_future_surfaces
    ):
        raise ValueError("V81-C closeout must not select V82")


def derive_v81c_cross_corpus_governance_closeout_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoCrossCorpusSourceIndex,
    RepoCrossCorpusGovernanceRequest,
    RepoCrossCorpusNonIngestionGuardrail,
    RepoCorpusBoundaryContract,
    RepoImportedSubstrateProvenanceRegister,
    RepoCrossCorpusAuthorityGapRegister,
    RepoCrossCorpusExceptionRegister,
    RepoCrossCorpusGovernanceSummary,
    RepoPostCrossCorpusReviewHandoff,
    RepoCrossCorpusGovernanceFamilyCloseoutAlignment,
]:
    (
        source_index,
        request,
        guardrail,
        boundary,
        provenance,
        authority_gap,
        exception_register,
    ) = derive_v81b_cross_corpus_boundary_bundle(repo_root=repo_root)
    summary = derive_v81c_repo_cross_corpus_governance_summary(
        repo_root=repo_root,
        cross_corpus_source_index=source_index,
        cross_corpus_governance_request=request,
        cross_corpus_non_ingestion_guardrail=guardrail,
        corpus_boundary_contract=boundary,
        imported_substrate_provenance_register=provenance,
        cross_corpus_authority_gap_register=authority_gap,
        cross_corpus_exception_register=exception_register,
    )
    handoff = derive_v81c_repo_post_cross_corpus_review_handoff(
        repo_root=repo_root,
        cross_corpus_source_index=source_index,
        cross_corpus_governance_request=request,
        cross_corpus_non_ingestion_guardrail=guardrail,
        corpus_boundary_contract=boundary,
        imported_substrate_provenance_register=provenance,
        cross_corpus_authority_gap_register=authority_gap,
        cross_corpus_exception_register=exception_register,
        cross_corpus_governance_summary=summary,
    )
    closeout = derive_v81c_repo_cross_corpus_governance_family_closeout_alignment(
        repo_root=repo_root,
        cross_corpus_governance_summary=summary,
        post_cross_corpus_review_handoff=handoff,
    )
    validate_v81c_cross_corpus_governance_closeout_bundle(
        cross_corpus_source_index=source_index,
        cross_corpus_governance_request=request,
        cross_corpus_non_ingestion_guardrail=guardrail,
        corpus_boundary_contract=boundary,
        imported_substrate_provenance_register=provenance,
        cross_corpus_authority_gap_register=authority_gap,
        cross_corpus_exception_register=exception_register,
        cross_corpus_governance_summary=summary,
        post_cross_corpus_review_handoff=handoff,
        cross_corpus_governance_family_closeout_alignment=closeout,
    )
    return (
        source_index,
        request,
        guardrail,
        boundary,
        provenance,
        authority_gap,
        exception_register,
        summary,
        handoff,
        closeout,
    )
