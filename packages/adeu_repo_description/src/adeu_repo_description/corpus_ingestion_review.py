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

REPO_CORPUS_INGESTION_REVIEW_REQUEST_SCHEMA = "repo_corpus_ingestion_review_request@1"
REPO_CORPUS_INGESTION_SOURCE_INDEX_SCHEMA = "repo_corpus_ingestion_source_index@1"
REPO_CORPUS_INGESTION_NON_TRANSFER_GUARDRAIL_SCHEMA = (
    "repo_corpus_ingestion_non_transfer_guardrail@1"
)
REPO_CORPUS_INGESTION_PREFLIGHT_CONTRACT_SCHEMA = "repo_corpus_ingestion_preflight_contract@1"
REPO_CONNECTOR_ACCESS_REVIEW_BOUNDARY_SCHEMA = "repo_connector_access_review_boundary@1"
REPO_CORPUS_DATA_HANDLING_AUTHORITY_REVIEW_SCHEMA = "repo_corpus_data_handling_authority_review@1"
REPO_CORPUS_INGESTION_EXCEPTION_REGISTER_SCHEMA = "repo_corpus_ingestion_exception_register@1"

IngestionSourceRole = Literal[
    "v81_summary_source",
    "v81_handoff_source",
    "v81_closeout_source",
    "v81_boundary_context",
    "v81_provenance_context",
    "v81_authority_gap_context",
    "v81_exception_context",
    "current_concrete_corpus_source",
    "current_customer_corpus_source",
    "current_benchmark_descriptor_source",
    "privacy_authority_source",
    "license_or_consent_authority_source",
    "customer_data_authority_source",
    "connector_authority_source",
    "endpoint_authority_source",
    "transfer_boundary_source",
    "explicit_corpus_absence_marker",
    "explicit_authority_absence_marker",
    "dogfood_context",
    "roadmap_context",
    "support_process_context",
    "absence_marker",
]
IngestionSourceCurrentness = Literal[
    "current_concrete_source",
    "explicit_absence_marker",
    "historical_context_only",
    "stale_or_superseded",
    "unknown_needs_review",
]
SourceContentHorizon = Literal[
    "corpus_content_reference",
    "corpus_descriptor_only",
    "benchmark_descriptor_only",
    "customer_corpus_reference",
    "connector_identifier_only",
    "endpoint_identifier_only",
    "privacy_or_license_authority_source",
    "explicit_absence_marker",
]
SourcePermissionPosture = Literal[
    "permission_not_claimed",
    "permission_explicitly_absent",
    "permission_requires_later_authority",
    "permission_source_present_for_review_only",
    "not_applicable",
]
RequestedCorpusIngestionReviewHorizon = Literal[
    "corpus_ingestion_authority_review",
    "connector_access_authority_review",
    "customer_data_handling_authority_review",
    "benchmark_descriptor_ingestion_review",
    "repo_local_corpus_transfer_review",
    "future_family_only",
]
IngestionReviewPosture = Literal[
    "request_recorded_absence_only",
    "request_recorded_boundary_only",
    "eligible_for_corpus_ingestion_review",
    "blocked_by_missing_v81_handoff",
    "blocked_by_missing_corpus_source",
    "blocked_by_missing_privacy_authority",
    "blocked_by_missing_license_or_consent",
    "blocked_by_missing_customer_data_authority",
    "blocked_by_missing_connector_authority",
    "blocked_by_missing_endpoint_authority",
    "blocked_by_missing_transfer_boundary",
    "blocked_by_product_authority_gap",
    "blocked_by_benchmark_truth_guardrail",
    "blocked_by_graph_memory_authority_gap",
    "future_family_only",
    "rejected_out_of_scope",
]
IngestionRequirementPosture = Literal[
    "required_for_later_review",
    "present_for_review_only",
    "not_selected_in_v82a",
    "not_applicable",
    "blocked_by_missing_corpus_source",
    "blocked_by_missing_privacy_authority",
    "blocked_by_missing_license_or_consent",
    "blocked_by_missing_customer_data_authority",
    "blocked_by_missing_connector_authority",
    "blocked_by_missing_endpoint_authority",
    "blocked_by_missing_transfer_boundary",
    "blocked_by_product_authority_gap",
    "blocked_by_benchmark_truth_guardrail",
    "blocked_by_graph_memory_authority_gap",
    "future_family_only",
]
CorpusIngestionPosture = Literal[
    "no_corpus_ingestion_performed_by_v82",
    "corpus_ingestion_requires_later_family",
    "corpus_ingestion_forbidden_by_this_family",
]
DataTransferPosture = Literal[
    "no_data_transfer_performed_by_v82",
    "data_transfer_requires_later_family",
    "data_transfer_forbidden_by_this_family",
]
CustomerDataHandlingPosture = Literal[
    "no_customer_data_handling_performed_by_v82",
    "customer_data_handling_requires_later_family",
    "customer_data_handling_forbidden_by_this_family",
]
ConnectorActivationPosture = Literal[
    "no_connector_activation_performed_by_v82",
    "connector_activation_requires_later_family",
    "connector_activation_forbidden_by_this_family",
]
EndpointAccessPosture = Literal[
    "no_endpoint_access_performed_by_v82",
    "endpoint_access_requires_later_family",
    "endpoint_access_forbidden_by_this_family",
]
AdjudicationExecutionPosture = Literal[
    "no_cross_corpus_adjudication_performed_by_v82",
    "cross_corpus_adjudication_requires_later_family",
    "cross_corpus_adjudication_forbidden_by_this_family",
]
ForbiddenIngestionAction = Literal[
    "ingest_corpus",
    "import_external_data",
    "export_repo_data",
    "persist_imported_corpus_content",
    "handle_customer_data",
]
ForbiddenTransferAction = Literal[
    "transfer_corpus_data",
    "copy_external_corpus_content",
    "upload_customer_data",
    "download_external_corpus_content",
]
ForbiddenConnectorAction = Literal[
    "activate_connector",
    "fetch_external_corpus",
    "invoke_external_tool_for_corpus",
    "credentialed_connector_call",
]
ForbiddenEndpointAction = Literal[
    "access_endpoint",
    "mutate_endpoint",
    "credentialed_endpoint_call",
    "submit_payload_to_endpoint",
]
ForbiddenIngestionDownstreamAuthority = Literal[
    "corpus_ingestion",
    "external_data_import_export",
    "customer_data_handling",
    "data_transfer",
    "connector_activation",
    "endpoint_access",
    "cross_corpus_adjudication_execution",
    "product_authorization",
    "release_authority",
    "benchmark_truth",
    "imported_result_truth",
    "graph_memory_authority",
    "recursive_policy_amendment",
    "v83_selection",
]
AuthorityRequirementKind = Literal[
    "privacy_authority",
    "license_or_consent_authority",
    "customer_data_authority",
    "connector_authority",
    "endpoint_authority",
    "transfer_boundary_authority",
    "product_authority",
    "benchmark_truth_guardrail_authority",
    "graph_memory_authority",
]
RequiredBeforeSurface = Literal[
    "v82a_corpus_ingestion_review_request",
    "v82b_corpus_ingestion_preflight_contract",
    "future_corpus_ingestion_authority_review",
    "future_connector_activation_authority_review",
    "future_endpoint_access_authority_review",
    "future_data_transfer_authority_review",
    "future_retention_authority_review",
    "future_deletion_or_withdrawal_authority_review",
    "future_product_review",
    "future_graph_memory_review",
    "none",
]
AuthorityGapPosture = Literal[
    "authority_missing",
    "authority_requires_later_review",
    "authority_present_for_review_only",
    "authority_not_applicable",
    "authority_future_family_only",
]
NonIngestionPosture = Literal["non_ingestion_guardrail_active"]
NonTransferPosture = Literal["non_transfer_guardrail_active"]
NonConnectorPosture = Literal["non_connector_guardrail_active"]

PreflightPosture = Literal[
    "preflight_recorded_for_review_only",
    "preflight_blocked_by_missing_source",
    "preflight_blocked_by_missing_authority",
    "preflight_future_family_only",
    "preflight_rejected_out_of_scope",
]
PlanCompletenessPosture = Literal[
    "incomplete_for_review",
    "complete_for_review_only",
    "blocked_by_missing_source",
    "blocked_by_missing_authority",
    "blocked_by_missing_connector_boundary",
    "blocked_by_missing_monitoring",
    "blocked_by_missing_rollback",
    "future_family_only",
]
MonitoringRequirementPosture = Literal[
    "requirement_recorded_for_review_only",
    "missing_required_monitoring",
    "monitoring_requires_later_authority",
    "not_applicable",
]
RollbackRequirementPosture = Literal[
    "requirement_recorded_for_review_only",
    "missing_required_rollback",
    "rollback_requires_later_authority",
    "not_applicable",
]
PreflightObservationPosture = Literal[
    "requirements_recorded_only",
    "prior_authorized_preflight_observed",
    "preflight_not_observed",
    "preflight_observation_requires_later_authority",
]
EndpointRefPosture = Literal[
    "endpoint_identifier_only",
    "endpoint_access_requires_later_authority",
    "endpoint_access_forbidden_by_this_family",
    "endpoint_absent_or_unknown",
]
AllowedConnectorReviewAction = Literal[
    "describe_connector_boundary",
    "inspect_connector_metadata",
    "record_absence_posture",
    "request_later_connector_authority_review",
    "preserve_connector_gap",
]
AllowedDataReviewAction = Literal[
    "describe_data_boundary",
    "inspect_source_metadata",
    "record_absence_posture",
    "request_later_data_authority_review",
    "preserve_data_gap",
]
CorpusDataHandlingAuthorityKind = Literal[
    "privacy_authority",
    "license_or_consent_authority",
    "customer_data_authority",
    "connector_authority",
    "endpoint_authority",
    "transfer_authority",
    "retention_authority",
    "deletion_or_withdrawal_authority",
    "product_authority",
    "benchmark_truth_guardrail_authority",
    "graph_memory_authority",
]
DataHandlingAuthorityReviewPosture = Literal[
    "authority_missing",
    "authority_requires_later_review",
    "authority_present_for_review_only",
    "authority_not_applicable",
    "authority_future_family_only",
    "authority_rejected_out_of_scope",
]
PrivacyOrLicensePosture = Literal[
    "clearance_not_present",
    "clearance_requires_later_authority",
    "license_not_present",
    "license_requires_later_authority",
    "consent_requires_later_authority",
    "not_applicable",
    "explicitly_absent",
]
CorpusIngestionExceptionKind = Literal[
    "missing_corpus_source",
    "missing_privacy_authority",
    "missing_license_or_consent",
    "missing_customer_data_authority",
    "missing_connector_authority",
    "missing_endpoint_access_boundary",
    "missing_transfer_authority",
    "missing_retention_authority",
    "missing_deletion_or_withdrawal_authority",
    "missing_data_handling_clearance",
    "benchmark_truth_guardrail_gap",
    "product_authority_gap",
    "graph_memory_authority_gap",
    "stale_or_historical_corpus_source",
    "unknown_needs_review",
]
CorpusIngestionExceptionBlockingPosture = Literal[
    "blocking_exception",
    "warning_only",
    "carried_forward_blocker",
    "not_applicable",
]
CorpusIngestionExceptionVisibilityPosture = Literal[
    "visible_to_later_review",
    "visibility_requires_later_review",
    "not_applicable",
]
CorpusIngestionExceptionRequiredNextSurface = Literal[
    "future_corpus_ingestion_authority_review",
    "future_connector_activation_authority_review",
    "future_endpoint_access_authority_review",
    "future_data_transfer_authority_review",
    "future_retention_authority_review",
    "future_deletion_or_withdrawal_authority_review",
    "future_product_review",
    "future_graph_memory_review",
    "future_family_review",
    "none",
]

_V81_ELIGIBILITY_SOURCE_ROLES = {
    "v81_summary_source",
    "v81_handoff_source",
    "v81_closeout_source",
}
_CONTENT_SOURCE_ROLES = {
    "current_concrete_corpus_source",
    "current_customer_corpus_source",
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
_ELIGIBLE_CONTENT_HORIZONS = {
    "corpus_content_reference",
    "customer_corpus_reference",
}
_NON_ELIGIBLE_DESCRIPTOR_HORIZONS = {
    "corpus_descriptor_only",
    "benchmark_descriptor_only",
    "connector_identifier_only",
    "endpoint_identifier_only",
    "explicit_absence_marker",
}
_FORBIDDEN_INGESTION_ACTIONS = {
    "ingest_corpus",
    "import_external_data",
    "export_repo_data",
    "persist_imported_corpus_content",
    "handle_customer_data",
}
_FORBIDDEN_TRANSFER_ACTIONS = {
    "transfer_corpus_data",
    "copy_external_corpus_content",
    "upload_customer_data",
    "download_external_corpus_content",
}
_FORBIDDEN_CONNECTOR_ACTIONS = {
    "activate_connector",
    "fetch_external_corpus",
    "invoke_external_tool_for_corpus",
    "credentialed_connector_call",
}
_FORBIDDEN_ENDPOINT_ACTIONS = {
    "access_endpoint",
    "mutate_endpoint",
    "credentialed_endpoint_call",
    "submit_payload_to_endpoint",
}
_FORBIDDEN_DOWNSTREAM_AUTHORITIES = {
    "corpus_ingestion",
    "external_data_import_export",
    "customer_data_handling",
    "data_transfer",
    "connector_activation",
    "endpoint_access",
    "cross_corpus_adjudication_execution",
    "product_authorization",
    "release_authority",
    "benchmark_truth",
    "imported_result_truth",
    "graph_memory_authority",
    "recursive_policy_amendment",
    "v83_selection",
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


def _reject_v82_action_claim(value: str, *, field_name: str) -> str:
    lowered = value.lower()
    forbidden_patterns = [
        r"corpus (?:is |was |has been |being |gets |got )?(?:ingested|ingestion)",
        r"ingest corpus",
        r"data (?:is |was |has been |being |gets |got )?(?:transferred|transfer)",
        r"transfer data",
        r"customer data (?:is |was |has been |being |gets |got )?(?:handled|handling)",
        r"connector (?:is |was |has been |being |gets |got )?(?:activated|activation)",
        r"activate connector",
        r"endpoint (?:is |was |has been |being |gets |got )?(?:accessed|access)",
        r"access endpoint",
        (
            r"cross-corpus adjudication "
            r"(?:is |was |has been |being |gets |got )?(?:executed|execution)"
        ),
        r"benchmark truth",
        r"imported result truth",
        r"graph[- ]memory authority (?:is |was |has been |being |gets |got )?(?:created|granted)",
        r"living[- ]memory authority (?:is |was |has been |being |gets |got )?(?:created|granted)",
        r"authority (?:is |was |has been |being |gets |got )?granted",
        r"product (?:is |was |has been |being |gets |got )?(?:authorized|authorization)",
        r"release",
        r"v83 (?:is |was |has been |being |gets |got )?(?:selected|selection)",
    ]
    negation_markers = ("no ", "not ", "without ", "forbidden ", "non-")
    for pattern in forbidden_patterns:
        match = re.search(pattern, lowered)
        if match is None:
            continue
        prefix = lowered[max(0, match.start() - 32) : match.start()]
        if not any(marker in prefix for marker in negation_markers):
            raise ValueError(f"{field_name} may not carry corpus-ingestion action authority")
    return value


class RepoCorpusIngestionSourceRow(_CartographyBase):
    source_ref: str
    source_kind: CandidateSourceKind
    authority_layer: CandidateAuthorityLayer
    source_status: SourceStatus
    source_presence_posture: CandidateSourcePresencePosture
    ingestion_source_role: IngestionSourceRole
    source_horizon: str
    source_currentness: IngestionSourceCurrentness
    source_content_horizon: SourceContentHorizon
    source_permission_posture: SourcePermissionPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_corpus_ingestion_source_row(self) -> RepoCorpusIngestionSourceRow:
        _repo_ref(self.source_ref, field_name="source_ref")
        _non_empty(self.source_horizon, field_name="source_horizon")
        _reject_v82_action_claim(self.limitation_note, field_name="limitation_note")
        if (
            self.ingestion_source_role not in _ABSENCE_SOURCE_ROLES
            and self.source_presence_posture != "present"
        ):
            raise ValueError("non-absence corpus-ingestion source rows must be present")
        if (
            self.ingestion_source_role in _ABSENCE_SOURCE_ROLES
            and self.source_presence_posture == "present"
        ):
            raise ValueError("absence-marker corpus-ingestion rows must not be present sources")
        if (
            self.source_content_horizon == "explicit_absence_marker"
            and self.source_presence_posture == "present"
        ):
            raise ValueError("explicit absence content horizon must not be present")
        if (
            self.ingestion_source_role in _CONTEXT_SOURCE_ROLES
            and self.authority_layer == "lock"
            and self.source_kind in {"support_doc", "planning_doc"}
        ):
            raise ValueError("context source rows may not be marked as lock authority")
        if (
            self.source_permission_posture == "permission_source_present_for_review_only"
            and self.source_presence_posture != "present"
        ):
            raise ValueError("present permission posture requires a present source")
        return self


class RepoCorpusIngestionSourceIndex(_CartographyBase):
    schema: Literal["repo_corpus_ingestion_source_index@1"] = (
        REPO_CORPUS_INGESTION_SOURCE_INDEX_SCHEMA
    )
    corpus_ingestion_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    source_rows: list[RepoCorpusIngestionSourceRow] = Field(min_length=1)
    corpus_ingestion_source_summary: str

    @model_validator(mode="after")
    def _validate_corpus_ingestion_source_index(self) -> RepoCorpusIngestionSourceIndex:
        object.__setattr__(
            self,
            "source_rows",
            _sorted_unique_by_ref(self.source_rows, attr="source_ref", field_name="source_rows"),
        )
        _non_empty(self.review_id, field_name="review_id")
        _non_empty(self.snapshot_id, field_name="snapshot_id")
        _non_empty(self.source_set_id, field_name="source_set_id")
        _require_terms(
            self.corpus_ingestion_source_summary,
            field_name="corpus_ingestion_source_summary",
            terms=("eligibility", "absence", "no corpus ingestion", "no data transfer"),
        )
        expected_id = _surface_id(
            "repo_corpus_ingestion_source_index",
            self.schema,
            self.model_dump(mode="json"),
            "corpus_ingestion_source_index_id",
        )
        if self.corpus_ingestion_source_index_id != expected_id:
            raise ValueError("corpus_ingestion_source_index_id does not match canonical hash")
        return self


class RepoCorpusIngestionReviewRequestRow(_CartographyBase):
    corpus_ingestion_review_request_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    v81_summary_refs: list[str] = Field(default_factory=list)
    v81_handoff_refs: list[str] = Field(default_factory=list)
    v81_closeout_refs: list[str] = Field(default_factory=list)
    requested_corpus_ingestion_review_horizon: RequestedCorpusIngestionReviewHorizon
    ingestion_review_posture: IngestionReviewPosture
    corpus_source_currentness: IngestionSourceCurrentness
    required_privacy_posture: IngestionRequirementPosture
    required_license_posture: IngestionRequirementPosture
    required_customer_data_posture: IngestionRequirementPosture
    required_connector_posture: IngestionRequirementPosture
    required_endpoint_posture: IngestionRequirementPosture
    requested_preflight_horizon: RequestedCorpusIngestionReviewHorizon
    requested_connector_boundary_horizon: RequestedCorpusIngestionReviewHorizon
    requested_data_handling_authority_horizon: RequestedCorpusIngestionReviewHorizon
    guardrail_refs: list[str] = Field(min_length=1)
    corpus_ingestion_posture: CorpusIngestionPosture
    data_transfer_posture: DataTransferPosture
    customer_data_handling_posture: CustomerDataHandlingPosture
    connector_activation_posture: ConnectorActivationPosture
    endpoint_access_posture: EndpointAccessPosture
    adjudication_execution_posture: AdjudicationExecutionPosture
    odeu_lanes: list[OdeuLane] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_corpus_ingestion_request_row(
        self,
    ) -> RepoCorpusIngestionReviewRequestRow:
        _non_empty(
            self.corpus_ingestion_review_request_ref,
            field_name="corpus_ingestion_review_request_ref",
        )
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "v81_summary_refs",
            "v81_handoff_refs",
            "v81_closeout_refs",
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
        if self.corpus_ingestion_posture != "no_corpus_ingestion_performed_by_v82":
            raise ValueError("V82-A request rows must not ingest corpora")
        if self.data_transfer_posture != "no_data_transfer_performed_by_v82":
            raise ValueError("V82-A request rows must not transfer data")
        if self.customer_data_handling_posture != "no_customer_data_handling_performed_by_v82":
            raise ValueError("V82-A request rows must not handle customer data")
        if self.connector_activation_posture != "no_connector_activation_performed_by_v82":
            raise ValueError("V82-A request rows must not activate connectors")
        if self.endpoint_access_posture != "no_endpoint_access_performed_by_v82":
            raise ValueError("V82-A request rows must not access endpoints")
        if self.adjudication_execution_posture != "no_cross_corpus_adjudication_performed_by_v82":
            raise ValueError("V82-A request rows must not execute cross-corpus adjudication")
        _reject_v82_action_claim(self.limitation_note, field_name="limitation_note")
        if self.ingestion_review_posture == "eligible_for_corpus_ingestion_review":
            if self.corpus_source_currentness != "current_concrete_source":
                raise ValueError("eligible corpus-ingestion requests require current corpus source")
            if not (self.v81_summary_refs or self.v81_handoff_refs or self.v81_closeout_refs):
                raise ValueError("eligible corpus-ingestion requests require V81-C refs")
        if self.ingestion_review_posture == "request_recorded_absence_only":
            if self.corpus_source_currentness != "explicit_absence_marker":
                raise ValueError("absence-only ingestion requests require explicit source absence")
        if "product" in self.candidate_ref:
            if self.ingestion_review_posture not in {
                "blocked_by_product_authority_gap",
                "future_family_only",
                "rejected_out_of_scope",
            }:
                raise ValueError("product pressure must remain blocked in V82-A")
            if self.required_privacy_posture != "not_applicable":
                raise ValueError("product pressure cannot become ingestion authority")
        if self.ingestion_review_posture == "blocked_by_benchmark_truth_guardrail":
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("no benchmark truth",),
            )
        if self.ingestion_review_posture == "blocked_by_graph_memory_authority_gap":
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("no graph", "authority"),
            )
        return self


class RepoCorpusIngestionReviewRequest(_CartographyBase):
    schema: Literal["repo_corpus_ingestion_review_request@1"] = (
        REPO_CORPUS_INGESTION_REVIEW_REQUEST_SCHEMA
    )
    corpus_ingestion_review_request_id: str
    corpus_ingestion_source_index_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    request_rows: list[RepoCorpusIngestionReviewRequestRow] = Field(min_length=1)
    corpus_ingestion_review_summary: str

    @model_validator(mode="after")
    def _validate_corpus_ingestion_request(self) -> RepoCorpusIngestionReviewRequest:
        object.__setattr__(
            self,
            "request_rows",
            _sorted_unique_by_ref(
                self.request_rows,
                attr="corpus_ingestion_review_request_ref",
                field_name="request_rows",
            ),
        )
        _require_terms(
            self.corpus_ingestion_review_summary,
            field_name="corpus_ingestion_review_summary",
            terms=("review", "no corpus ingestion", "no data transfer", "no connector"),
        )
        expected_id = _surface_id(
            "repo_corpus_ingestion_review_request",
            self.schema,
            self.model_dump(mode="json"),
            "corpus_ingestion_review_request_id",
        )
        if self.corpus_ingestion_review_request_id != expected_id:
            raise ValueError("corpus_ingestion_review_request_id does not match canonical hash")
        return self


class RepoCorpusIngestionAuthorityRequirementRow(_CartographyBase):
    authority_requirement_ref: str
    candidate_ref: str
    authority_kind: AuthorityRequirementKind
    required_before_surface: RequiredBeforeSurface
    source_refs: list[str] = Field(min_length=1)
    source_presence_posture: CandidateSourcePresencePosture
    authority_gap_posture: AuthorityGapPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_authority_requirement_row(
        self,
    ) -> RepoCorpusIngestionAuthorityRequirementRow:
        _repo_ref(self.authority_requirement_ref, field_name="authority_requirement_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        object.__setattr__(
            self,
            "source_refs",
            _sorted_unique(self.source_refs, field_name="source_refs"),
        )
        _reject_v82_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("authority", "review"),
        )
        return self


class RepoCorpusIngestionNonTransferGuardrailRow(_CartographyBase):
    guardrail_ref: str
    candidate_ref: str
    source_refs: list[str] = Field(min_length=1)
    corpus_ingestion_review_request_refs: list[str] = Field(min_length=1)
    forbidden_ingestion_actions: list[ForbiddenIngestionAction] = Field(min_length=1)
    forbidden_transfer_actions: list[ForbiddenTransferAction] = Field(min_length=1)
    forbidden_connector_actions: list[ForbiddenConnectorAction] = Field(min_length=1)
    forbidden_endpoint_actions: list[ForbiddenEndpointAction] = Field(min_length=1)
    forbidden_downstream_authority: list[ForbiddenIngestionDownstreamAuthority] = Field(
        min_length=1
    )
    required_later_authority_refs: list[str] = Field(default_factory=list)
    authority_requirement_rows: list[RepoCorpusIngestionAuthorityRequirementRow] = Field(
        default_factory=list
    )
    non_ingestion_posture: NonIngestionPosture
    non_transfer_posture: NonTransferPosture
    non_connector_posture: NonConnectorPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_non_transfer_guardrail_row(
        self,
    ) -> RepoCorpusIngestionNonTransferGuardrailRow:
        _non_empty(self.guardrail_ref, field_name="guardrail_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "source_refs",
            "corpus_ingestion_review_request_refs",
            "forbidden_ingestion_actions",
            "forbidden_transfer_actions",
            "forbidden_connector_actions",
            "forbidden_endpoint_actions",
            "forbidden_downstream_authority",
            "required_later_authority_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
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
        missing_ingestion = _FORBIDDEN_INGESTION_ACTIONS.difference(
            self.forbidden_ingestion_actions
        )
        if missing_ingestion:
            raise ValueError("corpus-ingestion guardrail omits forbidden ingestion actions")
        missing_transfer = _FORBIDDEN_TRANSFER_ACTIONS.difference(self.forbidden_transfer_actions)
        if missing_transfer:
            raise ValueError("corpus-ingestion guardrail omits forbidden transfer actions")
        missing_connector = _FORBIDDEN_CONNECTOR_ACTIONS.difference(
            self.forbidden_connector_actions
        )
        if missing_connector:
            raise ValueError("corpus-ingestion guardrail omits forbidden connector actions")
        missing_endpoint = _FORBIDDEN_ENDPOINT_ACTIONS.difference(self.forbidden_endpoint_actions)
        if missing_endpoint:
            raise ValueError("corpus-ingestion guardrail omits forbidden endpoint actions")
        missing_authority = _FORBIDDEN_DOWNSTREAM_AUTHORITIES.difference(
            self.forbidden_downstream_authority
        )
        if missing_authority:
            raise ValueError("corpus-ingestion guardrail omits forbidden downstream authority")
        _reject_v82_action_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("no corpus ingestion", "no data transfer", "no connector"),
        )
        return self


class RepoCorpusIngestionNonTransferGuardrail(_CartographyBase):
    schema: Literal["repo_corpus_ingestion_non_transfer_guardrail@1"] = (
        REPO_CORPUS_INGESTION_NON_TRANSFER_GUARDRAIL_SCHEMA
    )
    corpus_ingestion_non_transfer_guardrail_id: str
    corpus_ingestion_review_request_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    guardrail_rows: list[RepoCorpusIngestionNonTransferGuardrailRow] = Field(min_length=1)
    non_transfer_summary: str

    @model_validator(mode="after")
    def _validate_non_transfer_guardrail(
        self,
    ) -> RepoCorpusIngestionNonTransferGuardrail:
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
            self.non_transfer_summary,
            field_name="non_transfer_summary",
            terms=("no corpus ingestion", "no data transfer", "no connector"),
        )
        expected_id = _surface_id(
            "repo_corpus_ingestion_non_transfer_guardrail",
            self.schema,
            self.model_dump(mode="json"),
            "corpus_ingestion_non_transfer_guardrail_id",
        )
        if self.corpus_ingestion_non_transfer_guardrail_id != expected_id:
            raise ValueError(
                "corpus_ingestion_non_transfer_guardrail_id does not match canonical hash"
            )
        return self


def derive_v82a_repo_corpus_ingestion_source_index(
    *, repo_root: Path | None = None
) -> RepoCorpusIngestionSourceIndex:
    _ = repo_root
    payload = {
        "schema": REPO_CORPUS_INGESTION_SOURCE_INDEX_SCHEMA,
        "corpus_ingestion_source_index_id": "",
        "review_id": "review:v82a:corpus-ingestion-review",
        "snapshot_id": "vNext+229-cross-corpus-governance-closeout",
        "source_set_id": "source-set:v82a:released-v81c-corpus-ingestion-pressure",
        "source_rows": [
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus229/"
                    "repo_cross_corpus_governance_summary_v229_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "ingestion_source_role": "v81_summary_source",
                "source_horizon": "Released V81-C cross-corpus governance summary rows.",
                "source_currentness": "current_concrete_source",
                "source_content_horizon": "corpus_descriptor_only",
                "source_permission_posture": "permission_not_claimed",
                "limitation_note": (
                    "Summary substrate for corpus-ingestion review only; "
                    "no corpus ingestion and no data transfer."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus229/"
                    "repo_post_cross_corpus_review_handoff_v229_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "ingestion_source_role": "v81_handoff_source",
                "source_horizon": "Released V81-C post-cross-corpus-review handoff rows.",
                "source_currentness": "current_concrete_source",
                "source_content_horizon": "corpus_descriptor_only",
                "source_permission_posture": "permission_not_claimed",
                "limitation_note": (
                    "Handoff substrate for corpus-ingestion review only; "
                    "no corpus ingestion and no connector activation."
                ),
            },
            {
                "source_ref": _source_path(
                    "apps/api/fixtures/repo_description/vnext_plus229/"
                    "repo_cross_corpus_governance_family_closeout_alignment_v229_reference.json"
                ),
                "source_kind": "fixture_file",
                "authority_layer": "fixture",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "ingestion_source_role": "v81_closeout_source",
                "source_horizon": "Released V81 family closeout alignment rows.",
                "source_currentness": "current_concrete_source",
                "source_content_horizon": "corpus_descriptor_only",
                "source_permission_posture": "permission_not_claimed",
                "limitation_note": (
                    "Family closeout context for review boundary only; "
                    "no corpus ingestion and no data transfer."
                ),
            },
            {
                "source_ref": _source_path(
                    "docs/support/arc_series_mapping/"
                    "V68_V69_V70_V71_V72_V73_V74_V75_V76_V77_V78_V79_V80_V81_"
                    "COMBINED_DOGFOOD_TEST_v0.json"
                ),
                "source_kind": "support_doc",
                "authority_layer": "support",
                "source_status": "integrated_shaping_source",
                "source_presence_posture": "present",
                "ingestion_source_role": "dogfood_context",
                "source_horizon": "Combined V68-V81 dogfood context.",
                "source_currentness": "current_concrete_source",
                "source_content_horizon": "corpus_descriptor_only",
                "source_permission_posture": "permission_not_claimed",
                "limitation_note": (
                    "Context source only and not sufficient for eligibility; "
                    "no corpus ingestion and no data transfer."
                ),
            },
            {
                "source_ref": "corpus-source:ingestion:current:absent",
                "source_kind": "external_artifact",
                "authority_layer": "support",
                "source_status": "review_pending_input",
                "source_presence_posture": "external_unavailable",
                "ingestion_source_role": "explicit_corpus_absence_marker",
                "source_horizon": "Current concrete corpus content source is absent.",
                "source_currentness": "explicit_absence_marker",
                "source_content_horizon": "explicit_absence_marker",
                "source_permission_posture": "permission_explicitly_absent",
                "limitation_note": "Explicit corpus-source absence marker; no corpus ingestion.",
            },
            {
                "source_ref": "privacy-authority:corpus-ingestion:current:absent",
                "source_kind": "external_artifact",
                "authority_layer": "support",
                "source_status": "review_pending_input",
                "source_presence_posture": "external_unavailable",
                "ingestion_source_role": "explicit_authority_absence_marker",
                "source_horizon": "Privacy authority source is absent.",
                "source_currentness": "explicit_absence_marker",
                "source_content_horizon": "explicit_absence_marker",
                "source_permission_posture": "permission_explicitly_absent",
                "limitation_note": "Explicit privacy-authority absence marker; no data transfer.",
            },
            {
                "source_ref": "license-authority:corpus-ingestion:current:absent",
                "source_kind": "external_artifact",
                "authority_layer": "support",
                "source_status": "review_pending_input",
                "source_presence_posture": "external_unavailable",
                "ingestion_source_role": "explicit_authority_absence_marker",
                "source_horizon": "License or consent authority source is absent.",
                "source_currentness": "explicit_absence_marker",
                "source_content_horizon": "explicit_absence_marker",
                "source_permission_posture": "permission_explicitly_absent",
                "limitation_note": (
                    "Explicit license-authority absence marker; no corpus ingestion."
                ),
            },
            {
                "source_ref": "connector-authority:corpus-ingestion:current:absent",
                "source_kind": "external_artifact",
                "authority_layer": "support",
                "source_status": "review_pending_input",
                "source_presence_posture": "external_unavailable",
                "ingestion_source_role": "explicit_authority_absence_marker",
                "source_horizon": "Connector authority source is absent.",
                "source_currentness": "explicit_absence_marker",
                "source_content_horizon": "explicit_absence_marker",
                "source_permission_posture": "permission_explicitly_absent",
                "limitation_note": (
                    "Explicit connector-authority absence marker; no connector activation."
                ),
            },
            {
                "source_ref": "endpoint-authority:corpus-ingestion:current:absent",
                "source_kind": "external_artifact",
                "authority_layer": "support",
                "source_status": "review_pending_input",
                "source_presence_posture": "external_unavailable",
                "ingestion_source_role": "explicit_authority_absence_marker",
                "source_horizon": "Endpoint authority source is absent.",
                "source_currentness": "explicit_absence_marker",
                "source_content_horizon": "explicit_absence_marker",
                "source_permission_posture": "permission_explicitly_absent",
                "limitation_note": (
                    "Explicit endpoint-authority absence marker; no endpoint access."
                ),
            },
            {
                "source_ref": "transfer-boundary:corpus-ingestion:current:absent",
                "source_kind": "external_artifact",
                "authority_layer": "support",
                "source_status": "review_pending_input",
                "source_presence_posture": "external_unavailable",
                "ingestion_source_role": "explicit_authority_absence_marker",
                "source_horizon": "Transfer boundary authority source is absent.",
                "source_currentness": "explicit_absence_marker",
                "source_content_horizon": "explicit_absence_marker",
                "source_permission_posture": "permission_explicitly_absent",
                "limitation_note": "Explicit transfer-boundary absence marker; no data transfer.",
            },
            {
                "source_ref": "product-authority:corpus-ingestion:current:absent",
                "source_kind": "external_artifact",
                "authority_layer": "support",
                "source_status": "review_pending_input",
                "source_presence_posture": "external_unavailable",
                "ingestion_source_role": "explicit_authority_absence_marker",
                "source_horizon": "Product authority source is absent for corpus-ingestion review.",
                "source_currentness": "explicit_absence_marker",
                "source_content_horizon": "explicit_absence_marker",
                "source_permission_posture": "permission_explicitly_absent",
                "limitation_note": (
                    "Explicit product-authority absence marker; no product authority."
                ),
            },
        ],
        "corpus_ingestion_source_summary": (
            "Corpus-ingestion source rows separate eligibility from absence and "
            "context with no corpus ingestion and no data transfer."
        ),
    }
    payload["source_rows"] = sorted(payload["source_rows"], key=lambda row: row["source_ref"])
    payload["corpus_ingestion_source_index_id"] = _surface_id(
        "repo_corpus_ingestion_source_index",
        REPO_CORPUS_INGESTION_SOURCE_INDEX_SCHEMA,
        payload,
        "corpus_ingestion_source_index_id",
    )
    return RepoCorpusIngestionSourceIndex.model_validate(payload)


def derive_v82a_repo_corpus_ingestion_review_request(
    *,
    repo_root: Path | None = None,
    corpus_ingestion_source_index: RepoCorpusIngestionSourceIndex | None = None,
) -> RepoCorpusIngestionReviewRequest:
    _ = repo_root
    source_index = corpus_ingestion_source_index or derive_v82a_repo_corpus_ingestion_source_index()
    source_refs = [row.source_ref for row in source_index.source_rows]
    self_candidate = "candidate:internal:self_evidencing_workflow_type_emergence"
    product_candidate = "candidate:internal:typed_adjudication_product_wedge"
    payload = {
        "schema": REPO_CORPUS_INGESTION_REVIEW_REQUEST_SCHEMA,
        "corpus_ingestion_review_request_id": "",
        "corpus_ingestion_source_index_id": source_index.corpus_ingestion_source_index_id,
        "review_id": source_index.review_id,
        "snapshot_id": source_index.snapshot_id,
        "source_set_id": source_index.source_set_id,
        "request_rows": [
            {
                "corpus_ingestion_review_request_ref": (
                    "corpus-ingestion-review:v82a:self-evidencing:source-absent"
                ),
                "candidate_ref": self_candidate,
                "source_refs": sorted(source_refs),
                "v81_summary_refs": [
                    "cross-corpus-summary:v81c:self_evidencing_workflow_type_emergence"
                ],
                "v81_handoff_refs": [
                    "post-cross-corpus-handoff:v81c:self_evidencing_workflow_type_emergence"
                ],
                "v81_closeout_refs": [
                    "repo_cross_corpus_governance_family_closeout_alignment_9fb999b059ad5e0d04a9e72c"
                ],
                "requested_corpus_ingestion_review_horizon": ("corpus_ingestion_authority_review"),
                "ingestion_review_posture": "blocked_by_missing_corpus_source",
                "corpus_source_currentness": "explicit_absence_marker",
                "required_privacy_posture": "blocked_by_missing_privacy_authority",
                "required_license_posture": "blocked_by_missing_license_or_consent",
                "required_customer_data_posture": "not_applicable",
                "required_connector_posture": "blocked_by_missing_connector_authority",
                "required_endpoint_posture": "blocked_by_missing_endpoint_authority",
                "requested_preflight_horizon": "corpus_ingestion_authority_review",
                "requested_connector_boundary_horizon": "connector_access_authority_review",
                "requested_data_handling_authority_horizon": (
                    "customer_data_handling_authority_review"
                ),
                "guardrail_refs": ["guardrail:v82a:self-evidencing:non-transfer"],
                "corpus_ingestion_posture": "no_corpus_ingestion_performed_by_v82",
                "data_transfer_posture": "no_data_transfer_performed_by_v82",
                "customer_data_handling_posture": ("no_customer_data_handling_performed_by_v82"),
                "connector_activation_posture": "no_connector_activation_performed_by_v82",
                "endpoint_access_posture": "no_endpoint_access_performed_by_v82",
                "adjudication_execution_posture": ("no_cross_corpus_adjudication_performed_by_v82"),
                "odeu_lanes": ["deontic", "epistemic", "utility"],
                "limitation_note": (
                    "Corpus-ingestion review is blocked by missing corpus source, "
                    "privacy, license, connector, endpoint, and transfer authority "
                    "with no corpus ingestion, no data transfer, no connector "
                    "activation, no endpoint access, and no release."
                ),
            },
            {
                "corpus_ingestion_review_request_ref": (
                    "corpus-ingestion-review:v82a:product-wedge:product-blocked"
                ),
                "candidate_ref": product_candidate,
                "source_refs": sorted(source_refs),
                "v81_summary_refs": ["cross-corpus-summary:v81c:typed_adjudication_product_wedge"],
                "v81_handoff_refs": [
                    "post-cross-corpus-handoff:v81c:typed_adjudication_product_wedge"
                ],
                "v81_closeout_refs": [
                    "repo_cross_corpus_governance_family_closeout_alignment_9fb999b059ad5e0d04a9e72c"
                ],
                "requested_corpus_ingestion_review_horizon": "future_family_only",
                "ingestion_review_posture": "blocked_by_product_authority_gap",
                "corpus_source_currentness": "explicit_absence_marker",
                "required_privacy_posture": "not_applicable",
                "required_license_posture": "not_applicable",
                "required_customer_data_posture": "not_applicable",
                "required_connector_posture": "not_applicable",
                "required_endpoint_posture": "not_applicable",
                "requested_preflight_horizon": "future_family_only",
                "requested_connector_boundary_horizon": "future_family_only",
                "requested_data_handling_authority_horizon": "future_family_only",
                "guardrail_refs": ["guardrail:v82a:product-wedge:non-transfer"],
                "corpus_ingestion_posture": "no_corpus_ingestion_performed_by_v82",
                "data_transfer_posture": "no_data_transfer_performed_by_v82",
                "customer_data_handling_posture": ("no_customer_data_handling_performed_by_v82"),
                "connector_activation_posture": "no_connector_activation_performed_by_v82",
                "endpoint_access_posture": "no_endpoint_access_performed_by_v82",
                "adjudication_execution_posture": ("no_cross_corpus_adjudication_performed_by_v82"),
                "odeu_lanes": ["deontic", "utility"],
                "limitation_note": (
                    "Product-pressure corpus-ingestion row remains product blocked "
                    "with no corpus ingestion, no data transfer, no connector "
                    "activation, no endpoint access, and no release."
                ),
            },
        ],
        "corpus_ingestion_review_summary": (
            "Corpus-ingestion review requests are review only: no corpus ingestion, "
            "no data transfer, no connector activation, no endpoint access, "
            "no cross-corpus adjudication, and no release."
        ),
    }
    payload["request_rows"] = sorted(
        payload["request_rows"],
        key=lambda row: row["corpus_ingestion_review_request_ref"],
    )
    payload["corpus_ingestion_review_request_id"] = _surface_id(
        "repo_corpus_ingestion_review_request",
        REPO_CORPUS_INGESTION_REVIEW_REQUEST_SCHEMA,
        payload,
        "corpus_ingestion_review_request_id",
    )
    return RepoCorpusIngestionReviewRequest.model_validate(payload)


def derive_v82a_repo_corpus_ingestion_non_transfer_guardrail(
    *,
    repo_root: Path | None = None,
    corpus_ingestion_review_request: RepoCorpusIngestionReviewRequest | None = None,
) -> RepoCorpusIngestionNonTransferGuardrail:
    _ = repo_root
    request = corpus_ingestion_review_request or derive_v82a_repo_corpus_ingestion_review_request()
    grouped_rows: dict[str, dict[str, object]] = {}
    for request_row in request.request_rows:
        for guardrail_ref in request_row.guardrail_refs:
            existing = grouped_rows.setdefault(
                guardrail_ref,
                {
                    "guardrail_ref": guardrail_ref,
                    "candidate_ref": request_row.candidate_ref,
                    "source_refs": [],
                    "corpus_ingestion_review_request_refs": [],
                    "forbidden_ingestion_actions": sorted(_FORBIDDEN_INGESTION_ACTIONS),
                    "forbidden_transfer_actions": sorted(_FORBIDDEN_TRANSFER_ACTIONS),
                    "forbidden_connector_actions": sorted(_FORBIDDEN_CONNECTOR_ACTIONS),
                    "forbidden_endpoint_actions": sorted(_FORBIDDEN_ENDPOINT_ACTIONS),
                    "forbidden_downstream_authority": sorted(_FORBIDDEN_DOWNSTREAM_AUTHORITIES),
                    "required_later_authority_refs": [],
                    "authority_requirement_rows": [],
                    "non_ingestion_posture": "non_ingestion_guardrail_active",
                    "non_transfer_posture": "non_transfer_guardrail_active",
                    "non_connector_posture": "non_connector_guardrail_active",
                    "limitation_note": (
                        "This V82-A row is review only: no corpus ingestion, "
                        "no data transfer, no customer data handling, no connector "
                        "activation, no endpoint access, no cross-corpus adjudication, "
                        "no product authorization, and no release."
                    ),
                },
            )
            if existing["candidate_ref"] != request_row.candidate_ref:
                raise ValueError("corpus-ingestion guardrail cannot merge candidates")
            existing["corpus_ingestion_review_request_refs"] = sorted(
                {
                    *existing["corpus_ingestion_review_request_refs"],
                    request_row.corpus_ingestion_review_request_ref,
                }
            )
            existing["source_refs"] = sorted({*existing["source_refs"], *request_row.source_refs})
            authority_rows = list(existing["authority_requirement_rows"])
            if "product" in request_row.candidate_ref:
                authority_rows.append(
                    {
                        "authority_requirement_ref": "authority:v82a:product-wedge:product-review",
                        "candidate_ref": request_row.candidate_ref,
                        "authority_kind": "product_authority",
                        "required_before_surface": "future_product_review",
                        "source_refs": ["product-authority:corpus-ingestion:current:absent"],
                        "source_presence_posture": "external_unavailable",
                        "authority_gap_posture": "authority_requires_later_review",
                        "limitation_note": (
                            "Product authority is required for later review; "
                            "no corpus ingestion and no product authority granted."
                        ),
                    }
                )
                existing["required_later_authority_refs"] = sorted(
                    {
                        *existing["required_later_authority_refs"],
                        "authority:v82a:product-wedge:product-review",
                    }
                )
            if request_row.ingestion_review_posture in {
                "blocked_by_missing_corpus_source",
                "request_recorded_absence_only",
            }:
                for source_ref, authority_kind in (
                    ("corpus-source:ingestion:current:absent", "transfer_boundary_authority"),
                    ("privacy-authority:corpus-ingestion:current:absent", "privacy_authority"),
                    (
                        "license-authority:corpus-ingestion:current:absent",
                        "license_or_consent_authority",
                    ),
                    (
                        "connector-authority:corpus-ingestion:current:absent",
                        "connector_authority",
                    ),
                    ("endpoint-authority:corpus-ingestion:current:absent", "endpoint_authority"),
                    (
                        "transfer-boundary:corpus-ingestion:current:absent",
                        "transfer_boundary_authority",
                    ),
                ):
                    authority_ref = f"authority:v82a:self-evidencing:{source_ref}"
                    authority_rows.append(
                        {
                            "authority_requirement_ref": authority_ref,
                            "candidate_ref": request_row.candidate_ref,
                            "authority_kind": authority_kind,
                            "required_before_surface": "future_corpus_ingestion_authority_review",
                            "source_refs": [source_ref],
                            "source_presence_posture": "external_unavailable",
                            "authority_gap_posture": "authority_requires_later_review",
                            "limitation_note": (
                                "Authority source is required for later review; "
                                "no corpus ingestion and no data transfer."
                            ),
                        }
                    )
                    existing["required_later_authority_refs"] = sorted(
                        {*existing["required_later_authority_refs"], authority_ref}
                    )
            deduped = {row["authority_requirement_ref"]: row for row in authority_rows}
            existing["authority_requirement_rows"] = sorted(
                deduped.values(),
                key=lambda row: row["authority_requirement_ref"],
            )
    payload = {
        "schema": REPO_CORPUS_INGESTION_NON_TRANSFER_GUARDRAIL_SCHEMA,
        "corpus_ingestion_non_transfer_guardrail_id": "",
        "corpus_ingestion_review_request_id": request.corpus_ingestion_review_request_id,
        "review_id": request.review_id,
        "snapshot_id": request.snapshot_id,
        "source_set_id": request.source_set_id,
        "guardrail_rows": sorted(grouped_rows.values(), key=lambda row: row["guardrail_ref"]),
        "non_transfer_summary": (
            "Corpus-ingestion non-transfer guardrails preserve review only: "
            "no corpus ingestion, no data transfer, no connector activation, "
            "no endpoint access, and no release."
        ),
    }
    payload["corpus_ingestion_non_transfer_guardrail_id"] = _surface_id(
        "repo_corpus_ingestion_non_transfer_guardrail",
        REPO_CORPUS_INGESTION_NON_TRANSFER_GUARDRAIL_SCHEMA,
        payload,
        "corpus_ingestion_non_transfer_guardrail_id",
    )
    return RepoCorpusIngestionNonTransferGuardrail.model_validate(payload)


def validate_v82a_corpus_ingestion_review_bundle(
    *,
    corpus_ingestion_source_index: RepoCorpusIngestionSourceIndex,
    corpus_ingestion_review_request: RepoCorpusIngestionReviewRequest,
    corpus_ingestion_non_transfer_guardrail: RepoCorpusIngestionNonTransferGuardrail,
) -> None:
    if (
        corpus_ingestion_review_request.corpus_ingestion_source_index_id
        != corpus_ingestion_source_index.corpus_ingestion_source_index_id
    ):
        raise ValueError("corpus-ingestion request must reference the source index")
    if (
        corpus_ingestion_review_request.review_id,
        corpus_ingestion_review_request.snapshot_id,
        corpus_ingestion_review_request.source_set_id,
    ) != (
        corpus_ingestion_source_index.review_id,
        corpus_ingestion_source_index.snapshot_id,
        corpus_ingestion_source_index.source_set_id,
    ):
        raise ValueError("corpus-ingestion request provenance must match source index")
    if (
        corpus_ingestion_non_transfer_guardrail.corpus_ingestion_review_request_id
        != corpus_ingestion_review_request.corpus_ingestion_review_request_id
    ):
        raise ValueError("corpus-ingestion guardrail must reference the request surface")
    if (
        corpus_ingestion_non_transfer_guardrail.review_id,
        corpus_ingestion_non_transfer_guardrail.snapshot_id,
        corpus_ingestion_non_transfer_guardrail.source_set_id,
    ) != (
        corpus_ingestion_review_request.review_id,
        corpus_ingestion_review_request.snapshot_id,
        corpus_ingestion_review_request.source_set_id,
    ):
        raise ValueError("corpus-ingestion guardrail provenance must match request")

    source_roles = {
        row.source_ref: row.ingestion_source_role
        for row in corpus_ingestion_source_index.source_rows
    }
    source_horizons = {
        row.source_ref: row.source_content_horizon
        for row in corpus_ingestion_source_index.source_rows
    }
    known_sources = set(source_roles)
    guardrail_rows = {
        row.guardrail_ref: row for row in corpus_ingestion_non_transfer_guardrail.guardrail_rows
    }
    for request_row in corpus_ingestion_review_request.request_rows:
        if any(source_ref not in known_sources for source_ref in request_row.source_refs):
            raise ValueError("corpus-ingestion request source refs must be known")
        roles = {source_roles[source_ref] for source_ref in request_row.source_refs}
        horizons = {source_horizons[source_ref] for source_ref in request_row.source_refs}
        if request_row.ingestion_review_posture == "eligible_for_corpus_ingestion_review":
            if not roles.intersection(_V81_ELIGIBILITY_SOURCE_ROLES):
                raise ValueError(
                    "eligible corpus-ingestion requests require released V81-C sources"
                )
            if not roles.intersection(_CONTENT_SOURCE_ROLES):
                raise ValueError(
                    "eligible corpus-ingestion requests require concrete corpus source"
                )
            if not horizons.intersection(_ELIGIBLE_CONTENT_HORIZONS):
                raise ValueError("eligible corpus-ingestion requests require corpus content source")
            if horizons.issubset(_NON_ELIGIBLE_DESCRIPTOR_HORIZONS):
                raise ValueError("descriptor or identifier sources cannot create eligibility")
            if request_row.corpus_source_currentness != "current_concrete_source":
                raise ValueError("eligible corpus-ingestion requests require current corpus source")
        if request_row.guardrail_refs:
            for guardrail_ref in request_row.guardrail_refs:
                guardrail = guardrail_rows.get(guardrail_ref)
                if guardrail is None:
                    raise ValueError("corpus-ingestion request guardrail refs must be known")
                if guardrail.candidate_ref != request_row.candidate_ref:
                    raise ValueError("corpus-ingestion guardrail candidate must match request")
                if (
                    request_row.corpus_ingestion_review_request_ref
                    not in guardrail.corpus_ingestion_review_request_refs
                ):
                    raise ValueError("corpus-ingestion guardrail must reference request row")
    request_rows = {
        row.corpus_ingestion_review_request_ref: row
        for row in corpus_ingestion_review_request.request_rows
    }
    for guardrail_row in corpus_ingestion_non_transfer_guardrail.guardrail_rows:
        if any(source_ref not in known_sources for source_ref in guardrail_row.source_refs):
            raise ValueError("corpus-ingestion guardrail source refs must be known")
        for request_ref in guardrail_row.corpus_ingestion_review_request_refs:
            request_row = request_rows.get(request_ref)
            if request_row is None:
                raise ValueError("corpus-ingestion guardrail request refs must be known")
            if request_row.candidate_ref != guardrail_row.candidate_ref:
                raise ValueError("corpus-ingestion guardrail request candidate must match")
        authority_refs = {
            row.authority_requirement_ref for row in guardrail_row.authority_requirement_rows
        }
        for authority_row in guardrail_row.authority_requirement_rows:
            if authority_row.candidate_ref != guardrail_row.candidate_ref:
                raise ValueError(
                    "corpus-ingestion authority requirement candidate must match guardrail"
                )
            if any(source_ref not in known_sources for source_ref in authority_row.source_refs):
                raise ValueError("corpus-ingestion authority requirement source refs must be known")
        if any(ref not in authority_refs for ref in guardrail_row.required_later_authority_refs):
            raise ValueError(
                "corpus-ingestion required later authority refs must resolve "
                "to same-row authority requirements"
            )


def derive_v82a_corpus_ingestion_review_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoCorpusIngestionSourceIndex,
    RepoCorpusIngestionReviewRequest,
    RepoCorpusIngestionNonTransferGuardrail,
]:
    source_index = derive_v82a_repo_corpus_ingestion_source_index(repo_root=repo_root)
    request = derive_v82a_repo_corpus_ingestion_review_request(
        repo_root=repo_root,
        corpus_ingestion_source_index=source_index,
    )
    guardrail = derive_v82a_repo_corpus_ingestion_non_transfer_guardrail(
        repo_root=repo_root,
        corpus_ingestion_review_request=request,
    )
    validate_v82a_corpus_ingestion_review_bundle(
        corpus_ingestion_source_index=source_index,
        corpus_ingestion_review_request=request,
        corpus_ingestion_non_transfer_guardrail=guardrail,
    )
    return source_index, request, guardrail


def _v82b_preflight_ref(request_row: RepoCorpusIngestionReviewRequestRow) -> str:
    if "product" in request_row.candidate_ref:
        return "preflight:v82b:product-wedge:product-blocked"
    return "preflight:v82b:self-evidencing:source-authority-blocked"


def _v82b_connector_boundary_ref(request_row: RepoCorpusIngestionReviewRequestRow) -> str:
    if "product" in request_row.candidate_ref:
        return "connector-boundary:v82b:product-wedge:future-family"
    return "connector-boundary:v82b:self-evidencing:connector-absent"


def _v82b_authority_review_specs(
    request_row: RepoCorpusIngestionReviewRequestRow,
) -> list[tuple[str, str, str, str, str]]:
    if "product" in request_row.candidate_ref:
        return [
            (
                "authority-review:v82b:product-wedge:product-authority-gap",
                "product_authority",
                "product-authority:corpus-ingestion:current:absent",
                "future_product_review",
                "not_applicable",
            )
        ]
    specs = [
        (
            "authority-review:v82b:self-evidencing:connector-missing",
            "connector_authority",
            "connector-authority:corpus-ingestion:current:absent",
            "future_connector_activation_authority_review",
            "explicitly_absent",
        ),
        (
            "authority-review:v82b:self-evidencing:deletion-withdrawal-missing",
            "deletion_or_withdrawal_authority",
            "transfer-boundary:corpus-ingestion:current:absent",
            "future_deletion_or_withdrawal_authority_review",
            "explicitly_absent",
        ),
        (
            "authority-review:v82b:self-evidencing:endpoint-missing",
            "endpoint_authority",
            "endpoint-authority:corpus-ingestion:current:absent",
            "future_endpoint_access_authority_review",
            "explicitly_absent",
        ),
        (
            "authority-review:v82b:self-evidencing:license-missing",
            "license_or_consent_authority",
            "license-authority:corpus-ingestion:current:absent",
            "future_corpus_ingestion_authority_review",
            "license_not_present",
        ),
        (
            "authority-review:v82b:self-evidencing:privacy-missing",
            "privacy_authority",
            "privacy-authority:corpus-ingestion:current:absent",
            "future_corpus_ingestion_authority_review",
            "clearance_not_present",
        ),
        (
            "authority-review:v82b:self-evidencing:retention-missing",
            "retention_authority",
            "transfer-boundary:corpus-ingestion:current:absent",
            "future_retention_authority_review",
            "explicitly_absent",
        ),
        (
            "authority-review:v82b:self-evidencing:transfer-missing",
            "transfer_authority",
            "transfer-boundary:corpus-ingestion:current:absent",
            "future_data_transfer_authority_review",
            "explicitly_absent",
        ),
    ]
    return sorted(specs, key=lambda spec: spec[0])


def _v82b_authority_review_refs(request_row: RepoCorpusIngestionReviewRequestRow) -> list[str]:
    return [spec[0] for spec in _v82b_authority_review_specs(request_row)]


def _reject_v82b_permission_claim(value: str, *, field_name: str) -> str:
    lowered = value.lower()
    forbidden_fragments = (
        "preflight passed",
        "preflight success",
        "monitoring observed",
        "monitoring succeeded",
        "observed monitoring",
        "rollback verified",
        "verified rollback",
        "clearance granted",
        "permission granted",
        "connector activated",
        "endpoint accessed",
        "data handled",
        "corpus imported",
    )
    negation_markers = ("no ", "not ", "without ", "forbidden ", "requires later ")
    for fragment in forbidden_fragments:
        index = lowered.find(fragment)
        if index == -1:
            continue
        prefix = lowered[max(0, index - 32) : index]
        if not any(marker in prefix for marker in negation_markers):
            raise ValueError(f"{field_name} may not claim V82-B permission or observation")
    return _reject_v82_action_claim(value, field_name=field_name)


class RepoCorpusIngestionPreflightContractRow(_CartographyBase):
    preflight_contract_ref: str
    candidate_ref: str
    request_refs: list[str] = Field(min_length=1)
    source_refs: list[str] = Field(min_length=1)
    guardrail_refs: list[str] = Field(min_length=1)
    upstream_corpus_boundary_refs: list[str] = Field(default_factory=list)
    upstream_provenance_refs: list[str] = Field(default_factory=list)
    connector_boundary_refs: list[str] = Field(default_factory=list)
    data_handling_authority_refs: list[str] = Field(default_factory=list)
    monitoring_requirement_posture: MonitoringRequirementPosture
    rollback_requirement_posture: RollbackRequirementPosture
    preflight_observation_posture: PreflightObservationPosture
    preflight_posture: PreflightPosture
    plan_completeness_posture: PlanCompletenessPosture
    corpus_ingestion_posture: CorpusIngestionPosture
    data_transfer_posture: DataTransferPosture
    customer_data_handling_posture: CustomerDataHandlingPosture
    connector_activation_posture: ConnectorActivationPosture
    endpoint_access_posture: EndpointAccessPosture
    adjudication_execution_posture: AdjudicationExecutionPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_preflight_contract_row(self) -> RepoCorpusIngestionPreflightContractRow:
        _repo_ref(self.preflight_contract_ref, field_name="preflight_contract_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "request_refs",
            "source_refs",
            "guardrail_refs",
            "upstream_corpus_boundary_refs",
            "upstream_provenance_refs",
            "connector_boundary_refs",
            "data_handling_authority_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        if self.corpus_ingestion_posture != "no_corpus_ingestion_performed_by_v82":
            raise ValueError("V82-B preflight contracts must not ingest corpora")
        if self.data_transfer_posture != "no_data_transfer_performed_by_v82":
            raise ValueError("V82-B preflight contracts must not transfer data")
        if self.customer_data_handling_posture != "no_customer_data_handling_performed_by_v82":
            raise ValueError("V82-B preflight contracts must not handle customer data")
        if self.connector_activation_posture != "no_connector_activation_performed_by_v82":
            raise ValueError("V82-B preflight contracts must not activate connectors")
        if self.endpoint_access_posture != "no_endpoint_access_performed_by_v82":
            raise ValueError("V82-B preflight contracts must not access endpoints")
        if self.adjudication_execution_posture != "no_cross_corpus_adjudication_performed_by_v82":
            raise ValueError("V82-B preflight contracts must not execute adjudication")
        if self.preflight_observation_posture == "prior_authorized_preflight_observed":
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("prior authorized", "no corpus ingestion"),
            )
        if self.plan_completeness_posture == "complete_for_review_only":
            if not self.connector_boundary_refs or not self.data_handling_authority_refs:
                raise ValueError(
                    "complete-for-review preflights require boundary and authority refs"
                )
        _reject_v82b_permission_claim(self.limitation_note, field_name="limitation_note")
        return self


class RepoCorpusIngestionPreflightContract(_CartographyBase):
    schema: Literal["repo_corpus_ingestion_preflight_contract@1"] = (
        REPO_CORPUS_INGESTION_PREFLIGHT_CONTRACT_SCHEMA
    )
    corpus_ingestion_preflight_contract_id: str
    corpus_ingestion_source_index_id: str
    corpus_ingestion_review_request_id: str
    corpus_ingestion_non_transfer_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    preflight_rows: list[RepoCorpusIngestionPreflightContractRow] = Field(min_length=1)
    preflight_summary: str

    @model_validator(mode="after")
    def _validate_preflight_contract(self) -> RepoCorpusIngestionPreflightContract:
        object.__setattr__(
            self,
            "preflight_rows",
            _sorted_unique_by_ref(
                self.preflight_rows,
                attr="preflight_contract_ref",
                field_name="preflight_rows",
            ),
        )
        _require_terms(
            self.preflight_summary,
            field_name="preflight_summary",
            terms=("review", "no corpus ingestion", "no data transfer", "no connector"),
        )
        expected_id = _surface_id(
            "repo_corpus_ingestion_preflight_contract",
            self.schema,
            self.model_dump(mode="json"),
            "corpus_ingestion_preflight_contract_id",
        )
        if self.corpus_ingestion_preflight_contract_id != expected_id:
            raise ValueError("corpus_ingestion_preflight_contract_id does not match canonical hash")
        return self


class RepoConnectorAccessReviewBoundaryRow(_CartographyBase):
    connector_boundary_ref: str
    candidate_ref: str
    request_refs: list[str] = Field(min_length=1)
    source_refs: list[str] = Field(min_length=1)
    guardrail_refs: list[str] = Field(min_length=1)
    connector_identifier_refs: list[str] = Field(default_factory=list)
    endpoint_identifier_refs: list[str] = Field(default_factory=list)
    endpoint_ref_posture: EndpointRefPosture
    connector_activation_posture: ConnectorActivationPosture
    endpoint_access_posture: EndpointAccessPosture
    allowed_connector_review_actions: list[AllowedConnectorReviewAction] = Field(min_length=1)
    allowed_data_review_actions: list[AllowedDataReviewAction] = Field(min_length=1)
    forbidden_connector_actions: list[ForbiddenConnectorAction] = Field(min_length=1)
    forbidden_endpoint_actions: list[ForbiddenEndpointAction] = Field(min_length=1)
    limitation_note: str

    @model_validator(mode="after")
    def _validate_connector_boundary_row(self) -> RepoConnectorAccessReviewBoundaryRow:
        _repo_ref(self.connector_boundary_ref, field_name="connector_boundary_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "request_refs",
            "source_refs",
            "guardrail_refs",
            "connector_identifier_refs",
            "endpoint_identifier_refs",
            "allowed_connector_review_actions",
            "allowed_data_review_actions",
            "forbidden_connector_actions",
            "forbidden_endpoint_actions",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        if self.connector_activation_posture != "no_connector_activation_performed_by_v82":
            raise ValueError("V82-B connector boundaries must not activate connectors")
        if self.endpoint_access_posture != "no_endpoint_access_performed_by_v82":
            raise ValueError("V82-B connector boundaries must not access endpoints")
        if set(self.forbidden_connector_actions) != _FORBIDDEN_CONNECTOR_ACTIONS:
            raise ValueError("connector boundary must forbid all connector actions")
        if set(self.forbidden_endpoint_actions) != _FORBIDDEN_ENDPOINT_ACTIONS:
            raise ValueError("connector boundary must forbid all endpoint actions")
        if (
            self.endpoint_ref_posture == "endpoint_identifier_only"
            and not self.endpoint_identifier_refs
        ):
            raise ValueError("endpoint identifier posture requires endpoint identifier refs")
        _reject_v82b_permission_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("review", "no connector", "no endpoint"),
        )
        return self


class RepoConnectorAccessReviewBoundary(_CartographyBase):
    schema: Literal["repo_connector_access_review_boundary@1"] = (
        REPO_CONNECTOR_ACCESS_REVIEW_BOUNDARY_SCHEMA
    )
    connector_access_review_boundary_id: str
    corpus_ingestion_source_index_id: str
    corpus_ingestion_review_request_id: str
    corpus_ingestion_non_transfer_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    connector_boundary_rows: list[RepoConnectorAccessReviewBoundaryRow] = Field(min_length=1)
    connector_boundary_summary: str

    @model_validator(mode="after")
    def _validate_connector_boundary(self) -> RepoConnectorAccessReviewBoundary:
        object.__setattr__(
            self,
            "connector_boundary_rows",
            _sorted_unique_by_ref(
                self.connector_boundary_rows,
                attr="connector_boundary_ref",
                field_name="connector_boundary_rows",
            ),
        )
        _require_terms(
            self.connector_boundary_summary,
            field_name="connector_boundary_summary",
            terms=("review", "no connector", "no endpoint"),
        )
        expected_id = _surface_id(
            "repo_connector_access_review_boundary",
            self.schema,
            self.model_dump(mode="json"),
            "connector_access_review_boundary_id",
        )
        if self.connector_access_review_boundary_id != expected_id:
            raise ValueError("connector_access_review_boundary_id does not match canonical hash")
        return self


class RepoCorpusDataHandlingAuthorityReviewRow(_CartographyBase):
    authority_review_ref: str
    candidate_ref: str
    request_refs: list[str] = Field(min_length=1)
    source_refs: list[str] = Field(min_length=1)
    guardrail_refs: list[str] = Field(min_length=1)
    authority_kind: CorpusDataHandlingAuthorityKind
    authority_review_posture: DataHandlingAuthorityReviewPosture
    required_before_surface: RequiredBeforeSurface
    source_presence_posture: CandidateSourcePresencePosture
    privacy_or_license_posture: PrivacyOrLicensePosture
    customer_data_handling_posture: CustomerDataHandlingPosture
    connector_activation_posture: ConnectorActivationPosture
    endpoint_access_posture: EndpointAccessPosture
    data_transfer_posture: DataTransferPosture
    limitation_note: str

    @model_validator(mode="after")
    def _validate_authority_review_row(self) -> RepoCorpusDataHandlingAuthorityReviewRow:
        _repo_ref(self.authority_review_ref, field_name="authority_review_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in ("request_refs", "source_refs", "guardrail_refs"):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        for source_ref in self.source_refs:
            _repo_ref(source_ref, field_name="source_refs")
        if self.customer_data_handling_posture != "no_customer_data_handling_performed_by_v82":
            raise ValueError("V82-B authority reviews must not handle customer data")
        if self.connector_activation_posture != "no_connector_activation_performed_by_v82":
            raise ValueError("V82-B authority reviews must not activate connectors")
        if self.endpoint_access_posture != "no_endpoint_access_performed_by_v82":
            raise ValueError("V82-B authority reviews must not access endpoints")
        if self.data_transfer_posture != "no_data_transfer_performed_by_v82":
            raise ValueError("V82-B authority reviews must not transfer data")
        if (
            self.authority_review_posture == "authority_present_for_review_only"
            and self.source_presence_posture != "present"
        ):
            raise ValueError("present authority review posture requires present source")
        if (
            self.authority_review_posture
            in {
                "authority_missing",
                "authority_requires_later_review",
            }
            and self.source_presence_posture == "present"
        ):
            _require_terms(
                self.limitation_note,
                field_name="limitation_note",
                terms=("review",),
            )
        _reject_v82b_permission_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("authority", "review"),
        )
        return self


class RepoCorpusDataHandlingAuthorityReview(_CartographyBase):
    schema: Literal["repo_corpus_data_handling_authority_review@1"] = (
        REPO_CORPUS_DATA_HANDLING_AUTHORITY_REVIEW_SCHEMA
    )
    corpus_data_handling_authority_review_id: str
    corpus_ingestion_source_index_id: str
    corpus_ingestion_review_request_id: str
    corpus_ingestion_non_transfer_guardrail_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    authority_review_rows: list[RepoCorpusDataHandlingAuthorityReviewRow] = Field(min_length=1)
    authority_review_summary: str

    @model_validator(mode="after")
    def _validate_authority_review(self) -> RepoCorpusDataHandlingAuthorityReview:
        object.__setattr__(
            self,
            "authority_review_rows",
            _sorted_unique_by_ref(
                self.authority_review_rows,
                attr="authority_review_ref",
                field_name="authority_review_rows",
            ),
        )
        _require_terms(
            self.authority_review_summary,
            field_name="authority_review_summary",
            terms=("authority", "review", "no data transfer"),
        )
        expected_id = _surface_id(
            "repo_corpus_data_handling_authority_review",
            self.schema,
            self.model_dump(mode="json"),
            "corpus_data_handling_authority_review_id",
        )
        if self.corpus_data_handling_authority_review_id != expected_id:
            raise ValueError(
                "corpus_data_handling_authority_review_id does not match canonical hash"
            )
        return self


class RepoCorpusIngestionExceptionRow(_CartographyBase):
    exception_ref: str
    candidate_ref: str
    request_refs: list[str] = Field(min_length=1)
    preflight_contract_refs: list[str] = Field(default_factory=list)
    connector_boundary_refs: list[str] = Field(default_factory=list)
    data_handling_authority_refs: list[str] = Field(default_factory=list)
    exception_kind: CorpusIngestionExceptionKind
    blocking_posture: CorpusIngestionExceptionBlockingPosture
    visibility_posture: CorpusIngestionExceptionVisibilityPosture
    required_next_surface: CorpusIngestionExceptionRequiredNextSurface
    limitation_note: str

    @model_validator(mode="after")
    def _validate_exception_row(self) -> RepoCorpusIngestionExceptionRow:
        _repo_ref(self.exception_ref, field_name="exception_ref")
        _non_empty(self.candidate_ref, field_name="candidate_ref")
        for field_name in (
            "request_refs",
            "preflight_contract_refs",
            "connector_boundary_refs",
            "data_handling_authority_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if self.blocking_posture in {"blocking_exception", "carried_forward_blocker"}:
            if not (
                self.preflight_contract_refs
                or self.connector_boundary_refs
                or self.data_handling_authority_refs
            ):
                raise ValueError("blocking corpus-ingestion exceptions require evidence refs")
            if self.required_next_surface == "none":
                raise ValueError("blocking corpus-ingestion exceptions require next surface")
        lowered = self.limitation_note.lower()
        if "resolved by v82-b" in lowered or "exception resolved" in lowered:
            raise ValueError("V82-B exceptions must not be marked resolved")
        _reject_v82b_permission_claim(self.limitation_note, field_name="limitation_note")
        _require_terms(
            self.limitation_note,
            field_name="limitation_note",
            terms=("visible", "review"),
        )
        return self


class RepoCorpusIngestionExceptionRegister(_CartographyBase):
    schema: Literal["repo_corpus_ingestion_exception_register@1"] = (
        REPO_CORPUS_INGESTION_EXCEPTION_REGISTER_SCHEMA
    )
    corpus_ingestion_exception_register_id: str
    corpus_ingestion_source_index_id: str
    corpus_ingestion_review_request_id: str
    corpus_ingestion_non_transfer_guardrail_id: str
    corpus_ingestion_preflight_contract_id: str
    connector_access_review_boundary_id: str
    corpus_data_handling_authority_review_id: str
    review_id: str
    snapshot_id: str
    source_set_id: str
    exception_rows: list[RepoCorpusIngestionExceptionRow] = Field(min_length=1)
    exception_summary: str

    @model_validator(mode="after")
    def _validate_exception_register(self) -> RepoCorpusIngestionExceptionRegister:
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
            terms=("visible", "review", "no corpus ingestion"),
        )
        expected_id = _surface_id(
            "repo_corpus_ingestion_exception_register",
            self.schema,
            self.model_dump(mode="json"),
            "corpus_ingestion_exception_register_id",
        )
        if self.corpus_ingestion_exception_register_id != expected_id:
            raise ValueError("corpus_ingestion_exception_register_id does not match canonical hash")
        return self


def derive_v82b_repo_corpus_ingestion_preflight_contract(
    *,
    repo_root: Path | None = None,
    corpus_ingestion_source_index: RepoCorpusIngestionSourceIndex | None = None,
    corpus_ingestion_review_request: RepoCorpusIngestionReviewRequest | None = None,
    corpus_ingestion_non_transfer_guardrail: RepoCorpusIngestionNonTransferGuardrail | None = None,
) -> RepoCorpusIngestionPreflightContract:
    _ = repo_root
    if any(
        item is None
        for item in (
            corpus_ingestion_source_index,
            corpus_ingestion_review_request,
            corpus_ingestion_non_transfer_guardrail,
        )
    ):
        (
            corpus_ingestion_source_index,
            corpus_ingestion_review_request,
            corpus_ingestion_non_transfer_guardrail,
        ) = derive_v82a_corpus_ingestion_review_bundle(repo_root=repo_root)
    assert corpus_ingestion_source_index is not None
    assert corpus_ingestion_review_request is not None
    assert corpus_ingestion_non_transfer_guardrail is not None
    validate_v82a_corpus_ingestion_review_bundle(
        corpus_ingestion_source_index=corpus_ingestion_source_index,
        corpus_ingestion_review_request=corpus_ingestion_review_request,
        corpus_ingestion_non_transfer_guardrail=corpus_ingestion_non_transfer_guardrail,
    )
    rows: list[dict[str, object]] = []
    for request_row in corpus_ingestion_review_request.request_rows:
        is_product = "product" in request_row.candidate_ref
        rows.append(
            {
                "preflight_contract_ref": _v82b_preflight_ref(request_row),
                "candidate_ref": request_row.candidate_ref,
                "request_refs": [request_row.corpus_ingestion_review_request_ref],
                "source_refs": request_row.source_refs,
                "guardrail_refs": request_row.guardrail_refs,
                "upstream_corpus_boundary_refs": [],
                "upstream_provenance_refs": [],
                "connector_boundary_refs": [_v82b_connector_boundary_ref(request_row)],
                "data_handling_authority_refs": _v82b_authority_review_refs(request_row),
                "monitoring_requirement_posture": (
                    "not_applicable" if is_product else "missing_required_monitoring"
                ),
                "rollback_requirement_posture": (
                    "not_applicable" if is_product else "missing_required_rollback"
                ),
                "preflight_observation_posture": "requirements_recorded_only",
                "preflight_posture": (
                    "preflight_future_family_only"
                    if is_product
                    else "preflight_blocked_by_missing_source"
                ),
                "plan_completeness_posture": (
                    "future_family_only" if is_product else "blocked_by_missing_source"
                ),
                "corpus_ingestion_posture": "no_corpus_ingestion_performed_by_v82",
                "data_transfer_posture": "no_data_transfer_performed_by_v82",
                "customer_data_handling_posture": "no_customer_data_handling_performed_by_v82",
                "connector_activation_posture": "no_connector_activation_performed_by_v82",
                "endpoint_access_posture": "no_endpoint_access_performed_by_v82",
                "adjudication_execution_posture": "no_cross_corpus_adjudication_performed_by_v82",
                "limitation_note": (
                    "Product-pressure preflight remains future-family review only with "
                    "no corpus ingestion, no data transfer, no connector activation, "
                    "no endpoint access, and no authority granted."
                    if is_product
                    else "Preflight requirements are recorded for review while corpus "
                    "source, monitoring, rollback, connector, endpoint, privacy, license, "
                    "and transfer authority gaps remain visible; no corpus ingestion, "
                    "no data transfer, no connector activation, and no endpoint access."
                ),
            }
        )
    payload = {
        "schema": REPO_CORPUS_INGESTION_PREFLIGHT_CONTRACT_SCHEMA,
        "corpus_ingestion_preflight_contract_id": "",
        "corpus_ingestion_source_index_id": (
            corpus_ingestion_source_index.corpus_ingestion_source_index_id
        ),
        "corpus_ingestion_review_request_id": (
            corpus_ingestion_review_request.corpus_ingestion_review_request_id
        ),
        "corpus_ingestion_non_transfer_guardrail_id": (
            corpus_ingestion_non_transfer_guardrail.corpus_ingestion_non_transfer_guardrail_id
        ),
        "review_id": corpus_ingestion_review_request.review_id,
        "snapshot_id": corpus_ingestion_review_request.snapshot_id,
        "source_set_id": corpus_ingestion_review_request.source_set_id,
        "preflight_rows": sorted(rows, key=lambda row: row["preflight_contract_ref"]),
        "preflight_summary": (
            "Corpus-ingestion preflight contracts are review-only records with "
            "no corpus ingestion, no data transfer, no connector activation, "
            "and no endpoint access."
        ),
    }
    payload["corpus_ingestion_preflight_contract_id"] = _surface_id(
        "repo_corpus_ingestion_preflight_contract",
        REPO_CORPUS_INGESTION_PREFLIGHT_CONTRACT_SCHEMA,
        payload,
        "corpus_ingestion_preflight_contract_id",
    )
    return RepoCorpusIngestionPreflightContract.model_validate(payload)


def derive_v82b_repo_connector_access_review_boundary(
    *,
    repo_root: Path | None = None,
    corpus_ingestion_source_index: RepoCorpusIngestionSourceIndex | None = None,
    corpus_ingestion_review_request: RepoCorpusIngestionReviewRequest | None = None,
    corpus_ingestion_non_transfer_guardrail: RepoCorpusIngestionNonTransferGuardrail | None = None,
) -> RepoConnectorAccessReviewBoundary:
    _ = repo_root
    if any(
        item is None
        for item in (
            corpus_ingestion_source_index,
            corpus_ingestion_review_request,
            corpus_ingestion_non_transfer_guardrail,
        )
    ):
        (
            corpus_ingestion_source_index,
            corpus_ingestion_review_request,
            corpus_ingestion_non_transfer_guardrail,
        ) = derive_v82a_corpus_ingestion_review_bundle(repo_root=repo_root)
    assert corpus_ingestion_source_index is not None
    assert corpus_ingestion_review_request is not None
    assert corpus_ingestion_non_transfer_guardrail is not None
    rows: list[dict[str, object]] = []
    for request_row in corpus_ingestion_review_request.request_rows:
        is_product = "product" in request_row.candidate_ref
        rows.append(
            {
                "connector_boundary_ref": _v82b_connector_boundary_ref(request_row),
                "candidate_ref": request_row.candidate_ref,
                "request_refs": [request_row.corpus_ingestion_review_request_ref],
                "source_refs": request_row.source_refs,
                "guardrail_refs": request_row.guardrail_refs,
                "connector_identifier_refs": (
                    [] if is_product else ["connector-authority:corpus-ingestion:current:absent"]
                ),
                "endpoint_identifier_refs": (
                    [] if is_product else ["endpoint-authority:corpus-ingestion:current:absent"]
                ),
                "endpoint_ref_posture": "endpoint_absent_or_unknown",
                "connector_activation_posture": "no_connector_activation_performed_by_v82",
                "endpoint_access_posture": "no_endpoint_access_performed_by_v82",
                "allowed_connector_review_actions": sorted(
                    [
                        "describe_connector_boundary",
                        "inspect_connector_metadata",
                        "record_absence_posture",
                        "request_later_connector_authority_review",
                        "preserve_connector_gap",
                    ]
                ),
                "allowed_data_review_actions": sorted(
                    [
                        "describe_data_boundary",
                        "inspect_source_metadata",
                        "record_absence_posture",
                        "request_later_data_authority_review",
                        "preserve_data_gap",
                    ]
                ),
                "forbidden_connector_actions": sorted(_FORBIDDEN_CONNECTOR_ACTIONS),
                "forbidden_endpoint_actions": sorted(_FORBIDDEN_ENDPOINT_ACTIONS),
                "limitation_note": (
                    "Connector and endpoint review boundary is future-family only for "
                    "product pressure with no connector activation and no endpoint access."
                    if is_product
                    else "Connector and endpoint identifiers are absence markers for "
                    "review only; no connector activation and no endpoint access."
                ),
            }
        )
    payload = {
        "schema": REPO_CONNECTOR_ACCESS_REVIEW_BOUNDARY_SCHEMA,
        "connector_access_review_boundary_id": "",
        "corpus_ingestion_source_index_id": (
            corpus_ingestion_source_index.corpus_ingestion_source_index_id
        ),
        "corpus_ingestion_review_request_id": (
            corpus_ingestion_review_request.corpus_ingestion_review_request_id
        ),
        "corpus_ingestion_non_transfer_guardrail_id": (
            corpus_ingestion_non_transfer_guardrail.corpus_ingestion_non_transfer_guardrail_id
        ),
        "review_id": corpus_ingestion_review_request.review_id,
        "snapshot_id": corpus_ingestion_review_request.snapshot_id,
        "source_set_id": corpus_ingestion_review_request.source_set_id,
        "connector_boundary_rows": sorted(rows, key=lambda row: row["connector_boundary_ref"]),
        "connector_boundary_summary": (
            "Connector access review boundaries preserve review-only posture with "
            "no connector activation and no endpoint access."
        ),
    }
    payload["connector_access_review_boundary_id"] = _surface_id(
        "repo_connector_access_review_boundary",
        REPO_CONNECTOR_ACCESS_REVIEW_BOUNDARY_SCHEMA,
        payload,
        "connector_access_review_boundary_id",
    )
    return RepoConnectorAccessReviewBoundary.model_validate(payload)


def derive_v82b_repo_corpus_data_handling_authority_review(
    *,
    repo_root: Path | None = None,
    corpus_ingestion_source_index: RepoCorpusIngestionSourceIndex | None = None,
    corpus_ingestion_review_request: RepoCorpusIngestionReviewRequest | None = None,
    corpus_ingestion_non_transfer_guardrail: RepoCorpusIngestionNonTransferGuardrail | None = None,
) -> RepoCorpusDataHandlingAuthorityReview:
    _ = repo_root
    if any(
        item is None
        for item in (
            corpus_ingestion_source_index,
            corpus_ingestion_review_request,
            corpus_ingestion_non_transfer_guardrail,
        )
    ):
        (
            corpus_ingestion_source_index,
            corpus_ingestion_review_request,
            corpus_ingestion_non_transfer_guardrail,
        ) = derive_v82a_corpus_ingestion_review_bundle(repo_root=repo_root)
    assert corpus_ingestion_source_index is not None
    assert corpus_ingestion_review_request is not None
    assert corpus_ingestion_non_transfer_guardrail is not None
    rows: list[dict[str, object]] = []
    for request_row in corpus_ingestion_review_request.request_rows:
        if "product" in request_row.candidate_ref:
            note = (
                "Product authority is required for later review; no authority granted, "
                "no data transfer, no connector activation, and no endpoint access."
            )
        else:
            note = (
                "Authority source remains required for later review; no authority "
                "granted, no data transfer, no connector activation, and no "
                "endpoint access."
            )
        for (
            authority_ref,
            authority_kind,
            source_ref,
            required_before_surface,
            privacy_or_license_posture,
        ) in _v82b_authority_review_specs(request_row):
            rows.append(
                {
                    "authority_review_ref": authority_ref,
                    "candidate_ref": request_row.candidate_ref,
                    "request_refs": [request_row.corpus_ingestion_review_request_ref],
                    "source_refs": [source_ref],
                    "guardrail_refs": request_row.guardrail_refs,
                    "authority_kind": authority_kind,
                    "authority_review_posture": "authority_requires_later_review",
                    "required_before_surface": required_before_surface,
                    "source_presence_posture": "external_unavailable",
                    "privacy_or_license_posture": privacy_or_license_posture,
                    "customer_data_handling_posture": "no_customer_data_handling_performed_by_v82",
                    "connector_activation_posture": "no_connector_activation_performed_by_v82",
                    "endpoint_access_posture": "no_endpoint_access_performed_by_v82",
                    "data_transfer_posture": "no_data_transfer_performed_by_v82",
                    "limitation_note": note,
                }
            )
    payload = {
        "schema": REPO_CORPUS_DATA_HANDLING_AUTHORITY_REVIEW_SCHEMA,
        "corpus_data_handling_authority_review_id": "",
        "corpus_ingestion_source_index_id": (
            corpus_ingestion_source_index.corpus_ingestion_source_index_id
        ),
        "corpus_ingestion_review_request_id": (
            corpus_ingestion_review_request.corpus_ingestion_review_request_id
        ),
        "corpus_ingestion_non_transfer_guardrail_id": (
            corpus_ingestion_non_transfer_guardrail.corpus_ingestion_non_transfer_guardrail_id
        ),
        "review_id": corpus_ingestion_review_request.review_id,
        "snapshot_id": corpus_ingestion_review_request.snapshot_id,
        "source_set_id": corpus_ingestion_review_request.source_set_id,
        "authority_review_rows": sorted(rows, key=lambda row: row["authority_review_ref"]),
        "authority_review_summary": (
            "Corpus data-handling authority review rows record missing authority for "
            "review with no data transfer, no connector activation, and no endpoint access."
        ),
    }
    payload["corpus_data_handling_authority_review_id"] = _surface_id(
        "repo_corpus_data_handling_authority_review",
        REPO_CORPUS_DATA_HANDLING_AUTHORITY_REVIEW_SCHEMA,
        payload,
        "corpus_data_handling_authority_review_id",
    )
    return RepoCorpusDataHandlingAuthorityReview.model_validate(payload)


def derive_v82b_repo_corpus_ingestion_exception_register(
    *,
    repo_root: Path | None = None,
    corpus_ingestion_source_index: RepoCorpusIngestionSourceIndex | None = None,
    corpus_ingestion_review_request: RepoCorpusIngestionReviewRequest | None = None,
    corpus_ingestion_non_transfer_guardrail: RepoCorpusIngestionNonTransferGuardrail | None = None,
    corpus_ingestion_preflight_contract: RepoCorpusIngestionPreflightContract | None = None,
    connector_access_review_boundary: RepoConnectorAccessReviewBoundary | None = None,
    corpus_data_handling_authority_review: RepoCorpusDataHandlingAuthorityReview | None = None,
) -> RepoCorpusIngestionExceptionRegister:
    _ = repo_root
    if any(
        item is None
        for item in (
            corpus_ingestion_source_index,
            corpus_ingestion_review_request,
            corpus_ingestion_non_transfer_guardrail,
        )
    ):
        (
            corpus_ingestion_source_index,
            corpus_ingestion_review_request,
            corpus_ingestion_non_transfer_guardrail,
        ) = derive_v82a_corpus_ingestion_review_bundle(repo_root=repo_root)
    assert corpus_ingestion_source_index is not None
    assert corpus_ingestion_review_request is not None
    assert corpus_ingestion_non_transfer_guardrail is not None
    corpus_ingestion_preflight_contract = (
        corpus_ingestion_preflight_contract
        or derive_v82b_repo_corpus_ingestion_preflight_contract(
            repo_root=repo_root,
            corpus_ingestion_source_index=corpus_ingestion_source_index,
            corpus_ingestion_review_request=corpus_ingestion_review_request,
            corpus_ingestion_non_transfer_guardrail=corpus_ingestion_non_transfer_guardrail,
        )
    )
    connector_access_review_boundary = (
        connector_access_review_boundary
        or derive_v82b_repo_connector_access_review_boundary(
            repo_root=repo_root,
            corpus_ingestion_source_index=corpus_ingestion_source_index,
            corpus_ingestion_review_request=corpus_ingestion_review_request,
            corpus_ingestion_non_transfer_guardrail=corpus_ingestion_non_transfer_guardrail,
        )
    )
    corpus_data_handling_authority_review = (
        corpus_data_handling_authority_review
        or derive_v82b_repo_corpus_data_handling_authority_review(
            repo_root=repo_root,
            corpus_ingestion_source_index=corpus_ingestion_source_index,
            corpus_ingestion_review_request=corpus_ingestion_review_request,
            corpus_ingestion_non_transfer_guardrail=corpus_ingestion_non_transfer_guardrail,
        )
    )
    rows: list[dict[str, object]] = []
    for request_row in corpus_ingestion_review_request.request_rows:
        if "product" in request_row.candidate_ref:
            rows.append(
                {
                    "exception_ref": "exception:v82b:product-wedge:product-authority-gap",
                    "candidate_ref": request_row.candidate_ref,
                    "request_refs": [request_row.corpus_ingestion_review_request_ref],
                    "preflight_contract_refs": [_v82b_preflight_ref(request_row)],
                    "connector_boundary_refs": [_v82b_connector_boundary_ref(request_row)],
                    "data_handling_authority_refs": _v82b_authority_review_refs(request_row),
                    "exception_kind": "product_authority_gap",
                    "blocking_posture": "blocking_exception",
                    "visibility_posture": "visible_to_later_review",
                    "required_next_surface": "future_product_review",
                    "limitation_note": (
                        "Product authority gap stays visible for later review; no corpus "
                        "ingestion, no data transfer, no connector activation, and no "
                        "endpoint access."
                    ),
                }
            )
            continue
        exception_specs = [
            ("missing_corpus_source", "future_corpus_ingestion_authority_review"),
            ("missing_privacy_authority", "future_corpus_ingestion_authority_review"),
            ("missing_license_or_consent", "future_corpus_ingestion_authority_review"),
            ("missing_connector_authority", "future_connector_activation_authority_review"),
            ("missing_endpoint_access_boundary", "future_endpoint_access_authority_review"),
            ("missing_transfer_authority", "future_data_transfer_authority_review"),
            ("missing_retention_authority", "future_retention_authority_review"),
            (
                "missing_deletion_or_withdrawal_authority",
                "future_deletion_or_withdrawal_authority_review",
            ),
        ]
        for exception_kind, next_surface in exception_specs:
            rows.append(
                {
                    "exception_ref": f"exception:v82b:self-evidencing:{exception_kind}",
                    "candidate_ref": request_row.candidate_ref,
                    "request_refs": [request_row.corpus_ingestion_review_request_ref],
                    "preflight_contract_refs": [_v82b_preflight_ref(request_row)],
                    "connector_boundary_refs": [_v82b_connector_boundary_ref(request_row)],
                    "data_handling_authority_refs": _v82b_authority_review_refs(request_row),
                    "exception_kind": exception_kind,
                    "blocking_posture": "blocking_exception",
                    "visibility_posture": "visible_to_later_review",
                    "required_next_surface": next_surface,
                    "limitation_note": (
                        f"{exception_kind} remains visible for later review; no corpus "
                        "ingestion, no data transfer, no connector activation, and no "
                        "endpoint access."
                    ),
                }
            )
    payload = {
        "schema": REPO_CORPUS_INGESTION_EXCEPTION_REGISTER_SCHEMA,
        "corpus_ingestion_exception_register_id": "",
        "corpus_ingestion_source_index_id": (
            corpus_ingestion_source_index.corpus_ingestion_source_index_id
        ),
        "corpus_ingestion_review_request_id": (
            corpus_ingestion_review_request.corpus_ingestion_review_request_id
        ),
        "corpus_ingestion_non_transfer_guardrail_id": (
            corpus_ingestion_non_transfer_guardrail.corpus_ingestion_non_transfer_guardrail_id
        ),
        "corpus_ingestion_preflight_contract_id": (
            corpus_ingestion_preflight_contract.corpus_ingestion_preflight_contract_id
        ),
        "connector_access_review_boundary_id": (
            connector_access_review_boundary.connector_access_review_boundary_id
        ),
        "corpus_data_handling_authority_review_id": (
            corpus_data_handling_authority_review.corpus_data_handling_authority_review_id
        ),
        "review_id": corpus_ingestion_review_request.review_id,
        "snapshot_id": corpus_ingestion_review_request.snapshot_id,
        "source_set_id": corpus_ingestion_review_request.source_set_id,
        "exception_rows": sorted(rows, key=lambda row: row["exception_ref"]),
        "exception_summary": (
            "Corpus-ingestion exceptions remain visible for later review with no corpus "
            "ingestion, no data transfer, no connector activation, and no endpoint access."
        ),
    }
    payload["corpus_ingestion_exception_register_id"] = _surface_id(
        "repo_corpus_ingestion_exception_register",
        REPO_CORPUS_INGESTION_EXCEPTION_REGISTER_SCHEMA,
        payload,
        "corpus_ingestion_exception_register_id",
    )
    return RepoCorpusIngestionExceptionRegister.model_validate(payload)


def validate_v82b_corpus_ingestion_boundary_bundle(
    *,
    corpus_ingestion_source_index: RepoCorpusIngestionSourceIndex,
    corpus_ingestion_review_request: RepoCorpusIngestionReviewRequest,
    corpus_ingestion_non_transfer_guardrail: RepoCorpusIngestionNonTransferGuardrail,
    corpus_ingestion_preflight_contract: RepoCorpusIngestionPreflightContract,
    connector_access_review_boundary: RepoConnectorAccessReviewBoundary,
    corpus_data_handling_authority_review: RepoCorpusDataHandlingAuthorityReview,
    corpus_ingestion_exception_register: RepoCorpusIngestionExceptionRegister,
) -> None:
    validate_v82a_corpus_ingestion_review_bundle(
        corpus_ingestion_source_index=corpus_ingestion_source_index,
        corpus_ingestion_review_request=corpus_ingestion_review_request,
        corpus_ingestion_non_transfer_guardrail=corpus_ingestion_non_transfer_guardrail,
    )
    v82a_ids = (
        corpus_ingestion_source_index.corpus_ingestion_source_index_id,
        corpus_ingestion_review_request.corpus_ingestion_review_request_id,
        corpus_ingestion_non_transfer_guardrail.corpus_ingestion_non_transfer_guardrail_id,
    )
    for surface in (
        corpus_ingestion_preflight_contract,
        connector_access_review_boundary,
        corpus_data_handling_authority_review,
    ):
        if (
            surface.corpus_ingestion_source_index_id,
            surface.corpus_ingestion_review_request_id,
            surface.corpus_ingestion_non_transfer_guardrail_id,
        ) != v82a_ids:
            raise ValueError("V82-B surfaces must reference released V82-A surfaces")
        if (
            surface.review_id,
            surface.snapshot_id,
            surface.source_set_id,
        ) != (
            corpus_ingestion_review_request.review_id,
            corpus_ingestion_review_request.snapshot_id,
            corpus_ingestion_review_request.source_set_id,
        ):
            raise ValueError("V82-B surface provenance must match V82-A request")
    if (
        corpus_ingestion_exception_register.corpus_ingestion_source_index_id,
        corpus_ingestion_exception_register.corpus_ingestion_review_request_id,
        corpus_ingestion_exception_register.corpus_ingestion_non_transfer_guardrail_id,
    ) != v82a_ids:
        raise ValueError("V82-B exception register must reference released V82-A surfaces")
    if (
        corpus_ingestion_exception_register.corpus_ingestion_preflight_contract_id
        != corpus_ingestion_preflight_contract.corpus_ingestion_preflight_contract_id
    ):
        raise ValueError("V82-B exception register must reference preflight contract")
    if (
        corpus_ingestion_exception_register.connector_access_review_boundary_id
        != connector_access_review_boundary.connector_access_review_boundary_id
    ):
        raise ValueError("V82-B exception register must reference connector boundary")
    if (
        corpus_ingestion_exception_register.corpus_data_handling_authority_review_id
        != corpus_data_handling_authority_review.corpus_data_handling_authority_review_id
    ):
        raise ValueError("V82-B exception register must reference authority review")

    known_sources = {row.source_ref for row in corpus_ingestion_source_index.source_rows}
    request_rows = {
        row.corpus_ingestion_review_request_ref: row
        for row in corpus_ingestion_review_request.request_rows
    }
    guardrail_rows = {
        row.guardrail_ref: row for row in corpus_ingestion_non_transfer_guardrail.guardrail_rows
    }
    preflight_rows = {
        row.preflight_contract_ref: row
        for row in corpus_ingestion_preflight_contract.preflight_rows
    }
    connector_rows = {
        row.connector_boundary_ref: row
        for row in connector_access_review_boundary.connector_boundary_rows
    }
    authority_rows = {
        row.authority_review_ref: row
        for row in corpus_data_handling_authority_review.authority_review_rows
    }

    def _validate_common_refs(
        *,
        candidate_ref: str,
        request_refs: list[str],
        source_refs: list[str],
        guardrail_refs: list[str],
    ) -> None:
        for request_ref in request_refs:
            request_row = request_rows.get(request_ref)
            if request_row is None:
                raise ValueError("V82-B request refs must resolve to V82-A requests")
            if request_row.candidate_ref != candidate_ref:
                raise ValueError("V82-B request candidate must match row candidate")
        if any(source_ref not in known_sources for source_ref in source_refs):
            raise ValueError("V82-B source refs must resolve to V82-A source rows")
        for guardrail_ref in guardrail_refs:
            guardrail_row = guardrail_rows.get(guardrail_ref)
            if guardrail_row is None:
                raise ValueError("V82-B guardrail refs must resolve to V82-A guardrails")
            if guardrail_row.candidate_ref != candidate_ref:
                raise ValueError("V82-B guardrail candidate must match row candidate")

    for row in preflight_rows.values():
        _validate_common_refs(
            candidate_ref=row.candidate_ref,
            request_refs=row.request_refs,
            source_refs=row.source_refs,
            guardrail_refs=row.guardrail_refs,
        )
        for connector_ref in row.connector_boundary_refs:
            connector_row = connector_rows.get(connector_ref)
            if connector_row is None:
                raise ValueError("preflight connector refs must resolve to connector rows")
            if connector_row.candidate_ref != row.candidate_ref:
                raise ValueError("preflight connector candidate must match")
        for authority_ref in row.data_handling_authority_refs:
            authority_row = authority_rows.get(authority_ref)
            if authority_row is None:
                raise ValueError("preflight authority refs must resolve to authority rows")
            if authority_row.candidate_ref != row.candidate_ref:
                raise ValueError("preflight authority candidate must match")
        if "product" in row.candidate_ref and row.preflight_posture not in {
            "preflight_future_family_only",
            "preflight_rejected_out_of_scope",
        }:
            raise ValueError("product pressure preflight must remain future-family or rejected")
    for row in connector_rows.values():
        _validate_common_refs(
            candidate_ref=row.candidate_ref,
            request_refs=row.request_refs,
            source_refs=row.source_refs,
            guardrail_refs=row.guardrail_refs,
        )
    for row in authority_rows.values():
        _validate_common_refs(
            candidate_ref=row.candidate_ref,
            request_refs=row.request_refs,
            source_refs=row.source_refs,
            guardrail_refs=row.guardrail_refs,
        )
    for row in corpus_ingestion_exception_register.exception_rows:
        for request_ref in row.request_refs:
            request_row = request_rows.get(request_ref)
            if request_row is None:
                raise ValueError("exception request refs must resolve to V82-A requests")
            if request_row.candidate_ref != row.candidate_ref:
                raise ValueError("exception request candidate must match")
        for preflight_ref in row.preflight_contract_refs:
            preflight_row = preflight_rows.get(preflight_ref)
            if preflight_row is None:
                raise ValueError("exception preflight refs must resolve to preflight rows")
            if preflight_row.candidate_ref != row.candidate_ref:
                raise ValueError("exception preflight candidate must match")
        for connector_ref in row.connector_boundary_refs:
            connector_row = connector_rows.get(connector_ref)
            if connector_row is None:
                raise ValueError("exception connector refs must resolve to connector rows")
            if connector_row.candidate_ref != row.candidate_ref:
                raise ValueError("exception connector candidate must match")
        for authority_ref in row.data_handling_authority_refs:
            authority_row = authority_rows.get(authority_ref)
            if authority_row is None:
                raise ValueError("exception authority refs must resolve to authority rows")
            if authority_row.candidate_ref != row.candidate_ref:
                raise ValueError("exception authority candidate must match")


def derive_v82b_corpus_ingestion_boundary_bundle(
    *, repo_root: Path | None = None
) -> tuple[
    RepoCorpusIngestionSourceIndex,
    RepoCorpusIngestionReviewRequest,
    RepoCorpusIngestionNonTransferGuardrail,
    RepoCorpusIngestionPreflightContract,
    RepoConnectorAccessReviewBoundary,
    RepoCorpusDataHandlingAuthorityReview,
    RepoCorpusIngestionExceptionRegister,
]:
    source_index, request, guardrail = derive_v82a_corpus_ingestion_review_bundle(
        repo_root=repo_root
    )
    preflight = derive_v82b_repo_corpus_ingestion_preflight_contract(
        repo_root=repo_root,
        corpus_ingestion_source_index=source_index,
        corpus_ingestion_review_request=request,
        corpus_ingestion_non_transfer_guardrail=guardrail,
    )
    connector_boundary = derive_v82b_repo_connector_access_review_boundary(
        repo_root=repo_root,
        corpus_ingestion_source_index=source_index,
        corpus_ingestion_review_request=request,
        corpus_ingestion_non_transfer_guardrail=guardrail,
    )
    authority_review = derive_v82b_repo_corpus_data_handling_authority_review(
        repo_root=repo_root,
        corpus_ingestion_source_index=source_index,
        corpus_ingestion_review_request=request,
        corpus_ingestion_non_transfer_guardrail=guardrail,
    )
    exception_register = derive_v82b_repo_corpus_ingestion_exception_register(
        repo_root=repo_root,
        corpus_ingestion_source_index=source_index,
        corpus_ingestion_review_request=request,
        corpus_ingestion_non_transfer_guardrail=guardrail,
        corpus_ingestion_preflight_contract=preflight,
        connector_access_review_boundary=connector_boundary,
        corpus_data_handling_authority_review=authority_review,
    )
    validate_v82b_corpus_ingestion_boundary_bundle(
        corpus_ingestion_source_index=source_index,
        corpus_ingestion_review_request=request,
        corpus_ingestion_non_transfer_guardrail=guardrail,
        corpus_ingestion_preflight_contract=preflight,
        connector_access_review_boundary=connector_boundary,
        corpus_data_handling_authority_review=authority_review,
        corpus_ingestion_exception_register=exception_register,
    )
    return (
        source_index,
        request,
        guardrail,
        preflight,
        connector_boundary,
        authority_review,
        exception_register,
    )
