from __future__ import annotations

from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

REPO_PHASE_CIRCUIT_CATALOG_SCHEMA = "repo_phase_circuit_catalog@1"
REPO_PHASE_BRIDGE_CONTRACT_SCHEMA = "repo_phase_bridge_contract@1"
REPO_PHASE_TRANSITION_CLAIM_SCHEMA = "repo_phase_transition_claim@1"
REPO_PHASE_TRANSITION_VALIDATION_REPORT_SCHEMA = "repo_phase_transition_validation_report@1"
REPO_PHASE_LEGAL_FRONTIER_REPORT_SCHEMA = "repo_phase_legal_frontier_report@1"
REPO_TRANSITION_BROKER_NON_AUTHORITY_GUARDRAIL_SCHEMA = (
    "repo_transition_broker_non_authority_guardrail@1"
)

PhaseKind = Literal[
    "semantic_descent",
    "reconciliation",
    "hob_import",
    "scout",
    "probe_planning",
    "implementation",
    "local_parity",
    "packaged_preflight",
    "official_eval",
    "post_eval_audit",
    "manual_review",
]
ArtifactAuthorityLayer = Literal[
    "support",
    "planning",
    "architecture",
    "lock",
    "observed",
    "post_eval_pressure",
]
ClaimSource = Literal[
    "orchestrator",
    "worker_closeout",
    "planner",
    "broker_output",
    "manual_review",
]
EvidenceKind = Literal[
    "visible_spec",
    "public_schema_observation",
    "reference_behavior_observation",
    "implementation_observation",
    "post_eval_pressure",
    "source_tail",
    "methodological_equivalence",
    "support_doctrine",
]
EvidenceBoundaryPosture = Literal[
    "clean_first_pass_allowed",
    "clean_first_pass_disallowed",
    "post_eval_pressure_only",
    "source_postmortem_pressure",
    "official_like_pressure",
    "local_locked_probe_delta",
]
CleanFirstPassPosture = Literal["clean", "not_clean", "clean_first_pass_disallowed"]
ObligationTransferStatus = Literal[
    "created",
    "preserved",
    "discharged",
    "deferred",
    "blocked",
    "pass_through",
]
ReadinessPosture = Literal[
    "not_ready",
    "representative_only",
    "scoped_method_test_only",
    "scoped_ready",
    "gold_ready",
    "official_ready_candidate",
    "official_ready",
]
TransitionValidationStatus = Literal[
    "valid_for_broker_frontier",
    "blocked",
    "invalid",
    "stale",
    "conflict_isolated",
]
BridgeConsistencyStatus = Literal[
    "consistent",
    "inconsistent",
    "unknown_vocabulary",
    "hash_mismatch",
]
BridgeCompletenessStatus = Literal[
    "complete",
    "missing_required_object",
    "missing_required_evidence",
    "missing_obligation_transfer",
    "missing_equivalence",
    "missing_warrant",
    "missing_deferral_risk",
]
FrontierReason = Literal[
    "missing_object",
    "forbidden_evidence",
    "stale_artifact",
    "silent_obligation_drop",
    "illegal_promotion",
    "blocked_equivalence",
    "missing_warrant",
    "conflict_isolated",
    "posture_downgrade_required",
]
RequiredNextAction = Literal[
    "produce_object",
    "remove_forbidden_evidence",
    "refresh_artifact",
    "discharge_or_defer_obligation",
    "downgrade_promotion",
    "run_equivalence_preflight",
    "route_to_human_review",
]
PromotionKind = Literal[
    "none",
    "representative_to_scoped",
    "scoped_to_gold",
    "scoped_to_official",
    "official_eval_handoff",
]
DiagnosticSeverity = Literal["error", "warning"]
AuthorityPosture = Literal[
    "broker_validation_only_not_execution_authority",
    "no_semantic_judgment_authority",
    "no_domain_ontology_authority",
    "no_hob_closure_authority",
    "no_probe_generation_authority",
    "no_probe_execution_authority",
    "no_implementation_authority",
    "no_worker_dispatch_authority",
    "no_product_authority",
    "no_official_eval_authority",
    "no_future_family_selection_authority",
]

_READINESS_RANK: dict[str, int] = {
    "not_ready": 0,
    "representative_only": 1,
    "scoped_method_test_only": 2,
    "scoped_ready": 3,
    "gold_ready": 4,
    "official_ready_candidate": 5,
    "official_ready": 6,
}


def _assert_non_empty_text(value: str, *, field_name: str) -> str:
    normalized = value.strip()
    if not normalized:
        raise ValueError(f"{field_name} must not be empty")
    return normalized


def _assert_sorted_unique(values: list[str], *, field_name: str) -> list[str]:
    normalized = [_assert_non_empty_text(value, field_name=field_name) for value in values]
    if len(normalized) != len(set(normalized)):
        raise ValueError(f"{field_name} must not contain duplicates")
    return sorted(normalized)


def _assert_unique_rows(rows: list[Any], *, attr_name: str, field_name: str) -> None:
    seen: set[str] = set()
    for row in rows:
        value = getattr(row, attr_name)
        if value in seen:
            raise ValueError(f"{field_name} must not contain duplicate {attr_name} {value!r}")
        seen.add(value)


def _dump(model: BaseModel) -> dict[str, Any]:
    return model.model_dump(mode="json", by_alias=True, exclude_none=True)


def _hash_payload(payload: dict[str, Any], *, drop_keys: set[str] | None = None) -> str:
    subject = dict(payload)
    for key in drop_keys or set():
        subject.pop(key, None)
    return f"sha256:{sha256_canonical_json(subject)}"


def canonical_hash(
    payload: BaseModel | dict[str, Any], *, drop_keys: set[str] | None = None
) -> str:
    if isinstance(payload, BaseModel):
        return _hash_payload(_dump(payload), drop_keys=drop_keys)
    return _hash_payload(payload, drop_keys=drop_keys)


class _OtbBase(BaseModel):
    model_config = MODEL_CONFIG


class PhaseRow(_OtbBase):
    phase_id: str
    phase_label: str
    phase_kind: PhaseKind
    allowed_input_object_kinds: list[str] = Field(default_factory=list)
    allowed_output_object_kinds: list[str] = Field(default_factory=list)
    forbidden_evidence_kinds: list[EvidenceKind] = Field(default_factory=list)
    authority_layer: ArtifactAuthorityLayer

    @model_validator(mode="after")
    def _validate_row(self) -> PhaseRow:
        object.__setattr__(
            self, "phase_id", _assert_non_empty_text(self.phase_id, field_name="phase_id")
        )
        object.__setattr__(
            self,
            "phase_label",
            _assert_non_empty_text(self.phase_label, field_name="phase_label"),
        )
        object.__setattr__(
            self,
            "allowed_input_object_kinds",
            _assert_sorted_unique(
                self.allowed_input_object_kinds,
                field_name="allowed_input_object_kinds",
            ),
        )
        object.__setattr__(
            self,
            "allowed_output_object_kinds",
            _assert_sorted_unique(
                self.allowed_output_object_kinds,
                field_name="allowed_output_object_kinds",
            ),
        )
        return self


class TransitionRow(_OtbBase):
    transition_id: str
    from_phase: str
    to_phase: str
    bridge_contract_ref: str
    transition_kind: str
    default_failure_route: str

    @model_validator(mode="after")
    def _validate_row(self) -> TransitionRow:
        for field_name in (
            "transition_id",
            "from_phase",
            "to_phase",
            "bridge_contract_ref",
            "transition_kind",
            "default_failure_route",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        return self


class RepoPhaseCircuitCatalog(_OtbBase):
    schema: Literal[REPO_PHASE_CIRCUIT_CATALOG_SCHEMA]
    circuit_id: str
    circuit_version: str
    circuit_authority: ArtifactAuthorityLayer
    phase_rows: list[PhaseRow]
    transition_rows: list[TransitionRow]
    allowed_status_vocabulary: list[str]
    shared_vocabulary_ref: str
    circuit_hash: str | None = None

    @model_validator(mode="after")
    def _validate_catalog(self) -> RepoPhaseCircuitCatalog:
        object.__setattr__(
            self,
            "circuit_id",
            _assert_non_empty_text(self.circuit_id, field_name="circuit_id"),
        )
        object.__setattr__(
            self,
            "circuit_version",
            _assert_non_empty_text(self.circuit_version, field_name="circuit_version"),
        )
        object.__setattr__(
            self,
            "shared_vocabulary_ref",
            _assert_non_empty_text(
                self.shared_vocabulary_ref,
                field_name="shared_vocabulary_ref",
            ),
        )
        _assert_unique_rows(self.phase_rows, attr_name="phase_id", field_name="phase_rows")
        _assert_unique_rows(
            self.transition_rows,
            attr_name="transition_id",
            field_name="transition_rows",
        )
        phase_ids = {row.phase_id for row in self.phase_rows}
        for row in self.transition_rows:
            if row.from_phase not in phase_ids:
                raise ValueError(f"transition {row.transition_id!r} has unknown from_phase")
            if row.to_phase not in phase_ids:
                raise ValueError(f"transition {row.transition_id!r} has unknown to_phase")
        object.__setattr__(
            self,
            "phase_rows",
            sorted(self.phase_rows, key=lambda row: row.phase_id),
        )
        object.__setattr__(
            self,
            "transition_rows",
            sorted(self.transition_rows, key=lambda row: row.transition_id),
        )
        object.__setattr__(
            self,
            "allowed_status_vocabulary",
            _assert_sorted_unique(
                self.allowed_status_vocabulary,
                field_name="allowed_status_vocabulary",
            ),
        )
        if self.circuit_hash is not None:
            expected = canonical_hash(self, drop_keys={"circuit_hash"})
            if self.circuit_hash != expected:
                raise ValueError("circuit_hash must match canonical circuit payload")
        return self


class RequiredObjectRow(_OtbBase):
    object_kind: str
    required_artifact_ref: str | None = None
    required_source_phase: str | None = None
    required_authority_layer: ArtifactAuthorityLayer | None = None
    required_file_hash: str | None = None
    required_canonical_payload_hash: str | None = None
    required_semantic_object_hash: str | None = None
    required_evidence_boundary_hash: str | None = None
    required_obligation_set_hash: str | None = None
    required_object_identity_claim: str | None = None
    required_freshness_basis: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_row(self) -> RequiredObjectRow:
        object.__setattr__(
            self,
            "object_kind",
            _assert_non_empty_text(self.object_kind, field_name="object_kind"),
        )
        for field_name in (
            "required_artifact_ref",
            "required_source_phase",
            "required_file_hash",
            "required_canonical_payload_hash",
            "required_semantic_object_hash",
            "required_evidence_boundary_hash",
            "required_obligation_set_hash",
            "required_object_identity_claim",
        ):
            value = getattr(self, field_name)
            if value is not None:
                object.__setattr__(
                    self,
                    field_name,
                    _assert_non_empty_text(value, field_name=field_name),
                )
        object.__setattr__(
            self,
            "required_freshness_basis",
            _assert_sorted_unique(
                self.required_freshness_basis,
                field_name="required_freshness_basis",
            ),
        )
        return self


class OBridge(_OtbBase):
    required_objects: list[RequiredObjectRow] = Field(default_factory=list)
    object_identity_checks: list[str] = Field(default_factory=list)
    required_artifact_hash_checks: list[str] = Field(default_factory=list)
    transformation_claims: list[str] = Field(default_factory=list)
    stale_object_checks: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_lists(self) -> OBridge:
        for field_name in (
            "object_identity_checks",
            "required_artifact_hash_checks",
            "transformation_claims",
            "stale_object_checks",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        return self


class EBridge(_OtbBase):
    required_evidence: list[str] = Field(default_factory=list)
    forbidden_evidence: list[str] = Field(default_factory=list)
    evidence_boundary_rules: list[str] = Field(default_factory=list)
    warrant_requirements: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_lists(self) -> EBridge:
        for field_name in (
            "required_evidence",
            "forbidden_evidence",
            "evidence_boundary_rules",
            "warrant_requirements",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        return self


class DBridge(_OtbBase):
    obligations_created: list[str] = Field(default_factory=list)
    obligations_preserved: list[str] = Field(default_factory=list)
    obligations_discharged: list[str] = Field(default_factory=list)
    obligations_blocked_or_deferred: list[str] = Field(default_factory=list)
    forbidden_silent_drops: bool = True

    @model_validator(mode="after")
    def _validate_lists(self) -> DBridge:
        for field_name in (
            "obligations_created",
            "obligations_preserved",
            "obligations_discharged",
            "obligations_blocked_or_deferred",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        return self


class UBridge(_OtbBase):
    purpose: list[str] = Field(default_factory=list)
    next_allowed_phases: list[str] = Field(default_factory=list)
    forbidden_promotions: list[PromotionKind] = Field(default_factory=list)
    failure_routes: list[str] = Field(default_factory=list)
    supported_readiness_postures: list[ReadinessPosture] = Field(default_factory=list)
    maximum_supported_posture: ReadinessPosture | None = None

    @model_validator(mode="after")
    def _validate_lists(self) -> UBridge:
        for field_name in ("purpose", "next_allowed_phases", "failure_routes"):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "supported_readiness_postures",
            sorted(set(self.supported_readiness_postures), key=lambda item: _READINESS_RANK[item]),
        )
        object.__setattr__(
            self,
            "forbidden_promotions",
            sorted(set(self.forbidden_promotions)),
        )
        return self


class RepoPhaseBridgeContract(_OtbBase):
    schema: Literal[REPO_PHASE_BRIDGE_CONTRACT_SCHEMA]
    bridge_contract_ref: str
    circuit_id: str
    circuit_version: str
    circuit_hash: str
    transition_id: str
    from_phase: str
    to_phase: str
    O_bridge: OBridge
    E_bridge: EBridge
    D_bridge: DBridge
    U_bridge: UBridge
    bridge_hash: str | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> RepoPhaseBridgeContract:
        for field_name in (
            "bridge_contract_ref",
            "circuit_id",
            "circuit_version",
            "circuit_hash",
            "transition_id",
            "from_phase",
            "to_phase",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        if self.bridge_hash is not None:
            expected = canonical_hash(self, drop_keys={"bridge_hash"})
            if self.bridge_hash != expected:
                raise ValueError("bridge_hash must match canonical bridge payload")
        return self


class RepoPhaseTransitionClaim(_OtbBase):
    schema: Literal[REPO_PHASE_TRANSITION_CLAIM_SCHEMA]
    transition_claim_ref: str
    claiming_actor_ref: str
    claim_source: ClaimSource
    circuit_id: str
    circuit_version: str
    circuit_hash: str
    from_phase: str
    to_phase: str
    transition_id: str
    claimed_transition_kind: str
    claimed_readiness_posture: ReadinessPosture
    claimed_evidence_posture: EvidenceBoundaryPosture
    claimed_promotion: PromotionKind = "none"
    artifact_refs: list[str] = Field(default_factory=list)
    evidence_refs: list[str] = Field(default_factory=list)
    obligation_transfer_refs: list[str] = Field(default_factory=list)
    intended_use: str
    requested_next_frontier: str | None = None
    claim_hash: str | None = None

    @model_validator(mode="after")
    def _validate_claim(self) -> RepoPhaseTransitionClaim:
        for field_name in (
            "transition_claim_ref",
            "claiming_actor_ref",
            "circuit_id",
            "circuit_version",
            "circuit_hash",
            "from_phase",
            "to_phase",
            "transition_id",
            "claimed_transition_kind",
            "intended_use",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        if self.requested_next_frontier is not None:
            object.__setattr__(
                self,
                "requested_next_frontier",
                _assert_non_empty_text(
                    self.requested_next_frontier,
                    field_name="requested_next_frontier",
                ),
            )
        for field_name in ("artifact_refs", "evidence_refs", "obligation_transfer_refs"):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if self.claim_hash is not None:
            expected = canonical_hash(self, drop_keys={"claim_hash"})
            if self.claim_hash != expected:
                raise ValueError("claim_hash must match canonical claim payload")
        return self


class PhaseArtifactRow(_OtbBase):
    artifact_ref: str
    artifact_kind: str
    source_phase: str
    authority_layer: ArtifactAuthorityLayer
    file_hash: str
    canonical_payload_hash: str
    semantic_object_hash: str
    catalog_hash: str
    bridge_hash: str
    evidence_boundary_hash: str
    obligation_set_hash: str
    object_identity_claim: str
    evidence_refs: list[str] = Field(default_factory=list)
    freshness_basis: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_row(self) -> PhaseArtifactRow:
        for field_name in (
            "artifact_ref",
            "artifact_kind",
            "source_phase",
            "file_hash",
            "canonical_payload_hash",
            "semantic_object_hash",
            "catalog_hash",
            "bridge_hash",
            "evidence_boundary_hash",
            "obligation_set_hash",
            "object_identity_claim",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "evidence_refs",
            _assert_sorted_unique(self.evidence_refs, field_name="evidence_refs"),
        )
        object.__setattr__(
            self,
            "freshness_basis",
            _assert_sorted_unique(self.freshness_basis, field_name="freshness_basis"),
        )
        return self


class EvidenceRow(_OtbBase):
    evidence_ref: str
    evidence_kind: EvidenceKind
    source_phase: str
    authority_layer: ArtifactAuthorityLayer
    boundary_posture: EvidenceBoundaryPosture | None = None
    clean_first_pass_posture: CleanFirstPassPosture | None = None
    evidence_hash: str
    derived_from_evidence_refs: list[str] = Field(default_factory=list)
    contamination_tags: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_row(self) -> EvidenceRow:
        for field_name in ("evidence_ref", "source_phase", "evidence_hash"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in ("derived_from_evidence_refs", "contamination_tags"):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        return self


class ObligationTransferRow(_OtbBase):
    obligation_ref: str
    source_phase: str
    target_phase: str
    transfer_status: ObligationTransferStatus
    discharge_ref: str | None = None
    deferral_ref: str | None = None
    blocker_ref: str | None = None
    preservation_required: bool = False
    deferral_risk_posture: str | None = None

    @model_validator(mode="after")
    def _validate_row(self) -> ObligationTransferRow:
        for field_name in ("obligation_ref", "source_phase", "target_phase"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in ("discharge_ref", "deferral_ref", "blocker_ref", "deferral_risk_posture"):
            value = getattr(self, field_name)
            if value is not None:
                object.__setattr__(
                    self,
                    field_name,
                    _assert_non_empty_text(value, field_name=field_name),
                )
        return self


class TransitionDiagnosticRow(_OtbBase):
    diagnostic_ref: str
    severity: DiagnosticSeverity
    diagnostic_code: str
    bridge_field: Literal["O_bridge", "E_bridge", "D_bridge", "U_bridge", "claim", "catalog"]
    message: str
    object_refs: list[str] = Field(default_factory=list)
    evidence_refs: list[str] = Field(default_factory=list)
    required_action: RequiredNextAction

    @model_validator(mode="after")
    def _validate_row(self) -> TransitionDiagnosticRow:
        for field_name in ("diagnostic_ref", "diagnostic_code", "message"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in ("object_refs", "evidence_refs"):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        return self


class LegalFrontierRow(_OtbBase):
    frontier_ref: str
    transition_id: str
    frontier_reason: FrontierReason
    required_next_action: RequiredNextAction
    authority_posture: Literal["broker_validation_only_not_execution_authority"]
    target_phase_constraint: str
    requested_posture: ReadinessPosture | None = None
    maximum_supported_posture: ReadinessPosture | None = None
    downgrade_basis: list[str] = Field(default_factory=list)
    required_revalidation_frontier: list[str] = Field(default_factory=list)
    source_diagnostic_refs: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_row(self) -> LegalFrontierRow:
        for field_name in ("frontier_ref", "transition_id", "target_phase_constraint"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "downgrade_basis",
            "required_revalidation_frontier",
            "source_diagnostic_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        return self


class RepoPhaseTransitionValidationReport(_OtbBase):
    schema: Literal[REPO_PHASE_TRANSITION_VALIDATION_REPORT_SCHEMA]
    transition_validation_report_ref: str
    circuit_id: str
    circuit_version: str
    circuit_hash: str
    transition_id: str
    bridge_contract_ref: str
    transition_claim_ref: str
    validation_status: TransitionValidationStatus
    bridge_consistency_status: BridgeConsistencyStatus
    bridge_completeness_status: BridgeCompletenessStatus
    diagnostic_rows: list[TransitionDiagnosticRow]
    frontier_rows: list[LegalFrontierRow]
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_report(self) -> RepoPhaseTransitionValidationReport:
        for field_name in (
            "transition_validation_report_ref",
            "circuit_id",
            "circuit_version",
            "circuit_hash",
            "transition_id",
            "bridge_contract_ref",
            "transition_claim_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        _assert_unique_rows(
            self.diagnostic_rows,
            attr_name="diagnostic_ref",
            field_name="diagnostic_rows",
        )
        _assert_unique_rows(
            self.frontier_rows,
            attr_name="frontier_ref",
            field_name="frontier_rows",
        )
        object.__setattr__(
            self,
            "diagnostic_rows",
            sorted(self.diagnostic_rows, key=lambda row: row.diagnostic_ref),
        )
        object.__setattr__(
            self,
            "frontier_rows",
            sorted(self.frontier_rows, key=lambda row: row.frontier_ref),
        )
        if self.validation_status == "valid_for_broker_frontier" and self.diagnostic_rows:
            raise ValueError("valid_for_broker_frontier report cannot contain diagnostics")
        if self.validation_status != "valid_for_broker_frontier" and not self.diagnostic_rows:
            raise ValueError("blocked/invalid/stale/conflict reports require diagnostics")
        if self.canonical_output_hash is not None:
            expected = canonical_hash(self, drop_keys={"canonical_output_hash"})
            if self.canonical_output_hash != expected:
                raise ValueError("canonical_output_hash must match canonical report payload")
        return self


class RepoPhaseLegalFrontierReport(_OtbBase):
    schema: Literal[REPO_PHASE_LEGAL_FRONTIER_REPORT_SCHEMA]
    legal_frontier_report_ref: str
    transition_validation_report_ref: str
    frontier_rows: list[LegalFrontierRow]
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_report(self) -> RepoPhaseLegalFrontierReport:
        object.__setattr__(
            self,
            "legal_frontier_report_ref",
            _assert_non_empty_text(
                self.legal_frontier_report_ref,
                field_name="legal_frontier_report_ref",
            ),
        )
        object.__setattr__(
            self,
            "transition_validation_report_ref",
            _assert_non_empty_text(
                self.transition_validation_report_ref,
                field_name="transition_validation_report_ref",
            ),
        )
        _assert_unique_rows(
            self.frontier_rows,
            attr_name="frontier_ref",
            field_name="frontier_rows",
        )
        object.__setattr__(
            self,
            "frontier_rows",
            sorted(self.frontier_rows, key=lambda row: row.frontier_ref),
        )
        if self.canonical_output_hash is not None:
            expected = canonical_hash(self, drop_keys={"canonical_output_hash"})
            if self.canonical_output_hash != expected:
                raise ValueError("canonical_output_hash must match canonical frontier payload")
        return self


class RepoTransitionBrokerNonAuthorityGuardrail(_OtbBase):
    schema: Literal[REPO_TRANSITION_BROKER_NON_AUTHORITY_GUARDRAIL_SCHEMA]
    transition_broker_non_authority_guardrail_ref: str
    semantic_authority_posture: Literal["no_semantic_judgment_authority"]
    domain_ontology_authority_posture: Literal["no_domain_ontology_authority"]
    hob_closure_authority_posture: Literal["no_hob_closure_authority"]
    probe_generation_authority_posture: Literal["no_probe_generation_authority"]
    probe_execution_authority_posture: Literal["no_probe_execution_authority"]
    implementation_authority_posture: Literal["no_implementation_authority"]
    worker_dispatch_authority_posture: Literal["no_worker_dispatch_authority"]
    product_authority_posture: Literal["no_product_authority"]
    official_eval_authority_posture: Literal["no_official_eval_authority"]
    future_family_selection_posture: Literal["no_future_family_selection_authority"]
    slice_scope_posture: Literal["otb_0a_structural_transition_validation_only"]
    closure_planning_posture: Literal["deferred_to_otb_0b"]
    delta_attribution_posture: Literal["deferred_to_otb_0c"]

    @model_validator(mode="after")
    def _validate_guardrail(self) -> RepoTransitionBrokerNonAuthorityGuardrail:
        object.__setattr__(
            self,
            "transition_broker_non_authority_guardrail_ref",
            _assert_non_empty_text(
                self.transition_broker_non_authority_guardrail_ref,
                field_name="transition_broker_non_authority_guardrail_ref",
            ),
        )
        return self


def load_phase_catalog(
    payload: RepoPhaseCircuitCatalog | dict[str, Any],
) -> RepoPhaseCircuitCatalog:
    if isinstance(payload, RepoPhaseCircuitCatalog):
        return payload
    return RepoPhaseCircuitCatalog.model_validate(payload)


def validate_phase_catalog(
    catalog: RepoPhaseCircuitCatalog | dict[str, Any],
) -> RepoPhaseCircuitCatalog:
    return load_phase_catalog(catalog)


def load_bridge_contract(
    payload: RepoPhaseBridgeContract | dict[str, Any],
) -> RepoPhaseBridgeContract:
    if isinstance(payload, RepoPhaseBridgeContract):
        return payload
    return RepoPhaseBridgeContract.model_validate(payload)


def validate_bridge_contract(
    catalog: RepoPhaseCircuitCatalog,
    bridge: RepoPhaseBridgeContract | dict[str, Any],
) -> RepoPhaseBridgeContract:
    contract = load_bridge_contract(bridge)
    _validate_circuit_binding(
        catalog,
        contract.circuit_id,
        contract.circuit_version,
        contract.circuit_hash,
    )
    transition = _transition_by_id(catalog).get(contract.transition_id)
    if transition is None:
        raise ValueError(f"bridge references unknown transition_id {contract.transition_id!r}")
    if (
        transition.from_phase != contract.from_phase
        or transition.to_phase != contract.to_phase
        or transition.bridge_contract_ref != contract.bridge_contract_ref
    ):
        raise ValueError("bridge transition fields must match phase circuit transition row")
    phase_ids = {row.phase_id for row in catalog.phase_rows}
    unknown_next = sorted(set(contract.U_bridge.next_allowed_phases) - phase_ids)
    if unknown_next:
        raise ValueError(f"bridge references unknown next_allowed_phases: {unknown_next}")
    return contract


def validate_transition(
    *,
    catalog: RepoPhaseCircuitCatalog,
    bridge: RepoPhaseBridgeContract,
    transition_claim: RepoPhaseTransitionClaim | dict[str, Any],
    artifacts: list[PhaseArtifactRow | dict[str, Any]],
    evidence: list[EvidenceRow | dict[str, Any]],
    obligations: list[ObligationTransferRow | dict[str, Any]],
) -> RepoPhaseTransitionValidationReport:
    bridge = validate_bridge_contract(catalog, bridge)
    claim = (
        transition_claim
        if isinstance(transition_claim, RepoPhaseTransitionClaim)
        else RepoPhaseTransitionClaim.model_validate(transition_claim)
    )
    artifact_rows = [
        row if isinstance(row, PhaseArtifactRow) else PhaseArtifactRow.model_validate(row)
        for row in artifacts
    ]
    evidence_rows = [
        row if isinstance(row, EvidenceRow) else EvidenceRow.model_validate(row) for row in evidence
    ]
    obligation_rows = [
        row if isinstance(row, ObligationTransferRow) else ObligationTransferRow.model_validate(row)
        for row in obligations
    ]

    diagnostics: list[TransitionDiagnosticRow] = []
    frontier_rows: list[LegalFrontierRow] = []
    completeness: BridgeCompletenessStatus = "complete"
    hash_mismatch = False

    def mark_completeness(status: BridgeCompletenessStatus) -> None:
        nonlocal completeness
        if completeness == "complete":
            completeness = status

    def add_diag(
        *,
        code: str,
        bridge_field: Literal["O_bridge", "E_bridge", "D_bridge", "U_bridge", "claim", "catalog"],
        message: str,
        action: RequiredNextAction,
        object_refs: list[str] | None = None,
        evidence_refs: list[str] | None = None,
        severity: DiagnosticSeverity = "error",
    ) -> str:
        diagnostic_ref = f"otb-0a-diagnostic:{len(diagnostics) + 1:04d}:{code.lower()}"
        diagnostics.append(
            TransitionDiagnosticRow(
                diagnostic_ref=diagnostic_ref,
                severity=severity,
                diagnostic_code=code,
                bridge_field=bridge_field,
                message=message,
                object_refs=object_refs or [],
                evidence_refs=evidence_refs or [],
                required_action=action,
            )
        )
        return diagnostic_ref

    def add_frontier(
        *,
        reason: FrontierReason,
        action: RequiredNextAction,
        diagnostic_ref: str,
        requested_posture: ReadinessPosture | None = None,
        maximum_supported_posture: ReadinessPosture | None = None,
        downgrade_basis: list[str] | None = None,
        target_phase_constraint: str | None = None,
    ) -> None:
        frontier_rows.append(
            LegalFrontierRow(
                frontier_ref=f"otb-0a-frontier:{len(frontier_rows) + 1:04d}:{reason}",
                transition_id=bridge.transition_id,
                frontier_reason=reason,
                required_next_action=action,
                authority_posture="broker_validation_only_not_execution_authority",
                target_phase_constraint=target_phase_constraint or bridge.to_phase,
                requested_posture=requested_posture,
                maximum_supported_posture=maximum_supported_posture,
                downgrade_basis=downgrade_basis or [],
                required_revalidation_frontier=[action],
                source_diagnostic_refs=[diagnostic_ref],
            )
        )

    def diagnose(
        *,
        code: str,
        bridge_field: Literal["O_bridge", "E_bridge", "D_bridge", "U_bridge", "claim", "catalog"],
        message: str,
        action: RequiredNextAction,
        reason: FrontierReason,
        object_refs: list[str] | None = None,
        evidence_refs: list[str] | None = None,
        requested_posture: ReadinessPosture | None = None,
        maximum_supported_posture: ReadinessPosture | None = None,
        downgrade_basis: list[str] | None = None,
        completeness_status: BridgeCompletenessStatus | None = None,
    ) -> None:
        if completeness_status is not None:
            mark_completeness(completeness_status)
        diagnostic_ref = add_diag(
            code=code,
            bridge_field=bridge_field,
            message=message,
            action=action,
            object_refs=object_refs,
            evidence_refs=evidence_refs,
        )
        add_frontier(
            reason=reason,
            action=action,
            diagnostic_ref=diagnostic_ref,
            requested_posture=requested_posture,
            maximum_supported_posture=maximum_supported_posture,
            downgrade_basis=downgrade_basis,
        )

    if _claim_mismatches(catalog, bridge, claim):
        diagnose(
            code="TRANSITION_CLAIM_MISMATCH",
            bridge_field="claim",
            message="transition claim must match catalog and bridge transition identity",
            action="route_to_human_review",
            reason="conflict_isolated",
        )

    artifact_by_ref = {row.artifact_ref: row for row in artifact_rows}
    evidence_by_ref = {row.evidence_ref: row for row in evidence_rows}
    obligation_by_ref = {row.obligation_ref: row for row in obligation_rows}

    for required in bridge.O_bridge.required_objects:
        artifact = _select_required_artifact(required, artifact_rows)
        if artifact is None:
            diagnose(
                code="MISSING_REQUIRED_OBJECT",
                bridge_field="O_bridge",
                message=f"required object {required.object_kind!r} is absent",
                action="produce_object",
                reason="missing_object",
                object_refs=[required.required_artifact_ref or required.object_kind],
                completeness_status="missing_required_object",
            )
            continue
        expected_catalog_hash = catalog.circuit_hash or canonical_hash(
            catalog,
            drop_keys={"circuit_hash"},
        )
        if artifact.catalog_hash != expected_catalog_hash:
            hash_mismatch = True
            diagnose(
                code="ARTIFACT_CATALOG_HASH_MISMATCH",
                bridge_field="O_bridge",
                message=f"artifact {artifact.artifact_ref!r} is bound to stale catalog hash",
                action="refresh_artifact",
                reason="stale_artifact",
                object_refs=[artifact.artifact_ref],
            )
        expected_bridge_hash = bridge.bridge_hash or canonical_hash(
            bridge,
            drop_keys={"bridge_hash"},
        )
        if artifact.bridge_hash != expected_bridge_hash:
            hash_mismatch = True
            diagnose(
                code="ARTIFACT_BRIDGE_HASH_MISMATCH",
                bridge_field="O_bridge",
                message=f"artifact {artifact.artifact_ref!r} is bound to stale bridge hash",
                action="refresh_artifact",
                reason="stale_artifact",
                object_refs=[artifact.artifact_ref],
            )
        mismatched_hash = _first_hash_mismatch(required, artifact)
        if mismatched_hash is not None:
            hash_mismatch = True
            diagnose(
                code="ARTIFACT_HASH_MISMATCH",
                bridge_field="O_bridge",
                message=f"artifact {artifact.artifact_ref!r} has mismatched {mismatched_hash}",
                action="refresh_artifact",
                reason="stale_artifact",
                object_refs=[artifact.artifact_ref],
            )
        if required.required_authority_layer is not None and (
            artifact.authority_layer != required.required_authority_layer
        ):
            diagnose(
                code="ARTIFACT_AUTHORITY_LAYER_MISMATCH",
                bridge_field="O_bridge",
                message=f"artifact {artifact.artifact_ref!r} has wrong authority layer",
                action="route_to_human_review",
                reason="blocked_equivalence",
                object_refs=[artifact.artifact_ref],
            )
        if required.required_source_phase is not None and (
            artifact.source_phase != required.required_source_phase
        ):
            diagnose(
                code="ARTIFACT_SOURCE_PHASE_MISMATCH",
                bridge_field="O_bridge",
                message=f"artifact {artifact.artifact_ref!r} comes from wrong source phase",
                action="refresh_artifact",
                reason="stale_artifact",
                object_refs=[artifact.artifact_ref],
            )
        if required.required_object_identity_claim is not None and (
            artifact.object_identity_claim != required.required_object_identity_claim
        ):
            diagnose(
                code="OBJECT_IDENTITY_CLAIM_MISMATCH",
                bridge_field="O_bridge",
                message=f"artifact {artifact.artifact_ref!r} has wrong object identity claim",
                action="refresh_artifact",
                reason="stale_artifact",
                object_refs=[artifact.artifact_ref],
            )
        missing_freshness = sorted(
            set(required.required_freshness_basis) - set(artifact.freshness_basis)
        )
        if missing_freshness:
            missing_freshness_text = ", ".join(missing_freshness)
            diagnose(
                code="STALE_FRESHNESS_BASIS",
                bridge_field="O_bridge",
                message=(
                    f"artifact {artifact.artifact_ref!r} lacks freshness basis "
                    f"{missing_freshness_text}"
                ),
                action="refresh_artifact",
                reason="stale_artifact",
                object_refs=[artifact.artifact_ref],
            )

    for artifact_ref in claim.artifact_refs:
        if artifact_ref not in artifact_by_ref:
            diagnose(
                code="CLAIM_REFERENCES_UNKNOWN_ARTIFACT",
                bridge_field="claim",
                message=f"claim references unknown artifact {artifact_ref!r}",
                action="produce_object",
                reason="missing_object",
                object_refs=[artifact_ref],
                completeness_status="missing_required_object",
            )

    _validate_evidence_bridge(
        bridge=bridge,
        claim=claim,
        artifact_rows=artifact_rows,
        evidence_by_ref=evidence_by_ref,
        diagnose=diagnose,
        mark_completeness=mark_completeness,
    )
    _validate_obligation_bridge(
        bridge=bridge,
        claim=claim,
        obligation_by_ref=obligation_by_ref,
        diagnose=diagnose,
        mark_completeness=mark_completeness,
    )
    _validate_use_bridge(bridge=bridge, claim=claim, diagnose=diagnose)

    consistency: BridgeConsistencyStatus = "consistent"
    if hash_mismatch:
        consistency = "hash_mismatch"
    elif any(row.bridge_field == "claim" for row in diagnostics):
        consistency = "inconsistent"
    validation_status: TransitionValidationStatus = "valid_for_broker_frontier"
    if diagnostics:
        validation_status = "stale" if hash_mismatch else "blocked"
    return RepoPhaseTransitionValidationReport(
        schema=REPO_PHASE_TRANSITION_VALIDATION_REPORT_SCHEMA,
        transition_validation_report_ref=f"otb-0a-validation:{claim.transition_claim_ref}",
        circuit_id=catalog.circuit_id,
        circuit_version=catalog.circuit_version,
        circuit_hash=catalog.circuit_hash or canonical_hash(catalog, drop_keys={"circuit_hash"}),
        transition_id=bridge.transition_id,
        bridge_contract_ref=bridge.bridge_contract_ref,
        transition_claim_ref=claim.transition_claim_ref,
        validation_status=validation_status,
        bridge_consistency_status=consistency,
        bridge_completeness_status=completeness,
        diagnostic_rows=diagnostics,
        frontier_rows=frontier_rows,
    )


def emit_legal_frontier(
    report: RepoPhaseTransitionValidationReport,
) -> RepoPhaseLegalFrontierReport:
    return RepoPhaseLegalFrontierReport(
        schema=REPO_PHASE_LEGAL_FRONTIER_REPORT_SCHEMA,
        legal_frontier_report_ref=f"otb-0a-legal-frontier:{report.transition_validation_report_ref}",
        transition_validation_report_ref=report.transition_validation_report_ref,
        frontier_rows=report.frontier_rows,
    )


def default_non_authority_guardrail(
    guardrail_ref: str = "guardrail:otb-0a:default",
) -> RepoTransitionBrokerNonAuthorityGuardrail:
    return RepoTransitionBrokerNonAuthorityGuardrail(
        schema=REPO_TRANSITION_BROKER_NON_AUTHORITY_GUARDRAIL_SCHEMA,
        transition_broker_non_authority_guardrail_ref=guardrail_ref,
        semantic_authority_posture="no_semantic_judgment_authority",
        domain_ontology_authority_posture="no_domain_ontology_authority",
        hob_closure_authority_posture="no_hob_closure_authority",
        probe_generation_authority_posture="no_probe_generation_authority",
        probe_execution_authority_posture="no_probe_execution_authority",
        implementation_authority_posture="no_implementation_authority",
        worker_dispatch_authority_posture="no_worker_dispatch_authority",
        product_authority_posture="no_product_authority",
        official_eval_authority_posture="no_official_eval_authority",
        future_family_selection_posture="no_future_family_selection_authority",
        slice_scope_posture="otb_0a_structural_transition_validation_only",
        closure_planning_posture="deferred_to_otb_0b",
        delta_attribution_posture="deferred_to_otb_0c",
    )


def _validate_circuit_binding(
    catalog: RepoPhaseCircuitCatalog,
    circuit_id: str,
    circuit_version: str,
    circuit_hash: str,
) -> None:
    if circuit_id != catalog.circuit_id or circuit_version != catalog.circuit_version:
        raise ValueError("artifact circuit_id/circuit_version must match catalog")
    expected = catalog.circuit_hash or canonical_hash(catalog, drop_keys={"circuit_hash"})
    if circuit_hash != expected:
        raise ValueError("artifact circuit_hash must match catalog")


def _transition_by_id(catalog: RepoPhaseCircuitCatalog) -> dict[str, TransitionRow]:
    return {row.transition_id: row for row in catalog.transition_rows}


def _claim_mismatches(
    catalog: RepoPhaseCircuitCatalog,
    bridge: RepoPhaseBridgeContract,
    claim: RepoPhaseTransitionClaim,
) -> bool:
    expected_circuit_hash = catalog.circuit_hash or canonical_hash(
        catalog,
        drop_keys={"circuit_hash"},
    )
    return (
        claim.circuit_id != catalog.circuit_id
        or claim.circuit_version != catalog.circuit_version
        or claim.circuit_hash != expected_circuit_hash
        or claim.transition_id != bridge.transition_id
        or claim.from_phase != bridge.from_phase
        or claim.to_phase != bridge.to_phase
    )


def _select_required_artifact(
    required: RequiredObjectRow,
    artifact_rows: list[PhaseArtifactRow],
) -> PhaseArtifactRow | None:
    if required.required_artifact_ref is not None:
        return next(
            (row for row in artifact_rows if row.artifact_ref == required.required_artifact_ref),
            None,
        )
    return next((row for row in artifact_rows if row.artifact_kind == required.object_kind), None)


def _first_hash_mismatch(required: RequiredObjectRow, artifact: PhaseArtifactRow) -> str | None:
    hash_fields = (
        ("required_file_hash", "file_hash"),
        ("required_canonical_payload_hash", "canonical_payload_hash"),
        ("required_semantic_object_hash", "semantic_object_hash"),
        ("required_evidence_boundary_hash", "evidence_boundary_hash"),
        ("required_obligation_set_hash", "obligation_set_hash"),
    )
    for required_field, artifact_field in hash_fields:
        expected = getattr(required, required_field)
        if expected is not None and getattr(artifact, artifact_field) != expected:
            return artifact_field
    return None


def _validate_evidence_bridge(
    *,
    bridge: RepoPhaseBridgeContract,
    claim: RepoPhaseTransitionClaim,
    artifact_rows: list[PhaseArtifactRow],
    evidence_by_ref: dict[str, EvidenceRow],
    diagnose: Any,
    mark_completeness: Any,
) -> None:
    root_evidence_refs = set(claim.evidence_refs)
    artifact_by_ref = {row.artifact_ref: row for row in artifact_rows}
    for artifact_ref in claim.artifact_refs:
        artifact = artifact_by_ref.get(artifact_ref)
        if artifact is not None:
            root_evidence_refs.update(artifact.evidence_refs)
    for token in bridge.E_bridge.required_evidence:
        if not _evidence_token_present(token, evidence_by_ref):
            mark_completeness("missing_required_evidence")
            diagnose(
                code="MISSING_REQUIRED_EVIDENCE",
                bridge_field="E_bridge",
                message=f"required evidence {token!r} is absent",
                action="route_to_human_review",
                reason="missing_warrant",
                evidence_refs=[token],
                completeness_status="missing_required_evidence",
            )
    for evidence_ref in sorted(root_evidence_refs):
        evidence = evidence_by_ref.get(evidence_ref)
        if evidence is None:
            diagnose(
                code="UNKNOWN_EVIDENCE_REF",
                bridge_field="E_bridge",
                message=f"transition input references unknown evidence {evidence_ref!r}",
                action="route_to_human_review",
                reason="missing_warrant",
                evidence_refs=[evidence_ref],
                completeness_status="missing_required_evidence",
            )
            continue
        if evidence.boundary_posture is None:
            diagnose(
                code="MISSING_EVIDENCE_BOUNDARY_POSTURE",
                bridge_field="E_bridge",
                message=f"evidence {evidence_ref!r} lacks boundary posture",
                action="route_to_human_review",
                reason="missing_warrant",
                evidence_refs=[evidence_ref],
                completeness_status="missing_warrant",
            )
        if evidence.clean_first_pass_posture is None:
            diagnose(
                code="MISSING_CLEAN_FIRST_PASS_POSTURE",
                bridge_field="E_bridge",
                message=f"evidence {evidence_ref!r} lacks clean-first-pass posture",
                action="route_to_human_review",
                reason="missing_warrant",
                evidence_refs=[evidence_ref],
                completeness_status="missing_warrant",
            )
        elif (
            evidence.clean_first_pass_posture == "clean"
            and evidence.authority_layer == "post_eval_pressure"
        ):
            diagnose(
                code="CLEAN_FIRST_PASS_POSTURE_OVERCLAIM",
                bridge_field="E_bridge",
                message=f"post-eval evidence {evidence_ref!r} cannot claim clean posture",
                action="remove_forbidden_evidence",
                reason="forbidden_evidence",
                evidence_refs=[evidence_ref],
            )
        forbidden = _first_forbidden_evidence_token(
            evidence_ref=evidence_ref,
            evidence_by_ref=evidence_by_ref,
            forbidden_tokens=set(bridge.E_bridge.forbidden_evidence),
        )
        if forbidden is not None:
            diagnose(
                code="FORBIDDEN_EVIDENCE_CONTAMINATION",
                bridge_field="E_bridge",
                message=(
                    f"evidence {evidence_ref!r} is contaminated by forbidden token "
                    f"{forbidden!r}"
                ),
                action="remove_forbidden_evidence",
                reason="forbidden_evidence",
                evidence_refs=[evidence_ref, forbidden],
            )


def _evidence_token_present(token: str, evidence_by_ref: dict[str, EvidenceRow]) -> bool:
    for evidence in evidence_by_ref.values():
        if token in {evidence.evidence_ref, evidence.evidence_kind, *evidence.contamination_tags}:
            return True
    return False


def _first_forbidden_evidence_token(
    *,
    evidence_ref: str,
    evidence_by_ref: dict[str, EvidenceRow],
    forbidden_tokens: set[str],
) -> str | None:
    visited: set[str] = set()

    def walk(ref: str) -> str | None:
        if ref in visited:
            return None
        visited.add(ref)
        evidence = evidence_by_ref.get(ref)
        if evidence is None:
            return None
        tokens = {evidence.evidence_ref, evidence.evidence_kind, *evidence.contamination_tags}
        matched = sorted(tokens & forbidden_tokens)
        if matched:
            return matched[0]
        for parent_ref in evidence.derived_from_evidence_refs:
            result = walk(parent_ref)
            if result is not None:
                return result
        return None

    return walk(evidence_ref)


def _validate_obligation_bridge(
    *,
    bridge: RepoPhaseBridgeContract,
    claim: RepoPhaseTransitionClaim,
    obligation_by_ref: dict[str, ObligationTransferRow],
    diagnose: Any,
    mark_completeness: Any,
) -> None:
    required_refs = set(bridge.D_bridge.obligations_preserved)
    required_refs.update(claim.obligation_transfer_refs)
    for obligation_ref in sorted(required_refs):
        if obligation_ref not in obligation_by_ref:
            mark_completeness("missing_obligation_transfer")
            diagnose(
                code="SILENT_OBLIGATION_DROP",
                bridge_field="D_bridge",
                message=f"obligation {obligation_ref!r} is required but absent",
                action="discharge_or_defer_obligation",
                reason="silent_obligation_drop",
                object_refs=[obligation_ref],
                completeness_status="missing_obligation_transfer",
            )
    for row in obligation_by_ref.values():
        if row.transfer_status == "discharged" and row.discharge_ref is None:
            diagnose(
                code="DISCHARGE_REF_REQUIRED",
                bridge_field="D_bridge",
                message=f"discharged obligation {row.obligation_ref!r} lacks discharge_ref",
                action="discharge_or_defer_obligation",
                reason="silent_obligation_drop",
                object_refs=[row.obligation_ref],
                completeness_status="missing_obligation_transfer",
            )
        if row.transfer_status == "deferred" and (
            row.deferral_ref is None or row.deferral_risk_posture is None
        ):
            mark_completeness("missing_deferral_risk")
            diagnose(
                code="DEFERRAL_RISK_POSTURE_REQUIRED",
                bridge_field="D_bridge",
                message=f"deferred obligation {row.obligation_ref!r} lacks deferral risk posture",
                action="discharge_or_defer_obligation",
                reason="silent_obligation_drop",
                object_refs=[row.obligation_ref],
                completeness_status="missing_deferral_risk",
            )


def _validate_use_bridge(
    *,
    bridge: RepoPhaseBridgeContract,
    claim: RepoPhaseTransitionClaim,
    diagnose: Any,
) -> None:
    if claim.to_phase not in bridge.U_bridge.next_allowed_phases:
        diagnose(
            code="TARGET_PHASE_NOT_ALLOWED",
            bridge_field="U_bridge",
            message=f"target phase {claim.to_phase!r} is not allowed by bridge",
            action="route_to_human_review",
            reason="illegal_promotion",
            object_refs=[claim.to_phase],
        )
    if claim.claimed_promotion in bridge.U_bridge.forbidden_promotions:
        diagnose(
            code="FORBIDDEN_PROMOTION",
            bridge_field="U_bridge",
            message=f"promotion {claim.claimed_promotion!r} is forbidden by bridge",
            action="downgrade_promotion",
            reason="illegal_promotion",
            object_refs=[claim.transition_claim_ref],
        )
    if bridge.U_bridge.supported_readiness_postures and (
        claim.claimed_readiness_posture not in bridge.U_bridge.supported_readiness_postures
    ):
        maximum = (
            bridge.U_bridge.maximum_supported_posture
            or bridge.U_bridge.supported_readiness_postures[-1]
        )
        diagnose(
            code="POSTURE_DOWNGRADE_REQUIRED",
            bridge_field="U_bridge",
            message=(
                f"claimed posture {claim.claimed_readiness_posture!r} exceeds supported "
                f"postures {bridge.U_bridge.supported_readiness_postures!r}"
            ),
            action="downgrade_promotion",
            reason="posture_downgrade_required",
            object_refs=[claim.transition_claim_ref],
            requested_posture=claim.claimed_readiness_posture,
            maximum_supported_posture=maximum,
            downgrade_basis=["unsupported_readiness_posture"],
        )
