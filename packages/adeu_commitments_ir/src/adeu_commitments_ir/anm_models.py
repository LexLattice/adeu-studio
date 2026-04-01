from __future__ import annotations

from typing import Annotated, Any, Literal

from pydantic import BaseModel, ConfigDict, Field, TypeAdapter, model_validator
from urm_runtime.hashing import canonical_json, sha256_canonical_json

JsonScalar = str | int | float | bool | None

D1_NORMALIZED_IR_SCHEMA = "d1_normalized_ir@1"
PREDICATE_CONTRACTS_BOOTSTRAP_SCHEMA = "predicate_contracts_bootstrap@1"
CHECKER_FACT_BUNDLE_SCHEMA = "checker_fact_bundle@1"
POLICY_EVALUATION_RESULT_SET_SCHEMA = "policy_evaluation_result_set@1"
POLICY_OBLIGATION_LEDGER_SCHEMA = "policy_obligation_ledger@1"
ANM_MARKDOWN_COEXISTENCE_PROFILE_SCHEMA = "anm_markdown_coexistence_profile@1"

D1SchemaVersion = Literal["d1_normalized_ir@1"]
PredicateContractsBootstrapSchemaVersion = Literal["predicate_contracts_bootstrap@1"]
CheckerFactBundleSchemaVersion = Literal["checker_fact_bundle@1"]
PolicyEvaluationResultSetSchemaVersion = Literal["policy_evaluation_result_set@1"]
PolicyObligationLedgerSchemaVersion = Literal["policy_obligation_ledger@1"]
AnmMarkdownCoexistenceProfileSchemaVersion = Literal["anm_markdown_coexistence_profile@1"]

SelectorKind = Literal["bootstrap_string_selector"]
SelectorZeroMatchPolicy = Literal["allow_empty_with_notice"]
D1Modal = Literal["MUST", "MUST_NOT"]
AssertionKind = Literal["required", "explicit", "exactly_one", "comparison", "predicate_call"]
NormalizedPredicateId = Literal["present", "explicit", "cardinality_eq", "bind_to", "eq"]
QualifierKind = Literal["only_if", "unless"]
PredicateOwnerLayer = Literal["bootstrap_d"]
ArgumentKind = Literal["path", "integer", "scalar"]
FactType = Literal[
    "value_observation",
    "value_type_observation",
    "binding_observation",
    "carrier_read",
    "path_presence_observation",
    "path_cardinality_observation",
    "explicit_carriage_observation",
]
ProvenanceMode = Literal["direct", "derived", "indirect", "absent", "inconclusive"]
Applicability = Literal["active", "gated_off", "excepted"]
ObservedOutcome = Literal[
    "not_evaluated",
    "pass",
    "fail",
    "unknown_evidence",
    "unknown_resolution",
]
EffectiveVerdict = Literal[
    "pass",
    "fail",
    "waived",
    "deferred",
    "gated_off",
    "unknown_evidence",
    "unknown_resolution",
]
ResultScopeKind = Literal["subject_scoped", "clause_scope_blocker"]
LedgerState = Literal[
    "satisfied",
    "violated",
    "waived",
    "deferred",
    "gated_off",
    "blocked_unknown_evidence",
    "blocked_unknown_resolution",
]
NoticeKind = Literal["selector_zero_match"]
SourcePosture = Literal["standalone_anm", "companion_anm"]
CurrentMarkdownAuthorityRelation = Literal[
    "current_markdown_controlling",
    "coexisting_non_override",
    "later_lock_required_for_supersession",
]
MigrationPosture = Literal["none", "prefer_companion", "prefer_standalone", "defer_to_later_lock"]
CompanionEmbeddingPosture = Literal[
    "not_applicable",
    "embedded_in_host_markdown",
    "adjacent_companion_document",
]
AllowedConstrainAction = Literal[
    "reference_released_anm_artifact",
    "embed_authoritative_d1_block",
    "record_non_override_binding",
    "emit_migration_signal",
]
AdoptionBoundaryPosture = Literal["allowed_now", "allowed_with_later_lock", "forbidden_in_v47c"]
NonOverrideRule = Literal["current_markdown_not_overridden"]


def stable_payload_hash(value: Any) -> str:
    return sha256_canonical_json(value)


def _require_non_empty(value: str, *, field_name: str) -> str:
    normalized = value.strip()
    if not normalized:
        raise ValueError(f"{field_name} must not be empty")
    return normalized


def _require_sorted_unique(values: list[str], *, field_name: str) -> None:
    if any(not item for item in values):
        raise ValueError(f"{field_name} must not contain empty values")
    if values != sorted(values):
        raise ValueError(f"{field_name} must be lexicographically sorted")
    if len(values) != len(set(values)):
        raise ValueError(f"{field_name} must not contain duplicates")


class D1SelectorRef(BaseModel):
    model_config = ConfigDict(extra="forbid")

    selector_ref: str = Field(min_length=1)
    selector_source_text: str = Field(min_length=1)
    selector_kind: SelectorKind

    @model_validator(mode="after")
    def _validate_contract(self) -> "D1SelectorRef":
        self.selector_ref = _require_non_empty(self.selector_ref, field_name="selector_ref")
        self.selector_source_text = _require_non_empty(
            self.selector_source_text,
            field_name="selector_source_text",
        )
        return self


class D1Qualifier(BaseModel):
    model_config = ConfigDict(extra="forbid")

    qualifier_kind: QualifierKind
    normalized_predicate_id: NormalizedPredicateId
    target_path: str | None = None
    expected_scalar: JsonScalar = None
    expected_count: int | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "D1Qualifier":
        if self.target_path is not None:
            self.target_path = _require_non_empty(self.target_path, field_name="target_path")
        if self.normalized_predicate_id in {"present", "explicit", "bind_to"}:
            if self.target_path is None:
                raise ValueError("target_path is required for present/explicit/bind_to")
            if self.expected_scalar is not None or self.expected_count is not None:
                raise ValueError("present/explicit/bind_to do not accept expected payload")
        elif self.normalized_predicate_id == "cardinality_eq":
            if self.target_path is None or self.expected_count is None:
                raise ValueError("cardinality_eq requires target_path and expected_count")
        elif self.normalized_predicate_id == "eq":
            if self.target_path is None:
                raise ValueError("eq requires target_path")
        return self


class D1Clause(BaseModel):
    model_config = ConfigDict(extra="forbid")

    clause_ref: str = Field(min_length=1)
    clause_label: str = Field(min_length=1)
    modal: D1Modal
    assertion_kind: AssertionKind
    normalized_predicate_id: NormalizedPredicateId
    target_path: str | None = None
    expected_scalar: JsonScalar = None
    expected_count: int | None = None
    subject_selector_ref: str = Field(min_length=1)
    qualifiers: list[D1Qualifier] = Field(default_factory=list)
    origin_block_ref: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "D1Clause":
        self.clause_ref = _require_non_empty(self.clause_ref, field_name="clause_ref")
        self.clause_label = _require_non_empty(self.clause_label, field_name="clause_label")
        self.subject_selector_ref = _require_non_empty(
            self.subject_selector_ref,
            field_name="subject_selector_ref",
        )
        self.origin_block_ref = _require_non_empty(
            self.origin_block_ref,
            field_name="origin_block_ref",
        )
        if self.target_path is not None:
            self.target_path = _require_non_empty(self.target_path, field_name="target_path")
        qualifier_identity = [
            (
                item.qualifier_kind,
                item.normalized_predicate_id,
                item.target_path or "",
                item.expected_count if item.expected_count is not None else -1,
                canonical_json(item.expected_scalar),
            )
            for item in self.qualifiers
        ]
        if qualifier_identity != sorted(qualifier_identity):
            raise ValueError(
                "qualifiers must be sorted by "
                "(qualifier_kind, normalized_predicate_id, target_path)"
            )
        if self.assertion_kind in {"required", "explicit"}:
            if self.target_path is None:
                raise ValueError("target_path is required for required/explicit assertions")
        elif self.assertion_kind == "exactly_one":
            if self.target_path is None or self.expected_count != 1:
                raise ValueError("exactly_one requires target_path and expected_count = 1")
        elif self.assertion_kind == "comparison":
            if self.target_path is None:
                raise ValueError("comparison requires target_path")
        elif self.assertion_kind == "predicate_call":
            if self.target_path is None:
                raise ValueError("predicate_call requires target_path in v47a")

        if self.modal == "MUST_NOT" and self.assertion_kind != "comparison":
            raise ValueError("MUST_NOT is restricted to comparison assertions in v47a")
        return self


class D1NormalizedIR(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: D1SchemaVersion = D1_NORMALIZED_IR_SCHEMA
    d1_ir_id: str = Field(min_length=1)
    source_doc_ref: str = Field(min_length=1)
    source_doc_sha256: str = Field(min_length=1)
    source_block_refs: list[str] = Field(default_factory=list)
    selector_refs: list[D1SelectorRef] = Field(default_factory=list)
    selector_zero_match_policy: SelectorZeroMatchPolicy
    clauses: list[D1Clause] = Field(default_factory=list)
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "D1NormalizedIR":
        self.d1_ir_id = _require_non_empty(self.d1_ir_id, field_name="d1_ir_id")
        self.source_doc_ref = _require_non_empty(self.source_doc_ref, field_name="source_doc_ref")
        self.source_doc_sha256 = _require_non_empty(
            self.source_doc_sha256,
            field_name="source_doc_sha256",
        )
        self.semantic_hash = _require_non_empty(self.semantic_hash, field_name="semantic_hash")
        _require_sorted_unique(self.source_block_refs, field_name="source_block_refs")
        selector_ids = [item.selector_ref for item in self.selector_refs]
        _require_sorted_unique(selector_ids, field_name="selector_refs.selector_ref")
        clause_ids = [item.clause_ref for item in self.clauses]
        _require_sorted_unique(clause_ids, field_name="clauses.clause_ref")
        selector_set = set(selector_ids)
        for clause in self.clauses:
            if clause.subject_selector_ref not in selector_set:
                raise ValueError(
                    "clause "
                    f"{clause.clause_ref} references unknown selector "
                    f"{clause.subject_selector_ref}"
                )
        return self


class PredicateArgumentSpec(BaseModel):
    model_config = ConfigDict(extra="forbid")

    name: str = Field(min_length=1)
    kind: ArgumentKind


class PredicateContract(BaseModel):
    model_config = ConfigDict(extra="forbid")

    predicate_id: str = Field(min_length=1)
    owner_layer: PredicateOwnerLayer
    version: str = Field(min_length=1)
    argument_schema: list[PredicateArgumentSpec] = Field(default_factory=list)
    required_evidence_kinds: list[str] = Field(default_factory=list)
    truth_conditions: list[str] = Field(default_factory=list)
    evidence_failure_conditions: list[str] = Field(default_factory=list)
    resolution_failure_conditions: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "PredicateContract":
        self.predicate_id = _require_non_empty(self.predicate_id, field_name="predicate_id")
        self.version = _require_non_empty(self.version, field_name="version")
        _require_sorted_unique(self.required_evidence_kinds, field_name="required_evidence_kinds")
        _require_sorted_unique(self.truth_conditions, field_name="truth_conditions")
        _require_sorted_unique(
            self.evidence_failure_conditions,
            field_name="evidence_failure_conditions",
        )
        _require_sorted_unique(
            self.resolution_failure_conditions,
            field_name="resolution_failure_conditions",
        )
        return self


class PredicateContractsBootstrap(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: PredicateContractsBootstrapSchemaVersion = PREDICATE_CONTRACTS_BOOTSTRAP_SCHEMA
    predicate_contract_bundle_id: str = Field(min_length=1)
    contracts: list[PredicateContract] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "PredicateContractsBootstrap":
        self.predicate_contract_bundle_id = _require_non_empty(
            self.predicate_contract_bundle_id,
            field_name="predicate_contract_bundle_id",
        )
        contract_ids = [item.predicate_id for item in self.contracts]
        _require_sorted_unique(contract_ids, field_name="contracts.predicate_id")
        return self


class FactProvenance(BaseModel):
    model_config = ConfigDict(extra="forbid")

    carrier_ref: str = Field(min_length=1)
    mode: ProvenanceMode
    notes: str | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "FactProvenance":
        self.carrier_ref = _require_non_empty(self.carrier_ref, field_name="carrier_ref")
        if self.notes is not None:
            self.notes = _require_non_empty(self.notes, field_name="notes")
        return self


class _CheckerFactRowBase(BaseModel):
    model_config = ConfigDict(extra="forbid")

    fact_id: str = Field(min_length=1)
    subject_ref: str = Field(min_length=1)
    fact_type: FactType
    provenance: FactProvenance
    checker_id: str = Field(min_length=1)
    emitted_at: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "_CheckerFactRowBase":
        self.fact_id = _require_non_empty(self.fact_id, field_name="fact_id")
        self.subject_ref = _require_non_empty(self.subject_ref, field_name="subject_ref")
        self.checker_id = _require_non_empty(self.checker_id, field_name="checker_id")
        self.emitted_at = _require_non_empty(self.emitted_at, field_name="emitted_at")
        return self


class ValueObservationFact(_CheckerFactRowBase):
    fact_type: Literal["value_observation"] = "value_observation"
    path: str = Field(min_length=1)
    values: list[JsonScalar] = Field(default_factory=list)


class ValueTypeObservationFact(_CheckerFactRowBase):
    fact_type: Literal["value_type_observation"] = "value_type_observation"
    path: str = Field(min_length=1)
    values: list[str] = Field(default_factory=list)


class BindingObservationFact(_CheckerFactRowBase):
    fact_type: Literal["binding_observation"] = "binding_observation"
    binding_payload: dict[str, JsonScalar] = Field(default_factory=dict)


class CarrierReadFact(_CheckerFactRowBase):
    fact_type: Literal["carrier_read"] = "carrier_read"
    carrier_payload: dict[str, JsonScalar] = Field(default_factory=dict)


class PathPresenceObservationFact(_CheckerFactRowBase):
    fact_type: Literal["path_presence_observation"] = "path_presence_observation"
    path: str = Field(min_length=1)
    values: list[bool] = Field(default_factory=list)


class PathCardinalityObservationFact(_CheckerFactRowBase):
    fact_type: Literal["path_cardinality_observation"] = "path_cardinality_observation"
    path: str = Field(min_length=1)
    values: list[int] = Field(default_factory=list)


class ExplicitCarriageObservationFact(_CheckerFactRowBase):
    fact_type: Literal["explicit_carriage_observation"] = "explicit_carriage_observation"
    path: str = Field(min_length=1)
    values: list[bool] = Field(default_factory=list)


CheckerFactRow = Annotated[
    ValueObservationFact
    | ValueTypeObservationFact
    | BindingObservationFact
    | CarrierReadFact
    | PathPresenceObservationFact
    | PathCardinalityObservationFact
    | ExplicitCarriageObservationFact,
    Field(discriminator="fact_type"),
]
_CHECKER_FACT_ROW_ADAPTER = TypeAdapter(CheckerFactRow)


class CheckerProfile(BaseModel):
    model_config = ConfigDict(extra="forbid")

    checker_profile_id: str = Field(min_length=1)
    checker_ids: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "CheckerProfile":
        self.checker_profile_id = _require_non_empty(
            self.checker_profile_id,
            field_name="checker_profile_id",
        )
        _require_sorted_unique(self.checker_ids, field_name="checker_ids")
        return self


class CheckerFactBundle(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: CheckerFactBundleSchemaVersion = CHECKER_FACT_BUNDLE_SCHEMA
    bundle_id: str = Field(min_length=1)
    scope_snapshot: str = Field(min_length=1)
    checker_profile: CheckerProfile
    facts: list[CheckerFactRow] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "CheckerFactBundle":
        self.bundle_id = _require_non_empty(self.bundle_id, field_name="bundle_id")
        self.scope_snapshot = _require_non_empty(
            self.scope_snapshot,
            field_name="scope_snapshot",
        )
        fact_ids = [item.fact_id for item in self.facts]
        _require_sorted_unique(fact_ids, field_name="facts.fact_id")
        return self


class EvaluationNotice(BaseModel):
    model_config = ConfigDict(extra="forbid")

    notice_id: str = Field(min_length=1)
    notice_kind: NoticeKind
    clause_ref: str = Field(min_length=1)
    selector_ref: str = Field(min_length=1)
    message: str = Field(min_length=1)


class _ResultRowBase(BaseModel):
    model_config = ConfigDict(extra="forbid")

    result_id: str = Field(min_length=1)
    clause_ref: str = Field(min_length=1)
    clause_semantic_hash: str = Field(min_length=1)
    result_scope_kind: ResultScopeKind
    applicability: Applicability
    observed_outcome: ObservedOutcome
    effective_verdict: EffectiveVerdict
    supporting_fact_refs: list[str] = Field(default_factory=list)
    supporting_contract_refs: list[str] = Field(default_factory=list)
    message: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "_ResultRowBase":
        self.result_id = _require_non_empty(self.result_id, field_name="result_id")
        self.clause_ref = _require_non_empty(self.clause_ref, field_name="clause_ref")
        self.clause_semantic_hash = _require_non_empty(
            self.clause_semantic_hash,
            field_name="clause_semantic_hash",
        )
        _require_sorted_unique(self.supporting_fact_refs, field_name="supporting_fact_refs")
        _require_sorted_unique(
            self.supporting_contract_refs,
            field_name="supporting_contract_refs",
        )
        self.message = _require_non_empty(self.message, field_name="message")
        return self


class SubjectScopedResultRow(_ResultRowBase):
    result_scope_kind: Literal["subject_scoped"] = "subject_scoped"
    subject_ref: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_subject(self) -> "SubjectScopedResultRow":
        self.subject_ref = _require_non_empty(self.subject_ref, field_name="subject_ref")
        return self


class ClauseScopeBlockerResultRow(_ResultRowBase):
    result_scope_kind: Literal["clause_scope_blocker"] = "clause_scope_blocker"

    @model_validator(mode="after")
    def _validate_clause_scope(self) -> "ClauseScopeBlockerResultRow":
        if self.observed_outcome not in {"unknown_evidence", "unknown_resolution"}:
            raise ValueError("clause_scope_blocker rows require unknown_* observed outcome")
        if self.effective_verdict not in {"unknown_evidence", "unknown_resolution"}:
            raise ValueError("clause_scope_blocker rows require unknown_* effective verdict")
        return self


PolicyEvaluationResultRow = Annotated[
    SubjectScopedResultRow | ClauseScopeBlockerResultRow,
    Field(discriminator="result_scope_kind"),
]
_POLICY_EVALUATION_RESULT_ROW_ADAPTER = TypeAdapter(PolicyEvaluationResultRow)


class PolicyEvaluationResultSet(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: PolicyEvaluationResultSetSchemaVersion = POLICY_EVALUATION_RESULT_SET_SCHEMA
    result_set_id: str = Field(min_length=1)
    scope_snapshot: str = Field(min_length=1)
    d_ir_ref: str = Field(min_length=1)
    fact_bundle_ref: str = Field(min_length=1)
    predicate_contract_ref: str = Field(min_length=1)
    results: list[PolicyEvaluationResultRow] = Field(default_factory=list)
    notices: list[EvaluationNotice] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "PolicyEvaluationResultSet":
        self.result_set_id = _require_non_empty(self.result_set_id, field_name="result_set_id")
        self.scope_snapshot = _require_non_empty(
            self.scope_snapshot,
            field_name="scope_snapshot",
        )
        self.d_ir_ref = _require_non_empty(self.d_ir_ref, field_name="d_ir_ref")
        self.fact_bundle_ref = _require_non_empty(
            self.fact_bundle_ref,
            field_name="fact_bundle_ref",
        )
        self.predicate_contract_ref = _require_non_empty(
            self.predicate_contract_ref,
            field_name="predicate_contract_ref",
        )
        result_ids = [item.result_id for item in self.results]
        _require_sorted_unique(result_ids, field_name="results.result_id")
        notice_ids = [item.notice_id for item in self.notices]
        _require_sorted_unique(notice_ids, field_name="notices.notice_id")
        return self


class PolicyObligationLedgerRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    obligation_id: str = Field(min_length=1)
    clause_ref: str = Field(min_length=1)
    clause_semantic_hash: str = Field(min_length=1)
    subject_ref: str = Field(min_length=1)
    latest_applicability: Applicability
    latest_observed_outcome: ObservedOutcome
    latest_effective_verdict: EffectiveVerdict
    ledger_state: LedgerState
    first_seen_run: str = Field(min_length=1)
    latest_result_run: str = Field(min_length=1)
    waiver_ref: str | None = None
    deferral_ref: str | None = None
    updated_at: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "PolicyObligationLedgerRow":
        self.obligation_id = _require_non_empty(self.obligation_id, field_name="obligation_id")
        self.clause_ref = _require_non_empty(self.clause_ref, field_name="clause_ref")
        self.clause_semantic_hash = _require_non_empty(
            self.clause_semantic_hash,
            field_name="clause_semantic_hash",
        )
        self.subject_ref = _require_non_empty(self.subject_ref, field_name="subject_ref")
        self.first_seen_run = _require_non_empty(self.first_seen_run, field_name="first_seen_run")
        self.latest_result_run = _require_non_empty(
            self.latest_result_run,
            field_name="latest_result_run",
        )
        self.updated_at = _require_non_empty(self.updated_at, field_name="updated_at")
        mapping = {
            "pass": "satisfied",
            "fail": "violated",
            "waived": "waived",
            "deferred": "deferred",
            "gated_off": "gated_off",
            "unknown_evidence": "blocked_unknown_evidence",
            "unknown_resolution": "blocked_unknown_resolution",
        }
        expected_ledger_state = mapping[self.latest_effective_verdict]
        if self.ledger_state != expected_ledger_state:
            raise ValueError(
                f"{self.latest_effective_verdict} verdict must map to "
                f"{expected_ledger_state} ledger_state"
            )
        return self


class PolicyObligationLedger(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: PolicyObligationLedgerSchemaVersion = POLICY_OBLIGATION_LEDGER_SCHEMA
    ledger_id: str = Field(min_length=1)
    scope_snapshot: str = Field(min_length=1)
    result_set_refs: list[str] = Field(default_factory=list)
    rows: list[PolicyObligationLedgerRow] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "PolicyObligationLedger":
        self.ledger_id = _require_non_empty(self.ledger_id, field_name="ledger_id")
        self.scope_snapshot = _require_non_empty(
            self.scope_snapshot,
            field_name="scope_snapshot",
        )
        _require_sorted_unique(self.result_set_refs, field_name="result_set_refs")
        row_ids = [item.obligation_id for item in self.rows]
        _require_sorted_unique(row_ids, field_name="rows.obligation_id")
        return self


class MigrationDiscipline(BaseModel):
    model_config = ConfigDict(extra="forbid")

    repo_wide_migration_forbidden: bool
    current_markdown_supersession_requires_later_lock: bool
    standalone_posture_allowed: bool
    companion_posture_allowed: bool
    compatible_local_source_scopes: list[str] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    preferred_source_postures: list[SourcePosture] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )

    @model_validator(mode="after")
    def _validate_contract(self) -> "MigrationDiscipline":
        _require_sorted_unique(
            self.compatible_local_source_scopes,
            field_name="compatible_local_source_scopes",
        )
        if self.preferred_source_postures != sorted(set(self.preferred_source_postures)):
            raise ValueError("preferred_source_postures must be sorted and unique")
        return self


class AnmCoexistenceSourceRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    source_ref: str = Field(min_length=1)
    source_posture: SourcePosture
    current_markdown_authority_relation: CurrentMarkdownAuthorityRelation
    host_or_companion_ref: str | None = None
    companion_embedding_posture: CompanionEmbeddingPosture
    non_override_rule: NonOverrideRule
    allowed_constrain_actions: list[AllowedConstrainAction] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    migration_posture: MigrationPosture
    requires_later_lock_for_supersession: bool

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmCoexistenceSourceRow":
        self.source_ref = _require_non_empty(self.source_ref, field_name="source_ref")
        if self.host_or_companion_ref is not None:
            self.host_or_companion_ref = _require_non_empty(
                self.host_or_companion_ref,
                field_name="host_or_companion_ref",
            )
        if self.allowed_constrain_actions != sorted(set(self.allowed_constrain_actions)):
            raise ValueError("allowed_constrain_actions must be sorted and unique")
        expects_later_lock = (
            self.current_markdown_authority_relation
            == "later_lock_required_for_supersession"
        )
        if self.requires_later_lock_for_supersession != expects_later_lock:
            raise ValueError(
                "requires_later_lock_for_supersession must match "
                "current_markdown_authority_relation"
            )
        if self.source_posture == "standalone_anm":
            if self.host_or_companion_ref is not None:
                raise ValueError("standalone_anm rows may not set host_or_companion_ref")
            if self.companion_embedding_posture != "not_applicable":
                raise ValueError(
                    "standalone_anm rows require companion_embedding_posture = not_applicable"
                )
        else:
            if self.host_or_companion_ref is None:
                raise ValueError("companion_anm rows require host_or_companion_ref")
            if self.companion_embedding_posture == "not_applicable":
                raise ValueError(
                    "companion_anm rows must declare explicit companion_embedding_posture"
                )
            if self.current_markdown_authority_relation == "current_markdown_controlling":
                raise ValueError(
                    "companion_anm rows may not declare current_markdown_controlling"
                )
        return self


class AnmAdoptionBoundaryRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    consumer_surface: str = Field(min_length=1)
    adoption_boundary_posture: AdoptionBoundaryPosture
    allowed_now_actions: list[AllowedConstrainAction] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    later_lock_required_actions: list[AllowedConstrainAction] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    forbidden_actions: list[AllowedConstrainAction] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmAdoptionBoundaryRow":
        self.consumer_surface = _require_non_empty(
            self.consumer_surface,
            field_name="consumer_surface",
        )
        for field_name in (
            "allowed_now_actions",
            "later_lock_required_actions",
            "forbidden_actions",
        ):
            values = getattr(self, field_name)
            if values != sorted(set(values)):
                raise ValueError(f"{field_name} must be sorted and unique")
        action_sets = [
            set(self.allowed_now_actions),
            set(self.later_lock_required_actions),
            set(self.forbidden_actions),
        ]
        overlaps = (
            action_sets[0] & action_sets[1],
            action_sets[0] & action_sets[2],
            action_sets[1] & action_sets[2],
        )
        if any(overlaps):
            raise ValueError("adoption boundary action lists must not overlap")
        return self


class AnmMarkdownCoexistenceProfile(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: AnmMarkdownCoexistenceProfileSchemaVersion = ANM_MARKDOWN_COEXISTENCE_PROFILE_SCHEMA
    coexistence_profile_id: str = Field(min_length=1)
    snapshot_id: str = Field(min_length=1)
    snapshot_sha256: str = Field(min_length=1)
    source_scope_profile: str = Field(min_length=1)
    released_stack_refs: list[str] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    source_rows: list[AnmCoexistenceSourceRow] = Field(default_factory=list)
    migration_discipline: MigrationDiscipline
    adoption_boundary_rows: list[AnmAdoptionBoundaryRow] = Field(default_factory=list)
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmMarkdownCoexistenceProfile":
        self.coexistence_profile_id = _require_non_empty(
            self.coexistence_profile_id,
            field_name="coexistence_profile_id",
        )
        self.snapshot_id = _require_non_empty(self.snapshot_id, field_name="snapshot_id")
        self.snapshot_sha256 = _require_non_empty(
            self.snapshot_sha256,
            field_name="snapshot_sha256",
        )
        self.source_scope_profile = _require_non_empty(
            self.source_scope_profile,
            field_name="source_scope_profile",
        )
        self.semantic_hash = _require_non_empty(self.semantic_hash, field_name="semantic_hash")
        _require_sorted_unique(self.released_stack_refs, field_name="released_stack_refs")
        source_refs = [item.source_ref for item in self.source_rows]
        _require_sorted_unique(source_refs, field_name="source_rows.source_ref")
        consumer_surfaces = [item.consumer_surface for item in self.adoption_boundary_rows]
        _require_sorted_unique(
            consumer_surfaces,
            field_name="adoption_boundary_rows.consumer_surface",
        )
        return self


def canonicalize_d1_normalized_ir_payload(
    payload: D1NormalizedIR | dict[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload
        if isinstance(payload, D1NormalizedIR)
        else D1NormalizedIR.model_validate(payload)
    )
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonicalize_predicate_contracts_bootstrap_payload(
    payload: PredicateContractsBootstrap | dict[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload
        if isinstance(payload, PredicateContractsBootstrap)
        else PredicateContractsBootstrap.model_validate(payload)
    )
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonicalize_checker_fact_bundle_payload(
    payload: CheckerFactBundle | dict[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload
        if isinstance(payload, CheckerFactBundle)
        else CheckerFactBundle.model_validate(payload)
    )
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonicalize_policy_evaluation_result_set_payload(
    payload: PolicyEvaluationResultSet | dict[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload
        if isinstance(payload, PolicyEvaluationResultSet)
        else PolicyEvaluationResultSet.model_validate(payload)
    )
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonicalize_policy_obligation_ledger_payload(
    payload: PolicyObligationLedger | dict[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload
        if isinstance(payload, PolicyObligationLedger)
        else PolicyObligationLedger.model_validate(payload)
    )
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonicalize_anm_markdown_coexistence_profile_payload(
    payload: AnmMarkdownCoexistenceProfile | dict[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload
        if isinstance(payload, AnmMarkdownCoexistenceProfile)
        else AnmMarkdownCoexistenceProfile.model_validate(payload)
    )
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


__all__ = [
    "D1_NORMALIZED_IR_SCHEMA",
    "PREDICATE_CONTRACTS_BOOTSTRAP_SCHEMA",
    "CHECKER_FACT_BUNDLE_SCHEMA",
    "POLICY_EVALUATION_RESULT_SET_SCHEMA",
    "POLICY_OBLIGATION_LEDGER_SCHEMA",
    "D1NormalizedIR",
    "D1Clause",
    "D1Qualifier",
    "D1SelectorRef",
    "PredicateArgumentSpec",
    "PredicateContract",
    "PredicateContractsBootstrap",
    "FactProvenance",
    "CheckerProfile",
    "ValueObservationFact",
    "ValueTypeObservationFact",
    "BindingObservationFact",
    "CarrierReadFact",
    "PathPresenceObservationFact",
    "PathCardinalityObservationFact",
    "ExplicitCarriageObservationFact",
    "CheckerFactBundle",
    "EvaluationNotice",
    "SubjectScopedResultRow",
    "ClauseScopeBlockerResultRow",
    "PolicyEvaluationResultSet",
    "PolicyObligationLedgerRow",
    "PolicyObligationLedger",
    "stable_payload_hash",
    "canonicalize_d1_normalized_ir_payload",
    "canonicalize_predicate_contracts_bootstrap_payload",
    "canonicalize_checker_fact_bundle_payload",
    "canonicalize_policy_evaluation_result_set_payload",
    "canonicalize_policy_obligation_ledger_payload",
]
