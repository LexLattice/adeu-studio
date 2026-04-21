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
ANM_SELECTOR_PREDICATE_OWNERSHIP_PROFILE_SCHEMA = "anm_selector_predicate_ownership_profile@1"
ANM_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA = "anm_policy_consumer_binding_profile@1"
ANM_BENCHMARK_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA = (
    "anm_benchmark_policy_consumer_binding_profile@1"
)
ANM_SOURCE_SET_MANIFEST_SCHEMA = "anm_source_set_manifest@1"
ANM_DOC_AUTHORITY_PROFILE_SCHEMA = "anm_doc_authority_profile@1"
ANM_DOC_CLASS_POLICY_SCHEMA = "anm_doc_class_policy@1"
ANM_MIGRATION_BINDING_PROFILE_SCHEMA = "anm_migration_binding_profile@1"
ANM_READER_PROJECTION_MANIFEST_SCHEMA = "anm_reader_projection_manifest@1"
ANM_SEMANTIC_DIFF_REPORT_SCHEMA = "anm_semantic_diff_report@1"

D1SchemaVersion = Literal["d1_normalized_ir@1"]
PredicateContractsBootstrapSchemaVersion = Literal["predicate_contracts_bootstrap@1"]
CheckerFactBundleSchemaVersion = Literal["checker_fact_bundle@1"]
PolicyEvaluationResultSetSchemaVersion = Literal["policy_evaluation_result_set@1"]
PolicyObligationLedgerSchemaVersion = Literal["policy_obligation_ledger@1"]
AnmMarkdownCoexistenceProfileSchemaVersion = Literal["anm_markdown_coexistence_profile@1"]
AnmSelectorPredicateOwnershipProfileSchemaVersion = Literal[
    "anm_selector_predicate_ownership_profile@1"
]
AnmPolicyConsumerBindingProfileSchemaVersion = Literal["anm_policy_consumer_binding_profile@1"]
AnmBenchmarkPolicyConsumerBindingProfileSchemaVersion = Literal[
    "anm_benchmark_policy_consumer_binding_profile@1"
]
AnmSourceSetManifestSchemaVersion = Literal["anm_source_set_manifest@1"]
AnmDocAuthorityProfileSchemaVersion = Literal["anm_doc_authority_profile@1"]
AnmDocClassPolicySchemaVersion = Literal["anm_doc_class_policy@1"]
AnmMigrationBindingProfileSchemaVersion = Literal["anm_migration_binding_profile@1"]
AnmReaderProjectionManifestSchemaVersion = Literal["anm_reader_projection_manifest@1"]
AnmSemanticDiffReportSchemaVersion = Literal["anm_semantic_diff_report@1"]

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
SelectorOwnershipRefKind = Literal[
    "bootstrap_string_selector",
    "imported_o_owned_selector_handle",
]
SelectorOwnershipOwnerLayer = Literal["bootstrap", "o_owned"]
PredicateOwnershipRefKind = Literal[
    "bootstrap_predicate_contract",
    "imported_e_owned_predicate_ref",
]
PredicateOwnershipOwnerLayer = Literal["bootstrap", "e_owned"]
OwnershipCompatibilityPosture = Literal[
    "bootstrap_only",
    "bootstrap_compatible_with_owned_successor",
    "owned_preferred_bootstrap_still_allowed",
    "mixed_ownership_forbidden",
]
BootstrapRetirementPosture = Literal[
    "not_selected",
    "later_lock_required",
    "owned_successor_available_bootstrap_still_allowed",
]
ConsumerWorldKind = Literal[
    "released_v45_descriptive_artifact_world",
    "released_runtime_event_artifact_world",
]
ConsumerRefKind = Literal[
    "released_v45_artifact_ref",
    "released_runtime_event_stream_ref",
]
PolicySourceRefKind = Literal["d1_clause_ref"]
ConsumerAuthorityRelation = Literal[
    "constrain_only_non_executive",
    "later_lock_required_for_effective_action",
]
AllowedConsumerAction = Literal[
    "reference_released_policy_source",
    "emit_consumer_conformance_annotation",
    "record_fail_closed_consumer_block",
    "attach_traceable_policy_binding",
]
BenchmarkConsumerWorldKind = Literal[
    "released_v42_local_eval_artifact_world",
    "released_v42_scorecard_artifact_world",
    "released_v42_behavior_evidence_artifact_world",
]
BenchmarkConsumerRefKind = Literal[
    "released_v42_local_eval_record_ref",
    "released_v42_scorecard_manifest_ref",
    "released_v42_behavior_evidence_bundle_ref",
]
BenchmarkConsumerAuthorityRelation = Literal[
    "constrain_only_non_executive",
    "later_lock_required_for_effective_action",
]
AllowedBenchmarkConsumerAction = Literal[
    "reference_released_policy_source",
    "emit_benchmark_conformance_annotation",
    "record_fail_closed_benchmark_consumer_block",
    "attach_traceable_benchmark_policy_binding",
]
AnmDocClass = Literal["lock", "architecture", "planning", "support", "non_governance"]
AnmAuthorityLayer = Literal["lock", "architecture", "planning", "support", "none"]
AnmDocSourcePosture = Literal[
    "legacy_markdown",
    "standalone_anm",
    "companion_anm",
    "generated_projection",
]
AnmLifecycleStatus = Literal["living", "historical", "superseded", "draft", "generated"]
AnmClassificationStatus = Literal[
    "classified",
    "unknown_requires_registration",
    "excluded_non_governance",
]
CompanionRegistrationStatus = Literal[
    "registered_host_document",
    "registered_companion_overlay",
]
AnmAuthorityBlockKind = Literal["D@1", "adeu.doc_profile@1"]
AnmProfileOutputKind = Literal[
    "anm_doc_authority_profile@1",
    "d1_normalized_ir@1",
    "predicate_contracts_bootstrap@1",
    "checker_fact_bundle@1",
    "policy_evaluation_result_set@1",
    "policy_obligation_ledger@1",
]
AnmAllowedConsumer = Literal[
    "reader_projection",
    "semantic_source",
    "semantic_compiler",
    "policy_evaluator",
]
AnmHardGate = Literal[
    "reject_overpromotion",
    "reject_unregistered_companion",
    "reject_supersession_without_transition_law",
]
AnmWarningGate = Literal[
    "warn_unknown_requires_registration",
    "warn_profile_inferred_from_manifest",
]
V66BBindingPosture = Literal[
    "invalid_or_contradictory",
    "registered_non_overriding_companion",
    "standalone_no_companion",
]
V66BCurrentMarkdownAuthorityRelation = Literal[
    "anm_standalone_source_of_truth",
    "current_markdown_controlling",
    "generated_projection_non_authoritative",
    "not_applicable",
]
V66BSupersessionClaimStatus = Literal[
    "claimed_with_explicit_transition_law",
    "claimed_without_transition_law_rejected",
    "none",
]
V66BProjectionStatus = Literal["current", "invalid", "missing", "not_required", "stale"]
V66BProjectionAuthorityPosture = Literal[
    "invalid_claims_authority",
    "non_authoritative_generated_view",
]
V66BDriftStatus = Literal[
    "hash_unavailable",
    "in_sync",
    "not_required",
    "projection_missing",
    "source_changed_projection_stale",
]
V66BProjectionRequirementSource = Literal[
    "doc_authority_profile",
    "doc_class_policy",
    "explicit_projection_manifest",
    "not_required",
]
V66BDiffBaselineKind = Literal[
    "explicit_fixture_baseline",
    "none_initial_report",
    "prior_committed_artifact",
]
V66BChangeKind = Literal["added", "changed", "initial", "removed", "unchanged"]
V66BSurfaceKind = Literal[
    "doc_authority_profile",
    "doc_class_policy",
    "migration_binding",
    "reader_projection_manifest",
    "source_set_entry",
]
V66BAuthorityEffectKind = Literal[
    "invalid_authority_claim_rejected",
    "no_authority_minted",
    "review_visibility_only",
]


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
            self.current_markdown_authority_relation == "later_lock_required_for_supersession"
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
                raise ValueError("companion_anm rows may not declare current_markdown_controlling")
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


class SelectorOwnershipRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    selector_ref: str = Field(min_length=1)
    selector_ref_kind: SelectorOwnershipRefKind
    selector_owner_layer: SelectorOwnershipOwnerLayer
    bootstrap_selector_source_ref: str | None = None
    imported_selector_handle_ref: str | None = None
    imported_selector_identity: str | None = None
    imported_selector_version: str | None = None
    compatibility_posture: OwnershipCompatibilityPosture
    bootstrap_retirement_posture: BootstrapRetirementPosture

    @model_validator(mode="after")
    def _validate_contract(self) -> "SelectorOwnershipRow":
        self.selector_ref = _require_non_empty(self.selector_ref, field_name="selector_ref")
        if self.bootstrap_selector_source_ref is not None:
            self.bootstrap_selector_source_ref = _require_non_empty(
                self.bootstrap_selector_source_ref,
                field_name="bootstrap_selector_source_ref",
            )
        if self.imported_selector_handle_ref is not None:
            self.imported_selector_handle_ref = _require_non_empty(
                self.imported_selector_handle_ref,
                field_name="imported_selector_handle_ref",
            )
        if self.imported_selector_identity is not None:
            self.imported_selector_identity = _require_non_empty(
                self.imported_selector_identity,
                field_name="imported_selector_identity",
            )
        if self.imported_selector_version is not None:
            self.imported_selector_version = _require_non_empty(
                self.imported_selector_version,
                field_name="imported_selector_version",
            )

        if self.selector_ref_kind == "bootstrap_string_selector":
            if self.bootstrap_selector_source_ref is None:
                raise ValueError(
                    "bootstrap_string_selector rows require bootstrap_selector_source_ref"
                )
            if self.imported_selector_handle_ref is not None:
                raise ValueError(
                    "bootstrap_string_selector rows may not set imported_selector_handle_ref"
                )
            if self.imported_selector_identity is not None:
                raise ValueError(
                    "bootstrap_string_selector rows may not set imported_selector_identity"
                )
            if self.imported_selector_version is not None:
                raise ValueError(
                    "bootstrap_string_selector rows may not set imported_selector_version"
                )
            if self.selector_owner_layer != "bootstrap":
                raise ValueError(
                    "bootstrap_string_selector rows require selector_owner_layer = bootstrap"
                )
        else:
            if self.imported_selector_handle_ref is None:
                raise ValueError(
                    "imported_o_owned_selector_handle rows require imported_selector_handle_ref"
                )
            if self.imported_selector_identity is None or self.imported_selector_version is None:
                raise ValueError(
                    "imported_o_owned_selector_handle rows require imported selector "
                    "identity/version"
                )
            if self.bootstrap_selector_source_ref is not None:
                raise ValueError(
                    "imported_o_owned_selector_handle rows may not set "
                    "bootstrap_selector_source_ref"
                )
            if self.selector_owner_layer != "o_owned":
                raise ValueError(
                    "imported_o_owned_selector_handle rows require selector_owner_layer = o_owned"
                )
        return self


class PredicateOwnershipRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    predicate_ref: str = Field(min_length=1)
    predicate_ref_kind: PredicateOwnershipRefKind
    predicate_owner_layer: PredicateOwnershipOwnerLayer
    bootstrap_predicate_contract_ref: str | None = None
    imported_predicate_registry_ref: str | None = None
    imported_predicate_identity: str | None = None
    imported_predicate_version: str | None = None
    compatibility_posture: OwnershipCompatibilityPosture
    bootstrap_retirement_posture: BootstrapRetirementPosture

    @model_validator(mode="after")
    def _validate_contract(self) -> "PredicateOwnershipRow":
        self.predicate_ref = _require_non_empty(self.predicate_ref, field_name="predicate_ref")
        if self.bootstrap_predicate_contract_ref is not None:
            self.bootstrap_predicate_contract_ref = _require_non_empty(
                self.bootstrap_predicate_contract_ref,
                field_name="bootstrap_predicate_contract_ref",
            )
        if self.imported_predicate_registry_ref is not None:
            self.imported_predicate_registry_ref = _require_non_empty(
                self.imported_predicate_registry_ref,
                field_name="imported_predicate_registry_ref",
            )
        if self.imported_predicate_identity is not None:
            self.imported_predicate_identity = _require_non_empty(
                self.imported_predicate_identity,
                field_name="imported_predicate_identity",
            )
        if self.imported_predicate_version is not None:
            self.imported_predicate_version = _require_non_empty(
                self.imported_predicate_version,
                field_name="imported_predicate_version",
            )

        if self.predicate_ref_kind == "bootstrap_predicate_contract":
            if self.bootstrap_predicate_contract_ref is None:
                raise ValueError(
                    "bootstrap_predicate_contract rows require bootstrap_predicate_contract_ref"
                )
            if self.imported_predicate_registry_ref is not None:
                raise ValueError(
                    "bootstrap_predicate_contract rows may not set imported_predicate_registry_ref"
                )
            if self.imported_predicate_identity is not None:
                raise ValueError(
                    "bootstrap_predicate_contract rows may not set imported_predicate_identity"
                )
            if self.imported_predicate_version is not None:
                raise ValueError(
                    "bootstrap_predicate_contract rows may not set imported_predicate_version"
                )
            if self.predicate_owner_layer != "bootstrap":
                raise ValueError(
                    "bootstrap_predicate_contract rows require predicate_owner_layer = bootstrap"
                )
        else:
            if self.imported_predicate_registry_ref is None:
                raise ValueError(
                    "imported_e_owned_predicate_ref rows require imported_predicate_registry_ref"
                )
            if self.imported_predicate_identity is None or self.imported_predicate_version is None:
                raise ValueError(
                    "imported_e_owned_predicate_ref rows require imported predicate "
                    "identity/version"
                )
            if self.bootstrap_predicate_contract_ref is not None:
                raise ValueError(
                    "imported_e_owned_predicate_ref rows may not set "
                    "bootstrap_predicate_contract_ref"
                )
            if self.predicate_owner_layer != "e_owned":
                raise ValueError(
                    "imported_e_owned_predicate_ref rows require predicate_owner_layer = e_owned"
                )
        return self


class OwnershipCompatibilityRule(BaseModel):
    model_config = ConfigDict(extra="forbid")

    selector_ref_kind: SelectorOwnershipRefKind
    predicate_ref_kind: PredicateOwnershipRefKind
    combination_allowed: bool
    compatibility_posture: OwnershipCompatibilityPosture
    backward_replay_preserved: bool
    later_lock_required_before_retirement: bool
    mixed_ownership_normatively_constrained: bool

    @model_validator(mode="after")
    def _validate_contract(self) -> "OwnershipCompatibilityRule":
        if (
            not self.combination_allowed
            and self.compatibility_posture != "mixed_ownership_forbidden"
        ):
            raise ValueError(
                "forbidden compatibility rows require compatibility_posture = "
                "mixed_ownership_forbidden"
            )
        if self.combination_allowed and self.compatibility_posture == "mixed_ownership_forbidden":
            raise ValueError(
                "allowed compatibility rows may not use compatibility_posture = "
                "mixed_ownership_forbidden"
            )
        return self


class AnmSelectorPredicateOwnershipProfile(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: AnmSelectorPredicateOwnershipProfileSchemaVersion = (
        ANM_SELECTOR_PREDICATE_OWNERSHIP_PROFILE_SCHEMA
    )
    ownership_profile_id: str = Field(min_length=1)
    snapshot_id: str = Field(min_length=1)
    snapshot_sha256: str = Field(min_length=1)
    source_scope_profile: str = Field(min_length=1)
    released_stack_refs: list[str] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    selector_rows: list[SelectorOwnershipRow] = Field(default_factory=list)
    predicate_rows: list[PredicateOwnershipRow] = Field(default_factory=list)
    compatibility_rules: list[OwnershipCompatibilityRule] = Field(default_factory=list)
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmSelectorPredicateOwnershipProfile":
        self.ownership_profile_id = _require_non_empty(
            self.ownership_profile_id,
            field_name="ownership_profile_id",
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

        selector_refs = [item.selector_ref for item in self.selector_rows]
        _require_sorted_unique(selector_refs, field_name="selector_rows.selector_ref")
        predicate_refs = [item.predicate_ref for item in self.predicate_rows]
        _require_sorted_unique(predicate_refs, field_name="predicate_rows.predicate_ref")

        compatibility_pairs = [
            (item.selector_ref_kind, item.predicate_ref_kind) for item in self.compatibility_rules
        ]
        if compatibility_pairs != sorted(compatibility_pairs):
            raise ValueError(
                "compatibility_rules must be sorted by (selector_ref_kind, predicate_ref_kind)"
            )
        if len(compatibility_pairs) != len(set(compatibility_pairs)):
            raise ValueError("compatibility_rules must not contain duplicate combinations")

        expected_pairs = {
            ("bootstrap_string_selector", "bootstrap_predicate_contract"),
            ("bootstrap_string_selector", "imported_e_owned_predicate_ref"),
            ("imported_o_owned_selector_handle", "bootstrap_predicate_contract"),
            ("imported_o_owned_selector_handle", "imported_e_owned_predicate_ref"),
        }
        if set(compatibility_pairs) != expected_pairs:
            raise ValueError("compatibility_rules must cover the four ownership combinations")
        return self


class AnmPolicyConsumerRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    consumer_ref: str = Field(min_length=1)
    consumer_world_kind: ConsumerWorldKind
    consumer_ref_kind: ConsumerRefKind
    policy_source_ref: str = Field(min_length=1)
    policy_source_ref_kind: PolicySourceRefKind
    supporting_result_refs: list[str] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    supporting_ledger_refs: list[str] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    current_consumer_authority_relation: ConsumerAuthorityRelation
    allowed_now_actions: list[AllowedConsumerAction] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    later_lock_required_actions: list[AllowedConsumerAction] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    forbidden_actions: list[AllowedConsumerAction] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmPolicyConsumerRow":
        self.consumer_ref = _require_non_empty(self.consumer_ref, field_name="consumer_ref")
        self.policy_source_ref = _require_non_empty(
            self.policy_source_ref,
            field_name="policy_source_ref",
        )
        if self.consumer_world_kind == "released_v45_descriptive_artifact_world":
            if self.consumer_ref_kind != "released_v45_artifact_ref":
                raise ValueError(
                    "released_v45_descriptive_artifact_world rows require "
                    "consumer_ref_kind = released_v45_artifact_ref"
                )
        else:
            if self.consumer_ref_kind != "released_runtime_event_stream_ref":
                raise ValueError(
                    "released_runtime_event_artifact_world rows require "
                    "consumer_ref_kind = released_runtime_event_stream_ref"
                )
        _require_sorted_unique(
            self.supporting_result_refs,
            field_name="supporting_result_refs",
        )
        _require_sorted_unique(
            self.supporting_ledger_refs,
            field_name="supporting_ledger_refs",
        )
        for field_name in (
            "allowed_now_actions",
            "later_lock_required_actions",
            "forbidden_actions",
        ):
            _require_sorted_unique(getattr(self, field_name), field_name=field_name)
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
            raise ValueError("consumer action lists must not overlap")
        return self


class AnmPolicyConsumerBindingProfile(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: AnmPolicyConsumerBindingProfileSchemaVersion = (
        ANM_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA
    )
    consumer_binding_profile_id: str = Field(min_length=1)
    snapshot_id: str = Field(min_length=1)
    snapshot_sha256: str = Field(min_length=1)
    source_scope_profile: str = Field(min_length=1)
    released_stack_refs: list[str] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    consumer_rows: list[AnmPolicyConsumerRow] = Field(default_factory=list)
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmPolicyConsumerBindingProfile":
        self.consumer_binding_profile_id = _require_non_empty(
            self.consumer_binding_profile_id,
            field_name="consumer_binding_profile_id",
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
        consumer_refs = [item.consumer_ref for item in self.consumer_rows]
        _require_sorted_unique(consumer_refs, field_name="consumer_rows.consumer_ref")
        return self


class AnmBenchmarkPolicyConsumerRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    benchmark_consumer_ref: str = Field(min_length=1)
    benchmark_consumer_world_kind: BenchmarkConsumerWorldKind
    benchmark_consumer_ref_kind: BenchmarkConsumerRefKind
    policy_source_ref: str = Field(min_length=1)
    policy_source_ref_kind: PolicySourceRefKind
    supporting_result_refs: list[str] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    supporting_ledger_refs: list[str] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    current_benchmark_consumer_authority_relation: BenchmarkConsumerAuthorityRelation
    allowed_now_actions: list[AllowedBenchmarkConsumerAction] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    later_lock_required_actions: list[AllowedBenchmarkConsumerAction] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    forbidden_actions: list[AllowedBenchmarkConsumerAction] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmBenchmarkPolicyConsumerRow":
        self.benchmark_consumer_ref = _require_non_empty(
            self.benchmark_consumer_ref,
            field_name="benchmark_consumer_ref",
        )
        self.policy_source_ref = _require_non_empty(
            self.policy_source_ref,
            field_name="policy_source_ref",
        )
        expected_ref_kind = {
            "released_v42_local_eval_artifact_world": "released_v42_local_eval_record_ref",
            "released_v42_scorecard_artifact_world": "released_v42_scorecard_manifest_ref",
            "released_v42_behavior_evidence_artifact_world": (
                "released_v42_behavior_evidence_bundle_ref"
            ),
        }[self.benchmark_consumer_world_kind]
        if self.benchmark_consumer_ref_kind != expected_ref_kind:
            raise ValueError(
                f"{self.benchmark_consumer_world_kind} rows require "
                f"benchmark_consumer_ref_kind = {expected_ref_kind}"
            )
        _require_sorted_unique(
            self.supporting_result_refs,
            field_name="supporting_result_refs",
        )
        _require_sorted_unique(
            self.supporting_ledger_refs,
            field_name="supporting_ledger_refs",
        )
        for field_name in (
            "allowed_now_actions",
            "later_lock_required_actions",
            "forbidden_actions",
        ):
            _require_sorted_unique(getattr(self, field_name), field_name=field_name)
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
            raise ValueError("benchmark consumer action lists must not overlap")
        if self.current_benchmark_consumer_authority_relation == "constrain_only_non_executive":
            if self.later_lock_required_actions:
                raise ValueError(
                    "constrain_only_non_executive rows must not declare later_lock_required_actions"
                )
        else:
            if not self.later_lock_required_actions:
                raise ValueError(
                    "later_lock_required_for_effective_action rows must declare "
                    "later_lock_required_actions"
                )
        return self


class AnmBenchmarkPolicyConsumerBindingProfile(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema: AnmBenchmarkPolicyConsumerBindingProfileSchemaVersion = (
        ANM_BENCHMARK_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA
    )
    benchmark_consumer_binding_profile_id: str = Field(min_length=1)
    snapshot_id: str = Field(min_length=1)
    snapshot_sha256: str = Field(min_length=1)
    source_scope_profile: str = Field(min_length=1)
    released_stack_refs: list[str] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    benchmark_consumer_rows: list[AnmBenchmarkPolicyConsumerRow] = Field(default_factory=list)
    semantic_hash: str = Field(min_length=1)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmBenchmarkPolicyConsumerBindingProfile":
        self.benchmark_consumer_binding_profile_id = _require_non_empty(
            self.benchmark_consumer_binding_profile_id,
            field_name="benchmark_consumer_binding_profile_id",
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
        consumer_refs = [item.benchmark_consumer_ref for item in self.benchmark_consumer_rows]
        _require_sorted_unique(
            consumer_refs,
            field_name="benchmark_consumer_rows.benchmark_consumer_ref",
        )
        return self


class AnmSourceSetEntry(BaseModel):
    model_config = ConfigDict(extra="forbid")

    doc_ref: str = Field(min_length=1)
    doc_id_or_none: str | None = None
    doc_class: AnmDocClass
    authority_layer: AnmAuthorityLayer
    source_posture: AnmDocSourcePosture
    lifecycle_status: AnmLifecycleStatus
    classification_status: AnmClassificationStatus
    content_hash: str = Field(min_length=1)
    profile_ref_or_none: str | None = None
    host_doc_ref_or_none: str | None = None
    companion_registration_status_or_none: CompanionRegistrationStatus | None = None
    generated_from_ref_or_none: str | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmSourceSetEntry":
        self.doc_ref = _require_non_empty(self.doc_ref, field_name="doc_ref")
        self.content_hash = _require_non_empty(self.content_hash, field_name="content_hash")
        for field_name in (
            "doc_id_or_none",
            "profile_ref_or_none",
            "host_doc_ref_or_none",
            "generated_from_ref_or_none",
        ):
            value = getattr(self, field_name)
            if value is not None:
                setattr(self, field_name, _require_non_empty(value, field_name=field_name))
        if self.doc_ref != self.doc_ref.replace("\\", "/"):
            raise ValueError("doc_ref must use POSIX separators")
        if self.source_posture == "companion_anm":
            if self.companion_registration_status_or_none != "registered_companion_overlay":
                raise ValueError(
                    "companion_anm entries require companion_registration_status_or_none = "
                    "registered_companion_overlay"
                )
            if self.host_doc_ref_or_none is None:
                raise ValueError("companion_anm entries require host_doc_ref_or_none")
        elif self.companion_registration_status_or_none == "registered_companion_overlay":
            raise ValueError("registered_companion_overlay is only valid for companion_anm entries")
        if (
            self.generated_from_ref_or_none is not None
            and self.source_posture != "generated_projection"
        ):
            raise ValueError(
                "generated_from_ref_or_none is only valid for generated_projection entries"
            )
        if (
            self.generated_from_ref_or_none is None
            and self.source_posture == "generated_projection"
        ):
            raise ValueError("generated_projection entries require generated_from_ref_or_none")
        if (
            self.classification_status == "excluded_non_governance"
            and self.doc_class != "non_governance"
        ):
            raise ValueError(
                "excluded_non_governance classification requires doc_class = non_governance"
            )
        if self.doc_class == "non_governance" and self.authority_layer != "none":
            raise ValueError("non_governance entries require authority_layer = none")
        if self.host_doc_ref_or_none == self.doc_ref:
            raise ValueError("host_doc_ref_or_none must not equal doc_ref")
        return self


class AnmSourceSetManifest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema_id: AnmSourceSetManifestSchemaVersion = ANM_SOURCE_SET_MANIFEST_SCHEMA
    manifest_id: str = Field(min_length=1)
    source_entries: list[AnmSourceSetEntry] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmSourceSetManifest":
        self.manifest_id = _require_non_empty(self.manifest_id, field_name="manifest_id")
        doc_refs = [item.doc_ref for item in self.source_entries]
        _require_sorted_unique(doc_refs, field_name="source_entries.doc_ref")
        return self


class AnmDocAuthorityProfile(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema_id: AnmDocAuthorityProfileSchemaVersion = ANM_DOC_AUTHORITY_PROFILE_SCHEMA
    doc_id: str = Field(min_length=1)
    doc_ref: str = Field(min_length=1)
    doc_class: AnmDocClass
    authority_layer: AnmAuthorityLayer
    source_posture: AnmDocSourcePosture
    lifecycle_status: AnmLifecycleStatus
    allowed_authority_blocks: list[AnmAuthorityBlockKind] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    allowed_outputs: list[AnmProfileOutputKind] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    forbidden_outputs: list[AnmProfileOutputKind] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    current_markdown_authority_relation: CurrentMarkdownAuthorityRelation
    allowed_consumers: list[AnmAllowedConsumer] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    requires_transition_law_for_supersession: bool

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmDocAuthorityProfile":
        self.doc_id = _require_non_empty(self.doc_id, field_name="doc_id")
        self.doc_ref = _require_non_empty(self.doc_ref, field_name="doc_ref")
        if self.doc_ref != self.doc_ref.replace("\\", "/"):
            raise ValueError("doc_ref must use POSIX separators")
        for field_name in (
            "allowed_authority_blocks",
            "allowed_outputs",
            "forbidden_outputs",
            "allowed_consumers",
        ):
            _require_sorted_unique(list(getattr(self, field_name)), field_name=field_name)
        if set(self.allowed_outputs) & set(self.forbidden_outputs):
            raise ValueError("allowed_outputs and forbidden_outputs must not overlap")
        if self.doc_class == "non_governance":
            raise ValueError("non_governance docs may not emit authority profiles")
        if self.authority_layer == "none":
            raise ValueError("authority_layer = none is forbidden for authority profiles")
        return self


class AnmDocClassPolicyRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    doc_class: AnmDocClass
    allowed_authority_layers: list[AnmAuthorityLayer] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    allowed_source_postures: list[AnmDocSourcePosture] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    allowed_authority_blocks: list[AnmAuthorityBlockKind] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    allowed_outputs: list[AnmProfileOutputKind] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    forbidden_outputs: list[AnmProfileOutputKind] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    hard_gates: list[AnmHardGate] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    warning_gates: list[AnmWarningGate] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmDocClassPolicyRow":
        for field_name in (
            "allowed_authority_layers",
            "allowed_source_postures",
            "allowed_authority_blocks",
            "allowed_outputs",
            "forbidden_outputs",
            "hard_gates",
            "warning_gates",
        ):
            _require_sorted_unique(list(getattr(self, field_name)), field_name=field_name)
        if set(self.allowed_outputs) & set(self.forbidden_outputs):
            raise ValueError("allowed_outputs and forbidden_outputs must not overlap")
        if self.doc_class == "non_governance":
            if self.allowed_authority_layers != ["none"]:
                raise ValueError(
                    "non_governance class policy must only allow authority_layer = none"
                )
            if self.allowed_authority_blocks or self.allowed_outputs:
                raise ValueError(
                    "non_governance class policy may not allow authority blocks or outputs"
                )
        return self


class AnmDocClassPolicy(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema_id: AnmDocClassPolicySchemaVersion = ANM_DOC_CLASS_POLICY_SCHEMA
    policy_id: str = Field(min_length=1)
    policy_rows: list[AnmDocClassPolicyRow] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmDocClassPolicy":
        self.policy_id = _require_non_empty(self.policy_id, field_name="policy_id")
        doc_classes = [item.doc_class for item in self.policy_rows]
        _require_sorted_unique(doc_classes, field_name="policy_rows.doc_class")
        return self


class AnmMigrationBindingRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    binding_id: str = Field(min_length=1)
    host_doc_ref: str = Field(min_length=1)
    companion_doc_ref_or_none: str | None = None
    host_profile_ref: str = Field(min_length=1)
    companion_profile_ref_or_none: str | None = None
    binding_posture: V66BBindingPosture
    current_markdown_authority_relation: V66BCurrentMarkdownAuthorityRelation
    supersession_claim_status: V66BSupersessionClaimStatus
    explicit_transition_law_ref_or_none: str | None = None
    generated_reader_projection_refs: list[str] = Field(
        default_factory=list,
        json_schema_extra={"uniqueItems": True},
    )
    semantic_diff_ref_or_none: str | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmMigrationBindingRow":
        self.binding_id = _require_non_empty(self.binding_id, field_name="binding_id")
        self.host_doc_ref = _require_non_empty(self.host_doc_ref, field_name="host_doc_ref")
        self.host_profile_ref = _require_non_empty(
            self.host_profile_ref, field_name="host_profile_ref"
        )
        if self.companion_doc_ref_or_none is not None:
            self.companion_doc_ref_or_none = _require_non_empty(
                self.companion_doc_ref_or_none,
                field_name="companion_doc_ref_or_none",
            )
        if self.companion_profile_ref_or_none is not None:
            self.companion_profile_ref_or_none = _require_non_empty(
                self.companion_profile_ref_or_none,
                field_name="companion_profile_ref_or_none",
            )
        if self.explicit_transition_law_ref_or_none is not None:
            self.explicit_transition_law_ref_or_none = _require_non_empty(
                self.explicit_transition_law_ref_or_none,
                field_name="explicit_transition_law_ref_or_none",
            )
        if self.semantic_diff_ref_or_none is not None:
            self.semantic_diff_ref_or_none = _require_non_empty(
                self.semantic_diff_ref_or_none,
                field_name="semantic_diff_ref_or_none",
            )
        _require_sorted_unique(
            list(self.generated_reader_projection_refs),
            field_name="generated_reader_projection_refs",
        )
        if self.host_doc_ref == self.companion_doc_ref_or_none:
            raise ValueError("host_doc_ref must not equal companion_doc_ref_or_none")
        if self.binding_posture == "registered_non_overriding_companion":
            if self.companion_doc_ref_or_none is None or self.companion_profile_ref_or_none is None:
                raise ValueError(
                    "registered_non_overriding_companion requires companion doc and profile refs"
                )
        if self.binding_posture == "standalone_no_companion":
            if (
                self.companion_doc_ref_or_none is not None
                or self.companion_profile_ref_or_none is not None
            ):
                raise ValueError("standalone_no_companion forbids companion doc and profile refs")
        if self.supersession_claim_status == "claimed_with_explicit_transition_law":
            if self.explicit_transition_law_ref_or_none is None:
                raise ValueError(
                    "claimed_with_explicit_transition_law requires "
                    "explicit_transition_law_ref_or_none"
                )
        elif self.explicit_transition_law_ref_or_none is not None:
            raise ValueError(
                "explicit_transition_law_ref_or_none requires claimed_with_explicit_transition_law"
            )
        return self


class AnmMigrationBindingProfile(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema_id: AnmMigrationBindingProfileSchemaVersion = ANM_MIGRATION_BINDING_PROFILE_SCHEMA
    migration_binding_profile_id: str = Field(min_length=1)
    consumed_source_set_manifest_ref: str = Field(min_length=1)
    consumed_source_set_manifest_hash: str = Field(min_length=1)
    consumed_doc_class_policy_ref: str = Field(min_length=1)
    consumed_doc_class_policy_hash: str = Field(min_length=1)
    consumed_authority_profile_set_ref_or_hash: str = Field(min_length=1)
    binding_rows: list[AnmMigrationBindingRow] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmMigrationBindingProfile":
        for field_name in (
            "migration_binding_profile_id",
            "consumed_source_set_manifest_ref",
            "consumed_source_set_manifest_hash",
            "consumed_doc_class_policy_ref",
            "consumed_doc_class_policy_hash",
            "consumed_authority_profile_set_ref_or_hash",
        ):
            setattr(
                self,
                field_name,
                _require_non_empty(getattr(self, field_name), field_name=field_name),
            )
        binding_ids = [item.binding_id for item in self.binding_rows]
        _require_sorted_unique(binding_ids, field_name="binding_rows.binding_id")
        return self


class AnmReaderProjectionRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    projection_doc_ref: str = Field(min_length=1)
    source_doc_ref: str = Field(min_length=1)
    source_profile_ref: str = Field(min_length=1)
    projection_required: bool
    projection_requirement_source: V66BProjectionRequirementSource
    projection_status: V66BProjectionStatus
    projection_authority_posture: V66BProjectionAuthorityPosture
    source_content_hash: str = Field(min_length=1)
    projection_content_hash_or_none: str | None = None
    drift_status: V66BDriftStatus

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmReaderProjectionRow":
        for field_name in (
            "projection_doc_ref",
            "source_doc_ref",
            "source_profile_ref",
            "source_content_hash",
        ):
            setattr(
                self,
                field_name,
                _require_non_empty(getattr(self, field_name), field_name=field_name),
            )
        if self.projection_content_hash_or_none is not None:
            self.projection_content_hash_or_none = _require_non_empty(
                self.projection_content_hash_or_none,
                field_name="projection_content_hash_or_none",
            )
        if self.projection_doc_ref == self.source_doc_ref:
            raise ValueError("projection_doc_ref must not equal source_doc_ref")
        if self.projection_required and self.projection_requirement_source == "not_required":
            raise ValueError(
                "projection_required=true forbids projection_requirement_source=not_required"
            )
        if not self.projection_required and self.projection_requirement_source != "not_required":
            raise ValueError(
                "projection_required=false requires projection_requirement_source=not_required"
            )
        if self.projection_status == "current" and self.projection_content_hash_or_none is None:
            raise ValueError("projection_status=current requires projection_content_hash_or_none")
        if self.projection_status == "not_required" and self.projection_required:
            raise ValueError("projection_status=not_required requires projection_required=false")
        if self.drift_status == "not_required" and self.projection_required:
            raise ValueError("drift_status=not_required requires projection_required=false")
        return self


class AnmReaderProjectionManifest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema_id: AnmReaderProjectionManifestSchemaVersion = ANM_READER_PROJECTION_MANIFEST_SCHEMA
    projection_manifest_id: str = Field(min_length=1)
    consumed_source_set_manifest_ref: str = Field(min_length=1)
    consumed_source_set_manifest_hash: str = Field(min_length=1)
    consumed_doc_class_policy_ref: str = Field(min_length=1)
    consumed_doc_class_policy_hash: str = Field(min_length=1)
    consumed_authority_profile_set_ref_or_hash: str = Field(min_length=1)
    projection_rows: list[AnmReaderProjectionRow] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmReaderProjectionManifest":
        for field_name in (
            "projection_manifest_id",
            "consumed_source_set_manifest_ref",
            "consumed_source_set_manifest_hash",
            "consumed_doc_class_policy_ref",
            "consumed_doc_class_policy_hash",
            "consumed_authority_profile_set_ref_or_hash",
        ):
            setattr(
                self,
                field_name,
                _require_non_empty(getattr(self, field_name), field_name=field_name),
            )
        projection_doc_refs = [item.projection_doc_ref for item in self.projection_rows]
        _require_sorted_unique(projection_doc_refs, field_name="projection_rows.projection_doc_ref")
        return self


class AnmSemanticDiffChangeRow(BaseModel):
    model_config = ConfigDict(extra="forbid")

    source_doc_ref: str = Field(min_length=1)
    baseline_profile_ref_or_none: str | None = None
    current_profile_ref: str = Field(min_length=1)
    change_kind: V66BChangeKind
    surface_kind: V66BSurfaceKind
    path_or_axis: str = Field(min_length=1)
    baseline_value_or_none: Any = None
    current_value_or_none: Any = None
    authority_effect_kind: V66BAuthorityEffectKind
    authority_effect_summary_or_none: str | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmSemanticDiffChangeRow":
        self.source_doc_ref = _require_non_empty(self.source_doc_ref, field_name="source_doc_ref")
        self.current_profile_ref = _require_non_empty(
            self.current_profile_ref, field_name="current_profile_ref"
        )
        self.path_or_axis = _require_non_empty(self.path_or_axis, field_name="path_or_axis")
        if self.baseline_profile_ref_or_none is not None:
            self.baseline_profile_ref_or_none = _require_non_empty(
                self.baseline_profile_ref_or_none,
                field_name="baseline_profile_ref_or_none",
            )
        if self.authority_effect_summary_or_none is not None:
            self.authority_effect_summary_or_none = _require_non_empty(
                self.authority_effect_summary_or_none,
                field_name="authority_effect_summary_or_none",
            )
        return self


class AnmSemanticDiffReport(BaseModel):
    model_config = ConfigDict(extra="forbid")

    schema_id: AnmSemanticDiffReportSchemaVersion = ANM_SEMANTIC_DIFF_REPORT_SCHEMA
    diff_report_id: str = Field(min_length=1)
    consumed_source_set_manifest_ref: str = Field(min_length=1)
    consumed_source_set_manifest_hash: str = Field(min_length=1)
    consumed_doc_class_policy_ref: str = Field(min_length=1)
    consumed_doc_class_policy_hash: str = Field(min_length=1)
    consumed_authority_profile_set_ref_or_hash: str = Field(min_length=1)
    baseline_kind: V66BDiffBaselineKind
    baseline_artifact_ref_or_none: str | None = None
    baseline_artifact_hash_or_none: str | None = None
    current_artifact_ref: str = Field(min_length=1)
    current_artifact_hash: str = Field(min_length=1)
    change_rows: list[AnmSemanticDiffChangeRow] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_contract(self) -> "AnmSemanticDiffReport":
        for field_name in (
            "diff_report_id",
            "consumed_source_set_manifest_ref",
            "consumed_source_set_manifest_hash",
            "consumed_doc_class_policy_ref",
            "consumed_doc_class_policy_hash",
            "consumed_authority_profile_set_ref_or_hash",
            "current_artifact_ref",
            "current_artifact_hash",
        ):
            setattr(
                self,
                field_name,
                _require_non_empty(getattr(self, field_name), field_name=field_name),
            )
        if self.baseline_artifact_ref_or_none is not None:
            self.baseline_artifact_ref_or_none = _require_non_empty(
                self.baseline_artifact_ref_or_none,
                field_name="baseline_artifact_ref_or_none",
            )
        if self.baseline_artifact_hash_or_none is not None:
            self.baseline_artifact_hash_or_none = _require_non_empty(
                self.baseline_artifact_hash_or_none,
                field_name="baseline_artifact_hash_or_none",
            )
        if self.baseline_kind == "none_initial_report":
            if (
                self.baseline_artifact_ref_or_none is not None
                or self.baseline_artifact_hash_or_none is not None
            ):
                raise ValueError(
                    "none_initial_report forbids baseline_artifact_ref_or_none "
                    "and baseline_artifact_hash_or_none"
                )
        elif (
            self.baseline_artifact_ref_or_none is None
            or self.baseline_artifact_hash_or_none is None
        ):
            raise ValueError(
                "explicit baseline kinds require baseline_artifact_ref_or_none "
                "and baseline_artifact_hash_or_none"
            )
        change_identity = [
            (
                item.source_doc_ref,
                item.surface_kind,
                item.path_or_axis,
            )
            for item in self.change_rows
        ]
        if change_identity != sorted(change_identity):
            raise ValueError(
                "change_rows must be sorted by (source_doc_ref, surface_kind, path_or_axis)"
            )
        if len(change_identity) != len(set(change_identity)):
            raise ValueError("change_rows must not contain duplicate diff identities")
        return self


def canonicalize_d1_normalized_ir_payload(
    payload: D1NormalizedIR | dict[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload if isinstance(payload, D1NormalizedIR) else D1NormalizedIR.model_validate(payload)
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


def canonicalize_anm_selector_predicate_ownership_profile_payload(
    payload: AnmSelectorPredicateOwnershipProfile | dict[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload
        if isinstance(payload, AnmSelectorPredicateOwnershipProfile)
        else AnmSelectorPredicateOwnershipProfile.model_validate(payload)
    )
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonicalize_anm_policy_consumer_binding_profile_payload(
    payload: AnmPolicyConsumerBindingProfile | dict[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload
        if isinstance(payload, AnmPolicyConsumerBindingProfile)
        else AnmPolicyConsumerBindingProfile.model_validate(payload)
    )
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonicalize_anm_benchmark_policy_consumer_binding_profile_payload(
    payload: AnmBenchmarkPolicyConsumerBindingProfile | dict[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload
        if isinstance(payload, AnmBenchmarkPolicyConsumerBindingProfile)
        else AnmBenchmarkPolicyConsumerBindingProfile.model_validate(payload)
    )
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonicalize_anm_source_set_manifest_payload(
    payload: AnmSourceSetManifest | dict[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload
        if isinstance(payload, AnmSourceSetManifest)
        else AnmSourceSetManifest.model_validate(payload)
    )
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonicalize_anm_doc_authority_profile_payload(
    payload: AnmDocAuthorityProfile | dict[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload
        if isinstance(payload, AnmDocAuthorityProfile)
        else AnmDocAuthorityProfile.model_validate(payload)
    )
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonicalize_anm_doc_class_policy_payload(
    payload: AnmDocClassPolicy | dict[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload
        if isinstance(payload, AnmDocClassPolicy)
        else AnmDocClassPolicy.model_validate(payload)
    )
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonicalize_anm_migration_binding_profile_payload(
    payload: AnmMigrationBindingProfile | dict[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload
        if isinstance(payload, AnmMigrationBindingProfile)
        else AnmMigrationBindingProfile.model_validate(payload)
    )
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonicalize_anm_reader_projection_manifest_payload(
    payload: AnmReaderProjectionManifest | dict[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload
        if isinstance(payload, AnmReaderProjectionManifest)
        else AnmReaderProjectionManifest.model_validate(payload)
    )
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


def canonicalize_anm_semantic_diff_report_payload(
    payload: AnmSemanticDiffReport | dict[str, Any],
) -> dict[str, Any]:
    normalized = (
        payload
        if isinstance(payload, AnmSemanticDiffReport)
        else AnmSemanticDiffReport.model_validate(payload)
    )
    return normalized.model_dump(mode="json", by_alias=True, exclude_none=True)


__all__ = [
    "D1_NORMALIZED_IR_SCHEMA",
    "PREDICATE_CONTRACTS_BOOTSTRAP_SCHEMA",
    "CHECKER_FACT_BUNDLE_SCHEMA",
    "POLICY_EVALUATION_RESULT_SET_SCHEMA",
    "POLICY_OBLIGATION_LEDGER_SCHEMA",
    "ANM_MARKDOWN_COEXISTENCE_PROFILE_SCHEMA",
    "ANM_SELECTOR_PREDICATE_OWNERSHIP_PROFILE_SCHEMA",
    "ANM_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA",
    "ANM_BENCHMARK_POLICY_CONSUMER_BINDING_PROFILE_SCHEMA",
    "ANM_SOURCE_SET_MANIFEST_SCHEMA",
    "ANM_DOC_AUTHORITY_PROFILE_SCHEMA",
    "ANM_DOC_CLASS_POLICY_SCHEMA",
    "ANM_MIGRATION_BINDING_PROFILE_SCHEMA",
    "ANM_READER_PROJECTION_MANIFEST_SCHEMA",
    "ANM_SEMANTIC_DIFF_REPORT_SCHEMA",
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
    "MigrationDiscipline",
    "AnmCoexistenceSourceRow",
    "AnmAdoptionBoundaryRow",
    "AnmMarkdownCoexistenceProfile",
    "SelectorOwnershipRow",
    "PredicateOwnershipRow",
    "OwnershipCompatibilityRule",
    "AnmSelectorPredicateOwnershipProfile",
    "ConsumerWorldKind",
    "ConsumerRefKind",
    "PolicySourceRefKind",
    "ConsumerAuthorityRelation",
    "AllowedConsumerAction",
    "AnmPolicyConsumerRow",
    "AnmPolicyConsumerBindingProfile",
    "BenchmarkConsumerWorldKind",
    "BenchmarkConsumerRefKind",
    "BenchmarkConsumerAuthorityRelation",
    "AllowedBenchmarkConsumerAction",
    "AnmBenchmarkPolicyConsumerRow",
    "AnmBenchmarkPolicyConsumerBindingProfile",
    "AnmSourceSetEntry",
    "AnmSourceSetManifest",
    "AnmDocAuthorityProfile",
    "AnmDocClassPolicyRow",
    "AnmDocClassPolicy",
    "AnmMigrationBindingRow",
    "AnmMigrationBindingProfile",
    "AnmReaderProjectionRow",
    "AnmReaderProjectionManifest",
    "AnmSemanticDiffChangeRow",
    "AnmSemanticDiffReport",
    "stable_payload_hash",
    "canonicalize_anm_markdown_coexistence_profile_payload",
    "canonicalize_anm_selector_predicate_ownership_profile_payload",
    "canonicalize_anm_policy_consumer_binding_profile_payload",
    "canonicalize_anm_benchmark_policy_consumer_binding_profile_payload",
    "canonicalize_anm_source_set_manifest_payload",
    "canonicalize_anm_doc_authority_profile_payload",
    "canonicalize_anm_doc_class_policy_payload",
    "canonicalize_anm_migration_binding_profile_payload",
    "canonicalize_anm_reader_projection_manifest_payload",
    "canonicalize_anm_semantic_diff_report_payload",
    "canonicalize_d1_normalized_ir_payload",
    "canonicalize_predicate_contracts_bootstrap_payload",
    "canonicalize_checker_fact_bundle_payload",
    "canonicalize_policy_evaluation_result_set_payload",
    "canonicalize_policy_obligation_ledger_payload",
    "SelectorOwnershipRefKind",
    "SelectorOwnershipOwnerLayer",
    "PredicateOwnershipRefKind",
    "PredicateOwnershipOwnerLayer",
    "OwnershipCompatibilityPosture",
    "BootstrapRetirementPosture",
    "AnmDocClass",
    "AnmAuthorityLayer",
    "AnmDocSourcePosture",
    "AnmLifecycleStatus",
    "AnmClassificationStatus",
    "CompanionRegistrationStatus",
    "AnmAuthorityBlockKind",
    "AnmProfileOutputKind",
    "AnmAllowedConsumer",
    "AnmHardGate",
    "AnmWarningGate",
]
