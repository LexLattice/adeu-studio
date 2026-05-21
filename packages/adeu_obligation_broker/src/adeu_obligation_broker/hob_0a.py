from __future__ import annotations

from collections import defaultdict
from typing import Annotated, Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator
from urm_runtime.hashing import sha256_canonical_json

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

REPO_HIERARCHICAL_OBLIGATION_CATALOG_SCHEMA = "repo_hierarchical_obligation_catalog@1"
REPO_OBLIGATION_ACTIVATION_ASSESSMENT_SCHEMA = "repo_obligation_activation_assessment@1"
REPO_INHERITED_OBLIGATION_LEDGER_SCHEMA = "repo_inherited_obligation_ledger@1"
REPO_OBLIGATION_TRAVERSAL_VALIDATION_REPORT_SCHEMA = "repo_obligation_traversal_validation_report@1"
REPO_OBLIGATION_BROKER_NON_AUTHORITY_GUARDRAIL_SCHEMA = (
    "repo_obligation_broker_non_authority_guardrail@1"
)

CatalogAuthority = Literal["support", "planning", "architecture", "lock"]
NodeKind = Literal["obligation_family", "macro", "branch", "terminal_leaf"]
DefaultInheritance = Literal["inherited_required", "optional_observed", "not_inherited"]
ActivationStatus = Literal[
    "applies",
    "not_applicable_proven",
    "candidate_pending",
    "conflict_isolated",
]
InheritanceStatus = Literal[
    "root_selected",
    "inherited_required",
    "locally_triggered",
    "optional_observed",
    "not_inherited",
]
ObligationStatus = Literal[
    "open",
    "covered_terminalized",
    "covered_by_probe_matrix",
    "proved_pass_through",
    "proved_irrelevant",
    "scoped_deferred_with_expected_risk",
    "gold_deferred_with_expected_risk",
    "blocked_pending_observation",
    "blocked_pending_equivalence",
    "conflict_isolated",
    "representative_examples_only",
]
ReadinessStatus = Literal[
    "not_ready",
    "representative_examples_only",
    "branch_matrix_partial",
    "scoped_ready",
    "gold_ready",
    "blocked",
]
ProofKind = Literal["irrelevance", "pass_through", "deferral", "blocking"]
ProofType = Literal[
    "semantic_impossibility",
    "public_schema_absence",
    "negative_reference_behavior",
    "outside_active_subtree",
    "protected_surface_pass_through",
    "scoped_deferral",
    "gold_deferral",
    "pending_observation",
    "pending_equivalence",
]
FrontierReason = Literal[
    "inherited_required_missing_status",
    "active_branch_needs_terminalization",
    "irrelevance_proof_invalid",
    "pass_through_proof_incomplete",
    "deferral_risk_statement_required",
    "blocked_pending_reference_observation",
    "blocked_pending_methodological_equivalence",
    "parent_closure_blocked_by_child",
]
RequiredNextAction = Literal[
    "semantic_adjudication",
    "terminalization",
    "proof_repair",
    "deferral_risk_statement",
    "reference_observation",
    "methodological_equivalence_check",
]
DiagnosticSeverity = Literal["error", "warning"]
AuthorityPosture = Literal[
    "no_semantic_judgment_authority",
    "no_ontology_generation_authority",
    "no_probe_planning_authority",
    "no_probe_execution_authority",
    "no_worker_dispatch_authority",
    "no_implementation_authority",
    "no_product_truth_authority",
    "no_future_family_selection_authority",
]

PROOF_STATUS_KIND: dict[str, str] = {
    "proved_irrelevant": "irrelevance",
    "proved_pass_through": "pass_through",
    "scoped_deferred_with_expected_risk": "deferral",
    "gold_deferred_with_expected_risk": "deferral",
    "blocked_pending_observation": "blocking",
    "blocked_pending_equivalence": "blocking",
}
CLOSED_CHILD_STATUSES = {
    "covered_terminalized",
    "covered_by_probe_matrix",
    "proved_pass_through",
    "proved_irrelevant",
    "conflict_isolated",
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


class _HobBase(BaseModel):
    model_config = MODEL_CONFIG


class ProtectedSurfaces(_HobBase):
    stdout: bool = False
    stderr: bool = False
    exit: bool = False
    files: bool = False
    state: bool = False
    row_universe: bool = False
    aggregation_denominator: bool = False

    @model_validator(mode="after")
    def _validate_any_surface(self) -> ProtectedSurfaces:
        if not any(_dump(self).values()):
            raise ValueError("protected_surfaces must mark at least one protected surface")
        return self


class CatalogNodeRow(_HobBase):
    node_id: str
    parent_node_id: str | None = None
    node_kind: NodeKind
    title: str
    default_inheritance: DefaultInheritance = "inherited_required"
    authority_ref: str
    required_child_node_ids: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_node(self) -> CatalogNodeRow:
        object.__setattr__(
            self, "node_id", _assert_non_empty_text(self.node_id, field_name="node_id")
        )
        if self.parent_node_id is not None:
            object.__setattr__(
                self,
                "parent_node_id",
                _assert_non_empty_text(self.parent_node_id, field_name="parent_node_id"),
            )
        object.__setattr__(self, "title", _assert_non_empty_text(self.title, field_name="title"))
        object.__setattr__(
            self,
            "authority_ref",
            _assert_non_empty_text(self.authority_ref, field_name="authority_ref"),
        )
        object.__setattr__(
            self,
            "required_child_node_ids",
            _assert_sorted_unique(
                self.required_child_node_ids,
                field_name="required_child_node_ids",
            ),
        )
        return self


class RepoHierarchicalObligationCatalog(_HobBase):
    schema: Literal[REPO_HIERARCHICAL_OBLIGATION_CATALOG_SCHEMA]
    catalog_id: str
    catalog_version: str
    catalog_authority: CatalogAuthority
    catalog_nodes: list[CatalogNodeRow]
    catalog_hash: str | None = None

    @model_validator(mode="after")
    def _validate_catalog(self) -> RepoHierarchicalObligationCatalog:
        object.__setattr__(
            self,
            "catalog_id",
            _assert_non_empty_text(self.catalog_id, field_name="catalog_id"),
        )
        object.__setattr__(
            self,
            "catalog_version",
            _assert_non_empty_text(self.catalog_version, field_name="catalog_version"),
        )
        _assert_unique_rows(self.catalog_nodes, attr_name="node_id", field_name="catalog_nodes")
        node_ids = {node.node_id for node in self.catalog_nodes}
        for node in self.catalog_nodes:
            if node.parent_node_id is not None and node.parent_node_id not in node_ids:
                raise ValueError(f"node {node.node_id!r} has unknown parent_node_id")
            unknown_children = sorted(set(node.required_child_node_ids) - node_ids)
            if unknown_children:
                raise ValueError(
                    f"node {node.node_id!r} has unknown required_child_node_ids: {unknown_children}"
                )
            for child_id in node.required_child_node_ids:
                child = _node_by_id(self)[child_id]
                if child.parent_node_id != node.node_id:
                    raise ValueError(
                        f"node {node.node_id!r} lists child {child_id!r} with mismatched parent"
                    )
        object.__setattr__(
            self,
            "catalog_nodes",
            sorted(self.catalog_nodes, key=lambda node: node.node_id),
        )
        if self.catalog_hash is not None:
            expected = canonical_hash(self, drop_keys={"catalog_hash"})
            if self.catalog_hash != expected:
                raise ValueError("catalog_hash must match canonical catalog payload")
        return self


class ActivationWarrantRow(_HobBase):
    warrant_ref: str
    warrant_kind: Literal[
        "visible_spec",
        "public_schema_observation",
        "reference_behavior_observation",
        "methodological_equivalence",
        "support_doctrine",
    ]
    authority_layer: Literal["support", "planning", "architecture", "lock"]
    warrant_summary: str

    @model_validator(mode="after")
    def _validate_text(self) -> ActivationWarrantRow:
        object.__setattr__(
            self,
            "warrant_ref",
            _assert_non_empty_text(self.warrant_ref, field_name="warrant_ref"),
        )
        object.__setattr__(
            self,
            "warrant_summary",
            _assert_non_empty_text(self.warrant_summary, field_name="warrant_summary"),
        )
        return self


class NodeActivationRow(_HobBase):
    node_id: str
    activation_status: ActivationStatus
    warrant_refs: list[str]
    activation_note: str

    @model_validator(mode="after")
    def _validate_row(self) -> NodeActivationRow:
        object.__setattr__(
            self, "node_id", _assert_non_empty_text(self.node_id, field_name="node_id")
        )
        object.__setattr__(
            self,
            "warrant_refs",
            _assert_sorted_unique(self.warrant_refs, field_name="warrant_refs"),
        )
        object.__setattr__(
            self,
            "activation_note",
            _assert_non_empty_text(self.activation_note, field_name="activation_note"),
        )
        return self


class RepoObligationActivationAssessment(_HobBase):
    schema: Literal[REPO_OBLIGATION_ACTIVATION_ASSESSMENT_SCHEMA]
    catalog_id: str
    catalog_version: str
    catalog_hash: str
    activation_rows: list[NodeActivationRow]
    warrant_rows: list[ActivationWarrantRow]
    semantic_judgment_authority_posture: Literal["model_authored_broker_schema_validated"]

    @model_validator(mode="after")
    def _validate_assessment(self) -> RepoObligationActivationAssessment:
        _assert_unique_rows(self.activation_rows, attr_name="node_id", field_name="activation_rows")
        _assert_unique_rows(self.warrant_rows, attr_name="warrant_ref", field_name="warrant_rows")
        warrant_refs = {row.warrant_ref for row in self.warrant_rows}
        for row in self.activation_rows:
            unknown = sorted(set(row.warrant_refs) - warrant_refs)
            if unknown:
                raise ValueError(
                    f"activation row {row.node_id!r} references unknown warrants: {unknown}"
                )
        object.__setattr__(
            self,
            "activation_rows",
            sorted(self.activation_rows, key=lambda row: row.node_id),
        )
        object.__setattr__(
            self,
            "warrant_rows",
            sorted(self.warrant_rows, key=lambda row: row.warrant_ref),
        )
        return self


class IrrelevanceProofRow(_HobBase):
    proof_ref: str
    node_id: str
    proof_kind: Literal["irrelevance"]
    proof_type: Literal[
        "semantic_impossibility",
        "public_schema_absence",
        "negative_reference_behavior",
        "outside_active_subtree",
    ]
    protected_surfaces: ProtectedSurfaces
    warrant_ref: str
    proof_text: str

    @model_validator(mode="after")
    def _validate_text(self) -> IrrelevanceProofRow:
        _validate_proof_text_fields(self)
        return self


class PassThroughProofRow(_HobBase):
    proof_ref: str
    node_id: str
    proof_kind: Literal["pass_through"]
    proof_type: Literal["protected_surface_pass_through"]
    protected_surfaces: ProtectedSurfaces
    warrant_ref: str
    pass_through_scope: str
    proof_text: str

    @model_validator(mode="after")
    def _validate_text(self) -> PassThroughProofRow:
        _validate_proof_text_fields(self)
        object.__setattr__(
            self,
            "pass_through_scope",
            _assert_non_empty_text(self.pass_through_scope, field_name="pass_through_scope"),
        )
        return self


class DeferralProofRow(_HobBase):
    proof_ref: str
    node_id: str
    proof_kind: Literal["deferral"]
    proof_type: Literal["scoped_deferral", "gold_deferral"]
    protected_surfaces: ProtectedSurfaces
    warrant_ref: str
    deferral_status: Literal[
        "scoped_deferred_with_expected_risk",
        "gold_deferred_with_expected_risk",
    ]
    expected_risk: str
    proof_text: str

    @model_validator(mode="after")
    def _validate_text(self) -> DeferralProofRow:
        _validate_proof_text_fields(self)
        object.__setattr__(
            self,
            "expected_risk",
            _assert_non_empty_text(self.expected_risk, field_name="expected_risk"),
        )
        if self.deferral_status == "scoped_deferred_with_expected_risk" and (
            self.proof_type != "scoped_deferral"
        ):
            raise ValueError("scoped deferral status requires scoped_deferral proof_type")
        if self.deferral_status == "gold_deferred_with_expected_risk" and (
            self.proof_type != "gold_deferral"
        ):
            raise ValueError("gold deferral status requires gold_deferral proof_type")
        return self


class BlockingProofRow(_HobBase):
    proof_ref: str
    node_id: str
    proof_kind: Literal["blocking"]
    proof_type: Literal["pending_observation", "pending_equivalence"]
    protected_surfaces: ProtectedSurfaces
    warrant_ref: str
    blocking_status: Literal["blocked_pending_observation", "blocked_pending_equivalence"]
    required_next_evidence: str
    proof_text: str

    @model_validator(mode="after")
    def _validate_text(self) -> BlockingProofRow:
        _validate_proof_text_fields(self)
        object.__setattr__(
            self,
            "required_next_evidence",
            _assert_non_empty_text(
                self.required_next_evidence,
                field_name="required_next_evidence",
            ),
        )
        if self.blocking_status == "blocked_pending_observation" and (
            self.proof_type != "pending_observation"
        ):
            raise ValueError("blocked_pending_observation requires pending_observation proof_type")
        if self.blocking_status == "blocked_pending_equivalence" and (
            self.proof_type != "pending_equivalence"
        ):
            raise ValueError("blocked_pending_equivalence requires pending_equivalence proof_type")
        return self


ProofRow = Annotated[
    IrrelevanceProofRow | PassThroughProofRow | DeferralProofRow | BlockingProofRow,
    Field(discriminator="proof_kind"),
]


def _validate_proof_text_fields(
    proof: IrrelevanceProofRow | PassThroughProofRow | DeferralProofRow | BlockingProofRow,
) -> None:
    object.__setattr__(
        proof,
        "proof_ref",
        _assert_non_empty_text(proof.proof_ref, field_name="proof_ref"),
    )
    object.__setattr__(
        proof,
        "node_id",
        _assert_non_empty_text(proof.node_id, field_name="node_id"),
    )
    object.__setattr__(
        proof,
        "warrant_ref",
        _assert_non_empty_text(proof.warrant_ref, field_name="warrant_ref"),
    )
    object.__setattr__(
        proof,
        "proof_text",
        _assert_non_empty_text(proof.proof_text, field_name="proof_text"),
    )


class InheritedObligationRow(_HobBase):
    node_id: str
    inherited_from_node_id: str | None = None
    inheritance_status: InheritanceStatus
    obligation_status: ObligationStatus
    warrant_ref: str | None = None
    proof_ref: str | None = None
    probe_refs: list[str] = Field(default_factory=list)
    implementation_owner: str | None = None
    expected_risk_if_deferred: str | None = None

    @model_validator(mode="after")
    def _validate_row(self) -> InheritedObligationRow:
        object.__setattr__(
            self, "node_id", _assert_non_empty_text(self.node_id, field_name="node_id")
        )
        if self.inherited_from_node_id is not None:
            object.__setattr__(
                self,
                "inherited_from_node_id",
                _assert_non_empty_text(
                    self.inherited_from_node_id,
                    field_name="inherited_from_node_id",
                ),
            )
        if self.warrant_ref is not None:
            object.__setattr__(
                self,
                "warrant_ref",
                _assert_non_empty_text(self.warrant_ref, field_name="warrant_ref"),
            )
        if self.proof_ref is not None:
            object.__setattr__(
                self,
                "proof_ref",
                _assert_non_empty_text(self.proof_ref, field_name="proof_ref"),
            )
        if self.implementation_owner is not None:
            object.__setattr__(
                self,
                "implementation_owner",
                _assert_non_empty_text(
                    self.implementation_owner,
                    field_name="implementation_owner",
                ),
            )
        if self.expected_risk_if_deferred is not None:
            object.__setattr__(
                self,
                "expected_risk_if_deferred",
                _assert_non_empty_text(
                    self.expected_risk_if_deferred,
                    field_name="expected_risk_if_deferred",
                ),
            )
        object.__setattr__(
            self,
            "probe_refs",
            _assert_sorted_unique(self.probe_refs, field_name="probe_refs"),
        )
        return self


class ReadinessClaimRow(_HobBase):
    node_id: str
    readiness_status: ReadinessStatus
    readiness_claim_ref: str

    @model_validator(mode="after")
    def _validate_text(self) -> ReadinessClaimRow:
        object.__setattr__(
            self, "node_id", _assert_non_empty_text(self.node_id, field_name="node_id")
        )
        object.__setattr__(
            self,
            "readiness_claim_ref",
            _assert_non_empty_text(
                self.readiness_claim_ref,
                field_name="readiness_claim_ref",
            ),
        )
        return self


class RepoInheritedObligationLedger(_HobBase):
    schema: Literal[REPO_INHERITED_OBLIGATION_LEDGER_SCHEMA]
    catalog_id: str
    catalog_version: str
    catalog_hash: str
    activation_assessment_ref: str
    obligation_rows: list[InheritedObligationRow]
    proof_rows: list[ProofRow] = Field(default_factory=list)
    readiness_claim_rows: list[ReadinessClaimRow] = Field(default_factory=list)
    ledger_hash: str | None = None
    stale_catalog_posture: Literal["current_catalog_hash_bound", "stale_catalog_blocked"]

    @model_validator(mode="after")
    def _validate_ledger(self) -> RepoInheritedObligationLedger:
        _assert_unique_rows(self.obligation_rows, attr_name="node_id", field_name="obligation_rows")
        proof_refs: set[str] = set()
        for proof in self.proof_rows:
            if proof.proof_ref in proof_refs:
                raise ValueError(
                    f"proof_rows must not contain duplicate proof_ref {proof.proof_ref!r}"
                )
            proof_refs.add(proof.proof_ref)
        _assert_unique_rows(
            self.readiness_claim_rows,
            attr_name="node_id",
            field_name="readiness_claim_rows",
        )
        object.__setattr__(
            self,
            "obligation_rows",
            sorted(self.obligation_rows, key=lambda row: row.node_id),
        )
        object.__setattr__(
            self,
            "proof_rows",
            sorted(self.proof_rows, key=lambda row: row.proof_ref),
        )
        object.__setattr__(
            self,
            "readiness_claim_rows",
            sorted(self.readiness_claim_rows, key=lambda row: row.node_id),
        )
        if self.ledger_hash is not None:
            expected = canonical_hash(self, drop_keys={"ledger_hash"})
            if self.ledger_hash != expected:
                raise ValueError("ledger_hash must match canonical ledger payload")
        return self


class TraversalDiagnosticRow(_HobBase):
    diagnostic_ref: str
    severity: DiagnosticSeverity
    diagnostic_code: str
    node_id: str | None = None
    message: str

    @model_validator(mode="after")
    def _validate_text(self) -> TraversalDiagnosticRow:
        object.__setattr__(
            self,
            "diagnostic_ref",
            _assert_non_empty_text(self.diagnostic_ref, field_name="diagnostic_ref"),
        )
        object.__setattr__(
            self,
            "diagnostic_code",
            _assert_non_empty_text(self.diagnostic_code, field_name="diagnostic_code"),
        )
        if self.node_id is not None:
            object.__setattr__(
                self,
                "node_id",
                _assert_non_empty_text(self.node_id, field_name="node_id"),
            )
        object.__setattr__(
            self,
            "message",
            _assert_non_empty_text(self.message, field_name="message"),
        )
        return self


class FrontierRow(_HobBase):
    frontier_ref: str
    node_id: str
    parent_node_id: str | None = None
    frontier_reason: FrontierReason
    required_next_action: RequiredNextAction
    source_diagnostic_refs: list[str]

    @model_validator(mode="after")
    def _validate_row(self) -> FrontierRow:
        object.__setattr__(
            self,
            "frontier_ref",
            _assert_non_empty_text(self.frontier_ref, field_name="frontier_ref"),
        )
        object.__setattr__(
            self, "node_id", _assert_non_empty_text(self.node_id, field_name="node_id")
        )
        if self.parent_node_id is not None:
            object.__setattr__(
                self,
                "parent_node_id",
                _assert_non_empty_text(self.parent_node_id, field_name="parent_node_id"),
            )
        object.__setattr__(
            self,
            "source_diagnostic_refs",
            _assert_sorted_unique(
                self.source_diagnostic_refs,
                field_name="source_diagnostic_refs",
            ),
        )
        return self


class RepoObligationTraversalValidationReport(_HobBase):
    schema: Literal[REPO_OBLIGATION_TRAVERSAL_VALIDATION_REPORT_SCHEMA]
    catalog_id: str
    catalog_version: str
    catalog_hash: str
    activation_assessment_hash: str
    inherited_obligation_ledger_hash: str
    validation_status: Literal["passed", "failed_closed"]
    diagnostic_rows: list[TraversalDiagnosticRow]
    frontier_rows: list[FrontierRow]
    false_parent_closure_blocked: bool
    report_hash: str | None = None

    @model_validator(mode="after")
    def _validate_report(self) -> RepoObligationTraversalValidationReport:
        _assert_unique_rows(
            self.diagnostic_rows,
            attr_name="diagnostic_ref",
            field_name="diagnostic_rows",
        )
        _assert_unique_rows(
            self.frontier_rows, attr_name="frontier_ref", field_name="frontier_rows"
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
        if self.validation_status == "passed" and self.diagnostic_rows:
            raise ValueError("passed validation report cannot contain diagnostics")
        if self.validation_status == "failed_closed" and not self.diagnostic_rows:
            raise ValueError("failed_closed validation report requires diagnostics")
        if self.report_hash is not None:
            expected = canonical_hash(self, drop_keys={"report_hash"})
            if self.report_hash != expected:
                raise ValueError("report_hash must match canonical report payload")
        return self


class RepoObligationBrokerNonAuthorityGuardrail(_HobBase):
    schema: Literal[REPO_OBLIGATION_BROKER_NON_AUTHORITY_GUARDRAIL_SCHEMA]
    guardrail_ref: str
    denied_authority_postures: list[AuthorityPosture]
    slice_scope_posture: Literal["hob_0a_structural_validation_only"]
    closure_aggregation_posture: Literal["deferred_to_hob_0b"]
    probe_matrix_posture: Literal["deferred_to_hob_0b"]
    delta_attribution_posture: Literal["deferred_to_hob_0c"]

    @model_validator(mode="after")
    def _validate_guardrail(self) -> RepoObligationBrokerNonAuthorityGuardrail:
        object.__setattr__(
            self,
            "guardrail_ref",
            _assert_non_empty_text(self.guardrail_ref, field_name="guardrail_ref"),
        )
        object.__setattr__(
            self,
            "denied_authority_postures",
            _assert_sorted_unique(
                self.denied_authority_postures,
                field_name="denied_authority_postures",
            ),
        )
        return self


def _node_by_id(catalog: RepoHierarchicalObligationCatalog) -> dict[str, CatalogNodeRow]:
    return {node.node_id: node for node in catalog.catalog_nodes}


def _children_by_parent(
    catalog: RepoHierarchicalObligationCatalog,
) -> dict[str, list[CatalogNodeRow]]:
    children: dict[str, list[CatalogNodeRow]] = defaultdict(list)
    for node in catalog.catalog_nodes:
        if node.parent_node_id is not None:
            children[node.parent_node_id].append(node)
    return {parent: sorted(rows, key=lambda row: row.node_id) for parent, rows in children.items()}


def _active_node_ids(activation: RepoObligationActivationAssessment) -> set[str]:
    return {row.node_id for row in activation.activation_rows if row.activation_status == "applies"}


def _descendant_rows(
    catalog: RepoHierarchicalObligationCatalog,
    root_node_id: str,
) -> list[tuple[str | None, CatalogNodeRow]]:
    children = _children_by_parent(catalog)
    rows: list[tuple[str | None, CatalogNodeRow]] = [(None, _node_by_id(catalog)[root_node_id])]
    stack = [(root_node_id, child) for child in reversed(children.get(root_node_id, []))]
    while stack:
        parent_id, node = stack.pop()
        rows.append((parent_id, node))
        for child in reversed(children.get(node.node_id, [])):
            stack.append((node.node_id, child))
    return sorted(rows, key=lambda item: item[1].node_id)


def load_catalog(
    payload: RepoHierarchicalObligationCatalog | dict[str, Any],
) -> RepoHierarchicalObligationCatalog:
    if isinstance(payload, RepoHierarchicalObligationCatalog):
        return payload
    return RepoHierarchicalObligationCatalog.model_validate(payload)


def validate_catalog(
    catalog: RepoHierarchicalObligationCatalog | dict[str, Any],
) -> RepoHierarchicalObligationCatalog:
    return load_catalog(catalog)


def expand_inherited_obligations(
    catalog: RepoHierarchicalObligationCatalog,
    activation: RepoObligationActivationAssessment,
) -> RepoInheritedObligationLedger:
    _validate_catalog_binding(
        catalog, activation.catalog_id, activation.catalog_version, activation.catalog_hash
    )
    known_nodes = _node_by_id(catalog)
    for row in activation.activation_rows:
        if row.node_id not in known_nodes:
            raise ValueError(f"activation row references unknown catalog node {row.node_id!r}")

    obligation_by_node: dict[str, InheritedObligationRow] = {}
    for active_id in sorted(_active_node_ids(activation)):
        for parent_id, node in _descendant_rows(catalog, active_id):
            if node.node_id in obligation_by_node:
                continue
            if parent_id is None:
                inheritance_status: InheritanceStatus = "root_selected"
            elif node.default_inheritance == "optional_observed":
                inheritance_status = "optional_observed"
            elif node.default_inheritance == "not_inherited":
                inheritance_status = "not_inherited"
            else:
                inheritance_status = "inherited_required"
            obligation_by_node[node.node_id] = InheritedObligationRow(
                node_id=node.node_id,
                inherited_from_node_id=parent_id,
                inheritance_status=inheritance_status,
                obligation_status="open",
            )

    return RepoInheritedObligationLedger(
        schema=REPO_INHERITED_OBLIGATION_LEDGER_SCHEMA,
        catalog_id=catalog.catalog_id,
        catalog_version=catalog.catalog_version,
        catalog_hash=activation.catalog_hash,
        activation_assessment_ref=canonical_hash(activation),
        obligation_rows=sorted(obligation_by_node.values(), key=lambda row: row.node_id),
        proof_rows=[],
        readiness_claim_rows=[],
        stale_catalog_posture="current_catalog_hash_bound",
    )


def validate_obligation_ledger(
    *,
    catalog: RepoHierarchicalObligationCatalog,
    activation: RepoObligationActivationAssessment,
    ledger: RepoInheritedObligationLedger,
) -> RepoObligationTraversalValidationReport:
    _validate_catalog_binding(
        catalog, activation.catalog_id, activation.catalog_version, activation.catalog_hash
    )
    _validate_catalog_binding(
        catalog, ledger.catalog_id, ledger.catalog_version, ledger.catalog_hash
    )
    diagnostics: list[TraversalDiagnosticRow] = []
    frontier_rows: list[FrontierRow] = []

    expected = expand_inherited_obligations(catalog, activation)
    expected_rows = {row.node_id: row for row in expected.obligation_rows}
    expected_node_ids = {
        row.node_id for row in expected.obligation_rows if row.inheritance_status != "not_inherited"
    }
    ledger_rows = {row.node_id: row for row in ledger.obligation_rows}
    catalog_nodes = _node_by_id(catalog)
    active_nodes = _active_node_ids(activation)
    proof_rows = {row.proof_ref: row for row in ledger.proof_rows}
    proofs_by_node: dict[str, list[ProofRow]] = defaultdict(list)
    for proof in ledger.proof_rows:
        proofs_by_node[proof.node_id].append(proof)

    def add_diag(
        *,
        code: str,
        node_id: str | None,
        message: str,
        severity: DiagnosticSeverity = "error",
    ) -> str:
        diagnostic_ref = f"hob-0a-diagnostic:{len(diagnostics) + 1:04d}:{code.lower()}"
        diagnostics.append(
            TraversalDiagnosticRow(
                diagnostic_ref=diagnostic_ref,
                severity=severity,
                diagnostic_code=code,
                node_id=node_id,
                message=message,
            )
        )
        return diagnostic_ref

    def add_frontier(
        *,
        node_id: str,
        parent_node_id: str | None,
        reason: FrontierReason,
        action: RequiredNextAction,
        diagnostic_ref: str,
    ) -> None:
        frontier_rows.append(
            FrontierRow(
                frontier_ref=f"hob-0a-frontier:{len(frontier_rows) + 1:04d}:{node_id}",
                node_id=node_id,
                parent_node_id=parent_node_id,
                frontier_reason=reason,
                required_next_action=action,
                source_diagnostic_refs=[diagnostic_ref],
            )
        )

    for node_id in sorted(expected_node_ids - set(ledger_rows)):
        node = catalog_nodes[node_id]
        diagnostic_ref = add_diag(
            code="MISSING_INHERITED_OBLIGATION",
            node_id=node_id,
            message=f"active parent inheritance requires status row for {node_id!r}",
        )
        add_frontier(
            node_id=node_id,
            parent_node_id=node.parent_node_id,
            reason="inherited_required_missing_status",
            action="semantic_adjudication",
            diagnostic_ref=diagnostic_ref,
        )

    for node_id in sorted(set(ledger_rows) - set(catalog_nodes)):
        diagnostic_ref = add_diag(
            code="UNKNOWN_OBLIGATION_NODE",
            node_id=node_id,
            message=f"ledger row references unknown catalog node {node_id!r}",
        )
        add_frontier(
            node_id=node_id,
            parent_node_id=None,
            reason="active_branch_needs_terminalization",
            action="terminalization",
            diagnostic_ref=diagnostic_ref,
        )

    for row in ledger.obligation_rows:
        node = catalog_nodes.get(row.node_id)
        if node is None:
            continue
        expected_row = expected_rows.get(row.node_id)
        if expected_row is not None and not _lineage_matches_expected(row, expected_row):
            diagnostic_ref = add_diag(
                code="INHERITED_OBLIGATION_LINEAGE_MISMATCH",
                node_id=row.node_id,
                message=(
                    f"obligation row {row.node_id!r} has inherited_from_node_id or "
                    "inheritance_status that does not match deterministic catalog expansion"
                ),
            )
            add_frontier(
                node_id=row.node_id,
                parent_node_id=expected_row.inherited_from_node_id,
                reason="active_branch_needs_terminalization",
                action="semantic_adjudication",
                diagnostic_ref=diagnostic_ref,
            )
        if row.proof_ref is not None and row.proof_ref not in proof_rows:
            diagnostic_ref = add_diag(
                code="UNKNOWN_PROOF_REF",
                node_id=row.node_id,
                message=f"obligation row {row.node_id!r} references unknown proof_ref",
            )
            add_frontier(
                node_id=row.node_id,
                parent_node_id=row.inherited_from_node_id,
                reason="irrelevance_proof_invalid",
                action="proof_repair",
                diagnostic_ref=diagnostic_ref,
            )
        _validate_status_proof(row, proof_rows, diagnostics, frontier_rows, add_diag, add_frontier)
        _validate_not_inherited(row, node, active_nodes, proofs_by_node, add_diag, add_frontier)
        _emit_open_or_blocked_frontier(row, add_diag, add_frontier)

    false_parent_closure_blocked = False
    for claim in ledger.readiness_claim_rows:
        if claim.node_id not in catalog_nodes:
            add_diag(
                code="UNKNOWN_READINESS_CLAIM_NODE",
                node_id=claim.node_id,
                message=f"readiness claim references unknown catalog node {claim.node_id!r}",
            )
            false_parent_closure_blocked = True
            continue
        if claim.readiness_status in {"gold_ready", "scoped_ready"}:
            for child_id in _required_descendant_ids(catalog, claim.node_id):
                child = ledger_rows.get(child_id)
                if child is None:
                    false_parent_closure_blocked = True
                    continue
                if claim.readiness_status == "gold_ready" and child.obligation_status in {
                    "scoped_deferred_with_expected_risk",
                    "representative_examples_only",
                    "open",
                    "blocked_pending_observation",
                    "blocked_pending_equivalence",
                }:
                    diagnostic_ref = add_diag(
                        code="FALSE_PARENT_GOLD_READY_CLAIM",
                        node_id=claim.node_id,
                        message=(
                            f"parent {claim.node_id!r} cannot claim gold_ready while child "
                            f"{child_id!r} is {child.obligation_status!r}"
                        ),
                    )
                    add_frontier(
                        node_id=child_id,
                        parent_node_id=claim.node_id,
                        reason="parent_closure_blocked_by_child",
                        action="terminalization",
                        diagnostic_ref=diagnostic_ref,
                    )
                    false_parent_closure_blocked = True
                if claim.readiness_status == "scoped_ready" and child.obligation_status in {
                    "representative_examples_only",
                    "open",
                    "blocked_pending_observation",
                    "blocked_pending_equivalence",
                }:
                    diagnostic_ref = add_diag(
                        code="FALSE_PARENT_SCOPED_READY_CLAIM",
                        node_id=claim.node_id,
                        message=(
                            f"parent {claim.node_id!r} cannot claim scoped_ready while child "
                            f"{child_id!r} is {child.obligation_status!r}"
                        ),
                    )
                    add_frontier(
                        node_id=child_id,
                        parent_node_id=claim.node_id,
                        reason="parent_closure_blocked_by_child",
                        action="terminalization",
                        diagnostic_ref=diagnostic_ref,
                    )
                    false_parent_closure_blocked = True
                if child.inheritance_status == "optional_observed" and (
                    child.obligation_status in CLOSED_CHILD_STATUSES
                ):
                    diagnostic_ref = add_diag(
                        code="OPTIONAL_OBSERVED_CANNOT_CLOSE_PARENT",
                        node_id=child_id,
                        message=(
                            f"optional_observed child {child_id!r} cannot support parent "
                            "readiness without local triggering or promotion"
                        ),
                    )
                    add_frontier(
                        node_id=child_id,
                        parent_node_id=claim.node_id,
                        reason="parent_closure_blocked_by_child",
                        action="semantic_adjudication",
                        diagnostic_ref=diagnostic_ref,
                    )
                    false_parent_closure_blocked = True

    validation_status = "failed_closed" if diagnostics else "passed"
    return RepoObligationTraversalValidationReport(
        schema=REPO_OBLIGATION_TRAVERSAL_VALIDATION_REPORT_SCHEMA,
        catalog_id=catalog.catalog_id,
        catalog_version=catalog.catalog_version,
        catalog_hash=catalog.catalog_hash or canonical_hash(catalog, drop_keys={"catalog_hash"}),
        activation_assessment_hash=canonical_hash(activation),
        inherited_obligation_ledger_hash=canonical_hash(ledger, drop_keys={"ledger_hash"}),
        validation_status=validation_status,
        diagnostic_rows=diagnostics,
        frontier_rows=frontier_rows,
        false_parent_closure_blocked=false_parent_closure_blocked,
    )


def emit_frontier(report: RepoObligationTraversalValidationReport) -> list[FrontierRow]:
    return report.frontier_rows


def _validate_catalog_binding(
    catalog: RepoHierarchicalObligationCatalog,
    catalog_id: str,
    catalog_version: str,
    catalog_hash: str,
) -> None:
    if catalog_id != catalog.catalog_id or catalog_version != catalog.catalog_version:
        raise ValueError("artifact catalog_id/catalog_version must match catalog")
    expected = catalog.catalog_hash or canonical_hash(catalog, drop_keys={"catalog_hash"})
    if catalog_hash != expected:
        raise ValueError("artifact catalog_hash must match catalog")


def _required_descendant_ids(
    catalog: RepoHierarchicalObligationCatalog,
    node_id: str,
) -> list[str]:
    return [
        node.node_id
        for parent_id, node in _descendant_rows(catalog, node_id)
        if parent_id is not None and node.default_inheritance != "not_inherited"
    ]


def _validate_status_proof(
    row: InheritedObligationRow,
    proof_rows: dict[str, ProofRow],
    diagnostics: list[TraversalDiagnosticRow],
    frontier_rows: list[FrontierRow],
    add_diag: Any,
    add_frontier: Any,
) -> None:
    required_kind = PROOF_STATUS_KIND.get(row.obligation_status)
    if required_kind is None:
        return
    if row.proof_ref is None:
        reason: FrontierReason = "irrelevance_proof_invalid"
        action: RequiredNextAction = "proof_repair"
        if required_kind == "deferral":
            reason = "deferral_risk_statement_required"
            action = "deferral_risk_statement"
        elif required_kind == "blocking":
            reason = (
                "blocked_pending_reference_observation"
                if row.obligation_status == "blocked_pending_observation"
                else "blocked_pending_methodological_equivalence"
            )
            action = (
                "reference_observation"
                if row.obligation_status == "blocked_pending_observation"
                else "methodological_equivalence_check"
            )
        diagnostic_ref = add_diag(
            code="PROOF_REQUIRED_FOR_STATUS",
            node_id=row.node_id,
            message=f"{row.obligation_status!r} requires a {required_kind!r} proof row",
        )
        add_frontier(
            node_id=row.node_id,
            parent_node_id=row.inherited_from_node_id,
            reason=reason,
            action=action,
            diagnostic_ref=diagnostic_ref,
        )
        return
    proof = proof_rows.get(row.proof_ref)
    if proof is None:
        return
    if proof.node_id != row.node_id or proof.proof_kind != required_kind:
        diagnostic_ref = add_diag(
            code="PROOF_KIND_MISMATCH",
            node_id=row.node_id,
            message=f"{row.obligation_status!r} requires {required_kind!r} proof for same node",
        )
        add_frontier(
            node_id=row.node_id,
            parent_node_id=row.inherited_from_node_id,
            reason="irrelevance_proof_invalid",
            action="proof_repair",
            diagnostic_ref=diagnostic_ref,
        )
    if isinstance(proof, DeferralProofRow) and proof.deferral_status != row.obligation_status:
        diagnostic_ref = add_diag(
            code="DEFERRAL_PROOF_STATUS_MISMATCH",
            node_id=row.node_id,
            message="deferral proof status must match obligation status",
        )
        add_frontier(
            node_id=row.node_id,
            parent_node_id=row.inherited_from_node_id,
            reason="deferral_risk_statement_required",
            action="deferral_risk_statement",
            diagnostic_ref=diagnostic_ref,
        )
    if isinstance(proof, BlockingProofRow) and proof.blocking_status != row.obligation_status:
        diagnostic_ref = add_diag(
            code="BLOCKING_PROOF_STATUS_MISMATCH",
            node_id=row.node_id,
            message="blocking proof status must match obligation status",
        )
        add_frontier(
            node_id=row.node_id,
            parent_node_id=row.inherited_from_node_id,
            reason="blocked_pending_reference_observation",
            action="reference_observation",
            diagnostic_ref=diagnostic_ref,
        )


def _lineage_matches_expected(
    row: InheritedObligationRow,
    expected_row: InheritedObligationRow,
) -> bool:
    if row.inherited_from_node_id != expected_row.inherited_from_node_id:
        return False
    if row.inheritance_status == expected_row.inheritance_status:
        return True
    return (
        expected_row.inheritance_status == "optional_observed"
        and row.inheritance_status == "locally_triggered"
    )


def _validate_not_inherited(
    row: InheritedObligationRow,
    node: CatalogNodeRow,
    active_nodes: set[str],
    proofs_by_node: dict[str, list[ProofRow]],
    add_diag: Any,
    add_frontier: Any,
) -> None:
    if row.inheritance_status != "not_inherited":
        return
    parent_inactive = (
        row.inherited_from_node_id is not None and row.inherited_from_node_id not in active_nodes
    )
    catalog_allows = node.default_inheritance == "not_inherited"
    proof_allows = any(
        isinstance(proof, IrrelevanceProofRow) and proof.proof_type == "outside_active_subtree"
        for proof in proofs_by_node[row.node_id]
    )
    if not (parent_inactive or catalog_allows or proof_allows):
        diagnostic_ref = add_diag(
            code="NOT_INHERITED_ESCAPE_HATCH_BLOCKED",
            node_id=row.node_id,
            message=(
                "not_inherited requires inactive parent, catalog default, or "
                "outside_active_subtree proof"
            ),
        )
        add_frontier(
            node_id=row.node_id,
            parent_node_id=row.inherited_from_node_id,
            reason="irrelevance_proof_invalid",
            action="proof_repair",
            diagnostic_ref=diagnostic_ref,
        )


def _emit_open_or_blocked_frontier(
    row: InheritedObligationRow,
    add_diag: Any,
    add_frontier: Any,
) -> None:
    if row.obligation_status == "open":
        diagnostic_ref = add_diag(
            code="OPEN_INHERITED_OBLIGATION",
            node_id=row.node_id,
            message=f"inherited obligation {row.node_id!r} remains open",
            severity="warning",
        )
        add_frontier(
            node_id=row.node_id,
            parent_node_id=row.inherited_from_node_id,
            reason="active_branch_needs_terminalization",
            action="terminalization",
            diagnostic_ref=diagnostic_ref,
        )
    elif row.obligation_status == "blocked_pending_observation":
        diagnostic_ref = add_diag(
            code="BLOCKED_PENDING_OBSERVATION",
            node_id=row.node_id,
            message=f"inherited obligation {row.node_id!r} needs reference observation",
        )
        add_frontier(
            node_id=row.node_id,
            parent_node_id=row.inherited_from_node_id,
            reason="blocked_pending_reference_observation",
            action="reference_observation",
            diagnostic_ref=diagnostic_ref,
        )
    elif row.obligation_status == "blocked_pending_equivalence":
        diagnostic_ref = add_diag(
            code="BLOCKED_PENDING_EQUIVALENCE",
            node_id=row.node_id,
            message=f"inherited obligation {row.node_id!r} needs equivalence evidence",
        )
        add_frontier(
            node_id=row.node_id,
            parent_node_id=row.inherited_from_node_id,
            reason="blocked_pending_methodological_equivalence",
            action="methodological_equivalence_check",
            diagnostic_ref=diagnostic_ref,
        )
