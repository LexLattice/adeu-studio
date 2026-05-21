from __future__ import annotations

from collections import defaultdict
from typing import Literal

from pydantic import Field, model_validator

from .hob_0a import (
    CatalogNodeRow,
    FrontierRow,
    InheritedObligationRow,
    RepoHierarchicalObligationCatalog,
    RepoInheritedObligationLedger,
    RepoObligationTraversalValidationReport,
    _assert_non_empty_text,
    _assert_sorted_unique,
    _assert_unique_rows,
    _HobBase,
    _node_by_id,
    canonical_hash,
)

REPO_OBLIGATION_CLOSURE_REPORT_SCHEMA = "repo_obligation_closure_report@1"
REPO_OBLIGATION_NEXT_FRONTIER_REPORT_SCHEMA = "repo_obligation_next_frontier_report@1"
REPO_OBLIGATION_PROBE_MATRIX_PLAN_SCHEMA = "repo_obligation_probe_matrix_plan@1"
REPO_OBLIGATION_IMPLEMENTATION_BATCH_CONTRACT_SCHEMA = (
    "repo_obligation_implementation_batch_contract@1"
)
REPO_OBLIGATION_OPERATIONALIZATION_REPORT_SCHEMA = (
    "repo_obligation_operationalization_report@1"
)

ClosureStatus = Literal[
    "gold_ready",
    "scoped_ready",
    "representative_only",
    "deferred_with_risk",
    "blocked",
    "not_ready",
]
ClosureBasis = Literal[
    "all_children_gold_ready",
    "all_children_scoped_ready",
    "representative_only",
    "blocked_by_child",
    "blocked_by_A_validation",
    "deferred_with_risk",
]
FrontierPriority = Literal["critical", "high", "normal", "low"]
FrontierBatchability = Literal["batchable", "requires_sequential_review"]
ProbeKind = Literal["terminal_behavior_probe", "boundary_probe", "held_out_regression_probe"]
ProbeAuthorityPosture = Literal["plan_only_not_observed"]
ProbePlanNonExecutionPosture = Literal["plan_only_no_probe_execution"]
SubmitAllowedPosture = Literal["submit_not_allowed_planning_only"]
WorkerDispatchAuthorityPosture = Literal["no_worker_dispatch_authority"]
OperationalizationStatus = Literal[
    "ready_for_implementation_planning",
    "partial_with_blockers",
    "blocked",
]
OperationalizationNonAuthorityPosture = Literal["planning_only_not_product_truth"]

_READINESS_RANK: dict[str, int] = {
    "blocked": 0,
    "not_ready": 0,
    "representative_only": 1,
    "deferred_with_risk": 2,
    "scoped_ready": 3,
    "gold_ready": 4,
}
_TERMINAL_GOLD_STATUSES = {
    "covered_terminalized",
    "proved_pass_through",
    "proved_irrelevant",
    "conflict_isolated",
}


def _status_weaker_than(left: ClosureStatus, right: ClosureStatus) -> bool:
    return _READINESS_RANK[left] < _READINESS_RANK[right]


class SubtreeClosureRow(_HobBase):
    node_id: str
    child_node_ids: list[str] = Field(default_factory=list)
    closure_basis: ClosureBasis
    closure_status: ClosureStatus
    blocker_node_refs: list[str] = Field(default_factory=list)
    representative_only: bool = False

    @model_validator(mode="after")
    def _validate_row(self) -> SubtreeClosureRow:
        object.__setattr__(
            self, "node_id", _assert_non_empty_text(self.node_id, field_name="node_id")
        )
        object.__setattr__(
            self,
            "child_node_ids",
            _assert_sorted_unique(self.child_node_ids, field_name="child_node_ids"),
        )
        object.__setattr__(
            self,
            "blocker_node_refs",
            _assert_sorted_unique(self.blocker_node_refs, field_name="blocker_node_refs"),
        )
        if self.closure_basis == "all_children_gold_ready" and self.closure_status != "gold_ready":
            raise ValueError("all_children_gold_ready requires gold_ready closure_status")
        if self.closure_basis == "all_children_scoped_ready" and (
            self.closure_status != "scoped_ready"
        ):
            raise ValueError("all_children_scoped_ready requires scoped_ready closure_status")
        if self.closure_basis == "representative_only":
            if self.closure_status != "representative_only" or not self.representative_only:
                raise ValueError("representative_only basis requires representative_only status")
        if self.closure_basis in {"blocked_by_child", "blocked_by_A_validation"}:
            if self.closure_status != "blocked" or not self.blocker_node_refs:
                raise ValueError("blocked closure basis requires blocked status and blockers")
        if self.closure_basis == "deferred_with_risk" and (
            self.closure_status != "deferred_with_risk"
        ):
            raise ValueError("deferred_with_risk basis requires deferred_with_risk status")
        return self


class WeakestChildReadinessRow(_HobBase):
    node_id: str
    weakest_child_node_id: str | None = None
    weakest_child_readiness: ClosureStatus

    @model_validator(mode="after")
    def _validate_row(self) -> WeakestChildReadinessRow:
        object.__setattr__(
            self, "node_id", _assert_non_empty_text(self.node_id, field_name="node_id")
        )
        if self.weakest_child_node_id is not None:
            object.__setattr__(
                self,
                "weakest_child_node_id",
                _assert_non_empty_text(
                    self.weakest_child_node_id,
                    field_name="weakest_child_node_id",
                ),
            )
        return self


class ClosureBasisRow(_HobBase):
    node_id: str
    closure_basis: ClosureBasis

    @model_validator(mode="after")
    def _validate_row(self) -> ClosureBasisRow:
        object.__setattr__(
            self, "node_id", _assert_non_empty_text(self.node_id, field_name="node_id")
        )
        return self


class RepoObligationClosureReport(_HobBase):
    schema: Literal[REPO_OBLIGATION_CLOSURE_REPORT_SCHEMA]
    catalog_id: str
    catalog_version: str
    catalog_hash: str
    inherited_obligation_ledger_hash: str
    traversal_validation_report_hash: str
    a_validation_status: Literal["passed", "failed_closed"]
    subtree_closure_rows: list[SubtreeClosureRow]
    weakest_child_readiness_rows: list[WeakestChildReadinessRow]
    closure_basis_rows: list[ClosureBasisRow]
    closure_status: ClosureStatus
    closure_blocker_refs: list[str] = Field(default_factory=list)
    closure_authority_posture: Literal["local_broker_accounting_only_not_product_truth"]
    report_hash: str | None = None

    @model_validator(mode="after")
    def _validate_report(self) -> RepoObligationClosureReport:
        _assert_unique_rows(
            self.subtree_closure_rows,
            attr_name="node_id",
            field_name="subtree_closure_rows",
        )
        _assert_unique_rows(
            self.weakest_child_readiness_rows,
            attr_name="node_id",
            field_name="weakest_child_readiness_rows",
        )
        _assert_unique_rows(
            self.closure_basis_rows,
            attr_name="node_id",
            field_name="closure_basis_rows",
        )
        object.__setattr__(
            self,
            "subtree_closure_rows",
            sorted(self.subtree_closure_rows, key=lambda row: row.node_id),
        )
        object.__setattr__(
            self,
            "weakest_child_readiness_rows",
            sorted(self.weakest_child_readiness_rows, key=lambda row: row.node_id),
        )
        object.__setattr__(
            self,
            "closure_basis_rows",
            sorted(self.closure_basis_rows, key=lambda row: row.node_id),
        )
        object.__setattr__(
            self,
            "closure_blocker_refs",
            _assert_sorted_unique(self.closure_blocker_refs, field_name="closure_blocker_refs"),
        )
        if any(row.closure_basis == "blocked_by_A_validation" for row in self.subtree_closure_rows):
            if self.closure_status != "blocked":
                raise ValueError("blocked_by_A_validation requires blocked closure_status")
        readiness_by_node = {row.node_id: row for row in self.weakest_child_readiness_rows}
        for row in self.subtree_closure_rows:
            weakest = readiness_by_node.get(row.node_id)
            if weakest is None:
                continue
            if _status_weaker_than(weakest.weakest_child_readiness, row.closure_status):
                raise ValueError("parent closure_status cannot exceed weakest child readiness")
        if self.report_hash is not None:
            expected = canonical_hash(self, drop_keys={"report_hash"})
            if self.report_hash != expected:
                raise ValueError("report_hash must match canonical closure report payload")
        return self


class FrontierPriorityRow(_HobBase):
    frontier_ref: str
    node_id: str
    priority: FrontierPriority
    batchability: FrontierBatchability
    priority_reason: str

    @model_validator(mode="after")
    def _validate_row(self) -> FrontierPriorityRow:
        object.__setattr__(
            self,
            "frontier_ref",
            _assert_non_empty_text(self.frontier_ref, field_name="frontier_ref"),
        )
        object.__setattr__(
            self, "node_id", _assert_non_empty_text(self.node_id, field_name="node_id")
        )
        object.__setattr__(
            self,
            "priority_reason",
            _assert_non_empty_text(self.priority_reason, field_name="priority_reason"),
        )
        return self


class FrontierBatchabilityRow(_HobBase):
    frontier_ref: str
    batchability: FrontierBatchability
    batchability_reason: str

    @model_validator(mode="after")
    def _validate_row(self) -> FrontierBatchabilityRow:
        object.__setattr__(
            self,
            "frontier_ref",
            _assert_non_empty_text(self.frontier_ref, field_name="frontier_ref"),
        )
        object.__setattr__(
            self,
            "batchability_reason",
            _assert_non_empty_text(self.batchability_reason, field_name="batchability_reason"),
        )
        return self


class RepoObligationNextFrontierReport(_HobBase):
    schema: Literal[REPO_OBLIGATION_NEXT_FRONTIER_REPORT_SCHEMA]
    obligation_closure_report_hash: str
    frontier_rows: list[FrontierRow]
    frontier_priority_rows: list[FrontierPriorityRow]
    frontier_batchability_rows: list[FrontierBatchabilityRow]
    frontier_plan_authority_posture: Literal["planning_only_not_implementation_authority"]
    report_hash: str | None = None

    @model_validator(mode="after")
    def _validate_report(self) -> RepoObligationNextFrontierReport:
        _assert_unique_rows(
            self.frontier_rows,
            attr_name="frontier_ref",
            field_name="frontier_rows",
        )
        _assert_unique_rows(
            self.frontier_priority_rows,
            attr_name="frontier_ref",
            field_name="frontier_priority_rows",
        )
        _assert_unique_rows(
            self.frontier_batchability_rows,
            attr_name="frontier_ref",
            field_name="frontier_batchability_rows",
        )
        frontier_refs = {row.frontier_ref for row in self.frontier_rows}
        if {row.frontier_ref for row in self.frontier_priority_rows} != frontier_refs:
            raise ValueError("frontier_priority_rows must match frontier_rows")
        if {row.frontier_ref for row in self.frontier_batchability_rows} != frontier_refs:
            raise ValueError("frontier_batchability_rows must match frontier_rows")
        object.__setattr__(
            self,
            "frontier_rows",
            sorted(self.frontier_rows, key=lambda row: row.frontier_ref),
        )
        object.__setattr__(
            self,
            "frontier_priority_rows",
            sorted(self.frontier_priority_rows, key=lambda row: row.frontier_ref),
        )
        object.__setattr__(
            self,
            "frontier_batchability_rows",
            sorted(self.frontier_batchability_rows, key=lambda row: row.frontier_ref),
        )
        if self.report_hash is not None:
            expected = canonical_hash(self, drop_keys={"report_hash"})
            if self.report_hash != expected:
                raise ValueError("report_hash must match canonical frontier report payload")
        return self


class ProbeMatrixRow(_HobBase):
    node_id: str
    probe_kind: ProbeKind
    expected_surface_refs: list[str]
    probe_authority_posture: ProbeAuthorityPosture

    @model_validator(mode="after")
    def _validate_row(self) -> ProbeMatrixRow:
        object.__setattr__(
            self, "node_id", _assert_non_empty_text(self.node_id, field_name="node_id")
        )
        object.__setattr__(
            self,
            "expected_surface_refs",
            _assert_sorted_unique(
                self.expected_surface_refs,
                field_name="expected_surface_refs",
            ),
        )
        return self


class RepoObligationProbeMatrixPlan(_HobBase):
    schema: Literal[REPO_OBLIGATION_PROBE_MATRIX_PLAN_SCHEMA]
    obligation_closure_report_hash: str
    probe_matrix_rows: list[ProbeMatrixRow]
    terminal_node_refs: list[str] = Field(default_factory=list)
    boundary_node_refs: list[str] = Field(default_factory=list)
    held_out_node_refs: list[str] = Field(default_factory=list)
    probe_plan_non_execution_posture: ProbePlanNonExecutionPosture
    probe_authority_posture: ProbeAuthorityPosture
    plan_hash: str | None = None

    @model_validator(mode="after")
    def _validate_plan(self) -> RepoObligationProbeMatrixPlan:
        _assert_unique_rows(
            self.probe_matrix_rows,
            attr_name="node_id",
            field_name="probe_matrix_rows",
        )
        object.__setattr__(
            self,
            "terminal_node_refs",
            _assert_sorted_unique(self.terminal_node_refs, field_name="terminal_node_refs"),
        )
        object.__setattr__(
            self,
            "boundary_node_refs",
            _assert_sorted_unique(self.boundary_node_refs, field_name="boundary_node_refs"),
        )
        object.__setattr__(
            self,
            "held_out_node_refs",
            _assert_sorted_unique(self.held_out_node_refs, field_name="held_out_node_refs"),
        )
        object.__setattr__(
            self,
            "probe_matrix_rows",
            sorted(self.probe_matrix_rows, key=lambda row: row.node_id),
        )
        for row in self.probe_matrix_rows:
            if row.probe_authority_posture != "plan_only_not_observed":
                raise ValueError("probe matrix rows must remain plan_only_not_observed")
        if self.plan_hash is not None:
            expected = canonical_hash(self, drop_keys={"plan_hash"})
            if self.plan_hash != expected:
                raise ValueError("plan_hash must match canonical probe matrix payload")
        return self


class ImplementationOwnerRow(_HobBase):
    owner_ref: str
    node_refs: list[str]

    @model_validator(mode="after")
    def _validate_row(self) -> ImplementationOwnerRow:
        object.__setattr__(
            self, "owner_ref", _assert_non_empty_text(self.owner_ref, field_name="owner_ref")
        )
        object.__setattr__(
            self,
            "node_refs",
            _assert_sorted_unique(self.node_refs, field_name="node_refs"),
        )
        return self


class RepoObligationImplementationBatchContract(_HobBase):
    schema: Literal[REPO_OBLIGATION_IMPLEMENTATION_BATCH_CONTRACT_SCHEMA]
    obligation_probe_matrix_plan_hash: str
    target_subtree_refs: list[str]
    included_node_refs: list[str]
    excluded_node_refs: list[str] = Field(default_factory=list)
    max_macro_count: int = Field(ge=1)
    implementation_owner_rows: list[ImplementationOwnerRow]
    regression_node_refs: list[str] = Field(default_factory=list)
    held_out_node_refs: list[str] = Field(default_factory=list)
    submit_allowed_posture: SubmitAllowedPosture
    worker_dispatch_authority_posture: WorkerDispatchAuthorityPosture
    contract_hash: str | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> RepoObligationImplementationBatchContract:
        object.__setattr__(
            self,
            "target_subtree_refs",
            _assert_sorted_unique(self.target_subtree_refs, field_name="target_subtree_refs"),
        )
        object.__setattr__(
            self,
            "included_node_refs",
            _assert_sorted_unique(self.included_node_refs, field_name="included_node_refs"),
        )
        object.__setattr__(
            self,
            "excluded_node_refs",
            _assert_sorted_unique(self.excluded_node_refs, field_name="excluded_node_refs"),
        )
        object.__setattr__(
            self,
            "regression_node_refs",
            _assert_sorted_unique(self.regression_node_refs, field_name="regression_node_refs"),
        )
        object.__setattr__(
            self,
            "held_out_node_refs",
            _assert_sorted_unique(self.held_out_node_refs, field_name="held_out_node_refs"),
        )
        _assert_unique_rows(
            self.implementation_owner_rows,
            attr_name="owner_ref",
            field_name="implementation_owner_rows",
        )
        object.__setattr__(
            self,
            "implementation_owner_rows",
            sorted(self.implementation_owner_rows, key=lambda row: row.owner_ref),
        )
        if not set(self.included_node_refs).issubset(set(self.target_subtree_refs)):
            raise ValueError("included_node_refs must stay inside target_subtree_refs")
        if len(self.included_node_refs) > self.max_macro_count:
            raise ValueError("included_node_refs cannot exceed max_macro_count")
        owned_refs = {
            node_ref
            for owner_row in self.implementation_owner_rows
            for node_ref in owner_row.node_refs
        }
        missing_owner = sorted(set(self.included_node_refs) - owned_refs)
        if missing_owner:
            raise ValueError(f"included nodes require implementation owners: {missing_owner}")
        if self.contract_hash is not None:
            expected = canonical_hash(self, drop_keys={"contract_hash"})
            if self.contract_hash != expected:
                raise ValueError("contract_hash must match canonical batch contract payload")
        return self


class RepoObligationOperationalizationReport(_HobBase):
    schema: Literal[REPO_OBLIGATION_OPERATIONALIZATION_REPORT_SCHEMA]
    closure_report_hash: str
    probe_matrix_plan_hash: str
    implementation_batch_contract_hash: str
    audit_node_refs: list[str]
    worker_task_ref: str
    ontology_nodes_preserved: bool
    macro_subbranches_expanded: bool
    probes_generated_before_patch: bool
    implementation_owners_bound: bool
    deferrals_explicit: bool
    closure_metric_defined: bool
    operationalization_status: OperationalizationStatus
    blocker_refs: list[str] = Field(default_factory=list)
    operationalization_non_authority_posture: OperationalizationNonAuthorityPosture
    report_hash: str | None = None

    @model_validator(mode="after")
    def _validate_report(self) -> RepoObligationOperationalizationReport:
        object.__setattr__(
            self,
            "audit_node_refs",
            _assert_sorted_unique(self.audit_node_refs, field_name="audit_node_refs"),
        )
        object.__setattr__(
            self,
            "worker_task_ref",
            _assert_non_empty_text(self.worker_task_ref, field_name="worker_task_ref"),
        )
        object.__setattr__(
            self,
            "blocker_refs",
            _assert_sorted_unique(self.blocker_refs, field_name="blocker_refs"),
        )
        if self.operationalization_status == "blocked" and not self.blocker_refs:
            raise ValueError("blocked operationalization requires blocker_refs")
        if self.operationalization_status == "ready_for_implementation_planning":
            readiness_flags = [
                self.ontology_nodes_preserved,
                self.macro_subbranches_expanded,
                self.probes_generated_before_patch,
                self.implementation_owners_bound,
                self.deferrals_explicit,
                self.closure_metric_defined,
            ]
            if not all(readiness_flags):
                raise ValueError("ready operationalization requires all readiness flags")
        if self.report_hash is not None:
            expected = canonical_hash(self, drop_keys={"report_hash"})
            if self.report_hash != expected:
                raise ValueError("report_hash must match canonical operationalization payload")
        return self


def compute_obligation_closure(
    *,
    catalog: RepoHierarchicalObligationCatalog,
    ledger: RepoInheritedObligationLedger,
    validation_report: RepoObligationTraversalValidationReport,
) -> RepoObligationClosureReport:
    _validate_catalog_hashes_match(catalog, ledger, validation_report)
    rows_by_node = {row.node_id: row for row in ledger.obligation_rows}
    children_by_parent = _children_by_parent(catalog)
    child_closure_by_node: dict[str, SubtreeClosureRow] = {}

    def close_node(node: CatalogNodeRow) -> SubtreeClosureRow:
        if node.node_id in child_closure_by_node:
            return child_closure_by_node[node.node_id]
        child_ids = [
            child.node_id
            for child in children_by_parent.get(node.node_id, [])
            if child.default_inheritance != "not_inherited"
        ]
        child_rows = [close_node(_node_by_id(catalog)[child_id]) for child_id in child_ids]
        if _a_validation_blocks_closure(validation_report):
            blockers = sorted(
                {
                    diag.node_id or node.node_id
                    for diag in validation_report.diagnostic_rows
                    if _diagnostic_blocks_closure(diag.diagnostic_code)
                }
            )
            result = SubtreeClosureRow(
                node_id=node.node_id,
                child_node_ids=child_ids,
                closure_basis="blocked_by_A_validation",
                closure_status="blocked",
                blocker_node_refs=blockers or [node.node_id],
            )
        elif child_rows:
            result = _close_parent_from_children(node.node_id, child_ids, child_rows)
        else:
            result = _close_leaf_from_obligation(node.node_id, rows_by_node.get(node.node_id))
        child_closure_by_node[node.node_id] = result
        return result

    for node_id in _closure_seed_node_ids(catalog, ledger, validation_report):
        node = _node_by_id(catalog).get(node_id)
        if node is not None:
            close_node(node)

    closure_rows = sorted(child_closure_by_node.values(), key=lambda row: row.node_id)
    weakest_rows = _weakest_child_rows(closure_rows)
    basis_rows = [
        ClosureBasisRow(node_id=row.node_id, closure_basis=row.closure_basis)
        for row in closure_rows
    ]
    overall = _weakest_status(row.closure_status for row in closure_rows) or "not_ready"
    blockers = sorted({ref for row in closure_rows for ref in row.blocker_node_refs})
    return RepoObligationClosureReport(
        schema=REPO_OBLIGATION_CLOSURE_REPORT_SCHEMA,
        catalog_id=catalog.catalog_id,
        catalog_version=catalog.catalog_version,
        catalog_hash=_catalog_hash(catalog),
        inherited_obligation_ledger_hash=canonical_hash(ledger, drop_keys={"ledger_hash"}),
        traversal_validation_report_hash=canonical_hash(
            validation_report,
            drop_keys={"report_hash"},
        ),
        a_validation_status=validation_report.validation_status,
        subtree_closure_rows=closure_rows,
        weakest_child_readiness_rows=weakest_rows,
        closure_basis_rows=basis_rows,
        closure_status=overall,
        closure_blocker_refs=blockers,
        closure_authority_posture="local_broker_accounting_only_not_product_truth",
    )


def plan_next_frontier(
    *,
    validation_report: RepoObligationTraversalValidationReport,
    closure_report: RepoObligationClosureReport,
) -> RepoObligationNextFrontierReport:
    priority_rows: list[FrontierPriorityRow] = []
    batchability_rows: list[FrontierBatchabilityRow] = []
    for row in validation_report.frontier_rows:
        priority, batchability = _priority_for_frontier(row)
        priority_rows.append(
            FrontierPriorityRow(
                frontier_ref=row.frontier_ref,
                node_id=row.node_id,
                priority=priority,
                batchability=batchability,
                priority_reason=f"{row.frontier_reason}:{row.required_next_action}",
            )
        )
        batchability_rows.append(
            FrontierBatchabilityRow(
                frontier_ref=row.frontier_ref,
                batchability=batchability,
                batchability_reason=f"frontier action {row.required_next_action}",
            )
        )
    return RepoObligationNextFrontierReport(
        schema=REPO_OBLIGATION_NEXT_FRONTIER_REPORT_SCHEMA,
        obligation_closure_report_hash=canonical_hash(closure_report, drop_keys={"report_hash"}),
        frontier_rows=list(validation_report.frontier_rows),
        frontier_priority_rows=priority_rows,
        frontier_batchability_rows=batchability_rows,
        frontier_plan_authority_posture="planning_only_not_implementation_authority",
    )


def plan_probe_matrix(
    *,
    catalog: RepoHierarchicalObligationCatalog,
    closure_report: RepoObligationClosureReport,
    held_out_node_refs: list[str] | None = None,
) -> RepoObligationProbeMatrixPlan:
    held_out = set(held_out_node_refs or [])
    closure_node_ids = {row.node_id for row in closure_report.subtree_closure_rows}
    unknown_held_out = sorted(held_out - closure_node_ids)
    if unknown_held_out:
        raise ValueError(f"held_out_node_refs must belong to closure nodes: {unknown_held_out}")
    terminal_refs = sorted(
        node.node_id
        for node in catalog.catalog_nodes
        if node.node_kind == "terminal_leaf" and node.node_id in closure_node_ids
    )
    boundary_refs = sorted(
        node.node_id
        for node in catalog.catalog_nodes
        if node.node_kind != "terminal_leaf" and node.node_id in closure_node_ids
    )
    rows: list[ProbeMatrixRow] = []
    for node_id in terminal_refs:
        probe_kind: ProbeKind = (
            "held_out_regression_probe" if node_id in held_out else "terminal_behavior_probe"
        )
        rows.append(
            ProbeMatrixRow(
                node_id=node_id,
                probe_kind=probe_kind,
                expected_surface_refs=[f"surface:{node_id}"],
                probe_authority_posture="plan_only_not_observed",
            )
        )
    for node_id in boundary_refs:
        probe_kind: ProbeKind = (
            "held_out_regression_probe" if node_id in held_out else "boundary_probe"
        )
        rows.append(
            ProbeMatrixRow(
                node_id=node_id,
                probe_kind=probe_kind,
                expected_surface_refs=[f"surface:{node_id}"],
                probe_authority_posture="plan_only_not_observed",
            )
        )
    return RepoObligationProbeMatrixPlan(
        schema=REPO_OBLIGATION_PROBE_MATRIX_PLAN_SCHEMA,
        obligation_closure_report_hash=canonical_hash(closure_report, drop_keys={"report_hash"}),
        probe_matrix_rows=rows,
        terminal_node_refs=terminal_refs,
        boundary_node_refs=boundary_refs,
        held_out_node_refs=sorted(held_out),
        probe_plan_non_execution_posture="plan_only_no_probe_execution",
        probe_authority_posture="plan_only_not_observed",
    )


def build_implementation_batch_contract(
    *,
    probe_matrix_plan: RepoObligationProbeMatrixPlan,
    included_node_refs: list[str],
    owner_ref: str,
    max_macro_count: int,
) -> RepoObligationImplementationBatchContract:
    target_refs = sorted(
        set(probe_matrix_plan.terminal_node_refs)
        | set(probe_matrix_plan.boundary_node_refs)
        | set(probe_matrix_plan.held_out_node_refs)
    )
    included = sorted(included_node_refs)
    excluded = sorted(set(target_refs) - set(included))
    return RepoObligationImplementationBatchContract(
        schema=REPO_OBLIGATION_IMPLEMENTATION_BATCH_CONTRACT_SCHEMA,
        obligation_probe_matrix_plan_hash=canonical_hash(
            probe_matrix_plan,
            drop_keys={"plan_hash"},
        ),
        target_subtree_refs=target_refs,
        included_node_refs=included,
        excluded_node_refs=excluded,
        max_macro_count=max_macro_count,
        implementation_owner_rows=[
            ImplementationOwnerRow(owner_ref=owner_ref, node_refs=included),
        ],
        regression_node_refs=probe_matrix_plan.held_out_node_refs,
        held_out_node_refs=probe_matrix_plan.held_out_node_refs,
        submit_allowed_posture="submit_not_allowed_planning_only",
        worker_dispatch_authority_posture="no_worker_dispatch_authority",
    )


def build_operationalization_report(
    *,
    closure_report: RepoObligationClosureReport,
    probe_matrix_plan: RepoObligationProbeMatrixPlan,
    batch_contract: RepoObligationImplementationBatchContract,
    worker_task_ref: str,
) -> RepoObligationOperationalizationReport:
    blocked = closure_report.closure_status == "blocked"
    return RepoObligationOperationalizationReport(
        schema=REPO_OBLIGATION_OPERATIONALIZATION_REPORT_SCHEMA,
        closure_report_hash=canonical_hash(closure_report, drop_keys={"report_hash"}),
        probe_matrix_plan_hash=canonical_hash(probe_matrix_plan, drop_keys={"plan_hash"}),
        implementation_batch_contract_hash=canonical_hash(
            batch_contract,
            drop_keys={"contract_hash"},
        ),
        audit_node_refs=batch_contract.included_node_refs,
        worker_task_ref=worker_task_ref,
        ontology_nodes_preserved=True,
        macro_subbranches_expanded=bool(probe_matrix_plan.boundary_node_refs),
        probes_generated_before_patch=bool(probe_matrix_plan.probe_matrix_rows),
        implementation_owners_bound=bool(batch_contract.implementation_owner_rows),
        deferrals_explicit=not any(
            row.closure_status == "deferred_with_risk"
            for row in closure_report.subtree_closure_rows
        )
        or bool(closure_report.closure_blocker_refs),
        closure_metric_defined=True,
        operationalization_status="blocked" if blocked else "ready_for_implementation_planning",
        blocker_refs=closure_report.closure_blocker_refs,
        operationalization_non_authority_posture="planning_only_not_product_truth",
    )


def _validate_catalog_hashes_match(
    catalog: RepoHierarchicalObligationCatalog,
    ledger: RepoInheritedObligationLedger,
    validation_report: RepoObligationTraversalValidationReport,
) -> None:
    expected_hash = _catalog_hash(catalog)
    if ledger.catalog_id != catalog.catalog_id or ledger.catalog_version != catalog.catalog_version:
        raise ValueError("ledger catalog_id/catalog_version must match catalog")
    if validation_report.catalog_id != catalog.catalog_id or (
        validation_report.catalog_version != catalog.catalog_version
    ):
        raise ValueError("validation report catalog_id/catalog_version must match catalog")
    if ledger.catalog_hash != expected_hash or validation_report.catalog_hash != expected_hash:
        raise ValueError("A records must share catalog_hash")


def _catalog_hash(catalog: RepoHierarchicalObligationCatalog) -> str:
    return catalog.catalog_hash or canonical_hash(catalog, drop_keys={"catalog_hash"})


def _children_by_parent(
    catalog: RepoHierarchicalObligationCatalog,
) -> dict[str, list[CatalogNodeRow]]:
    children: dict[str, list[CatalogNodeRow]] = defaultdict(list)
    for node in catalog.catalog_nodes:
        if node.parent_node_id is not None:
            children[node.parent_node_id].append(node)
    return {parent: sorted(rows, key=lambda row: row.node_id) for parent, rows in children.items()}


def _closure_seed_node_ids(
    catalog: RepoHierarchicalObligationCatalog,
    ledger: RepoInheritedObligationLedger,
    validation_report: RepoObligationTraversalValidationReport,
) -> list[str]:
    catalog_nodes = _node_by_id(catalog)
    seed_ids = {row.node_id for row in ledger.obligation_rows}
    seed_ids.update(
        row.node_id
        for row in validation_report.diagnostic_rows
        if row.node_id is not None and _diagnostic_blocks_closure(row.diagnostic_code)
    )
    expanded = set(seed_ids)
    for node_id in seed_ids:
        node = catalog_nodes.get(node_id)
        while node is not None and node.parent_node_id is not None:
            expanded.add(node.parent_node_id)
            node = catalog_nodes.get(node.parent_node_id)
    return sorted(expanded)


def _close_leaf_from_obligation(
    node_id: str,
    row: InheritedObligationRow | None,
) -> SubtreeClosureRow:
    if row is None:
        return SubtreeClosureRow(
            node_id=node_id,
            closure_basis="blocked_by_child",
            closure_status="blocked",
            blocker_node_refs=[node_id],
        )
    if row.obligation_status in _TERMINAL_GOLD_STATUSES:
        return SubtreeClosureRow(
            node_id=node_id,
            closure_basis="all_children_gold_ready",
            closure_status="gold_ready",
        )
    if row.obligation_status == "covered_by_probe_matrix":
        return SubtreeClosureRow(
            node_id=node_id,
            closure_basis="all_children_scoped_ready",
            closure_status="scoped_ready",
        )
    if row.obligation_status == "representative_examples_only":
        return SubtreeClosureRow(
            node_id=node_id,
            closure_basis="representative_only",
            closure_status="representative_only",
            blocker_node_refs=[node_id],
            representative_only=True,
        )
    if row.obligation_status in {
        "scoped_deferred_with_expected_risk",
        "gold_deferred_with_expected_risk",
    }:
        return SubtreeClosureRow(
            node_id=node_id,
            closure_basis="deferred_with_risk",
            closure_status="deferred_with_risk",
            blocker_node_refs=[node_id],
        )
    return SubtreeClosureRow(
        node_id=node_id,
        closure_basis="blocked_by_child",
        closure_status="blocked",
        blocker_node_refs=[node_id],
    )


def _close_parent_from_children(
    node_id: str,
    child_ids: list[str],
    child_rows: list[SubtreeClosureRow],
) -> SubtreeClosureRow:
    blockers = sorted({ref for row in child_rows for ref in row.blocker_node_refs})
    statuses = {row.closure_status for row in child_rows}
    if "blocked" in statuses or "not_ready" in statuses:
        return SubtreeClosureRow(
            node_id=node_id,
            child_node_ids=child_ids,
            closure_basis="blocked_by_child",
            closure_status="blocked",
            blocker_node_refs=blockers or [
                row.node_id
                for row in child_rows
                if row.closure_status in {"blocked", "not_ready"}
            ],
        )
    if "representative_only" in statuses:
        return SubtreeClosureRow(
            node_id=node_id,
            child_node_ids=child_ids,
            closure_basis="representative_only",
            closure_status="representative_only",
            blocker_node_refs=blockers,
            representative_only=True,
        )
    if "deferred_with_risk" in statuses:
        return SubtreeClosureRow(
            node_id=node_id,
            child_node_ids=child_ids,
            closure_basis="deferred_with_risk",
            closure_status="deferred_with_risk",
            blocker_node_refs=blockers,
        )
    if "scoped_ready" in statuses:
        return SubtreeClosureRow(
            node_id=node_id,
            child_node_ids=child_ids,
            closure_basis="all_children_scoped_ready",
            closure_status="scoped_ready",
        )
    return SubtreeClosureRow(
        node_id=node_id,
        child_node_ids=child_ids,
        closure_basis="all_children_gold_ready",
        closure_status="gold_ready",
    )


def _weakest_child_rows(closure_rows: list[SubtreeClosureRow]) -> list[WeakestChildReadinessRow]:
    closure_by_node = {row.node_id: row for row in closure_rows}
    rows: list[WeakestChildReadinessRow] = []
    for row in closure_rows:
        if not row.child_node_ids:
            rows.append(
                WeakestChildReadinessRow(
                    node_id=row.node_id,
                    weakest_child_readiness=row.closure_status,
                )
            )
            continue
        child_rows = [closure_by_node[child_id] for child_id in row.child_node_ids]
        weakest = sorted(
            child_rows,
            key=lambda child: (_READINESS_RANK[child.closure_status], child.node_id),
        )[0]
        rows.append(
            WeakestChildReadinessRow(
                node_id=row.node_id,
                weakest_child_node_id=weakest.node_id,
                weakest_child_readiness=weakest.closure_status,
            )
        )
    return rows


def _weakest_status(statuses: object) -> ClosureStatus | None:
    status_list = list(statuses)
    if not status_list:
        return None
    return sorted(status_list, key=lambda status: _READINESS_RANK[status])[0]


def _priority_for_frontier(row: FrontierRow) -> tuple[FrontierPriority, FrontierBatchability]:
    if row.required_next_action in {
        "methodological_equivalence_check",
        "reference_observation",
    }:
        return "critical", "requires_sequential_review"
    if row.required_next_action == "semantic_adjudication":
        return "high", "requires_sequential_review"
    if row.required_next_action == "proof_repair":
        return "high", "batchable"
    return "normal", "batchable"


def _a_validation_blocks_closure(report: RepoObligationTraversalValidationReport) -> bool:
    return any(_diagnostic_blocks_closure(row.diagnostic_code) for row in report.diagnostic_rows)


def _diagnostic_blocks_closure(code: str) -> bool:
    return code in {
        "MISSING_INHERITED_OBLIGATION",
        "UNKNOWN_OBLIGATION_NODE",
        "INHERITED_OBLIGATION_LINEAGE_MISMATCH",
        "UNKNOWN_PROOF_REF",
        "PROOF_REQUIRED_FOR_STATUS",
        "PROOF_KIND_MISMATCH",
        "DEFERRAL_PROOF_STATUS_MISMATCH",
        "BLOCKING_PROOF_STATUS_MISMATCH",
        "NOT_INHERITED_ESCAPE_HATCH_BLOCKED",
        "UNKNOWN_READINESS_CLAIM_NODE",
        "FALSE_PARENT_GOLD_READY_CLAIM",
        "FALSE_PARENT_SCOPED_READY_CLAIM",
        "OPTIONAL_OBSERVED_CANNOT_CLOSE_PARENT",
    }
