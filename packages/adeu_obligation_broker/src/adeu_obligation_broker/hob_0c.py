from __future__ import annotations

from typing import Literal

from pydantic import Field, model_validator

from .hob_0a import (
    RepoHierarchicalObligationCatalog,
    _assert_non_empty_text,
    _assert_sorted_unique,
    _assert_unique_rows,
    _HobBase,
    _node_by_id,
    canonical_hash,
)
from .hob_0b import RepoObligationClosureReport

REPO_OBLIGATION_DELTA_ATTRIBUTION_LEDGER_SCHEMA = (
    "repo_obligation_delta_attribution_ledger@1"
)
REPO_OBLIGATION_STALE_LEDGER_INVALIDATION_REPORT_SCHEMA = (
    "repo_obligation_stale_ledger_invalidation_report@1"
)
REPO_OBLIGATION_BROKER_INTEGRATION_HANDOFF_SCHEMA = (
    "repo_obligation_broker_integration_handoff@1"
)
REPO_OBLIGATION_BROKER_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "repo_obligation_broker_family_closeout_alignment@1"
)

EvidenceBoundaryPosture = Literal[
    "post_eval_pressure_only",
    "local_locked_probe_delta",
    "official_like_pressure",
    "source_postmortem_pressure",
    "clean_first_pass_disallowed",
]
AttributionKind = Literal[
    "failure_reduction_pressure",
    "regression_pressure",
    "failure_migration_pressure",
    "closure_evidence_pressure",
]
AttributionConfidence = Literal["low", "medium", "high"]
DeltaInterpretation = Literal[
    "representative_transfer_success",
    "macro_closure_success",
    "resource_or_substrate_masking",
    "implementation_transfer_error",
    "theory_gap_persists",
]
ClosureEffectPosture = Literal[
    "pressure_only_no_closure",
    "representative_transfer_only",
    "macro_closure_supported_by_released_closure",
    "regression_pressure_only",
]
DeltaAuthorityPosture = Literal["pressure_attribution_only_not_product_truth"]
StaleLedgerReusePosture = Literal[
    "current_catalog_hash_bound",
    "stale_catalog_hash_invalidated",
]
HandoffPressureKind = Literal[
    "future_programbench_broker_integration_review",
    "future_semantic_compiler_integration_review",
    "future_probe_execution_governance_review",
    "future_worker_taskpack_generation_review",
    "future_implementation_authority_review",
    "future_family_only",
]
HandoffNonSelectionPosture = Literal["pressure_only_no_future_family_selection"]
ProgramBenchIntegrationAuthorityPosture = Literal["no_programbench_integration_authority"]
SemanticCompilerIntegrationAuthorityPosture = Literal[
    "no_semantic_compiler_integration_authority"
]
ProbeExecutionAuthorityPosture = Literal["no_probe_execution_authority"]
ImplementationAuthorityPosture = Literal["no_implementation_authority"]
FutureFamilySelectionPosture = Literal["no_future_family_selection"]
FamilyScopePosture = Literal[
    "hob_0_family_closed",
    "hob_0_family_open_with_deferred_refs",
    "hob_0_family_blocked",
]

_HOB_0_SLICES = {"HOB-0-A", "HOB-0-B", "HOB-0-C"}


class DeltaAttributionRow(_HobBase):
    node_id: str
    macro_ref: str
    source_delta_ref: str
    attribution_kind: AttributionKind
    attribution_confidence: AttributionConfidence
    matrix_rows_green: list[str] = Field(default_factory=list)
    rows_moved_to_other_failure: list[str] = Field(default_factory=list)
    regressions: list[str] = Field(default_factory=list)
    interpretation: DeltaInterpretation
    closure_effect_posture: ClosureEffectPosture
    evidence_boundary_posture: EvidenceBoundaryPosture

    @model_validator(mode="after")
    def _validate_row(self) -> DeltaAttributionRow:
        object.__setattr__(
            self, "node_id", _assert_non_empty_text(self.node_id, field_name="node_id")
        )
        object.__setattr__(
            self, "macro_ref", _assert_non_empty_text(self.macro_ref, field_name="macro_ref")
        )
        object.__setattr__(
            self,
            "source_delta_ref",
            _assert_non_empty_text(self.source_delta_ref, field_name="source_delta_ref"),
        )
        object.__setattr__(
            self,
            "matrix_rows_green",
            _assert_sorted_unique(self.matrix_rows_green, field_name="matrix_rows_green"),
        )
        object.__setattr__(
            self,
            "rows_moved_to_other_failure",
            _assert_sorted_unique(
                self.rows_moved_to_other_failure,
                field_name="rows_moved_to_other_failure",
            ),
        )
        object.__setattr__(
            self,
            "regressions",
            _assert_sorted_unique(self.regressions, field_name="regressions"),
        )
        if self.interpretation == "macro_closure_success" and (
            self.closure_effect_posture != "macro_closure_supported_by_released_closure"
        ):
            raise ValueError("macro_closure_success requires released closure support posture")
        if self.evidence_boundary_posture == "clean_first_pass_disallowed":
            raise ValueError("attribution rows cannot claim clean_first_pass_disallowed evidence")
        return self


class RepoObligationDeltaAttributionLedger(_HobBase):
    schema: Literal[REPO_OBLIGATION_DELTA_ATTRIBUTION_LEDGER_SCHEMA]
    catalog_id: str
    catalog_version: str
    catalog_hash: str
    run_before_ref: str
    run_after_ref: str
    changed_failure_rows: list[str] = Field(default_factory=list)
    delta_attribution_rows: list[DeltaAttributionRow]
    regression_rows: list[str] = Field(default_factory=list)
    rows_moved_to_other_failure_rows: list[str] = Field(default_factory=list)
    closure_evidence_node_refs: list[str] = Field(default_factory=list)
    evidence_boundary_posture: EvidenceBoundaryPosture
    delta_authority_posture: DeltaAuthorityPosture
    ledger_hash: str | None = None

    @model_validator(mode="after")
    def _validate_ledger(self) -> RepoObligationDeltaAttributionLedger:
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
        object.__setattr__(
            self,
            "catalog_hash",
            _assert_non_empty_text(self.catalog_hash, field_name="catalog_hash"),
        )
        object.__setattr__(
            self,
            "run_before_ref",
            _assert_non_empty_text(self.run_before_ref, field_name="run_before_ref"),
        )
        object.__setattr__(
            self,
            "run_after_ref",
            _assert_non_empty_text(self.run_after_ref, field_name="run_after_ref"),
        )
        object.__setattr__(
            self,
            "changed_failure_rows",
            _assert_sorted_unique(self.changed_failure_rows, field_name="changed_failure_rows"),
        )
        object.__setattr__(
            self,
            "regression_rows",
            _assert_sorted_unique(self.regression_rows, field_name="regression_rows"),
        )
        object.__setattr__(
            self,
            "rows_moved_to_other_failure_rows",
            _assert_sorted_unique(
                self.rows_moved_to_other_failure_rows,
                field_name="rows_moved_to_other_failure_rows",
            ),
        )
        object.__setattr__(
            self,
            "closure_evidence_node_refs",
            _assert_sorted_unique(
                self.closure_evidence_node_refs,
                field_name="closure_evidence_node_refs",
            ),
        )
        _assert_unique_rows(
            self.delta_attribution_rows,
            attr_name="source_delta_ref",
            field_name="delta_attribution_rows",
        )
        object.__setattr__(
            self,
            "delta_attribution_rows",
            sorted(self.delta_attribution_rows, key=lambda row: row.source_delta_ref),
        )
        closure_evidence = set(self.closure_evidence_node_refs)
        for row in self.delta_attribution_rows:
            if row.closure_effect_posture == "macro_closure_supported_by_released_closure":
                if row.node_id not in closure_evidence:
                    raise ValueError(
                        "macro closure attribution requires closure_evidence_node_refs"
                    )
                if row.evidence_boundary_posture != "local_locked_probe_delta":
                    raise ValueError(
                        "macro closure attribution requires local locked-probe evidence"
                    )
        if self.ledger_hash is not None:
            expected = canonical_hash(self, drop_keys={"ledger_hash"})
            if self.ledger_hash != expected:
                raise ValueError("ledger_hash must match canonical delta attribution payload")
        return self


class StaleLedgerInvalidationReasonRow(_HobBase):
    invalidated_ref: str
    stale_reason: str
    invalidation_status: Literal["invalidated", "current"]

    @model_validator(mode="after")
    def _validate_row(self) -> StaleLedgerInvalidationReasonRow:
        object.__setattr__(
            self,
            "invalidated_ref",
            _assert_non_empty_text(self.invalidated_ref, field_name="invalidated_ref"),
        )
        object.__setattr__(
            self,
            "stale_reason",
            _assert_non_empty_text(self.stale_reason, field_name="stale_reason"),
        )
        return self


class RepoObligationStaleLedgerInvalidationReport(_HobBase):
    schema: Literal[REPO_OBLIGATION_STALE_LEDGER_INVALIDATION_REPORT_SCHEMA]
    prior_catalog_id: str
    prior_catalog_version: str
    prior_catalog_hash: str
    current_catalog_id: str
    current_catalog_version: str
    current_catalog_hash: str
    invalidated_ledger_refs: list[str] = Field(default_factory=list)
    invalidated_probe_plan_refs: list[str] = Field(default_factory=list)
    invalidation_reason_rows: list[StaleLedgerInvalidationReasonRow]
    stale_ledger_reuse_posture: StaleLedgerReusePosture
    report_hash: str | None = None

    @model_validator(mode="after")
    def _validate_report(self) -> RepoObligationStaleLedgerInvalidationReport:
        for field_name in (
            "prior_catalog_id",
            "prior_catalog_version",
            "prior_catalog_hash",
            "current_catalog_id",
            "current_catalog_version",
            "current_catalog_hash",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "invalidated_ledger_refs",
            _assert_sorted_unique(
                self.invalidated_ledger_refs,
                field_name="invalidated_ledger_refs",
            ),
        )
        object.__setattr__(
            self,
            "invalidated_probe_plan_refs",
            _assert_sorted_unique(
                self.invalidated_probe_plan_refs,
                field_name="invalidated_probe_plan_refs",
            ),
        )
        _assert_unique_rows(
            self.invalidation_reason_rows,
            attr_name="invalidated_ref",
            field_name="invalidation_reason_rows",
        )
        object.__setattr__(
            self,
            "invalidation_reason_rows",
            sorted(self.invalidation_reason_rows, key=lambda row: row.invalidated_ref),
        )
        catalog_changed = self.prior_catalog_hash != self.current_catalog_hash
        invalidated_refs = set(self.invalidated_ledger_refs) | set(
            self.invalidated_probe_plan_refs
        )
        if catalog_changed:
            if self.stale_ledger_reuse_posture != "stale_catalog_hash_invalidated":
                raise ValueError("catalog hash change requires stale_catalog_hash_invalidated")
            if not invalidated_refs or not self.invalidation_reason_rows:
                raise ValueError("catalog hash change requires invalidated refs and reasons")
            reason_refs = {row.invalidated_ref for row in self.invalidation_reason_rows}
            if reason_refs != invalidated_refs:
                raise ValueError("invalidation_reason_rows must match invalidated refs")
        elif self.stale_ledger_reuse_posture != "current_catalog_hash_bound":
            raise ValueError("unchanged catalog hash requires current_catalog_hash_bound")
        elif invalidated_refs or self.invalidation_reason_rows:
            raise ValueError("unchanged catalog hash cannot invalidate current refs")
        if self.report_hash is not None:
            expected = canonical_hash(self, drop_keys={"report_hash"})
            if self.report_hash != expected:
                raise ValueError("report_hash must match canonical stale-ledger payload")
        return self


class HandoffPressureRow(_HobBase):
    pressure_ref: str
    target_node_refs: list[str]
    handoff_pressure_kind: HandoffPressureKind
    pressure_summary: str
    evidence_boundary_posture: EvidenceBoundaryPosture

    @model_validator(mode="after")
    def _validate_row(self) -> HandoffPressureRow:
        object.__setattr__(
            self,
            "pressure_ref",
            _assert_non_empty_text(self.pressure_ref, field_name="pressure_ref"),
        )
        object.__setattr__(
            self,
            "target_node_refs",
            _assert_sorted_unique(self.target_node_refs, field_name="target_node_refs"),
        )
        if not self.target_node_refs:
            raise ValueError("handoff pressure rows require target_node_refs")
        object.__setattr__(
            self,
            "pressure_summary",
            _assert_non_empty_text(self.pressure_summary, field_name="pressure_summary"),
        )
        if self.evidence_boundary_posture == "clean_first_pass_disallowed":
            raise ValueError("handoff cannot launder disallowed clean-first-pass evidence")
        return self


class RepoObligationBrokerIntegrationHandoff(_HobBase):
    schema: Literal[REPO_OBLIGATION_BROKER_INTEGRATION_HANDOFF_SCHEMA]
    catalog_id: str
    catalog_version: str
    catalog_hash: str
    handoff_pressure_rows: list[HandoffPressureRow]
    handoff_pressure_kind: HandoffPressureKind
    handoff_non_selection_posture: HandoffNonSelectionPosture
    programbench_integration_authority_posture: ProgramBenchIntegrationAuthorityPosture
    semantic_compiler_integration_authority_posture: SemanticCompilerIntegrationAuthorityPosture
    probe_execution_authority_posture: ProbeExecutionAuthorityPosture
    implementation_authority_posture: ImplementationAuthorityPosture
    future_family_selection_posture: FutureFamilySelectionPosture
    handoff_hash: str | None = None

    @model_validator(mode="after")
    def _validate_handoff(self) -> RepoObligationBrokerIntegrationHandoff:
        for field_name in ("catalog_id", "catalog_version", "catalog_hash"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        _assert_unique_rows(
            self.handoff_pressure_rows,
            attr_name="pressure_ref",
            field_name="handoff_pressure_rows",
        )
        object.__setattr__(
            self,
            "handoff_pressure_rows",
            sorted(self.handoff_pressure_rows, key=lambda row: row.pressure_ref),
        )
        for row in self.handoff_pressure_rows:
            if row.handoff_pressure_kind != self.handoff_pressure_kind:
                raise ValueError(
                    f"handoff pressure row kind {row.handoff_pressure_kind!r} does not match "
                    f"handoff kind {self.handoff_pressure_kind!r}"
                )
        if self.handoff_hash is not None:
            expected = canonical_hash(self, drop_keys={"handoff_hash"})
            if self.handoff_hash != expected:
                raise ValueError("handoff_hash must match canonical integration handoff")
        return self


class RepoObligationBrokerFamilyCloseoutAlignment(_HobBase):
    schema: Literal[REPO_OBLIGATION_BROKER_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA]
    family_ref: Literal["HOB-0"]
    closed_slices: list[str]
    slice_a_closeout_ref: str
    slice_b_closeout_ref: str
    slice_c_closeout_ref: str
    family_scope_posture: FamilyScopePosture
    residual_deferred_refs: list[str] = Field(default_factory=list)
    blocker_refs: list[str] = Field(default_factory=list)
    integration_authority_posture: Literal["no_integration_authority"]
    implementation_authority_posture: ImplementationAuthorityPosture
    future_family_selection_posture: FutureFamilySelectionPosture
    alignment_hash: str | None = None

    @model_validator(mode="after")
    def _validate_alignment(self) -> RepoObligationBrokerFamilyCloseoutAlignment:
        object.__setattr__(
            self,
            "closed_slices",
            _assert_sorted_unique(self.closed_slices, field_name="closed_slices"),
        )
        unknown_slices = sorted(set(self.closed_slices) - _HOB_0_SLICES)
        if unknown_slices:
            raise ValueError(f"closed_slices contains unknown HOB-0 slices: {unknown_slices}")
        for field_name in (
            "slice_a_closeout_ref",
            "slice_b_closeout_ref",
            "slice_c_closeout_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "residual_deferred_refs",
            _assert_sorted_unique(
                self.residual_deferred_refs,
                field_name="residual_deferred_refs",
            ),
        )
        object.__setattr__(
            self,
            "blocker_refs",
            _assert_sorted_unique(self.blocker_refs, field_name="blocker_refs"),
        )
        if self.family_scope_posture == "hob_0_family_closed":
            if set(self.closed_slices) != _HOB_0_SLICES:
                raise ValueError("closed family requires all HOB-0 slices")
            if self.residual_deferred_refs or self.blocker_refs:
                raise ValueError("closed family cannot hide residual deferred refs or blockers")
        if self.family_scope_posture == "hob_0_family_blocked" and not self.blocker_refs:
            raise ValueError("blocked family closeout requires blocker_refs")
        if self.family_scope_posture == "hob_0_family_open_with_deferred_refs":
            if not self.residual_deferred_refs:
                raise ValueError(
                    "open-with-deferred family closeout requires residual_deferred_refs"
                )
            if self.blocker_refs:
                raise ValueError(
                    "open-with-deferred family closeout cannot have blocker_refs"
                )
        if self.alignment_hash is not None:
            expected = canonical_hash(self, drop_keys={"alignment_hash"})
            if self.alignment_hash != expected:
                raise ValueError("alignment_hash must match canonical family closeout alignment")
        return self


def build_delta_attribution_ledger(
    *,
    catalog: RepoHierarchicalObligationCatalog,
    closure_report: RepoObligationClosureReport,
    run_before_ref: str,
    run_after_ref: str,
    delta_attribution_rows: list[DeltaAttributionRow],
    changed_failure_rows: list[str] | None = None,
    regression_rows: list[str] | None = None,
    rows_moved_to_other_failure_rows: list[str] | None = None,
    evidence_boundary_posture: EvidenceBoundaryPosture = "local_locked_probe_delta",
) -> RepoObligationDeltaAttributionLedger:
    _validate_catalog_identity(catalog, closure_report)
    node_ids = set(_node_by_id(catalog))
    unknown = sorted({row.node_id for row in delta_attribution_rows} - node_ids)
    if unknown:
        raise ValueError(f"delta attribution references unknown node IDs: {unknown}")
    closure_evidence = sorted(
        row.node_id
        for row in closure_report.subtree_closure_rows
        if row.closure_status in {"gold_ready", "scoped_ready"}
    )
    return RepoObligationDeltaAttributionLedger(
        schema=REPO_OBLIGATION_DELTA_ATTRIBUTION_LEDGER_SCHEMA,
        catalog_id=catalog.catalog_id,
        catalog_version=catalog.catalog_version,
        catalog_hash=_catalog_hash(catalog),
        run_before_ref=run_before_ref,
        run_after_ref=run_after_ref,
        changed_failure_rows=changed_failure_rows or [],
        delta_attribution_rows=delta_attribution_rows,
        regression_rows=regression_rows or [],
        rows_moved_to_other_failure_rows=rows_moved_to_other_failure_rows or [],
        closure_evidence_node_refs=closure_evidence,
        evidence_boundary_posture=evidence_boundary_posture,
        delta_authority_posture="pressure_attribution_only_not_product_truth",
    )


def build_stale_ledger_invalidation_report(
    *,
    prior_catalog_id: str,
    prior_catalog_version: str,
    prior_catalog_hash: str,
    current_catalog_id: str,
    current_catalog_version: str,
    current_catalog_hash: str,
    prior_ledger_refs: list[str],
    prior_probe_plan_refs: list[str] | None = None,
) -> RepoObligationStaleLedgerInvalidationReport:
    catalog_changed = prior_catalog_hash != current_catalog_hash
    invalidated_ledger_refs = sorted(prior_ledger_refs) if catalog_changed else []
    invalidated_probe_plan_refs = sorted(prior_probe_plan_refs or []) if catalog_changed else []
    reason_rows = [
        StaleLedgerInvalidationReasonRow(
            invalidated_ref=ref,
            stale_reason="catalog identity changed",
            invalidation_status="invalidated",
        )
        for ref in [*invalidated_ledger_refs, *invalidated_probe_plan_refs]
    ]
    return RepoObligationStaleLedgerInvalidationReport(
        schema=REPO_OBLIGATION_STALE_LEDGER_INVALIDATION_REPORT_SCHEMA,
        prior_catalog_id=prior_catalog_id,
        prior_catalog_version=prior_catalog_version,
        prior_catalog_hash=prior_catalog_hash,
        current_catalog_id=current_catalog_id,
        current_catalog_version=current_catalog_version,
        current_catalog_hash=current_catalog_hash,
        invalidated_ledger_refs=invalidated_ledger_refs,
        invalidated_probe_plan_refs=invalidated_probe_plan_refs,
        invalidation_reason_rows=reason_rows,
        stale_ledger_reuse_posture=(
            "stale_catalog_hash_invalidated"
            if catalog_changed
            else "current_catalog_hash_bound"
        ),
    )


def build_integration_handoff(
    *,
    catalog: RepoHierarchicalObligationCatalog,
    handoff_pressure_kind: HandoffPressureKind,
    handoff_pressure_rows: list[HandoffPressureRow],
) -> RepoObligationBrokerIntegrationHandoff:
    node_ids = set(_node_by_id(catalog))
    unknown = sorted(
        {
            node_id
            for row in handoff_pressure_rows
            for node_id in row.target_node_refs
            if node_id not in node_ids
        }
    )
    if unknown:
        raise ValueError(f"handoff pressure references unknown node IDs: {unknown}")
    return RepoObligationBrokerIntegrationHandoff(
        schema=REPO_OBLIGATION_BROKER_INTEGRATION_HANDOFF_SCHEMA,
        catalog_id=catalog.catalog_id,
        catalog_version=catalog.catalog_version,
        catalog_hash=_catalog_hash(catalog),
        handoff_pressure_rows=handoff_pressure_rows,
        handoff_pressure_kind=handoff_pressure_kind,
        handoff_non_selection_posture="pressure_only_no_future_family_selection",
        programbench_integration_authority_posture="no_programbench_integration_authority",
        semantic_compiler_integration_authority_posture=(
            "no_semantic_compiler_integration_authority"
        ),
        probe_execution_authority_posture="no_probe_execution_authority",
        implementation_authority_posture="no_implementation_authority",
        future_family_selection_posture="no_future_family_selection",
    )


def build_family_closeout_alignment(
    *,
    slice_a_closeout_ref: str,
    slice_b_closeout_ref: str,
    slice_c_closeout_ref: str,
    residual_deferred_refs: list[str] | None = None,
    blocker_refs: list[str] | None = None,
) -> RepoObligationBrokerFamilyCloseoutAlignment:
    deferred = residual_deferred_refs or []
    blockers = blocker_refs or []
    if blockers:
        posture: FamilyScopePosture = "hob_0_family_blocked"
    elif deferred:
        posture = "hob_0_family_open_with_deferred_refs"
    else:
        posture = "hob_0_family_closed"
    return RepoObligationBrokerFamilyCloseoutAlignment(
        schema=REPO_OBLIGATION_BROKER_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        family_ref="HOB-0",
        closed_slices=["HOB-0-A", "HOB-0-B", "HOB-0-C"],
        slice_a_closeout_ref=slice_a_closeout_ref,
        slice_b_closeout_ref=slice_b_closeout_ref,
        slice_c_closeout_ref=slice_c_closeout_ref,
        family_scope_posture=posture,
        residual_deferred_refs=deferred,
        blocker_refs=blockers,
        integration_authority_posture="no_integration_authority",
        implementation_authority_posture="no_implementation_authority",
        future_family_selection_posture="no_future_family_selection",
    )


def _validate_catalog_identity(
    catalog: RepoHierarchicalObligationCatalog,
    closure_report: RepoObligationClosureReport,
) -> None:
    if catalog.catalog_id != closure_report.catalog_id:
        raise ValueError("catalog_id mismatch between catalog and closure report")
    if catalog.catalog_version != closure_report.catalog_version:
        raise ValueError("catalog_version mismatch between catalog and closure report")
    if _catalog_hash(catalog) != closure_report.catalog_hash:
        raise ValueError("catalog_hash mismatch between catalog and closure report")


def _catalog_hash(catalog: RepoHierarchicalObligationCatalog) -> str:
    return catalog.catalog_hash or canonical_hash(catalog, drop_keys={"catalog_hash"})
