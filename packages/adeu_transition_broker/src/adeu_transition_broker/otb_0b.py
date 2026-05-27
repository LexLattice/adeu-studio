from __future__ import annotations

from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .otb_0a import (
    EvidenceBoundaryPosture,
    EvidenceKind,
    LegalFrontierRow,
    PhaseKind,
    PromotionKind,
    ReadinessPosture,
    RepoPhaseBridgeContract,
    RepoPhaseCircuitCatalog,
    RepoPhaseTransitionValidationReport,
    canonical_hash,
    validate_bridge_contract,
)

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

REPO_PHASE_TRANSITION_CLOSURE_REPORT_SCHEMA = "repo_phase_transition_closure_report@1"
REPO_PHASE_GATE_EXECUTION_PLAN_SCHEMA = "repo_phase_gate_execution_plan@1"
REPO_PHASE_WORKER_BATON_CONTRACT_SCHEMA = "repo_phase_worker_baton_contract@1"
REPO_PHASE_EVIDENCE_POSTURE_PLAN_SCHEMA = "repo_phase_evidence_posture_plan@1"
REPO_PHASE_OPERATIONALIZATION_REPORT_SCHEMA = "repo_phase_operationalization_report@1"

TransitionClosureStatus = Literal[
    "closed",
    "blocked",
    "scoped_ready",
    "representative_only",
    "deferred",
    "conflict_isolated",
]
ClosureBasis = Literal[
    "all_required_bridges_valid",
    "blocked_by_A_validation",
    "blocked_by_frontier",
    "scoped_ready_with_known_risk",
    "representative_only",
    "deferred_with_risk",
    "conflict_isolated",
]
GateKind = Literal[
    "phase_transition_gate",
    "equivalence_preflight_gate",
    "evidence_boundary_gate",
    "baton_closeout_gate",
]
GatePlanAuthorityPosture = Literal["plan_only_not_execution_authority"]
BatonAuthorityPosture = Literal["baton_contract_only_not_dispatch_authority"]
EvidencePosturePlanAuthority = Literal["plan_only_not_observed_evidence"]
OperationalizationAuthorityPosture = Literal[
    "operationalization_summary_only_not_execution_authority"
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


def _rank(posture: ReadinessPosture) -> int:
    return _READINESS_RANK[posture]


def _model_with_hash[T: BaseModel](model: T, *, hash_field: str) -> T:
    payload = model.model_dump(mode="json", by_alias=True, exclude_none=True)
    payload[hash_field] = canonical_hash(model, drop_keys={hash_field})
    return type(model).model_validate(payload)


class _OtbBBase(BaseModel):
    model_config = MODEL_CONFIG


class FrontierSummaryRow(_OtbBBase):
    frontier_ref: str
    transition_id: str
    frontier_reason: str
    required_next_action: str
    source_validation_report_ref: str

    @model_validator(mode="after")
    def _validate_row(self) -> FrontierSummaryRow:
        for field_name in (
            "frontier_ref",
            "transition_id",
            "frontier_reason",
            "required_next_action",
            "source_validation_report_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        return self


class ClosureRow(_OtbBBase):
    transition_id: str
    from_phase: str
    to_phase: str
    closure_status: TransitionClosureStatus
    readiness_posture: ReadinessPosture
    closure_basis: ClosureBasis
    blocking_frontier_refs: list[str] = Field(default_factory=list)
    allowed_next_phase_refs: list[str] = Field(default_factory=list)
    known_risk_ref: str | None = None
    maximum_supported_posture: ReadinessPosture | None = None

    @model_validator(mode="after")
    def _validate_row(self) -> ClosureRow:
        for field_name in ("transition_id", "from_phase", "to_phase"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in ("blocking_frontier_refs", "allowed_next_phase_refs"):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if self.known_risk_ref is not None:
            object.__setattr__(
                self,
                "known_risk_ref",
                _assert_non_empty_text(self.known_risk_ref, field_name="known_risk_ref"),
            )
        if self.maximum_supported_posture is not None and (
            _rank(self.readiness_posture) > _rank(self.maximum_supported_posture)
        ):
            raise ValueError("readiness_posture cannot exceed maximum_supported_posture")
        if self.closure_status == "scoped_ready" and self.known_risk_ref is None:
            raise ValueError("scoped_ready closure rows require known_risk_ref")
        if self.closure_status == "representative_only" and _rank(self.readiness_posture) >= _rank(
            "gold_ready"
        ):
            raise ValueError("representative_only closure cannot claim gold or official readiness")
        return self


class RepoPhaseTransitionClosureReport(_OtbBBase):
    schema: Literal[REPO_PHASE_TRANSITION_CLOSURE_REPORT_SCHEMA]
    transition_closure_report_ref: str
    circuit_id: str
    circuit_version: str
    circuit_hash: str
    input_validation_report_refs: list[str]
    input_validation_report_hashes: dict[str, str] = Field(default_factory=dict)
    closure_rows: list[ClosureRow]
    frontier_summary_rows: list[FrontierSummaryRow]
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_report(self) -> RepoPhaseTransitionClosureReport:
        for field_name in (
            "transition_closure_report_ref",
            "circuit_id",
            "circuit_version",
            "circuit_hash",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "input_validation_report_refs",
            _assert_sorted_unique(
                self.input_validation_report_refs,
                field_name="input_validation_report_refs",
            ),
        )
        _assert_unique_rows(
            self.closure_rows,
            attr_name="transition_id",
            field_name="closure_rows",
        )
        _assert_unique_rows(
            self.frontier_summary_rows,
            attr_name="frontier_ref",
            field_name="frontier_summary_rows",
        )
        object.__setattr__(
            self,
            "closure_rows",
            sorted(self.closure_rows, key=lambda row: row.transition_id),
        )
        object.__setattr__(
            self,
            "frontier_summary_rows",
            sorted(self.frontier_summary_rows, key=lambda row: row.frontier_ref),
        )
        for key, value in self.input_validation_report_hashes.items():
            _assert_non_empty_text(key, field_name="input_validation_report_hashes key")
            _assert_non_empty_text(value, field_name="input_validation_report_hashes value")
        unknown_hash_keys = set(self.input_validation_report_hashes) - set(
            self.input_validation_report_refs
        )
        if unknown_hash_keys:
            raise ValueError(
                "input_validation_report_hashes cannot reference unknown validation reports"
            )
        if self.canonical_output_hash is not None:
            expected = canonical_hash(self, drop_keys={"canonical_output_hash"})
            if self.canonical_output_hash != expected:
                raise ValueError("canonical_output_hash must match canonical closure payload")
        return self


class GatePlanRow(_OtbBBase):
    gate_ref: str
    transition_id: str
    gate_kind: GateKind
    required_input_refs: list[str] = Field(default_factory=list)
    expected_output_kinds: list[str] = Field(default_factory=list)
    forbidden_evidence_kinds: list[EvidenceKind] = Field(default_factory=list)
    success_posture: ReadinessPosture
    failure_route: str
    plan_authority_posture: GatePlanAuthorityPosture

    @model_validator(mode="after")
    def _validate_row(self) -> GatePlanRow:
        for field_name in ("gate_ref", "transition_id", "failure_route"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in ("required_input_refs", "expected_output_kinds"):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "forbidden_evidence_kinds",
            sorted(set(self.forbidden_evidence_kinds)),
        )
        return self


class RepoPhaseGateExecutionPlan(_OtbBBase):
    schema: Literal[REPO_PHASE_GATE_EXECUTION_PLAN_SCHEMA]
    gate_execution_plan_ref: str
    transition_closure_report_ref: str
    gate_plan_rows: list[GatePlanRow]
    plan_authority_posture: GatePlanAuthorityPosture
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_plan(self) -> RepoPhaseGateExecutionPlan:
        for field_name in ("gate_execution_plan_ref", "transition_closure_report_ref"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        _assert_unique_rows(self.gate_plan_rows, attr_name="gate_ref", field_name="gate_plan_rows")
        object.__setattr__(
            self,
            "gate_plan_rows",
            sorted(self.gate_plan_rows, key=lambda row: row.gate_ref),
        )
        if any(
            row.plan_authority_posture != "plan_only_not_execution_authority"
            for row in self.gate_plan_rows
        ):
            raise ValueError("gate rows must not imply execution authority")
        if self.canonical_output_hash is not None:
            expected = canonical_hash(self, drop_keys={"canonical_output_hash"})
            if self.canonical_output_hash != expected:
                raise ValueError("canonical_output_hash must match canonical gate plan payload")
        return self


class BatonOutputRow(_OtbBBase):
    output_kind: str
    target_phase: str

    @model_validator(mode="after")
    def _validate_row(self) -> BatonOutputRow:
        for field_name in ("output_kind", "target_phase"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        return self


class RepoPhaseWorkerBatonContract(_OtbBBase):
    schema: Literal[REPO_PHASE_WORKER_BATON_CONTRACT_SCHEMA]
    worker_baton_contract_ref: str
    transition_id: str
    source_phase_refs: list[str]
    target_phase: str
    allowed_inputs: list[str]
    required_outputs: list[BatonOutputRow]
    forbidden_inputs: list[str]
    forbidden_promotions: list[PromotionKind]
    required_closeout_rows: list[str]
    baton_authority_posture: BatonAuthorityPosture
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_contract(self) -> RepoPhaseWorkerBatonContract:
        for field_name in ("worker_baton_contract_ref", "transition_id", "target_phase"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "source_phase_refs",
            "allowed_inputs",
            "forbidden_inputs",
            "required_closeout_rows",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "forbidden_promotions",
            sorted(set(self.forbidden_promotions)),
        )
        overlap = sorted(set(self.allowed_inputs) & set(self.forbidden_inputs))
        if overlap:
            raise ValueError(f"allowed_inputs cannot include forbidden_inputs: {overlap}")
        for output in self.required_outputs:
            if output.target_phase != self.target_phase:
                raise ValueError("required_outputs cannot target a phase outside target_phase")
        if self.canonical_output_hash is not None:
            expected = canonical_hash(self, drop_keys={"canonical_output_hash"})
            if self.canonical_output_hash != expected:
                raise ValueError("canonical_output_hash must match canonical baton payload")
        return self


class RepoPhaseEvidencePosturePlan(_OtbBBase):
    schema: Literal[REPO_PHASE_EVIDENCE_POSTURE_PLAN_SCHEMA]
    evidence_posture_plan_ref: str
    transition_id: str
    current_evidence_posture: EvidenceBoundaryPosture
    target_evidence_posture: EvidenceBoundaryPosture
    required_equivalence_checks: list[str]
    forbidden_evidence_leaks: list[EvidenceKind]
    official_readiness_requirements: list[str]
    plan_authority_posture: EvidencePosturePlanAuthority
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_plan(self) -> RepoPhaseEvidencePosturePlan:
        for field_name in ("evidence_posture_plan_ref", "transition_id"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in ("required_equivalence_checks", "official_readiness_requirements"):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if not self.required_equivalence_checks:
            raise ValueError("evidence posture plans require equivalence checks")
        object.__setattr__(
            self,
            "forbidden_evidence_leaks",
            sorted(set(self.forbidden_evidence_leaks)),
        )
        if self.target_evidence_posture == "official_like_pressure":
            required_for_official = {
                "packaged_artifact_equivalence",
                "target_substrate_equivalence",
            }
            missing = sorted(required_for_official - set(self.required_equivalence_checks))
            if missing:
                raise ValueError(
                    "official-like posture requires packaged and target-substrate equivalence"
                )
        if self.canonical_output_hash is not None:
            expected = canonical_hash(self, drop_keys={"canonical_output_hash"})
            if self.canonical_output_hash != expected:
                raise ValueError("canonical_output_hash must match canonical evidence plan payload")
        return self


class RepoPhaseOperationalizationReport(_OtbBBase):
    schema: Literal[REPO_PHASE_OPERATIONALIZATION_REPORT_SCHEMA]
    operationalization_report_ref: str
    transition_closure_report_ref: str
    recommended_next_frontier: list[str]
    blocked_frontier: list[str]
    deferred_frontier: list[str]
    handoff_constraints: list[str]
    operationalization_authority_posture: OperationalizationAuthorityPosture
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_report(self) -> RepoPhaseOperationalizationReport:
        for field_name in ("operationalization_report_ref", "transition_closure_report_ref"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "recommended_next_frontier",
            "blocked_frontier",
            "deferred_frontier",
            "handoff_constraints",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if self.canonical_output_hash is not None:
            expected = canonical_hash(self, drop_keys={"canonical_output_hash"})
            if self.canonical_output_hash != expected:
                raise ValueError(
                    "canonical_output_hash must match canonical operationalization payload"
                )
        return self


def compute_transition_closure(
    *,
    catalog: RepoPhaseCircuitCatalog,
    bridge_contracts: list[RepoPhaseBridgeContract | dict[str, Any]],
    validation_reports: list[RepoPhaseTransitionValidationReport | dict[str, Any]],
    known_risk_refs: dict[str, str] | None = None,
    input_validation_report_hashes: dict[str, str] | None = None,
    transition_closure_report_ref: str = "otb-0b-closure:default",
) -> RepoPhaseTransitionClosureReport:
    known_risk_refs = known_risk_refs or {}
    input_validation_report_hashes = input_validation_report_hashes or {}
    bridges = [
        validate_bridge_contract(
            catalog,
            row
            if isinstance(row, RepoPhaseBridgeContract)
            else RepoPhaseBridgeContract.model_validate(row),
        )
        for row in bridge_contracts
    ]
    reports = [
        row
        if isinstance(row, RepoPhaseTransitionValidationReport)
        else RepoPhaseTransitionValidationReport.model_validate(row)
        for row in validation_reports
    ]
    bridge_by_transition = {row.transition_id: row for row in bridges}
    if len(bridge_by_transition) != len(bridges):
        raise ValueError("bridge_contracts must not contain duplicate transition_id values")
    transition_by_id = {row.transition_id: row for row in catalog.transition_rows}
    expected_circuit_hash = catalog.circuit_hash or canonical_hash(
        catalog,
        drop_keys={"circuit_hash"},
    )

    closure_rows: list[ClosureRow] = []
    frontier_summary_rows: list[FrontierSummaryRow] = []
    input_refs: list[str] = []
    actual_report_hashes: dict[str, str] = {}
    for report in sorted(reports, key=lambda row: row.transition_validation_report_ref):
        input_refs.append(report.transition_validation_report_ref)
        actual_hash = report.canonical_output_hash or canonical_hash(
            report,
            drop_keys={"canonical_output_hash"},
        )
        actual_report_hashes[report.transition_validation_report_ref] = actual_hash
        expected_hash = input_validation_report_hashes.get(report.transition_validation_report_ref)
        if expected_hash is not None and expected_hash != actual_hash:
            raise ValueError("input validation report hash mismatch")
        if (
            report.circuit_id != catalog.circuit_id
            or report.circuit_version != catalog.circuit_version
            or report.circuit_hash != expected_circuit_hash
        ):
            raise ValueError("validation report circuit binding must match catalog")
        transition = transition_by_id.get(report.transition_id)
        if transition is None:
            raise ValueError(
                f"validation report references unknown transition_id {report.transition_id!r}"
            )
        bridge = bridge_by_transition.get(report.transition_id)
        if bridge is None:
            raise ValueError(f"missing bridge contract for transition_id {report.transition_id!r}")
        for frontier in report.frontier_rows:
            frontier_summary_rows.append(_frontier_summary(report, frontier))
        closure_rows.append(
            _closure_row_for_report(
                bridge=bridge,
                report=report,
                from_phase=transition.from_phase,
                to_phase=transition.to_phase,
                known_risk_ref=known_risk_refs.get(report.transition_id),
            )
        )
    merged_hashes = {**actual_report_hashes, **input_validation_report_hashes}
    closure = RepoPhaseTransitionClosureReport(
        schema=REPO_PHASE_TRANSITION_CLOSURE_REPORT_SCHEMA,
        transition_closure_report_ref=transition_closure_report_ref,
        circuit_id=catalog.circuit_id,
        circuit_version=catalog.circuit_version,
        circuit_hash=expected_circuit_hash,
        input_validation_report_refs=input_refs,
        input_validation_report_hashes=merged_hashes,
        closure_rows=closure_rows,
        frontier_summary_rows=frontier_summary_rows,
    )
    return _model_with_hash(closure, hash_field="canonical_output_hash")


def plan_transition_gates(
    closure_report: RepoPhaseTransitionClosureReport,
    *,
    gate_execution_plan_ref: str = "otb-0b-gate-plan:default",
) -> RepoPhaseGateExecutionPlan:
    rows = [
        GatePlanRow(
            gate_ref=f"otb-0b-gate:{row.transition_id}",
            transition_id=row.transition_id,
            gate_kind="phase_transition_gate",
            required_input_refs=[row.transition_id],
            expected_output_kinds=row.allowed_next_phase_refs or [row.to_phase],
            forbidden_evidence_kinds=[],
            success_posture=row.readiness_posture,
            failure_route=f"frontier:{row.transition_id}",
            plan_authority_posture="plan_only_not_execution_authority",
        )
        for row in closure_report.closure_rows
        if row.closure_status in {"closed", "scoped_ready"}
    ]
    plan = RepoPhaseGateExecutionPlan(
        schema=REPO_PHASE_GATE_EXECUTION_PLAN_SCHEMA,
        gate_execution_plan_ref=gate_execution_plan_ref,
        transition_closure_report_ref=closure_report.transition_closure_report_ref,
        gate_plan_rows=rows,
        plan_authority_posture="plan_only_not_execution_authority",
    )
    return _model_with_hash(plan, hash_field="canonical_output_hash")


def build_worker_baton_contract(
    closure_report: RepoPhaseTransitionClosureReport,
    *,
    transition_id: str | None = None,
    target_phase: str | None = None,
    allowed_inputs: list[str] | None = None,
    required_outputs: list[BatonOutputRow | dict[str, Any]] | None = None,
    forbidden_inputs: list[str] | None = None,
    forbidden_promotions: list[PromotionKind] | None = None,
    required_closeout_rows: list[str] | None = None,
    worker_baton_contract_ref: str = "otb-0b-baton:default",
) -> RepoPhaseWorkerBatonContract:
    row = _select_closure_row(closure_report, transition_id)
    selected_target_phase = target_phase or row.to_phase
    if selected_target_phase not in ({row.to_phase, *row.allowed_next_phase_refs}):
        raise ValueError("target_phase must be allowed by the closure row")
    output_rows = [
        item if isinstance(item, BatonOutputRow) else BatonOutputRow.model_validate(item)
        for item in (
            required_outputs
            if required_outputs is not None
            else [
                BatonOutputRow(
                    output_kind=f"{selected_target_phase}:closeout",
                    target_phase=selected_target_phase,
                )
            ]
        )
    ]
    contract = RepoPhaseWorkerBatonContract(
        schema=REPO_PHASE_WORKER_BATON_CONTRACT_SCHEMA,
        worker_baton_contract_ref=worker_baton_contract_ref,
        transition_id=row.transition_id,
        source_phase_refs=[row.from_phase],
        target_phase=selected_target_phase,
        allowed_inputs=allowed_inputs if allowed_inputs is not None else [row.transition_id],
        required_outputs=output_rows,
        forbidden_inputs=forbidden_inputs if forbidden_inputs is not None else [],
        forbidden_promotions=(
            forbidden_promotions
            if forbidden_promotions is not None
            else [
                "scoped_to_official",
                "official_eval_handoff",
            ]
        ),
        required_closeout_rows=(
            required_closeout_rows
            if required_closeout_rows is not None
            else ["worker_closeout"]
        ),
        baton_authority_posture="baton_contract_only_not_dispatch_authority",
    )
    return _model_with_hash(contract, hash_field="canonical_output_hash")


def plan_evidence_posture(
    closure_report: RepoPhaseTransitionClosureReport,
    *,
    transition_id: str | None = None,
    current_evidence_posture: EvidenceBoundaryPosture = "clean_first_pass_allowed",
    target_evidence_posture: EvidenceBoundaryPosture = "official_like_pressure",
    required_equivalence_checks: list[str] | None = None,
    forbidden_evidence_leaks: list[EvidenceKind] | None = None,
    official_readiness_requirements: list[str] | None = None,
    evidence_posture_plan_ref: str = "otb-0b-evidence-plan:default",
) -> RepoPhaseEvidencePosturePlan:
    row = _select_closure_row(closure_report, transition_id)
    plan = RepoPhaseEvidencePosturePlan(
        schema=REPO_PHASE_EVIDENCE_POSTURE_PLAN_SCHEMA,
        evidence_posture_plan_ref=evidence_posture_plan_ref,
        transition_id=row.transition_id,
        current_evidence_posture=current_evidence_posture,
        target_evidence_posture=target_evidence_posture,
        required_equivalence_checks=(
            required_equivalence_checks
            if required_equivalence_checks is not None
            else [
                "observation_oracle_equivalence",
                "packaged_artifact_equivalence",
                "target_substrate_equivalence",
            ]
        ),
        forbidden_evidence_leaks=(
            forbidden_evidence_leaks
            if forbidden_evidence_leaks is not None
            else ["post_eval_pressure"]
        ),
        official_readiness_requirements=(
            official_readiness_requirements
            if official_readiness_requirements is not None
            else ["packaged_preflight_record"]
        ),
        plan_authority_posture="plan_only_not_observed_evidence",
    )
    return _model_with_hash(plan, hash_field="canonical_output_hash")


def emit_operationalization_report(
    closure_report: RepoPhaseTransitionClosureReport,
    *,
    gate_plan: RepoPhaseGateExecutionPlan | None = None,
    baton_contract: RepoPhaseWorkerBatonContract | None = None,
    evidence_plan: RepoPhaseEvidencePosturePlan | None = None,
    operationalization_report_ref: str = "otb-0b-operationalization:default",
) -> RepoPhaseOperationalizationReport:
    recommended = [
        row.transition_id
        for row in closure_report.closure_rows
        if row.closure_status in {"closed", "scoped_ready"}
    ]
    blocked = [
        row.transition_id
        for row in closure_report.closure_rows
        if row.closure_status in {"blocked", "conflict_isolated", "representative_only"}
    ]
    deferred = [
        row.transition_id for row in closure_report.closure_rows if row.closure_status == "deferred"
    ]
    constraints = [
        "operationalization_report_is_not_execution_authority",
        "official_eval_authority_not_granted",
    ]
    if gate_plan is not None:
        constraints.append(gate_plan.plan_authority_posture)
    if baton_contract is not None:
        constraints.append(baton_contract.baton_authority_posture)
    if evidence_plan is not None:
        constraints.append(evidence_plan.plan_authority_posture)
    report = RepoPhaseOperationalizationReport(
        schema=REPO_PHASE_OPERATIONALIZATION_REPORT_SCHEMA,
        operationalization_report_ref=operationalization_report_ref,
        transition_closure_report_ref=closure_report.transition_closure_report_ref,
        recommended_next_frontier=recommended,
        blocked_frontier=blocked,
        deferred_frontier=deferred,
        handoff_constraints=constraints,
        operationalization_authority_posture=(
            "operationalization_summary_only_not_execution_authority"
        ),
    )
    return _model_with_hash(report, hash_field="canonical_output_hash")


def _frontier_summary(
    report: RepoPhaseTransitionValidationReport,
    frontier: LegalFrontierRow,
) -> FrontierSummaryRow:
    return FrontierSummaryRow(
        frontier_ref=(
            f"otb-0b-frontier-summary:{report.transition_validation_report_ref}:"
            f"{frontier.frontier_ref}"
        ),
        transition_id=frontier.transition_id,
        frontier_reason=frontier.frontier_reason,
        required_next_action=frontier.required_next_action,
        source_validation_report_ref=report.transition_validation_report_ref,
    )


def _closure_row_for_report(
    *,
    bridge: RepoPhaseBridgeContract,
    report: RepoPhaseTransitionValidationReport,
    from_phase: PhaseKind | str,
    to_phase: PhaseKind | str,
    known_risk_ref: str | None,
) -> ClosureRow:
    maximum = _maximum_supported_posture(bridge)
    blocking_frontier_refs = [row.frontier_ref for row in report.frontier_rows]
    if report.validation_status == "conflict_isolated":
        return ClosureRow(
            transition_id=report.transition_id,
            from_phase=str(from_phase),
            to_phase=str(to_phase),
            closure_status="conflict_isolated",
            readiness_posture="not_ready",
            closure_basis="conflict_isolated",
            blocking_frontier_refs=blocking_frontier_refs,
            allowed_next_phase_refs=[],
            maximum_supported_posture=maximum,
        )
    if report.validation_status != "valid_for_broker_frontier":
        return ClosureRow(
            transition_id=report.transition_id,
            from_phase=str(from_phase),
            to_phase=str(to_phase),
            closure_status="blocked",
            readiness_posture="not_ready",
            closure_basis="blocked_by_A_validation",
            blocking_frontier_refs=blocking_frontier_refs,
            allowed_next_phase_refs=[],
            maximum_supported_posture=maximum,
        )
    if report.frontier_rows:
        return ClosureRow(
            transition_id=report.transition_id,
            from_phase=str(from_phase),
            to_phase=str(to_phase),
            closure_status="blocked",
            readiness_posture="not_ready",
            closure_basis="blocked_by_frontier",
            blocking_frontier_refs=blocking_frontier_refs,
            allowed_next_phase_refs=[],
            maximum_supported_posture=maximum,
        )
    if maximum == "representative_only":
        return ClosureRow(
            transition_id=report.transition_id,
            from_phase=str(from_phase),
            to_phase=str(to_phase),
            closure_status="representative_only",
            readiness_posture=maximum,
            closure_basis="representative_only",
            blocking_frontier_refs=[],
            allowed_next_phase_refs=bridge.U_bridge.next_allowed_phases,
            maximum_supported_posture=maximum,
        )
    if _rank(maximum) <= _rank("scoped_ready"):
        return ClosureRow(
            transition_id=report.transition_id,
            from_phase=str(from_phase),
            to_phase=str(to_phase),
            closure_status="scoped_ready",
            readiness_posture=maximum,
            closure_basis="scoped_ready_with_known_risk",
            blocking_frontier_refs=[],
            allowed_next_phase_refs=bridge.U_bridge.next_allowed_phases,
            known_risk_ref=known_risk_ref,
            maximum_supported_posture=maximum,
        )
    return ClosureRow(
        transition_id=report.transition_id,
        from_phase=str(from_phase),
        to_phase=str(to_phase),
        closure_status="closed",
        readiness_posture=maximum,
        closure_basis="all_required_bridges_valid",
        blocking_frontier_refs=[],
        allowed_next_phase_refs=bridge.U_bridge.next_allowed_phases,
        known_risk_ref=known_risk_ref,
        maximum_supported_posture=maximum,
    )


def _maximum_supported_posture(bridge: RepoPhaseBridgeContract) -> ReadinessPosture:
    if bridge.U_bridge.maximum_supported_posture is not None:
        return bridge.U_bridge.maximum_supported_posture
    if bridge.U_bridge.supported_readiness_postures:
        return bridge.U_bridge.supported_readiness_postures[-1]
    return "scoped_ready"


def _select_closure_row(
    closure_report: RepoPhaseTransitionClosureReport,
    transition_id: str | None,
) -> ClosureRow:
    eligible = [
        row
        for row in closure_report.closure_rows
        if row.closure_status in {"closed", "scoped_ready"}
    ]
    if transition_id is not None:
        matching = [row for row in eligible if row.transition_id == transition_id]
        if not matching:
            raise ValueError(f"transition_id {transition_id!r} is not eligible for planning")
        return matching[0]
    if not eligible:
        raise ValueError("closure report has no transition eligible for planning")
    return sorted(eligible, key=lambda row: row.transition_id)[0]
