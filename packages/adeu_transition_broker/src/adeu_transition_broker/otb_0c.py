from __future__ import annotations

from typing import Any, Literal

from pydantic import BaseModel, ConfigDict, Field, model_validator

from .otb_0a import EvidenceBoundaryPosture, canonical_hash
from .otb_0b import RepoPhaseTransitionClosureReport

MODEL_CONFIG = ConfigDict(
    extra="forbid",
    frozen=True,
    populate_by_name=True,
    protected_namespaces=(),
)

REPO_PHASE_TRANSITION_DELTA_ATTRIBUTION_LEDGER_SCHEMA = (
    "repo_phase_transition_delta_attribution_ledger@1"
)
REPO_PHASE_STALE_OBJECT_INVALIDATION_REPORT_SCHEMA = "repo_phase_stale_object_invalidation_report@1"
REPO_TRANSITION_BROKER_INTEGRATION_HANDOFF_SCHEMA = "repo_transition_broker_integration_handoff@1"
REPO_TRANSITION_BROKER_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA = (
    "repo_transition_broker_family_closeout_alignment@1"
)

PressureKind = Literal[
    "score_movement",
    "assertion_failure",
    "official_failure",
    "source_postmortem",
    "local_probe_delta",
    "resource_topology",
    "artifact_identity",
]
ConfidencePosture = Literal[
    "candidate_pressure",
    "dominant_transition_pressure",
    "blocked_by_earlier_transition",
    "requires_revalidation",
]
AttributionDomain = Literal[
    "transition_bridge",
    "artifact_identity",
    "evidence_boundary",
    "product_semantics",
]
RecommendedRoute = Literal[
    "repair_transition_bridge",
    "invalidate_and_revalidate",
    "hold_as_pressure_only",
    "route_to_product_theory_after_bridge_closure",
]
InvalidationReason = Literal[
    "object_hash_changed",
    "catalog_hash_changed",
    "bridge_contract_hash_changed",
    "evidence_boundary_changed",
    "obligation_set_changed",
    "target_substrate_changed",
    "run_topology_changed",
]
HandoffPosture = Literal["handoff_constraints_only_not_authority"]
FamilyCloseoutAlignmentPosture = Literal["family_closeout_alignment_only_not_release_authority"]

_HASH_REASON_BY_FIELD: dict[str, InvalidationReason] = {
    "object_hash": "object_hash_changed",
    "catalog_hash": "catalog_hash_changed",
    "bridge_contract_hash": "bridge_contract_hash_changed",
    "evidence_boundary_hash": "evidence_boundary_changed",
    "obligation_set_hash": "obligation_set_changed",
    "target_substrate_hash": "target_substrate_changed",
    "run_topology_hash": "run_topology_changed",
}
_PRESSURE_ONLY_POSTURES: set[str] = {
    "post_eval_pressure_only",
    "source_postmortem_pressure",
    "official_like_pressure",
    "local_locked_probe_delta",
}
_FORBIDDEN_AUTHORITY_CONSUMPTION: set[str] = {
    "implementation_authority",
    "execution_authority",
    "product_truth_authority",
    "future_family_selection_authority",
    "official_eval_authority",
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


def _model_with_hash[T: BaseModel](model: T, *, hash_field: str) -> T:
    payload = model.model_dump(mode="json", by_alias=True, exclude_none=True)
    payload[hash_field] = canonical_hash(model, drop_keys={hash_field})
    return type(model).model_validate(payload)


class _OtbCBase(BaseModel):
    model_config = MODEL_CONFIG


class RunDeltaPressureRow(_OtbCBase):
    pressure_ref: str
    transition_id: str
    bridge_field: str
    pressure_kind: PressureKind
    pressure_summary: str
    evidence_boundary_posture: EvidenceBoundaryPosture
    confidence_posture: ConfidencePosture = "candidate_pressure"
    recommended_route: RecommendedRoute = "hold_as_pressure_only"
    transition_evidence_refs: list[str] = Field(default_factory=list)
    attribution_domain: AttributionDomain = "transition_bridge"
    earlier_unproven_transition_refs: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_row(self) -> RunDeltaPressureRow:
        for field_name in ("pressure_ref", "transition_id", "bridge_field", "pressure_summary"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in ("transition_evidence_refs", "earlier_unproven_transition_refs"):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        _validate_pressure_boundary(
            pressure_kind=self.pressure_kind,
            evidence_boundary_posture=self.evidence_boundary_posture,
            transition_evidence_refs=self.transition_evidence_refs,
            attribution_domain=self.attribution_domain,
            earlier_unproven_transition_refs=self.earlier_unproven_transition_refs,
        )
        return self


class RunDeltaInput(_OtbCBase):
    run_delta_ref: str
    pressure_rows: list[RunDeltaPressureRow]

    @model_validator(mode="after")
    def _validate_input(self) -> RunDeltaInput:
        object.__setattr__(
            self,
            "run_delta_ref",
            _assert_non_empty_text(self.run_delta_ref, field_name="run_delta_ref"),
        )
        _assert_unique_rows(
            self.pressure_rows,
            attr_name="pressure_ref",
            field_name="pressure_rows",
        )
        object.__setattr__(
            self,
            "pressure_rows",
            sorted(self.pressure_rows, key=lambda row: row.pressure_ref),
        )
        return self


class AttributionRow(_OtbCBase):
    attribution_ref: str
    transition_id: str
    bridge_field: str
    pressure_kind: PressureKind
    pressure_summary: str
    evidence_boundary_posture: EvidenceBoundaryPosture
    run_delta_refs: list[str]
    confidence_posture: ConfidencePosture
    recommended_route: RecommendedRoute
    transition_evidence_refs: list[str] = Field(default_factory=list)
    attribution_domain: AttributionDomain = "transition_bridge"
    earlier_unproven_transition_refs: list[str] = Field(default_factory=list)

    @model_validator(mode="after")
    def _validate_row(self) -> AttributionRow:
        for field_name in ("attribution_ref", "transition_id", "bridge_field", "pressure_summary"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "run_delta_refs",
            "transition_evidence_refs",
            "earlier_unproven_transition_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        if not self.run_delta_refs:
            raise ValueError("attribution rows require run_delta_refs")
        _validate_pressure_boundary(
            pressure_kind=self.pressure_kind,
            evidence_boundary_posture=self.evidence_boundary_posture,
            transition_evidence_refs=self.transition_evidence_refs,
            attribution_domain=self.attribution_domain,
            earlier_unproven_transition_refs=self.earlier_unproven_transition_refs,
        )
        return self


class RepoPhaseTransitionDeltaAttributionLedger(_OtbCBase):
    schema: Literal[REPO_PHASE_TRANSITION_DELTA_ATTRIBUTION_LEDGER_SCHEMA]
    transition_delta_attribution_ledger_ref: str
    circuit_id: str
    circuit_version: str
    circuit_hash: str
    input_closure_report_refs: list[str]
    run_delta_ref: str
    attribution_rows: list[AttributionRow]
    evidence_boundary_posture: EvidenceBoundaryPosture
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_ledger(self) -> RepoPhaseTransitionDeltaAttributionLedger:
        for field_name in (
            "transition_delta_attribution_ledger_ref",
            "circuit_id",
            "circuit_version",
            "circuit_hash",
            "run_delta_ref",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "input_closure_report_refs",
            _assert_sorted_unique(
                self.input_closure_report_refs,
                field_name="input_closure_report_refs",
            ),
        )
        _assert_unique_rows(
            self.attribution_rows,
            attr_name="attribution_ref",
            field_name="attribution_rows",
        )
        object.__setattr__(
            self,
            "attribution_rows",
            sorted(self.attribution_rows, key=lambda row: row.attribution_ref),
        )
        if self.evidence_boundary_posture == "clean_first_pass_allowed" and any(
            row.evidence_boundary_posture != "clean_first_pass_allowed"
            for row in self.attribution_rows
        ):
            raise ValueError(
                "disallowed or pressure-only attribution cannot make the ledger clean first-pass"
            )
        if self.canonical_output_hash is not None:
            expected = canonical_hash(self, drop_keys={"canonical_output_hash"})
            if self.canonical_output_hash != expected:
                raise ValueError("canonical_output_hash must match canonical attribution payload")
        return self


class PhaseArtifactIdentityRow(_OtbCBase):
    artifact_ref: str
    object_hash: str | None = None
    catalog_hash: str | None = None
    bridge_contract_hash: str | None = None
    evidence_boundary_hash: str | None = None
    obligation_set_hash: str | None = None
    target_substrate_hash: str | None = None
    run_topology_hash: str | None = None

    @model_validator(mode="after")
    def _validate_row(self) -> PhaseArtifactIdentityRow:
        object.__setattr__(
            self,
            "artifact_ref",
            _assert_non_empty_text(self.artifact_ref, field_name="artifact_ref"),
        )
        for field_name in _HASH_REASON_BY_FIELD:
            value = getattr(self, field_name)
            if value is not None:
                object.__setattr__(
                    self,
                    field_name,
                    _assert_non_empty_text(value, field_name=field_name),
                )
        return self


class InvalidatedArtifactRow(_OtbCBase):
    artifact_ref: str
    invalidation_reasons: list[InvalidationReason]

    @model_validator(mode="after")
    def _validate_row(self) -> InvalidatedArtifactRow:
        object.__setattr__(
            self,
            "artifact_ref",
            _assert_non_empty_text(self.artifact_ref, field_name="artifact_ref"),
        )
        object.__setattr__(
            self,
            "invalidation_reasons",
            sorted(set(self.invalidation_reasons)),
        )
        if not self.invalidation_reasons:
            raise ValueError("invalidated artifacts require invalidation_reasons")
        return self


class InvalidationReasonRow(_OtbCBase):
    invalidation_reason: InvalidationReason
    artifact_refs: list[str]

    @model_validator(mode="after")
    def _validate_row(self) -> InvalidationReasonRow:
        object.__setattr__(
            self,
            "artifact_refs",
            _assert_sorted_unique(self.artifact_refs, field_name="artifact_refs"),
        )
        if not self.artifact_refs:
            raise ValueError("invalidation reason rows require artifact_refs")
        return self


class RepoPhaseStaleObjectInvalidationReport(_OtbCBase):
    schema: Literal[REPO_PHASE_STALE_OBJECT_INVALIDATION_REPORT_SCHEMA]
    stale_object_invalidation_report_ref: str
    input_artifact_refs: list[str]
    new_artifact_refs: list[str]
    invalidated_artifact_rows: list[InvalidatedArtifactRow]
    invalidation_reason_rows: list[InvalidationReasonRow]
    required_revalidation_frontier: list[str]
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_report(self) -> RepoPhaseStaleObjectInvalidationReport:
        object.__setattr__(
            self,
            "stale_object_invalidation_report_ref",
            _assert_non_empty_text(
                self.stale_object_invalidation_report_ref,
                field_name="stale_object_invalidation_report_ref",
            ),
        )
        for field_name in (
            "input_artifact_refs",
            "new_artifact_refs",
            "required_revalidation_frontier",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        _assert_unique_rows(
            self.invalidated_artifact_rows,
            attr_name="artifact_ref",
            field_name="invalidated_artifact_rows",
        )
        _assert_unique_rows(
            self.invalidation_reason_rows,
            attr_name="invalidation_reason",
            field_name="invalidation_reason_rows",
        )
        object.__setattr__(
            self,
            "invalidated_artifact_rows",
            sorted(self.invalidated_artifact_rows, key=lambda row: row.artifact_ref),
        )
        object.__setattr__(
            self,
            "invalidation_reason_rows",
            sorted(self.invalidation_reason_rows, key=lambda row: row.invalidation_reason),
        )
        invalidated_refs = {row.artifact_ref for row in self.invalidated_artifact_rows}
        if invalidated_refs and not set(self.required_revalidation_frontier).issuperset(
            invalidated_refs
        ):
            raise ValueError("required_revalidation_frontier must include invalidated artifacts")
        reason_artifact_refs = {
            artifact_ref
            for row in self.invalidation_reason_rows
            for artifact_ref in row.artifact_refs
        }
        if reason_artifact_refs != invalidated_refs:
            raise ValueError("invalidation reason rows must cover invalidated artifacts exactly")
        reasons_by_artifact: dict[str, set[InvalidationReason]] = {}
        for row in self.invalidation_reason_rows:
            for artifact_ref in row.artifact_refs:
                reasons_by_artifact.setdefault(artifact_ref, set()).add(row.invalidation_reason)
        for row in self.invalidated_artifact_rows:
            expected_reasons = reasons_by_artifact.get(row.artifact_ref, set())
            if set(row.invalidation_reasons) != expected_reasons:
                raise ValueError("invalidation reason rows must match each artifact reason set")
        if self.canonical_output_hash is not None:
            expected = canonical_hash(self, drop_keys={"canonical_output_hash"})
            if self.canonical_output_hash != expected:
                raise ValueError("canonical_output_hash must match canonical invalidation payload")
        return self


class RepoTransitionBrokerIntegrationHandoff(_OtbCBase):
    schema: Literal[REPO_TRANSITION_BROKER_INTEGRATION_HANDOFF_SCHEMA]
    transition_broker_integration_handoff_ref: str
    source_family: str
    target_family_or_lane: str
    handoff_posture: HandoffPosture
    allowed_consumption: list[str]
    forbidden_consumption: list[str]
    pressure_rows: list[str]
    required_revalidation_rows: list[str]
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_handoff(self) -> RepoTransitionBrokerIntegrationHandoff:
        for field_name in (
            "transition_broker_integration_handoff_ref",
            "source_family",
            "target_family_or_lane",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "allowed_consumption",
            "forbidden_consumption",
            "pressure_rows",
            "required_revalidation_rows",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        forbidden_authority = sorted(
            _FORBIDDEN_AUTHORITY_CONSUMPTION & set(self.allowed_consumption)
        )
        if forbidden_authority:
            raise ValueError(f"handoff cannot grant authority: {forbidden_authority}")
        overlap = sorted(set(self.allowed_consumption) & set(self.forbidden_consumption))
        if overlap:
            raise ValueError(f"allowed_consumption cannot include forbidden_consumption: {overlap}")
        if self.canonical_output_hash is not None:
            expected = canonical_hash(self, drop_keys={"canonical_output_hash"})
            if self.canonical_output_hash != expected:
                raise ValueError("canonical_output_hash must match canonical handoff payload")
        return self


class AcceptedSurfaceRow(_OtbCBase):
    surface_ref: str
    slice_ref: str

    @model_validator(mode="after")
    def _validate_row(self) -> AcceptedSurfaceRow:
        for field_name in ("surface_ref", "slice_ref"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        return self


class DeferredSurfaceRow(_OtbCBase):
    surface_ref: str
    slice_ref: str
    deferral_reason: str

    @model_validator(mode="after")
    def _validate_row(self) -> DeferredSurfaceRow:
        for field_name in ("surface_ref", "slice_ref", "deferral_reason"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        return self


class RepoTransitionBrokerFamilyCloseoutAlignment(_OtbCBase):
    schema: Literal[REPO_TRANSITION_BROKER_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA]
    family_closeout_alignment_ref: str
    completed_slices: list[str]
    unimplemented_slices: list[str]
    accepted_surfaces: list[AcceptedSurfaceRow]
    deferred_surfaces: list[DeferredSurfaceRow]
    non_authority_boundary_confirmation: FamilyCloseoutAlignmentPosture
    future_pressure_notes: list[str]
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_alignment(self) -> RepoTransitionBrokerFamilyCloseoutAlignment:
        object.__setattr__(
            self,
            "family_closeout_alignment_ref",
            _assert_non_empty_text(
                self.family_closeout_alignment_ref,
                field_name="family_closeout_alignment_ref",
            ),
        )
        for field_name in ("completed_slices", "unimplemented_slices", "future_pressure_notes"):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        _assert_unique_rows(
            self.accepted_surfaces,
            attr_name="surface_ref",
            field_name="accepted_surfaces",
        )
        _assert_unique_rows(
            self.deferred_surfaces,
            attr_name="surface_ref",
            field_name="deferred_surfaces",
        )
        object.__setattr__(
            self,
            "accepted_surfaces",
            sorted(self.accepted_surfaces, key=lambda row: row.surface_ref),
        )
        object.__setattr__(
            self,
            "deferred_surfaces",
            sorted(self.deferred_surfaces, key=lambda row: row.surface_ref),
        )
        accepted_slice_refs = {row.slice_ref for row in self.accepted_surfaces}
        missing = sorted(set(self.completed_slices) - accepted_slice_refs)
        if missing:
            raise ValueError("completed slices require accepted surface rows")
        deferred_slice_refs = {row.slice_ref for row in self.deferred_surfaces}
        missing_deferred = sorted(set(self.unimplemented_slices) - deferred_slice_refs)
        if missing_deferred:
            raise ValueError("unimplemented slices require deferred surface rows")
        if set(self.completed_slices) & set(self.unimplemented_slices):
            raise ValueError("completed_slices cannot also be unimplemented")
        if self.canonical_output_hash is not None:
            expected = canonical_hash(self, drop_keys={"canonical_output_hash"})
            if self.canonical_output_hash != expected:
                raise ValueError("canonical_output_hash must match canonical closeout payload")
        return self


def attribute_transition_delta(
    closure_reports: list[RepoPhaseTransitionClosureReport | dict[str, Any]],
    run_delta: RunDeltaInput | dict[str, Any],
    *,
    transition_delta_attribution_ledger_ref: str = "otb-0c-attribution:default",
    evidence_boundary_posture: EvidenceBoundaryPosture = "post_eval_pressure_only",
) -> RepoPhaseTransitionDeltaAttributionLedger:
    reports = [
        report
        if isinstance(report, RepoPhaseTransitionClosureReport)
        else RepoPhaseTransitionClosureReport.model_validate(report)
        for report in closure_reports
    ]
    delta = (
        run_delta
        if isinstance(run_delta, RunDeltaInput)
        else RunDeltaInput.model_validate(run_delta)
    )
    if not reports:
        raise ValueError("attribute_transition_delta requires at least one closure report")
    first = reports[0]
    for report in reports[1:]:
        if (
            report.circuit_id != first.circuit_id
            or report.circuit_version != first.circuit_version
            or report.circuit_hash != first.circuit_hash
        ):
            raise ValueError("closure reports must share circuit binding")
    closure_transition_ids = {
        row.transition_id for report in reports for row in report.closure_rows
    }
    rows: list[AttributionRow] = []
    for pressure in delta.pressure_rows:
        if pressure.transition_id not in closure_transition_ids:
            raise ValueError(
                f"run delta references unknown transition_id {pressure.transition_id!r}"
            )
        rows.append(
            AttributionRow(
                attribution_ref=f"otb-0c-attribution:{pressure.pressure_ref}",
                transition_id=pressure.transition_id,
                bridge_field=pressure.bridge_field,
                pressure_kind=pressure.pressure_kind,
                pressure_summary=pressure.pressure_summary,
                evidence_boundary_posture=pressure.evidence_boundary_posture,
                run_delta_refs=[delta.run_delta_ref],
                confidence_posture=pressure.confidence_posture,
                recommended_route=pressure.recommended_route,
                transition_evidence_refs=pressure.transition_evidence_refs,
                attribution_domain=pressure.attribution_domain,
                earlier_unproven_transition_refs=pressure.earlier_unproven_transition_refs,
            )
        )
    ledger = RepoPhaseTransitionDeltaAttributionLedger(
        schema=REPO_PHASE_TRANSITION_DELTA_ATTRIBUTION_LEDGER_SCHEMA,
        transition_delta_attribution_ledger_ref=transition_delta_attribution_ledger_ref,
        circuit_id=first.circuit_id,
        circuit_version=first.circuit_version,
        circuit_hash=first.circuit_hash,
        input_closure_report_refs=[report.transition_closure_report_ref for report in reports],
        run_delta_ref=delta.run_delta_ref,
        attribution_rows=rows,
        evidence_boundary_posture=evidence_boundary_posture,
    )
    return _model_with_hash(ledger, hash_field="canonical_output_hash")


def invalidate_stale_phase_objects(
    old_artifacts: list[PhaseArtifactIdentityRow | dict[str, Any]],
    new_artifacts: list[PhaseArtifactIdentityRow | dict[str, Any]],
    bridge_contracts: list[Any] | None = None,
    *,
    stale_object_invalidation_report_ref: str = "otb-0c-invalidation:default",
) -> RepoPhaseStaleObjectInvalidationReport:
    _ = bridge_contracts
    old_rows = [
        row
        if isinstance(row, PhaseArtifactIdentityRow)
        else PhaseArtifactIdentityRow.model_validate(row)
        for row in old_artifacts
    ]
    new_rows = [
        row
        if isinstance(row, PhaseArtifactIdentityRow)
        else PhaseArtifactIdentityRow.model_validate(row)
        for row in new_artifacts
    ]
    old_by_ref = {row.artifact_ref: row for row in old_rows}
    new_by_ref = {row.artifact_ref: row for row in new_rows}
    if len(old_by_ref) != len(old_rows) or len(new_by_ref) != len(new_rows):
        raise ValueError("artifact identity rows must not contain duplicate artifact_ref values")
    invalidated_rows: list[InvalidatedArtifactRow] = []
    reasons_to_artifacts: dict[InvalidationReason, list[str]] = {}
    for artifact_ref in sorted(set(old_by_ref) & set(new_by_ref)):
        old = old_by_ref[artifact_ref]
        new = new_by_ref[artifact_ref]
        reasons = [
            reason
            for field_name, reason in _HASH_REASON_BY_FIELD.items()
            if getattr(old, field_name) != getattr(new, field_name)
        ]
        if not reasons:
            continue
        invalidated_rows.append(
            InvalidatedArtifactRow(
                artifact_ref=artifact_ref,
                invalidation_reasons=reasons,
            )
        )
        for reason in reasons:
            reasons_to_artifacts.setdefault(reason, []).append(artifact_ref)
    reason_rows = [
        InvalidationReasonRow(
            invalidation_reason=reason,
            artifact_refs=artifact_refs,
        )
        for reason, artifact_refs in reasons_to_artifacts.items()
    ]
    report = RepoPhaseStaleObjectInvalidationReport(
        schema=REPO_PHASE_STALE_OBJECT_INVALIDATION_REPORT_SCHEMA,
        stale_object_invalidation_report_ref=stale_object_invalidation_report_ref,
        input_artifact_refs=[row.artifact_ref for row in old_rows],
        new_artifact_refs=[row.artifact_ref for row in new_rows],
        invalidated_artifact_rows=invalidated_rows,
        invalidation_reason_rows=reason_rows,
        required_revalidation_frontier=[row.artifact_ref for row in invalidated_rows],
    )
    return _model_with_hash(report, hash_field="canonical_output_hash")


def build_integration_handoff(
    attribution: RepoPhaseTransitionDeltaAttributionLedger | dict[str, Any],
    invalidation: RepoPhaseStaleObjectInvalidationReport | dict[str, Any],
    target_lane: str,
    *,
    transition_broker_integration_handoff_ref: str = "otb-0c-handoff:default",
    allowed_consumption: list[str] | None = None,
    forbidden_consumption: list[str] | None = None,
) -> RepoTransitionBrokerIntegrationHandoff:
    attribution_row = (
        attribution
        if isinstance(attribution, RepoPhaseTransitionDeltaAttributionLedger)
        else RepoPhaseTransitionDeltaAttributionLedger.model_validate(attribution)
    )
    invalidation_row = (
        invalidation
        if isinstance(invalidation, RepoPhaseStaleObjectInvalidationReport)
        else RepoPhaseStaleObjectInvalidationReport.model_validate(invalidation)
    )
    handoff = RepoTransitionBrokerIntegrationHandoff(
        schema=REPO_TRANSITION_BROKER_INTEGRATION_HANDOFF_SCHEMA,
        transition_broker_integration_handoff_ref=transition_broker_integration_handoff_ref,
        source_family="OTB-0",
        target_family_or_lane=target_lane,
        handoff_posture="handoff_constraints_only_not_authority",
        allowed_consumption=(
            allowed_consumption
            if allowed_consumption is not None
            else [
                "consume_pressure_rows",
                "consume_revalidation_frontier",
            ]
        ),
        forbidden_consumption=(
            forbidden_consumption
            if forbidden_consumption is not None
            else sorted(_FORBIDDEN_AUTHORITY_CONSUMPTION)
        ),
        pressure_rows=[row.attribution_ref for row in attribution_row.attribution_rows],
        required_revalidation_rows=invalidation_row.required_revalidation_frontier,
    )
    return _model_with_hash(handoff, hash_field="canonical_output_hash")


def emit_family_closeout_alignment(
    *,
    accepted_surfaces: list[AcceptedSurfaceRow | dict[str, Any]],
    deferred_surfaces: list[DeferredSurfaceRow | dict[str, Any]],
    completed_slices: list[str] | None = None,
    unimplemented_slices: list[str] | None = None,
    future_pressure_notes: list[str] | None = None,
    family_closeout_alignment_ref: str = "otb-0c-family-closeout:default",
) -> RepoTransitionBrokerFamilyCloseoutAlignment:
    accepted = [
        row if isinstance(row, AcceptedSurfaceRow) else AcceptedSurfaceRow.model_validate(row)
        for row in accepted_surfaces
    ]
    deferred = [
        row if isinstance(row, DeferredSurfaceRow) else DeferredSurfaceRow.model_validate(row)
        for row in deferred_surfaces
    ]
    alignment = RepoTransitionBrokerFamilyCloseoutAlignment(
        schema=REPO_TRANSITION_BROKER_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
        family_closeout_alignment_ref=family_closeout_alignment_ref,
        completed_slices=(
            completed_slices
            if completed_slices is not None
            else sorted({row.slice_ref for row in accepted})
        ),
        unimplemented_slices=(
            unimplemented_slices
            if unimplemented_slices is not None
            else sorted({row.slice_ref for row in deferred})
        ),
        accepted_surfaces=accepted,
        deferred_surfaces=deferred,
        non_authority_boundary_confirmation=(
            "family_closeout_alignment_only_not_release_authority"
        ),
        future_pressure_notes=future_pressure_notes if future_pressure_notes is not None else [],
    )
    return _model_with_hash(alignment, hash_field="canonical_output_hash")


def _validate_pressure_boundary(
    *,
    pressure_kind: PressureKind,
    evidence_boundary_posture: EvidenceBoundaryPosture,
    transition_evidence_refs: list[str],
    attribution_domain: AttributionDomain,
    earlier_unproven_transition_refs: list[str],
) -> None:
    if pressure_kind == "score_movement" and not transition_evidence_refs:
        raise ValueError("score movement is not bridge proof without transition evidence")
    if pressure_kind in {"official_failure", "source_postmortem"} and (
        evidence_boundary_posture == "clean_first_pass_allowed"
    ):
        raise ValueError("official/postmortem pressure cannot be clean first-pass evidence")
    if attribution_domain == "product_semantics" and earlier_unproven_transition_refs:
        raise ValueError("earlier unproven transition bridge dominates product attribution")
