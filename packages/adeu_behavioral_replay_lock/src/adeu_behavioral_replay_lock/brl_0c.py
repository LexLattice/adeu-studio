from __future__ import annotations

from typing import Literal

from pydantic import BaseModel, Field, model_validator

from .brl_0a import (
    MODEL_CONFIG,
    RepoBehavioralReplayManifest,
    _assert_non_empty_text,
    _assert_sha256,
    _assert_sorted_unique,
    _assert_unique_rows,
    canonical_hash,
)
from .brl_0b import (
    ProbeExecutionRow,
    RepoBehavioralRegressionDiff,
    RepoBehavioralReplayExecutionReport,
    RepoBehavioralSuiteRootHashReport,
)

REPO_BEHAVIORAL_IMPACT_CONE_SELECTION_REPORT_SCHEMA = (
    "repo_behavioral_impact_cone_selection_report@1"
)
REPO_BEHAVIORAL_NO_REGRESSION_CERTIFICATE_SCHEMA = (
    "repo_behavioral_no_regression_certificate@1"
)
REPO_BEHAVIORAL_LOCK_STALENESS_REPORT_SCHEMA = "repo_behavioral_lock_staleness_report@1"
REPO_BEHAVIORAL_REPLAY_INTEGRATION_HANDOFF_SCHEMA = (
    "repo_behavioral_replay_integration_handoff@1"
)

ImpactConeSelectionStatus = Literal[
    "selected",
    "blocked_by_missing_scope",
    "blocked_by_missing_sentinel",
]
SentinelSelectionReason = Literal[
    "full_manifest_scope",
    "owner_surface_touched",
    "not_in_touched_owner_surface",
    "missing_required_coverage",
    "not_available_in_manifest",
]
ImpactConeAuthorityPosture = Literal[
    "impact_cone_selection_only_not_probe_generation"
]
CertificatePosture = Literal[
    "impact_cone_no_observed_regression",
    "full_manifest_no_observed_regression",
    "packaged_artifact_no_observed_regression",
    "blocked_by_missing_sentinel",
    "blocked_by_replay_diff",
    "blocked_by_stale_manifest",
    "blocked_by_stale_owner_surface_map",
    "blocked_by_unreplayed_required_sentinel",
]
CertificateAuthorityPosture = Literal[
    "bounded_replay_preservation_only_not_product_truth"
]
StalenessStatus = Literal["fresh", "stale"]
StaleReasonKind = Literal[
    "manifest_hash_changed",
    "probe_contract_hash_changed",
    "fixture_tree_hash_changed",
    "canonicalization_profile_hash_changed",
    "expected_observation_hash_changed",
    "owner_surface_map_hash_changed",
    "candidate_artifact_substrate_hash_changed",
    "hob_otb_handoff_hash_changed",
]
StalenessAuthorityPosture = Literal["staleness_report_only_not_refresh_authority"]
IntegrationHandoffStatus = Literal[
    "handoff_ready",
    "blocked_by_certificate",
    "blocked_by_staleness",
    "blocked_by_missing_sentinel",
]
IntegrationHandoffAuthorityPosture = Literal[
    "handoff_constraint_only_not_transition_authority"
]

_READY_CERTIFICATE_POSTURES = {
    "impact_cone_no_observed_regression",
    "full_manifest_no_observed_regression",
    "packaged_artifact_no_observed_regression",
}
_BLOCKED_CERTIFICATE_POSTURES = {
    "blocked_by_missing_sentinel",
    "blocked_by_replay_diff",
    "blocked_by_stale_manifest",
    "blocked_by_stale_owner_surface_map",
    "blocked_by_unreplayed_required_sentinel",
}
_REQUIRED_FORBIDDEN_PROMOTIONS = {
    "hob_closure",
    "otb_transition_legality",
    "product_truth",
    "official_eval_readiness",
}


class _BrlCBase(BaseModel):
    model_config = MODEL_CONFIG


def _with_hash(model: BaseModel, *, object_kind: str, hash_field: str) -> object:
    payload = model.model_dump(mode="json", exclude_none=True)
    payload[hash_field] = canonical_hash(
        model,
        object_kind=object_kind,
        drop_keys={hash_field},
    )
    return type(model).model_validate(payload)


def _assert_non_empty_sorted_unique(values: list[str], *, field_name: str) -> list[str]:
    normalized = _assert_sorted_unique(values, field_name=field_name)
    if not normalized:
        raise ValueError(f"{field_name} must not be empty")
    return normalized


class OmittedProbeRow(_BrlCBase):
    owner_surface: str
    omitted_probe_ref: str
    omission_reason: SentinelSelectionReason
    blocker_ref: str | None = None

    @model_validator(mode="after")
    def _validate_row(self) -> OmittedProbeRow:
        for field_name in ("owner_surface", "omitted_probe_ref"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        if self.blocker_ref is not None:
            object.__setattr__(
                self,
                "blocker_ref",
                _assert_non_empty_text(self.blocker_ref, field_name="blocker_ref"),
            )
        if self.omission_reason in {"missing_required_coverage", "not_available_in_manifest"}:
            if self.blocker_ref is None:
                raise ValueError("required sentinel omissions must include blocker_ref")
        return self


class RepoBehavioralImpactConeSelectionReport(_BrlCBase):
    schema: Literal[REPO_BEHAVIORAL_IMPACT_CONE_SELECTION_REPORT_SCHEMA]
    impact_cone_report_ref: str
    candidate_change_ref: str
    touched_owner_surfaces: list[str]
    available_manifest_refs: list[str]
    required_probe_refs: list[str]
    selected_probe_refs: list[str]
    omitted_probe_rows: list[OmittedProbeRow] = Field(default_factory=list)
    selection_status: ImpactConeSelectionStatus
    authority_posture: ImpactConeAuthorityPosture
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_report(self) -> RepoBehavioralImpactConeSelectionReport:
        for field_name in ("impact_cone_report_ref", "candidate_change_ref"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in (
            "touched_owner_surfaces",
            "available_manifest_refs",
            "required_probe_refs",
            "selected_probe_refs",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        _assert_unique_rows(
            self.omitted_probe_rows,
            attr_name="omitted_probe_ref",
            field_name="omitted_probe_rows",
        )
        object.__setattr__(
            self,
            "omitted_probe_rows",
            sorted(
                self.omitted_probe_rows,
                key=lambda row: (row.owner_surface, row.omitted_probe_ref),
            ),
        )
        required_missing_from_selected = sorted(
            set(self.required_probe_refs) - set(self.selected_probe_refs)
        )
        if self.selection_status == "selected" and required_missing_from_selected:
            raise ValueError("selected impact cone must include every required probe")
        if self.selection_status == "selected" and any(
            row.omission_reason in {"missing_required_coverage", "not_available_in_manifest"}
            for row in self.omitted_probe_rows
        ):
            raise ValueError("selected impact cone cannot contain required sentinel blockers")
        if self.selection_status != "selected" and not self.omitted_probe_rows:
            raise ValueError("blocked impact cone selections require omitted_probe_rows")
        if self.authority_posture != "impact_cone_selection_only_not_probe_generation":
            raise ValueError("impact-cone selection cannot claim probe generation authority")
        if self.canonical_output_hash is not None:
            expected = canonical_hash(
                self,
                object_kind="repo_behavioral_impact_cone_selection_report",
                drop_keys={"canonical_output_hash"},
            )
            if self.canonical_output_hash != expected:
                raise ValueError("canonical_output_hash must match impact-cone report")
        return self


class StaleReasonRow(_BrlCBase):
    stale_reason_ref: str
    stale_reason_kind: StaleReasonKind
    object_ref: str
    expected_hash: str | None = None
    actual_hash: str | None = None
    summary: str

    @model_validator(mode="after")
    def _validate_row(self) -> StaleReasonRow:
        for field_name in ("stale_reason_ref", "object_ref", "summary"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in ("expected_hash", "actual_hash"):
            value = getattr(self, field_name)
            if value is not None:
                object.__setattr__(self, field_name, _assert_sha256(value, field_name=field_name))
        if self.expected_hash is None and self.actual_hash is None:
            raise ValueError("stale reason rows require expected_hash or actual_hash")
        return self


class RequiredRefreshRow(_BrlCBase):
    refresh_ref: str
    stale_reason_ref: str
    required_action: str

    @model_validator(mode="after")
    def _validate_row(self) -> RequiredRefreshRow:
        for field_name in ("refresh_ref", "stale_reason_ref", "required_action"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        return self


class RepoBehavioralLockStalenessReport(_BrlCBase):
    schema: Literal[REPO_BEHAVIORAL_LOCK_STALENESS_REPORT_SCHEMA]
    staleness_report_ref: str
    manifest_id: str
    staleness_status: StalenessStatus
    stale_reason_rows: list[StaleReasonRow] = Field(default_factory=list)
    required_refresh_rows: list[RequiredRefreshRow] = Field(default_factory=list)
    authority_posture: StalenessAuthorityPosture
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_report(self) -> RepoBehavioralLockStalenessReport:
        for field_name in ("staleness_report_ref", "manifest_id"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        _assert_unique_rows(
            self.stale_reason_rows,
            attr_name="stale_reason_ref",
            field_name="stale_reason_rows",
        )
        _assert_unique_rows(
            self.required_refresh_rows,
            attr_name="refresh_ref",
            field_name="required_refresh_rows",
        )
        object.__setattr__(
            self,
            "stale_reason_rows",
            sorted(self.stale_reason_rows, key=lambda row: row.stale_reason_ref),
        )
        object.__setattr__(
            self,
            "required_refresh_rows",
            sorted(self.required_refresh_rows, key=lambda row: row.refresh_ref),
        )
        reason_refs = {row.stale_reason_ref for row in self.stale_reason_rows}
        missing_reason_refs = sorted(
            {row.stale_reason_ref for row in self.required_refresh_rows} - reason_refs
        )
        if missing_reason_refs:
            raise ValueError(
                "required refresh rows reference missing reasons: "
                f"{missing_reason_refs}"
            )
        if self.staleness_status == "fresh" and (
            self.stale_reason_rows or self.required_refresh_rows
        ):
            raise ValueError("fresh staleness reports cannot contain stale rows")
        if self.staleness_status == "stale" and not self.stale_reason_rows:
            raise ValueError("stale reports require stale_reason_rows")
        if self.authority_posture != "staleness_report_only_not_refresh_authority":
            raise ValueError("staleness reports cannot claim refresh authority")
        if self.canonical_output_hash is not None:
            expected = canonical_hash(
                self,
                object_kind="repo_behavioral_lock_staleness_report",
                drop_keys={"canonical_output_hash"},
            )
            if self.canonical_output_hash != expected:
                raise ValueError("canonical_output_hash must match staleness report")
        return self


class RepoBehavioralNoRegressionCertificate(_BrlCBase):
    schema: Literal[REPO_BEHAVIORAL_NO_REGRESSION_CERTIFICATE_SCHEMA]
    certificate_ref: str
    manifest_id: str
    manifest_hash: str
    candidate_artifact_ref: str
    candidate_artifact_hash: str
    execution_report_ref: str
    impact_cone_report_ref: str
    certificate_posture: CertificatePosture
    bounded_claim: str
    covered_probe_refs: list[str]
    covered_owner_surfaces: list[str]
    known_gaps: list[str] = Field(default_factory=list)
    authority_posture: CertificateAuthorityPosture
    certificate_hash: str | None = None

    @model_validator(mode="after")
    def _validate_certificate(self) -> RepoBehavioralNoRegressionCertificate:
        for field_name in (
            "certificate_ref",
            "manifest_id",
            "candidate_artifact_ref",
            "execution_report_ref",
            "impact_cone_report_ref",
            "bounded_claim",
        ):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in ("manifest_hash", "candidate_artifact_hash"):
            object.__setattr__(
                self,
                field_name,
                _assert_sha256(getattr(self, field_name), field_name=field_name),
            )
        object.__setattr__(
            self,
            "covered_probe_refs",
            _assert_sorted_unique(self.covered_probe_refs, field_name="covered_probe_refs"),
        )
        object.__setattr__(
            self,
            "covered_owner_surfaces",
            _assert_sorted_unique(
                self.covered_owner_surfaces,
                field_name="covered_owner_surfaces",
            ),
        )
        object.__setattr__(
            self,
            "known_gaps",
            _assert_sorted_unique(self.known_gaps, field_name="known_gaps"),
        )
        if self.certificate_posture in _READY_CERTIFICATE_POSTURES:
            if not self.covered_probe_refs or not self.covered_owner_surfaces:
                raise ValueError("ready certificates require covered probes and owner surfaces")
            if self.known_gaps:
                raise ValueError("ready certificates cannot contain known gaps")
        if self.certificate_posture in _BLOCKED_CERTIFICATE_POSTURES and not self.known_gaps:
            raise ValueError("blocked certificates require known gaps")
        if self.authority_posture != "bounded_replay_preservation_only_not_product_truth":
            raise ValueError("certificate cannot claim product truth authority")
        if self.certificate_hash is not None:
            expected = canonical_hash(
                self,
                object_kind="repo_behavioral_no_regression_certificate",
                drop_keys={"certificate_hash"},
            )
            if self.certificate_hash != expected:
                raise ValueError("certificate_hash must match certificate payload")
        return self


class RepoBehavioralReplayIntegrationHandoff(_BrlCBase):
    schema: Literal[REPO_BEHAVIORAL_REPLAY_INTEGRATION_HANDOFF_SCHEMA]
    handoff_ref: str
    source_family: str
    target_family: str
    certificate_refs: list[str] = Field(default_factory=list)
    blocker_refs: list[str] = Field(default_factory=list)
    bounded_use: str
    forbidden_promotions: list[str]
    handoff_status: IntegrationHandoffStatus
    authority_posture: IntegrationHandoffAuthorityPosture
    canonical_output_hash: str | None = None

    @model_validator(mode="after")
    def _validate_handoff(self) -> RepoBehavioralReplayIntegrationHandoff:
        for field_name in ("handoff_ref", "source_family", "target_family", "bounded_use"):
            object.__setattr__(
                self,
                field_name,
                _assert_non_empty_text(getattr(self, field_name), field_name=field_name),
            )
        for field_name in ("certificate_refs", "blocker_refs", "forbidden_promotions"):
            object.__setattr__(
                self,
                field_name,
                _assert_sorted_unique(getattr(self, field_name), field_name=field_name),
            )
        missing_forbidden = sorted(_REQUIRED_FORBIDDEN_PROMOTIONS - set(self.forbidden_promotions))
        if missing_forbidden:
            raise ValueError(f"handoff missing forbidden promotions: {missing_forbidden}")
        if self.handoff_status == "handoff_ready":
            if not self.certificate_refs:
                raise ValueError("ready handoffs require certificate_refs")
            if self.blocker_refs:
                raise ValueError("ready handoffs cannot contain blockers")
        if self.handoff_status != "handoff_ready" and not self.blocker_refs:
            raise ValueError("blocked handoffs require blocker_refs")
        if self.authority_posture != "handoff_constraint_only_not_transition_authority":
            raise ValueError("handoff cannot claim transition authority")
        if self.canonical_output_hash is not None:
            expected = canonical_hash(
                self,
                object_kind="repo_behavioral_replay_integration_handoff",
                drop_keys={"canonical_output_hash"},
            )
            if self.canonical_output_hash != expected:
                raise ValueError("canonical_output_hash must match integration handoff")
        return self


def select_impact_cone(
    *,
    manifest: RepoBehavioralReplayManifest | dict[str, object],
    candidate_change_ref: str,
    touched_owner_surfaces: list[str] | None = None,
    full_manifest_scope: bool = False,
    impact_cone_report_ref: str | None = None,
) -> RepoBehavioralImpactConeSelectionReport:
    loaded_manifest = (
        manifest
        if isinstance(manifest, RepoBehavioralReplayManifest)
        else RepoBehavioralReplayManifest.model_validate(manifest)
    )
    candidate_change_ref = _assert_non_empty_text(
        candidate_change_ref,
        field_name="candidate_change_ref",
    )
    if full_manifest_scope:
        touched = loaded_manifest.protected_owner_surfaces
        required_probe_refs = loaded_manifest.probe_contract_refs
        selected_probe_refs = loaded_manifest.probe_contract_refs
        omitted_rows: list[OmittedProbeRow] = []
        status: ImpactConeSelectionStatus = "selected"
    else:
        touched = _assert_non_empty_sorted_unique(
            touched_owner_surfaces or [],
            field_name="touched_owner_surfaces",
        )
        row_by_surface = {row.owner_surface: row for row in loaded_manifest.owner_surface_rows}
        required: set[str] = set()
        omitted_rows = []
        for owner_surface in touched:
            row = row_by_surface.get(owner_surface)
            if row is None:
                omitted_rows.append(
                    OmittedProbeRow(
                        owner_surface=owner_surface,
                        omitted_probe_ref=f"owner-surface:{owner_surface}",
                        omission_reason="missing_required_coverage",
                        blocker_ref=f"blocker:missing-sentinel:{owner_surface}",
                    )
                )
                continue
            required.update(row.protected_sibling_probe_refs)

        manifest_probe_refs = set(loaded_manifest.probe_contract_refs)
        missing_from_manifest = sorted(required - manifest_probe_refs)
        for probe_ref in missing_from_manifest:
            omitted_rows.append(
                OmittedProbeRow(
                    owner_surface="manifest",
                    omitted_probe_ref=probe_ref,
                    omission_reason="not_available_in_manifest",
                    blocker_ref=f"blocker:missing-manifest-probe:{probe_ref}",
                )
            )
        required_probe_refs = sorted(required)
        selected_probe_refs = sorted(required & manifest_probe_refs)
        non_required_probe_refs = sorted(manifest_probe_refs - set(required_probe_refs))
        for probe_ref in non_required_probe_refs:
            omitted_rows.append(
                OmittedProbeRow(
                    owner_surface="manifest",
                    omitted_probe_ref=probe_ref,
                    omission_reason="not_in_touched_owner_surface",
                )
            )
        has_required_blockers = any(
            row.omission_reason in {"missing_required_coverage", "not_available_in_manifest"}
            for row in omitted_rows
        )
        if has_required_blockers:
            status = "blocked_by_missing_sentinel"
        elif required_probe_refs:
            status = "selected"
        else:
            status = "blocked_by_missing_scope"

    report_without_hash = RepoBehavioralImpactConeSelectionReport(
        schema=REPO_BEHAVIORAL_IMPACT_CONE_SELECTION_REPORT_SCHEMA,
        impact_cone_report_ref=impact_cone_report_ref
        or f"impact-cone:{candidate_change_ref}",
        candidate_change_ref=candidate_change_ref,
        touched_owner_surfaces=touched,
        available_manifest_refs=[loaded_manifest.manifest_id],
        required_probe_refs=required_probe_refs,
        selected_probe_refs=selected_probe_refs,
        omitted_probe_rows=omitted_rows,
        selection_status=status,
        authority_posture="impact_cone_selection_only_not_probe_generation",
    )
    return _with_hash(
        report_without_hash,
        object_kind="repo_behavioral_impact_cone_selection_report",
        hash_field="canonical_output_hash",
    )


def build_lock_staleness_report(
    *,
    manifest: RepoBehavioralReplayManifest | dict[str, object],
    expected_manifest_hash: str | None = None,
    actual_manifest_hash: str | None = None,
    expected_owner_surface_map_hash: str | None = None,
    actual_owner_surface_map_hash: str | None = None,
    expected_canonicalization_profile_hash: str | None = None,
    actual_canonicalization_profile_hash: str | None = None,
    expected_suite_root_hash: str | None = None,
    actual_suite_root_hash: str | None = None,
    expected_candidate_artifact_hash: str | None = None,
    actual_candidate_artifact_hash: str | None = None,
    expected_hob_otb_handoff_hash: str | None = None,
    actual_hob_otb_handoff_hash: str | None = None,
    staleness_report_ref: str | None = None,
) -> RepoBehavioralLockStalenessReport:
    loaded_manifest = (
        manifest
        if isinstance(manifest, RepoBehavioralReplayManifest)
        else RepoBehavioralReplayManifest.model_validate(manifest)
    )
    comparisons: list[tuple[StaleReasonKind, str, str | None, str | None]] = [
        (
            "manifest_hash_changed",
            loaded_manifest.manifest_id,
            expected_manifest_hash or loaded_manifest.manifest_hash,
            actual_manifest_hash or loaded_manifest.manifest_hash,
        ),
        (
            "owner_surface_map_hash_changed",
            loaded_manifest.owner_surface_map_ref,
            expected_owner_surface_map_hash or loaded_manifest.owner_surface_map_hash,
            actual_owner_surface_map_hash or loaded_manifest.owner_surface_map_hash,
        ),
        (
            "canonicalization_profile_hash_changed",
            loaded_manifest.canonicalization_profile_ref,
            expected_canonicalization_profile_hash
            or loaded_manifest.canonicalization_profile_hash,
            actual_canonicalization_profile_hash
            or loaded_manifest.canonicalization_profile_hash,
        ),
        (
            "expected_observation_hash_changed",
            f"expected-observations:{loaded_manifest.manifest_id}",
            expected_suite_root_hash or loaded_manifest.suite_root_hash,
            actual_suite_root_hash or loaded_manifest.suite_root_hash,
        ),
    ]
    if expected_candidate_artifact_hash is not None or actual_candidate_artifact_hash is not None:
        comparisons.append(
            (
                "candidate_artifact_substrate_hash_changed",
                f"candidate-artifact:{loaded_manifest.manifest_id}",
                expected_candidate_artifact_hash,
                actual_candidate_artifact_hash,
            )
        )
    if expected_hob_otb_handoff_hash is not None or actual_hob_otb_handoff_hash is not None:
        comparisons.append(
            (
                "hob_otb_handoff_hash_changed",
                f"hob-otb-handoff:{loaded_manifest.manifest_id}",
                expected_hob_otb_handoff_hash,
                actual_hob_otb_handoff_hash,
            )
        )
    stale_rows: list[StaleReasonRow] = []
    refresh_rows: list[RequiredRefreshRow] = []
    for index, (kind, object_ref, expected_hash, actual_hash) in enumerate(comparisons, start=1):
        if expected_hash is not None:
            expected_hash = _assert_sha256(expected_hash, field_name="expected_hash")
        if actual_hash is not None:
            actual_hash = _assert_sha256(actual_hash, field_name="actual_hash")
        if expected_hash == actual_hash:
            continue
        reason_ref = f"stale:{index}:{kind}"
        stale_rows.append(
            StaleReasonRow(
                stale_reason_ref=reason_ref,
                stale_reason_kind=kind,
                object_ref=object_ref,
                expected_hash=expected_hash,
                actual_hash=actual_hash,
                summary=f"{kind} for {object_ref}",
            )
        )
        refresh_rows.append(
            RequiredRefreshRow(
                refresh_ref=f"refresh:{index}:{kind}",
                stale_reason_ref=reason_ref,
                required_action=f"refresh {kind}",
            )
        )
    report_without_hash = RepoBehavioralLockStalenessReport(
        schema=REPO_BEHAVIORAL_LOCK_STALENESS_REPORT_SCHEMA,
        staleness_report_ref=staleness_report_ref
        or f"staleness:{loaded_manifest.manifest_id}",
        manifest_id=loaded_manifest.manifest_id,
        staleness_status="stale" if stale_rows else "fresh",
        stale_reason_rows=stale_rows,
        required_refresh_rows=refresh_rows,
        authority_posture="staleness_report_only_not_refresh_authority",
    )
    return _with_hash(
        report_without_hash,
        object_kind="repo_behavioral_lock_staleness_report",
        hash_field="canonical_output_hash",
    )


def _diff_by_probe(
    diffs: list[RepoBehavioralRegressionDiff],
) -> dict[str, RepoBehavioralRegressionDiff]:
    _assert_unique_rows(diffs, attr_name="probe_id", field_name="diffs")
    return {diff.probe_id: diff for diff in diffs}


def _probe_execution_by_probe(
    rows: list[ProbeExecutionRow],
) -> dict[str, ProbeExecutionRow]:
    _assert_unique_rows(rows, attr_name="probe_id", field_name="probe_execution_rows")
    return {row.probe_id: row for row in rows}


def build_no_regression_certificate(
    *,
    manifest: RepoBehavioralReplayManifest | dict[str, object],
    execution_report: RepoBehavioralReplayExecutionReport | dict[str, object],
    suite_root_report: RepoBehavioralSuiteRootHashReport | dict[str, object],
    diffs: list[RepoBehavioralRegressionDiff | dict[str, object]],
    impact_cone_report: RepoBehavioralImpactConeSelectionReport | dict[str, object],
    staleness_report: RepoBehavioralLockStalenessReport | dict[str, object],
    candidate_artifact_ref: str,
    candidate_artifact_hash: str,
    certificate_ref: str | None = None,
) -> RepoBehavioralNoRegressionCertificate:
    loaded_manifest = (
        manifest
        if isinstance(manifest, RepoBehavioralReplayManifest)
        else RepoBehavioralReplayManifest.model_validate(manifest)
    )
    loaded_execution = (
        execution_report
        if isinstance(execution_report, RepoBehavioralReplayExecutionReport)
        else RepoBehavioralReplayExecutionReport.model_validate(execution_report)
    )
    loaded_suite = (
        suite_root_report
        if isinstance(suite_root_report, RepoBehavioralSuiteRootHashReport)
        else RepoBehavioralSuiteRootHashReport.model_validate(suite_root_report)
    )
    loaded_diffs = [
        diff
        if isinstance(diff, RepoBehavioralRegressionDiff)
        else RepoBehavioralRegressionDiff.model_validate(diff)
        for diff in diffs
    ]
    loaded_impact = (
        impact_cone_report
        if isinstance(impact_cone_report, RepoBehavioralImpactConeSelectionReport)
        else RepoBehavioralImpactConeSelectionReport.model_validate(impact_cone_report)
    )
    loaded_staleness = (
        staleness_report
        if isinstance(staleness_report, RepoBehavioralLockStalenessReport)
        else RepoBehavioralLockStalenessReport.model_validate(staleness_report)
    )
    candidate_artifact_ref = _assert_non_empty_text(
        candidate_artifact_ref,
        field_name="candidate_artifact_ref",
    )
    candidate_artifact_hash = _assert_sha256(
        candidate_artifact_hash,
        field_name="candidate_artifact_hash",
    )
    known_gaps: list[str] = []
    posture: CertificatePosture
    if loaded_manifest.manifest_hash != loaded_execution.manifest_hash:
        known_gaps.append("manifest hash differs from execution report")
    if loaded_manifest.manifest_hash != loaded_suite.manifest_hash:
        known_gaps.append("manifest hash differs from suite-root report")
    if loaded_execution.manifest_id != loaded_manifest.manifest_id:
        known_gaps.append("execution report manifest_id differs from manifest")
    if loaded_suite.manifest_id != loaded_manifest.manifest_id:
        known_gaps.append("suite-root report manifest_id differs from manifest")
    if loaded_execution.candidate_artifact_ref != candidate_artifact_ref:
        known_gaps.append("candidate artifact ref differs from execution report")
    if loaded_execution.candidate_artifact_hash != candidate_artifact_hash:
        known_gaps.append("candidate artifact hash differs from execution report")
    if loaded_staleness.manifest_id != loaded_manifest.manifest_id:
        known_gaps.append("staleness report manifest_id differs from manifest")
        posture = "blocked_by_stale_manifest"
    elif loaded_staleness.staleness_status == "stale":
        reason_kinds = {row.stale_reason_kind for row in loaded_staleness.stale_reason_rows}
        known_gaps.extend(
            f"stale lock: {row.stale_reason_kind}" for row in loaded_staleness.stale_reason_rows
        )
        posture = (
            "blocked_by_stale_owner_surface_map"
            if "owner_surface_map_hash_changed" in reason_kinds
            else "blocked_by_stale_manifest"
        )
    elif loaded_impact.selection_status != "selected":
        if loaded_impact.selection_status == "blocked_by_missing_scope":
            known_gaps.append("impact cone blocked by missing scope")
        else:
            known_gaps.extend(
                f"impact cone blocked: {row.omission_reason}:{row.omitted_probe_ref}"
                for row in loaded_impact.omitted_probe_rows
                if row.blocker_ref is not None
            )
            if not known_gaps:
                known_gaps.append("impact cone blocked by missing sentinel")
        posture = "blocked_by_missing_sentinel"
    else:
        diff_by_probe = _diff_by_probe(loaded_diffs)
        execution_by_probe = _probe_execution_by_probe(loaded_execution.probe_execution_rows)
        for probe_ref in loaded_impact.selected_probe_refs:
            row = execution_by_probe.get(probe_ref)
            diff = diff_by_probe.get(probe_ref)
            if row is None or diff is None:
                known_gaps.append(f"selected sentinel not replayed: {probe_ref}")
                continue
            if row.execution_status != "completed":
                known_gaps.append(f"selected sentinel execution not completed: {probe_ref}")
            if diff.diff_status != "match":
                known_gaps.append(f"selected sentinel diff not match: {probe_ref}")
        if known_gaps:
            posture = (
                "blocked_by_replay_diff"
                if any("diff not match" in gap for gap in known_gaps)
                else "blocked_by_unreplayed_required_sentinel"
            )
        elif loaded_suite.suite_root_status != "match":
            known_gaps.append(f"suite root status is {loaded_suite.suite_root_status}")
            posture = "blocked_by_replay_diff"
        elif set(loaded_impact.selected_probe_refs) == set(loaded_manifest.probe_contract_refs):
            posture = "full_manifest_no_observed_regression"
        else:
            posture = "impact_cone_no_observed_regression"
    if known_gaps and posture in _READY_CERTIFICATE_POSTURES:
        posture = "blocked_by_replay_diff"
    covered_probe_refs = (
        loaded_impact.selected_probe_refs if posture in _READY_CERTIFICATE_POSTURES else []
    )
    covered_owner_surfaces = (
        loaded_impact.touched_owner_surfaces if posture in _READY_CERTIFICATE_POSTURES else []
    )
    certificate_without_hash = RepoBehavioralNoRegressionCertificate(
        schema=REPO_BEHAVIORAL_NO_REGRESSION_CERTIFICATE_SCHEMA,
        certificate_ref=certificate_ref or f"certificate:{loaded_impact.impact_cone_report_ref}",
        manifest_id=loaded_manifest.manifest_id,
        manifest_hash=loaded_manifest.manifest_hash or loaded_execution.manifest_hash,
        candidate_artifact_ref=candidate_artifact_ref,
        candidate_artifact_hash=candidate_artifact_hash,
        execution_report_ref=loaded_execution.execution_report_ref,
        impact_cone_report_ref=loaded_impact.impact_cone_report_ref,
        certificate_posture=posture,
        bounded_claim=(
            "bounded replay preservation over selected impact-cone sentinels"
            if posture == "impact_cone_no_observed_regression"
            else "bounded replay preservation over full manifest"
            if posture == "full_manifest_no_observed_regression"
            else "no-regression certificate blocked by known gaps"
        ),
        covered_probe_refs=covered_probe_refs,
        covered_owner_surfaces=covered_owner_surfaces,
        known_gaps=known_gaps,
        authority_posture="bounded_replay_preservation_only_not_product_truth",
    )
    return _with_hash(
        certificate_without_hash,
        object_kind="repo_behavioral_no_regression_certificate",
        hash_field="certificate_hash",
    )


def build_replay_integration_handoff(
    *,
    source_family: str,
    target_family: str,
    certificates: list[RepoBehavioralNoRegressionCertificate | dict[str, object]],
    staleness_reports: list[RepoBehavioralLockStalenessReport | dict[str, object]] | None = None,
    handoff_ref: str = "handoff:behavioral-replay-lock",
    bounded_use: str = "constrain downstream transitions with bounded replay preservation evidence",
) -> RepoBehavioralReplayIntegrationHandoff:
    loaded_certificates = [
        certificate
        if isinstance(certificate, RepoBehavioralNoRegressionCertificate)
        else RepoBehavioralNoRegressionCertificate.model_validate(certificate)
        for certificate in certificates
    ]
    loaded_staleness = [
        report
        if isinstance(report, RepoBehavioralLockStalenessReport)
        else RepoBehavioralLockStalenessReport.model_validate(report)
        for report in staleness_reports or []
    ]
    certificate_refs = [
        certificate.certificate_ref
        for certificate in loaded_certificates
        if certificate.certificate_posture in _READY_CERTIFICATE_POSTURES
    ]
    blocker_refs = [
        certificate.certificate_ref
        for certificate in loaded_certificates
        if certificate.certificate_posture in _BLOCKED_CERTIFICATE_POSTURES
    ]
    blocker_refs.extend(
        report.staleness_report_ref
        for report in loaded_staleness
        if report.staleness_status == "stale"
    )
    if any(
        certificate.certificate_posture == "blocked_by_missing_sentinel"
        for certificate in loaded_certificates
    ):
        handoff_status: IntegrationHandoffStatus = "blocked_by_missing_sentinel"
    elif blocker_refs:
        handoff_status = (
            "blocked_by_staleness"
            if any(report.staleness_status == "stale" for report in loaded_staleness)
            else "blocked_by_certificate"
        )
    else:
        handoff_status = "handoff_ready"
    handoff_without_hash = RepoBehavioralReplayIntegrationHandoff(
        schema=REPO_BEHAVIORAL_REPLAY_INTEGRATION_HANDOFF_SCHEMA,
        handoff_ref=handoff_ref,
        source_family=source_family,
        target_family=target_family,
        certificate_refs=certificate_refs,
        blocker_refs=blocker_refs,
        bounded_use=bounded_use,
        forbidden_promotions=sorted(_REQUIRED_FORBIDDEN_PROMOTIONS),
        handoff_status=handoff_status,
        authority_posture="handoff_constraint_only_not_transition_authority",
    )
    return _with_hash(
        handoff_without_hash,
        object_kind="repo_behavioral_replay_integration_handoff",
        hash_field="canonical_output_hash",
    )
