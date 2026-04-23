from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .ux_ergonomics import (
    FROZEN_V67A_REQUIRED_EVIDENCE_COMPONENT_REFS,
    UX_COMPONENT_VISIBILITY_CONTRACT_SCHEMA,
    UX_ERGONOMIC_ADJUDICATION_REQUEST_SCHEMA,
    UX_ERGONOMIC_ADJUDICATION_RESULT_SCHEMA,
    UX_ERGONOMIC_CANDIDATE_PROJECTION_PROFILE_TABLE_SCHEMA,
    UX_ERGONOMIC_CASE_ENVELOPE_SCHEMA,
    UXComponentVisibilityContract,
    UXErgonomicActionTargetingClaim,
    UXErgonomicAdjudicationRequest,
    UXErgonomicAdjudicationResult,
    UXErgonomicCandidateProjectionProfileRow,
    UXErgonomicCandidateProjectionProfileTable,
    UXErgonomicCaseEnvelope,
    UXErgonomicRuntimeBridgeReport,
    UXErgonomicRuntimeMeasurementEvidence,
    UXErgonomicRuntimeMismatchRow,
    _assert_source_artifact_hashes_match_actual,
    _load_repo_relative_json_artifact,
)
from .ux_governance import (
    UX_CONFORMANCE_REPORT_SCHEMA,
    UX_MORPH_DIAGNOSTICS_SCHEMA,
    UXConformanceReport,
    UXMorphDiagnostics,
)

_REQUIRED_SOURCE_SCHEMAS = {
    UX_COMPONENT_VISIBILITY_CONTRACT_SCHEMA,
    UX_ERGONOMIC_CANDIDATE_PROJECTION_PROFILE_TABLE_SCHEMA,
    UX_ERGONOMIC_CASE_ENVELOPE_SCHEMA,
    UX_ERGONOMIC_ADJUDICATION_REQUEST_SCHEMA,
    UX_ERGONOMIC_ADJUDICATION_RESULT_SCHEMA,
}


@dataclass(slots=True)
class _RuntimeBridgeSourceBundle:
    visibility_contract_ref: str
    visibility_contract: UXComponentVisibilityContract
    candidate_projection_table_ref: str
    candidate_projection_table: UXErgonomicCandidateProjectionProfileTable
    case_envelope_ref: str
    case_envelope: UXErgonomicCaseEnvelope
    request_ref: str
    request: UXErgonomicAdjudicationRequest
    adjudication_result_ref: str
    adjudication_result: UXErgonomicAdjudicationResult
    ux_morph_diagnostics_ref_or_none: str | None
    ux_morph_diagnostics_or_none: UXMorphDiagnostics | None
    ux_conformance_report_ref_or_none: str | None
    ux_conformance_report_or_none: UXConformanceReport | None


def _invalid_bridge_report(
    *,
    runtime_measurement_evidence: UXErgonomicRuntimeMeasurementEvidence,
    bridge_status: str,
    mismatch_rows: list[dict[str, Any]],
) -> UXErgonomicRuntimeBridgeReport:
    return UXErgonomicRuntimeBridgeReport.model_validate(
        {
            "schema": "ux_ergonomic_runtime_bridge_report@1",
            "bridge_report_id": (
                f"{runtime_measurement_evidence.evidence_id}_computed_invalid_runtime_bridge"
            ),
            "reference_surface_family": runtime_measurement_evidence.reference_surface_family,
            "reference_instance_id": runtime_measurement_evidence.reference_instance_id,
            "request_ref": runtime_measurement_evidence.request_ref,
            "adjudication_result_ref": runtime_measurement_evidence.adjudication_result_ref,
            "runtime_measurement_evidence_ref": runtime_measurement_evidence.evidence_id,
            "ux_morph_diagnostics_ref_or_none": (
                runtime_measurement_evidence.ux_morph_diagnostics_ref_or_none
            ),
            "ux_conformance_report_ref_or_none": (
                runtime_measurement_evidence.ux_conformance_report_ref_or_none
            ),
            "source_artifact_refs": runtime_measurement_evidence.source_artifact_refs,
            "source_artifact_hashes": [
                row.model_dump(mode="json")
                for row in runtime_measurement_evidence.source_artifact_hashes
            ],
            "bridge_status": bridge_status,
            "mismatch_rows": mismatch_rows,
        }
    )


def _load_runtime_bridge_source_bundle(
    *,
    runtime_measurement_evidence: UXErgonomicRuntimeMeasurementEvidence,
) -> _RuntimeBridgeSourceBundle:
    _assert_source_artifact_hashes_match_actual(
        runtime_measurement_evidence.source_artifact_hashes,
        field_name="ux_ergonomic_runtime_measurement_evidence.source_artifact_hashes",
    )

    visibility_contract_ref: str | None = None
    visibility_contract: UXComponentVisibilityContract | None = None
    candidate_projection_table_ref: str | None = None
    candidate_projection_table: UXErgonomicCandidateProjectionProfileTable | None = None
    case_envelope_ref: str | None = None
    case_envelope: UXErgonomicCaseEnvelope | None = None
    request_ref: str | None = None
    request: UXErgonomicAdjudicationRequest | None = None
    adjudication_result_ref: str | None = None
    adjudication_result: UXErgonomicAdjudicationResult | None = None
    diagnostics_ref: str | None = None
    diagnostics: UXMorphDiagnostics | None = None
    conformance_ref: str | None = None
    conformance: UXConformanceReport | None = None

    seen_required_schemas: set[str] = set()
    for index, ref in enumerate(runtime_measurement_evidence.source_artifact_refs):
        payload = _load_repo_relative_json_artifact(
            ref=ref,
            field_name=f"ux_ergonomic_runtime_measurement_evidence.source_artifact_refs[{index}]",
        )
        if not isinstance(payload, dict) or "schema" not in payload:
            raise ValueError(
                "runtime bridge source artifacts must be typed canonical json payloads"
            )
        schema = payload["schema"]
        if schema in seen_required_schemas and schema in _REQUIRED_SOURCE_SCHEMAS:
            raise ValueError(f"runtime bridge source bundle must not repeat schema {schema!r}")
        if schema == UX_COMPONENT_VISIBILITY_CONTRACT_SCHEMA:
            visibility_contract_ref = ref
            visibility_contract = UXComponentVisibilityContract.model_validate(payload)
            seen_required_schemas.add(schema)
        elif schema == UX_ERGONOMIC_CANDIDATE_PROJECTION_PROFILE_TABLE_SCHEMA:
            candidate_projection_table_ref = ref
            candidate_projection_table = UXErgonomicCandidateProjectionProfileTable.model_validate(
                payload
            )
            seen_required_schemas.add(schema)
        elif schema == UX_ERGONOMIC_CASE_ENVELOPE_SCHEMA:
            case_envelope_ref = ref
            case_envelope = UXErgonomicCaseEnvelope.model_validate(payload)
            seen_required_schemas.add(schema)
        elif schema == UX_ERGONOMIC_ADJUDICATION_REQUEST_SCHEMA:
            request_ref = ref
            request = UXErgonomicAdjudicationRequest.model_validate(payload)
            seen_required_schemas.add(schema)
        elif schema == UX_ERGONOMIC_ADJUDICATION_RESULT_SCHEMA:
            adjudication_result_ref = ref
            adjudication_result = UXErgonomicAdjudicationResult.model_validate(payload)
            seen_required_schemas.add(schema)
        elif schema == UX_MORPH_DIAGNOSTICS_SCHEMA:
            diagnostics_ref = ref
            diagnostics = UXMorphDiagnostics.model_validate(payload)
        elif schema == UX_CONFORMANCE_REPORT_SCHEMA:
            conformance_ref = ref
            conformance = UXConformanceReport.model_validate(payload)

    missing = _REQUIRED_SOURCE_SCHEMAS - seen_required_schemas
    if missing:
        raise ValueError(
            f"runtime bridge source bundle is missing required schemas: {sorted(missing)!r}"
        )

    assert visibility_contract_ref is not None and visibility_contract is not None
    assert candidate_projection_table_ref is not None and candidate_projection_table is not None
    assert case_envelope_ref is not None and case_envelope is not None
    assert request_ref is not None and request is not None
    assert adjudication_result_ref is not None and adjudication_result is not None

    return _RuntimeBridgeSourceBundle(
        visibility_contract_ref=visibility_contract_ref,
        visibility_contract=visibility_contract,
        candidate_projection_table_ref=candidate_projection_table_ref,
        candidate_projection_table=candidate_projection_table,
        case_envelope_ref=case_envelope_ref,
        case_envelope=case_envelope,
        request_ref=request_ref,
        request=request,
        adjudication_result_ref=adjudication_result_ref,
        adjudication_result=adjudication_result,
        ux_morph_diagnostics_ref_or_none=diagnostics_ref,
        ux_morph_diagnostics_or_none=diagnostics,
        ux_conformance_report_ref_or_none=conformance_ref,
        ux_conformance_report_or_none=conformance,
    )


def _expected_candidate_row(
    *,
    candidate_projection_table: UXErgonomicCandidateProjectionProfileTable,
    candidate_profile_id: str,
) -> UXErgonomicCandidateProjectionProfileRow:
    for row in candidate_projection_table.candidate_rows:
        if row.candidate_profile_id == candidate_profile_id:
            return row
    raise ValueError(
        "runtime measurement evidence candidate_profile_id not found in candidate table"
    )


def _expected_action_claim(
    *,
    candidate_row: UXErgonomicCandidateProjectionProfileRow,
    action_ref: str,
) -> UXErgonomicActionTargetingClaim | None:
    for row in candidate_row.action_targeting_claims:
        if row.action_ref == action_ref:
            return row
    return None


def _bridge_status_for_mismatch_families(mismatch_families: set[str]) -> str:
    if not mismatch_families:
        return "advisory_clean"
    if "runtime_missing_measurement_for_required_obligation" in mismatch_families:
        return "advisory_incomplete_missing_evidence"
    return "advisory_drift_detected"


def evaluate_ux_ergonomic_runtime_bridge(
    *,
    runtime_measurement_evidence: UXErgonomicRuntimeMeasurementEvidence,
) -> UXErgonomicRuntimeBridgeReport:
    try:
        bundle = _load_runtime_bridge_source_bundle(
            runtime_measurement_evidence=runtime_measurement_evidence
        )
    except ValueError:
        return _invalid_bridge_report(
            runtime_measurement_evidence=runtime_measurement_evidence,
            bridge_status="invalid_basis_mismatch",
            mismatch_rows=[
                {
                    "mismatch_id": "runtime_source_hash_mismatch",
                    "mismatch_family": "runtime_source_hash_mismatch",
                    "candidate_profile_id_or_none": (
                        runtime_measurement_evidence.candidate_profile_id
                    ),
                }
            ],
        )

    request = bundle.request
    adjudication_result = bundle.adjudication_result
    if request.request_id != runtime_measurement_evidence.request_ref:
        return _invalid_bridge_report(
            runtime_measurement_evidence=runtime_measurement_evidence,
            bridge_status="invalid_basis_mismatch",
            mismatch_rows=[
                {
                    "mismatch_id": "runtime_source_hash_mismatch",
                    "mismatch_family": "runtime_source_hash_mismatch",
                    "candidate_profile_id_or_none": (
                        runtime_measurement_evidence.candidate_profile_id
                    ),
                    "source_ref_or_none": bundle.request_ref,
                }
            ],
        )
    if adjudication_result.result_id != runtime_measurement_evidence.adjudication_result_ref:
        return _invalid_bridge_report(
            runtime_measurement_evidence=runtime_measurement_evidence,
            bridge_status="invalid_basis_mismatch",
            mismatch_rows=[
                {
                    "mismatch_id": "runtime_source_hash_mismatch",
                    "mismatch_family": "runtime_source_hash_mismatch",
                    "candidate_profile_id_or_none": (
                        runtime_measurement_evidence.candidate_profile_id
                    ),
                    "source_ref_or_none": bundle.adjudication_result_ref,
                }
            ],
        )
    if adjudication_result.request_ref != request.request_id:
        return _invalid_bridge_report(
            runtime_measurement_evidence=runtime_measurement_evidence,
            bridge_status="invalid_basis_mismatch",
            mismatch_rows=[
                {
                    "mismatch_id": "runtime_source_hash_mismatch",
                    "mismatch_family": "runtime_source_hash_mismatch",
                    "candidate_profile_id_or_none": (
                        runtime_measurement_evidence.candidate_profile_id
                    ),
                }
            ],
        )
    if request.source_artifact_hashes != adjudication_result.source_artifact_hashes:
        return _invalid_bridge_report(
            runtime_measurement_evidence=runtime_measurement_evidence,
            bridge_status="invalid_basis_mismatch",
            mismatch_rows=[
                {
                    "mismatch_id": "runtime_source_hash_mismatch",
                    "mismatch_family": "runtime_source_hash_mismatch",
                    "candidate_profile_id_or_none": (
                        runtime_measurement_evidence.candidate_profile_id
                    ),
                }
            ],
        )
    if request.reference_surface_family != runtime_measurement_evidence.reference_surface_family:
        return _invalid_bridge_report(
            runtime_measurement_evidence=runtime_measurement_evidence,
            bridge_status="invalid_basis_mismatch",
            mismatch_rows=[
                {
                    "mismatch_id": "runtime_source_hash_mismatch",
                    "mismatch_family": "runtime_source_hash_mismatch",
                    "candidate_profile_id_or_none": (
                        runtime_measurement_evidence.candidate_profile_id
                    ),
                }
            ],
        )
    if request.reference_instance_id != runtime_measurement_evidence.reference_instance_id:
        return _invalid_bridge_report(
            runtime_measurement_evidence=runtime_measurement_evidence,
            bridge_status="invalid_basis_mismatch",
            mismatch_rows=[
                {
                    "mismatch_id": "runtime_source_hash_mismatch",
                    "mismatch_family": "runtime_source_hash_mismatch",
                    "candidate_profile_id_or_none": (
                        runtime_measurement_evidence.candidate_profile_id
                    ),
                }
            ],
        )

    if (
        runtime_measurement_evidence.ux_morph_diagnostics_ref_or_none
        != bundle.ux_morph_diagnostics_ref_or_none
    ):
        return _invalid_bridge_report(
            runtime_measurement_evidence=runtime_measurement_evidence,
            bridge_status="invalid_basis_mismatch",
            mismatch_rows=[
                {
                    "mismatch_id": "runtime_source_hash_mismatch",
                    "mismatch_family": "runtime_source_hash_mismatch",
                    "candidate_profile_id_or_none": (
                        runtime_measurement_evidence.candidate_profile_id
                    ),
                }
            ],
        )
    if (
        runtime_measurement_evidence.ux_conformance_report_ref_or_none
        != bundle.ux_conformance_report_ref_or_none
    ):
        return _invalid_bridge_report(
            runtime_measurement_evidence=runtime_measurement_evidence,
            bridge_status="invalid_basis_mismatch",
            mismatch_rows=[
                {
                    "mismatch_id": "runtime_source_hash_mismatch",
                    "mismatch_family": "runtime_source_hash_mismatch",
                    "candidate_profile_id_or_none": (
                        runtime_measurement_evidence.candidate_profile_id
                    ),
                }
            ],
        )

    expected_candidate = _expected_candidate_row(
        candidate_projection_table=bundle.candidate_projection_table,
        candidate_profile_id=runtime_measurement_evidence.candidate_profile_id,
    )
    feasible_rows_by_id = {
        row.candidate_profile_id: row for row in adjudication_result.feasible_candidate_rows
    }
    measurement_rows_by_component = {
        row.component_ref: row for row in runtime_measurement_evidence.measurement_rows
    }
    mismatch_rows: list[dict[str, Any]] = []

    def add_mismatch(
        *,
        mismatch_id: str,
        mismatch_family: str,
        candidate_profile_id_or_none: str | None = None,
        component_ref_or_none: str | None = None,
        obligation_id_or_none: str | None = None,
        source_ref_or_none: str | None = None,
    ) -> None:
        mismatch_rows.append(
            {
                "mismatch_id": mismatch_id,
                "mismatch_family": mismatch_family,
                "candidate_profile_id_or_none": candidate_profile_id_or_none,
                "component_ref_or_none": component_ref_or_none,
                "obligation_id_or_none": obligation_id_or_none,
                "source_ref_or_none": source_ref_or_none,
            }
        )

    if runtime_measurement_evidence.candidate_profile_id not in feasible_rows_by_id:
        add_mismatch(
            mismatch_id="runtime_candidate_profile_not_realized",
            mismatch_family="runtime_candidate_profile_not_realized",
            candidate_profile_id_or_none=runtime_measurement_evidence.candidate_profile_id,
        )

    expected_visibility_by_ref = {
        row.component_ref: row for row in expected_candidate.component_visibility_claims
    }

    expected_component_refs = set(expected_visibility_by_ref)
    expected_component_refs.add("action_cluster:commit-actions")
    for component_ref, row in measurement_rows_by_component.items():
        if component_ref not in expected_component_refs:
            add_mismatch(
                mismatch_id=f"runtime_unknown_component_ref_{component_ref.replace(':', '_')}",
                mismatch_family="runtime_unknown_component_ref",
                candidate_profile_id_or_none=runtime_measurement_evidence.candidate_profile_id,
                component_ref_or_none=component_ref,
                source_ref_or_none=row.source_ref,
            )

    for component_ref in FROZEN_V67A_REQUIRED_EVIDENCE_COMPONENT_REFS:
        row = measurement_rows_by_component.get(component_ref)
        if row is None or row.observed_visibility_state == "not_observed":
            family = (
                "runtime_trust_boundary_not_observed"
                if component_ref == "lane:trust-boundary-lane"
                else (
                    "runtime_commit_gate_not_observed_or_not_targetable"
                    if component_ref == "action_cluster:commit-actions"
                    else "runtime_required_evidence_not_observed"
                )
            )
            add_mismatch(
                mismatch_id=f"{family}_{component_ref.replace(':', '_')}",
                mismatch_family=family,
                candidate_profile_id_or_none=runtime_measurement_evidence.candidate_profile_id,
                component_ref_or_none=component_ref,
            )

    for component_ref, expected_claim in expected_visibility_by_ref.items():
        row = measurement_rows_by_component.get(component_ref)
        if row is None:
            continue
        if row.observed_reveal_transition_or_none == "unexpected_route_transition":
            add_mismatch(
                mismatch_id=(
                    f"runtime_unexpected_route_transition_{component_ref.replace(':', '_')}"
                ),
                mismatch_family="runtime_unexpected_route_transition",
                candidate_profile_id_or_none=runtime_measurement_evidence.candidate_profile_id,
                component_ref_or_none=component_ref,
                source_ref_or_none=row.source_ref,
            )
        if expected_claim.visibility_state == "continuously_visible":
            if row.observed_visibility_state != "continuously_visible":
                add_mismatch(
                    mismatch_id=f"runtime_visibility_drift_{component_ref.replace(':', '_')}",
                    mismatch_family="runtime_visibility_drift_from_adjudicated_claim",
                    candidate_profile_id_or_none=runtime_measurement_evidence.candidate_profile_id,
                    component_ref_or_none=component_ref,
                    source_ref_or_none=row.source_ref,
                )
        elif expected_claim.visibility_state == "same_context_reachable":
            if row.observed_visibility_state not in {
                "same_context_reachable",
                "continuously_visible",
            }:
                add_mismatch(
                    mismatch_id=f"runtime_visibility_drift_{component_ref.replace(':', '_')}",
                    mismatch_family="runtime_visibility_drift_from_adjudicated_claim",
                    candidate_profile_id_or_none=runtime_measurement_evidence.candidate_profile_id,
                    component_ref_or_none=component_ref,
                    source_ref_or_none=row.source_ref,
                )
            if (
                row.observed_visibility_state == "same_context_reachable"
                and (
                    row.observed_reveal_transition_or_none
                    != expected_claim.reveal_transition_or_none
                )
            ):
                add_mismatch(
                    mismatch_id=(
                        f"runtime_same_context_reveal_drift_{component_ref.replace(':', '_')}"
                    ),
                    mismatch_family="runtime_same_context_reveal_drift",
                    candidate_profile_id_or_none=runtime_measurement_evidence.candidate_profile_id,
                    component_ref_or_none=component_ref,
                    source_ref_or_none=row.source_ref,
                )

    if bundle.case_envelope.preferred_text_min_css_px_or_none is not None:
        required_text_floor = bundle.case_envelope.preferred_text_min_css_px_or_none.numeric_value
        for row in runtime_measurement_evidence.measurement_rows:
            if row.computed_font_size_css_px_or_none is None:
                continue
            if row.computed_font_size_css_px_or_none < required_text_floor:
                add_mismatch(
                    mismatch_id=(
                        "runtime_text_floor_below_adjudicated_floor_"
                        f"{row.component_ref.replace(':', '_')}"
                    ),
                    mismatch_family="runtime_text_floor_below_adjudicated_floor",
                    candidate_profile_id_or_none=runtime_measurement_evidence.candidate_profile_id,
                    component_ref_or_none=row.component_ref,
                    source_ref_or_none=row.source_ref,
                )

    commit_action = _expected_action_claim(
        candidate_row=expected_candidate,
        action_ref="submit-commit-request",
    )
    commit_row = measurement_rows_by_component.get("action_cluster:commit-actions")
    if commit_row is not None and commit_action is not None:
        measured_target_size = min(
            commit_row.measured_bounding_box_css_px.width,
            commit_row.measured_bounding_box_css_px.height,
        )
        if measured_target_size < commit_action.min_target_size_css_px:
            add_mismatch(
                mismatch_id="runtime_targetability_below_adjudicated_floor_commit_actions",
                mismatch_family="runtime_targetability_below_adjudicated_floor",
                candidate_profile_id_or_none=runtime_measurement_evidence.candidate_profile_id,
                component_ref_or_none="action_cluster:commit-actions",
                source_ref_or_none=commit_row.source_ref,
            )

    required_obligations = [
        row
        for row in adjudication_result.measurement_obligation_rows
        if row.candidate_profile_id == runtime_measurement_evidence.candidate_profile_id
    ]
    for obligation in required_obligations:
        if obligation.measurement_kind == "runtime_targetability_measurement":
            row = measurement_rows_by_component.get("action_cluster:commit-actions")
            if row is None:
                add_mismatch(
                    mismatch_id=f"runtime_missing_obligation_{obligation.obligation_id}",
                    mismatch_family="runtime_missing_measurement_for_required_obligation",
                    candidate_profile_id_or_none=runtime_measurement_evidence.candidate_profile_id,
                    obligation_id_or_none=obligation.obligation_id,
                )
        elif obligation.measurement_kind == "runtime_text_measurement":
            if not any(
                row.computed_font_size_css_px_or_none is not None
                for row in runtime_measurement_evidence.measurement_rows
            ):
                add_mismatch(
                    mismatch_id=f"runtime_missing_obligation_{obligation.obligation_id}",
                    mismatch_family="runtime_missing_measurement_for_required_obligation",
                    candidate_profile_id_or_none=runtime_measurement_evidence.candidate_profile_id,
                    obligation_id_or_none=obligation.obligation_id,
                )
        elif obligation.measurement_kind == "runtime_visibility_measurement":
            if not any(
                row.component_ref in FROZEN_V67A_REQUIRED_EVIDENCE_COMPONENT_REFS
                for row in runtime_measurement_evidence.measurement_rows
            ):
                add_mismatch(
                    mismatch_id=f"runtime_missing_obligation_{obligation.obligation_id}",
                    mismatch_family="runtime_missing_measurement_for_required_obligation",
                    candidate_profile_id_or_none=runtime_measurement_evidence.candidate_profile_id,
                    obligation_id_or_none=obligation.obligation_id,
                )

    for row in runtime_measurement_evidence.measurement_rows:
        if row.provenance_state != "measured_runtime" or row.source_kind != "playwright_replay":
            add_mismatch(
                mismatch_id=(
                    "runtime_measurement_provenance_inadmissible_"
                    f"{row.component_ref.replace(':', '_')}"
                ),
                mismatch_family="runtime_measurement_provenance_inadmissible",
                candidate_profile_id_or_none=runtime_measurement_evidence.candidate_profile_id,
                component_ref_or_none=row.component_ref,
                source_ref_or_none=row.source_ref,
            )

    mismatch_rows = sorted(
        (
            UXErgonomicRuntimeMismatchRow.model_validate(row).model_dump(
                mode="json",
                exclude_none=True,
            )
            for row in mismatch_rows
        ),
        key=lambda row: row["mismatch_id"],
    )
    mismatch_families = {row["mismatch_family"] for row in mismatch_rows}
    bridge_status = _bridge_status_for_mismatch_families(mismatch_families)
    return UXErgonomicRuntimeBridgeReport.model_validate(
        {
            "schema": "ux_ergonomic_runtime_bridge_report@1",
            "bridge_report_id": f"{runtime_measurement_evidence.evidence_id}_computed_v67c",
            "reference_surface_family": runtime_measurement_evidence.reference_surface_family,
            "reference_instance_id": runtime_measurement_evidence.reference_instance_id,
            "request_ref": runtime_measurement_evidence.request_ref,
            "adjudication_result_ref": runtime_measurement_evidence.adjudication_result_ref,
            "runtime_measurement_evidence_ref": runtime_measurement_evidence.evidence_id,
            "ux_morph_diagnostics_ref_or_none": (
                runtime_measurement_evidence.ux_morph_diagnostics_ref_or_none
            ),
            "ux_conformance_report_ref_or_none": (
                runtime_measurement_evidence.ux_conformance_report_ref_or_none
            ),
            "source_artifact_refs": runtime_measurement_evidence.source_artifact_refs,
            "source_artifact_hashes": [
                row.model_dump(mode="json")
                for row in runtime_measurement_evidence.source_artifact_hashes
            ],
            "bridge_status": bridge_status,
            "mismatch_rows": mismatch_rows,
        }
    )


def canonicalize_computed_ux_ergonomic_runtime_bridge_report_payload(
    *,
    runtime_measurement_evidence: UXErgonomicRuntimeMeasurementEvidence,
) -> dict[str, object]:
    report = evaluate_ux_ergonomic_runtime_bridge(
        runtime_measurement_evidence=runtime_measurement_evidence
    )
    return report.model_dump(mode="json", exclude_none=True)
