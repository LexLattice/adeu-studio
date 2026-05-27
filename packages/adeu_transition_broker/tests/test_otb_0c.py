from __future__ import annotations

from copy import deepcopy

import pytest
from adeu_transition_broker import (
    REPO_PHASE_TRANSITION_CLOSURE_REPORT_SCHEMA,
    AcceptedSurfaceRow,
    AttributionRow,
    ClosureRow,
    DeferredSurfaceRow,
    InvalidatedArtifactRow,
    InvalidationReasonRow,
    PhaseArtifactIdentityRow,
    RepoPhaseStaleObjectInvalidationReport,
    RepoPhaseTransitionDeltaAttributionLedger,
    RepoTransitionBrokerFamilyCloseoutAlignment,
    RepoTransitionBrokerIntegrationHandoff,
    RunDeltaInput,
    RunDeltaPressureRow,
    attribute_transition_delta,
    build_integration_handoff,
    canonical_hash,
    emit_family_closeout_alignment,
    invalidate_stale_phase_objects,
)
from pydantic import ValidationError


def _closure_report():
    closure = {
        "schema": REPO_PHASE_TRANSITION_CLOSURE_REPORT_SCHEMA,
        "transition_closure_report_ref": "closure:test",
        "circuit_id": "program-reconstruction",
        "circuit_version": "v0-test",
        "circuit_hash": "sha256:circuit",
        "input_validation_report_refs": ["validation:T03"],
        "input_validation_report_hashes": {"validation:T03": "sha256:validation"},
        "closure_rows": [
            ClosureRow(
                transition_id="T03",
                from_phase="utility_program_reconciliation",
                to_phase="implementation",
                closure_status="scoped_ready",
                readiness_posture="scoped_ready",
                closure_basis="scoped_ready_with_known_risk",
                blocking_frontier_refs=[],
                allowed_next_phase_refs=["implementation"],
                known_risk_ref="risk:T03",
                maximum_supported_posture="scoped_ready",
            )
        ],
        "frontier_summary_rows": [],
    }
    from adeu_transition_broker import RepoPhaseTransitionClosureReport

    report = RepoPhaseTransitionClosureReport.model_validate(closure)
    payload = report.model_dump(mode="json", exclude_none=True)
    payload["canonical_output_hash"] = canonical_hash(report, drop_keys={"canonical_output_hash"})
    return RepoPhaseTransitionClosureReport.model_validate(payload)


def _run_delta(
    *,
    pressure_kind: str = "official_failure",
    evidence_boundary_posture: str = "post_eval_pressure_only",
    transition_evidence_refs: list[str] | None = None,
    attribution_domain: str = "transition_bridge",
    earlier_unproven_transition_refs: list[str] | None = None,
) -> RunDeltaInput:
    return RunDeltaInput(
        run_delta_ref="run-delta:test",
        pressure_rows=[
            RunDeltaPressureRow(
                pressure_ref="pressure:T03",
                transition_id="T03",
                bridge_field="E_bridge",
                pressure_kind=pressure_kind,
                pressure_summary="official result applies pressure to evidence boundary",
                evidence_boundary_posture=evidence_boundary_posture,
                confidence_posture="candidate_pressure",
                recommended_route="hold_as_pressure_only",
                transition_evidence_refs=transition_evidence_refs or [],
                attribution_domain=attribution_domain,
                earlier_unproven_transition_refs=earlier_unproven_transition_refs or [],
            )
        ],
    )


def _artifact(
    *,
    object_hash: str = "sha256:object:a",
    catalog_hash: str = "sha256:catalog:a",
    bridge_contract_hash: str = "sha256:bridge:a",
    evidence_boundary_hash: str = "sha256:evidence:a",
    obligation_set_hash: str = "sha256:obligation:a",
    target_substrate_hash: str = "sha256:substrate:a",
    run_topology_hash: str = "sha256:topology:a",
) -> PhaseArtifactIdentityRow:
    return PhaseArtifactIdentityRow(
        artifact_ref="artifact:T03",
        object_hash=object_hash,
        catalog_hash=catalog_hash,
        bridge_contract_hash=bridge_contract_hash,
        evidence_boundary_hash=evidence_boundary_hash,
        obligation_set_hash=obligation_set_hash,
        target_substrate_hash=target_substrate_hash,
        run_topology_hash=run_topology_hash,
    )


def test_post_eval_pressure_row_remains_pressure_only() -> None:
    ledger = attribute_transition_delta([_closure_report()], _run_delta())

    assert ledger.evidence_boundary_posture == "post_eval_pressure_only"
    assert ledger.attribution_rows[0].evidence_boundary_posture == "post_eval_pressure_only"
    assert ledger.attribution_rows[0].recommended_route == "hold_as_pressure_only"


def test_score_movement_without_bridge_evidence_fails_closed() -> None:
    with pytest.raises(ValidationError, match="score movement"):
        _run_delta(pressure_kind="score_movement")


def test_clean_first_pass_label_on_official_pressure_fails_closed() -> None:
    with pytest.raises(ValidationError, match="clean first-pass"):
        _run_delta(evidence_boundary_posture="clean_first_pass_allowed")


def test_clean_ledger_rejects_any_non_clean_attribution_row() -> None:
    delta = _run_delta(
        pressure_kind="assertion_failure",
        evidence_boundary_posture="clean_first_pass_disallowed",
    )

    with pytest.raises(ValidationError, match="cannot make the ledger clean first-pass"):
        attribute_transition_delta(
            [_closure_report()],
            delta,
            evidence_boundary_posture="clean_first_pass_allowed",
        )


def test_missing_evidence_boundary_posture_fails_closed() -> None:
    payload = {
        "attribution_ref": "attribution:T03",
        "transition_id": "T03",
        "bridge_field": "E_bridge",
        "pressure_kind": "official_failure",
        "pressure_summary": "missing boundary posture",
        "run_delta_refs": ["run-delta:test"],
        "confidence_posture": "candidate_pressure",
        "recommended_route": "hold_as_pressure_only",
    }

    with pytest.raises(ValidationError):
        AttributionRow.model_validate(payload)


def test_earlier_unproven_bridge_dominates_product_attribution() -> None:
    with pytest.raises(ValidationError, match="earlier unproven"):
        _run_delta(
            attribution_domain="product_semantics",
            earlier_unproven_transition_refs=["T02"],
        )


def test_object_hash_change_emits_stale_object_invalidation() -> None:
    report = invalidate_stale_phase_objects(
        [_artifact(object_hash="sha256:old")],
        [_artifact(object_hash="sha256:new")],
    )

    assert report.invalidated_artifact_rows[0].artifact_ref == "artifact:T03"
    assert report.invalidated_artifact_rows[0].invalidation_reasons == ["object_hash_changed"]
    assert report.required_revalidation_frontier == ["artifact:T03"]


def test_distinct_hash_changes_emit_distinct_invalidation_reasons() -> None:
    report = invalidate_stale_phase_objects(
        [_artifact()],
        [
            _artifact(
                catalog_hash="sha256:catalog:b",
                bridge_contract_hash="sha256:bridge:b",
                evidence_boundary_hash="sha256:evidence:b",
                obligation_set_hash="sha256:obligation:b",
                target_substrate_hash="sha256:substrate:b",
                run_topology_hash="sha256:topology:b",
            )
        ],
    )

    assert report.invalidated_artifact_rows[0].invalidation_reasons == [
        "bridge_contract_hash_changed",
        "catalog_hash_changed",
        "evidence_boundary_changed",
        "obligation_set_changed",
        "run_topology_changed",
        "target_substrate_changed",
    ]


def test_invalidation_reason_rows_must_match_each_artifact_reason_set() -> None:
    with pytest.raises(ValidationError, match="match each artifact reason set"):
        RepoPhaseStaleObjectInvalidationReport(
            schema="repo_phase_stale_object_invalidation_report@1",
            stale_object_invalidation_report_ref="invalidation:bad",
            input_artifact_refs=["artifact:T03"],
            new_artifact_refs=["artifact:T03"],
            invalidated_artifact_rows=[
                InvalidatedArtifactRow(
                    artifact_ref="artifact:T03",
                    invalidation_reasons=["object_hash_changed"],
                )
            ],
            invalidation_reason_rows=[
                InvalidationReasonRow(
                    invalidation_reason="catalog_hash_changed",
                    artifact_refs=["artifact:T03"],
                )
            ],
            required_revalidation_frontier=["artifact:T03"],
        )


def test_handoff_cannot_grant_implementation_or_execution_authority() -> None:
    ledger = attribute_transition_delta([_closure_report()], _run_delta())
    invalidation = invalidate_stale_phase_objects(
        [_artifact(object_hash="sha256:old")],
        [_artifact(object_hash="sha256:new")],
    )

    with pytest.raises(ValidationError, match="cannot grant authority"):
        build_integration_handoff(
            ledger,
            invalidation,
            "programbench-repair",
            allowed_consumption=["implementation_authority"],
        )


def test_family_closeout_cannot_mark_unaccepted_slice_complete() -> None:
    with pytest.raises(ValidationError, match="accepted surface"):
        emit_family_closeout_alignment(
            accepted_surfaces=[],
            deferred_surfaces=[],
            completed_slices=["OTB-0-C"],
        )


def test_family_closeout_cannot_mark_undeferred_slice_unimplemented() -> None:
    with pytest.raises(ValidationError, match="deferred surface"):
        emit_family_closeout_alignment(
            accepted_surfaces=[],
            deferred_surfaces=[],
            unimplemented_slices=["future-family"],
        )


def test_shuffled_input_order_preserves_output_order_and_hashes() -> None:
    closure = _closure_report()
    first_delta = RunDeltaInput(
        run_delta_ref="run-delta:test",
        pressure_rows=[
            RunDeltaPressureRow(
                pressure_ref="pressure:b",
                transition_id="T03",
                bridge_field="U_bridge",
                pressure_kind="local_probe_delta",
                pressure_summary="probe pressure",
                evidence_boundary_posture="local_locked_probe_delta",
            ),
            RunDeltaPressureRow(
                pressure_ref="pressure:a",
                transition_id="T03",
                bridge_field="E_bridge",
                pressure_kind="official_failure",
                pressure_summary="official pressure",
                evidence_boundary_posture="post_eval_pressure_only",
            ),
        ],
    )
    second_payload = deepcopy(first_delta.model_dump(mode="json"))
    second_payload["pressure_rows"] = list(reversed(second_payload["pressure_rows"]))
    first = attribute_transition_delta([closure], first_delta)
    second = attribute_transition_delta([closure], RunDeltaInput.model_validate(second_payload))

    assert [row.attribution_ref for row in first.attribution_rows] == [
        "otb-0c-attribution:pressure:a",
        "otb-0c-attribution:pressure:b",
    ]
    assert first.canonical_output_hash == second.canonical_output_hash


def test_integration_handoff_remains_constrained_and_non_authoritative() -> None:
    ledger = attribute_transition_delta([_closure_report()], _run_delta())
    invalidation = invalidate_stale_phase_objects(
        [_artifact(object_hash="sha256:old")],
        [_artifact(object_hash="sha256:new")],
    )
    handoff = build_integration_handoff(ledger, invalidation, "programbench-repair")

    assert handoff.handoff_posture == "handoff_constraints_only_not_authority"
    assert "implementation_authority" in handoff.forbidden_consumption
    assert "artifact:T03" in handoff.required_revalidation_rows


def test_family_closeout_alignment_records_accepted_and_deferred_surfaces() -> None:
    alignment = emit_family_closeout_alignment(
        accepted_surfaces=[
            AcceptedSurfaceRow(
                surface_ref="repo_phase_transition_delta_attribution_ledger@1",
                slice_ref="OTB-0-C",
            ),
            AcceptedSurfaceRow(
                surface_ref="repo_phase_stale_object_invalidation_report@1",
                slice_ref="OTB-0-C",
            ),
        ],
        deferred_surfaces=[
            DeferredSurfaceRow(
                surface_ref="official-result-governance",
                slice_ref="future-family",
                deferral_reason="outside OTB-0-C authority",
            )
        ],
        future_pressure_notes=["future family may consume pressure rows"],
    )

    assert isinstance(alignment, RepoTransitionBrokerFamilyCloseoutAlignment)
    assert alignment.completed_slices == ["OTB-0-C"]
    assert alignment.unimplemented_slices == ["future-family"]


def test_direct_handoff_overlap_validation_fails_closed() -> None:
    with pytest.raises(ValidationError, match="allowed_consumption"):
        RepoTransitionBrokerIntegrationHandoff(
            schema="repo_transition_broker_integration_handoff@1",
            transition_broker_integration_handoff_ref="handoff:bad",
            source_family="OTB-0",
            target_family_or_lane="programbench-repair",
            handoff_posture="handoff_constraints_only_not_authority",
            allowed_consumption=["consume_pressure_rows"],
            forbidden_consumption=["consume_pressure_rows"],
            pressure_rows=[],
            required_revalidation_rows=[],
        )


def test_direct_clean_ledger_validation_rejects_clean_first_pass_disallowed_row() -> None:
    with pytest.raises(ValidationError, match="cannot make the ledger clean first-pass"):
        RepoPhaseTransitionDeltaAttributionLedger(
            schema="repo_phase_transition_delta_attribution_ledger@1",
            transition_delta_attribution_ledger_ref="ledger:bad",
            circuit_id="program-reconstruction",
            circuit_version="v0-test",
            circuit_hash="sha256:circuit",
            input_closure_report_refs=["closure:test"],
            run_delta_ref="run-delta:test",
            attribution_rows=[
                AttributionRow(
                    attribution_ref="attribution:T03",
                    transition_id="T03",
                    bridge_field="E_bridge",
                    pressure_kind="assertion_failure",
                    pressure_summary="disallowed clean pass",
                    evidence_boundary_posture="clean_first_pass_disallowed",
                    run_delta_refs=["run-delta:test"],
                    confidence_posture="candidate_pressure",
                    recommended_route="hold_as_pressure_only",
                )
            ],
            evidence_boundary_posture="clean_first_pass_allowed",
        )
