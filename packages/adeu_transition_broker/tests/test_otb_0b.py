from __future__ import annotations

from copy import deepcopy

import pytest
from adeu_transition_broker import (
    REPO_PHASE_BRIDGE_CONTRACT_SCHEMA,
    REPO_PHASE_CIRCUIT_CATALOG_SCHEMA,
    REPO_PHASE_TRANSITION_CLAIM_SCHEMA,
    BatonOutputRow,
    DBridge,
    EBridge,
    OBridge,
    PhaseArtifactRow,
    RepoPhaseBridgeContract,
    RepoPhaseCircuitCatalog,
    RepoPhaseEvidencePosturePlan,
    RepoPhaseGateExecutionPlan,
    RepoPhaseTransitionClaim,
    RepoPhaseTransitionClosureReport,
    RepoPhaseWorkerBatonContract,
    RequiredObjectRow,
    UBridge,
    build_worker_baton_contract,
    canonical_hash,
    compute_transition_closure,
    emit_operationalization_report,
    plan_evidence_posture,
    plan_transition_gates,
    validate_transition,
)
from pydantic import ValidationError


def _catalog_payload() -> dict[str, object]:
    return {
        "schema": REPO_PHASE_CIRCUIT_CATALOG_SCHEMA,
        "circuit_id": "program-reconstruction",
        "circuit_version": "v0-test",
        "circuit_authority": "support",
        "shared_vocabulary_ref": "docs/support/example.md#vocabulary",
        "allowed_status_vocabulary": [
            "blocked",
            "conflict_isolated",
            "invalid",
            "stale",
            "valid_for_broker_frontier",
        ],
        "phase_rows": [
            {
                "phase_id": "blind_utility_descent",
                "phase_label": "Blind Utility Descent",
                "phase_kind": "semantic_descent",
                "allowed_input_object_kinds": ["visible_packet"],
                "allowed_output_object_kinds": ["utility_obligation_set"],
                "forbidden_evidence_kinds": ["post_eval_pressure"],
                "authority_layer": "support",
            },
            {
                "phase_id": "utility_program_reconciliation",
                "phase_label": "Utility Program Reconciliation",
                "phase_kind": "reconciliation",
                "allowed_input_object_kinds": ["utility_obligation_set"],
                "allowed_output_object_kinds": ["program_ontology_patch"],
                "forbidden_evidence_kinds": ["post_eval_pressure"],
                "authority_layer": "support",
            },
            {
                "phase_id": "implementation",
                "phase_label": "Implementation",
                "phase_kind": "implementation",
                "allowed_input_object_kinds": ["program_ontology_patch"],
                "allowed_output_object_kinds": ["candidate_witness"],
                "forbidden_evidence_kinds": ["post_eval_pressure"],
                "authority_layer": "support",
            },
        ],
        "transition_rows": [
            {
                "transition_id": "T03",
                "from_phase": "blind_utility_descent",
                "to_phase": "utility_program_reconciliation",
                "bridge_contract_ref": "bridge:T03",
                "transition_kind": "utility_reconciliation_input",
                "default_failure_route": "frontier:repair",
            },
            {
                "transition_id": "T04",
                "from_phase": "utility_program_reconciliation",
                "to_phase": "implementation",
                "bridge_contract_ref": "bridge:T04",
                "transition_kind": "implementation_handoff_input",
                "default_failure_route": "frontier:repair",
            },
        ],
    }


def _catalog() -> RepoPhaseCircuitCatalog:
    catalog_without_hash = RepoPhaseCircuitCatalog.model_validate(_catalog_payload())
    payload = catalog_without_hash.model_dump(mode="json", exclude_none=True)
    payload["circuit_hash"] = canonical_hash(catalog_without_hash, drop_keys={"circuit_hash"})
    return RepoPhaseCircuitCatalog.model_validate(payload)


def _bridge(
    catalog: RepoPhaseCircuitCatalog,
    *,
    transition_id: str = "T03",
    from_phase: str = "blind_utility_descent",
    to_phase: str = "utility_program_reconciliation",
    transition_kind: str = "utility_reconciliation_input",
    object_kind: str = "utility_obligation_set",
    artifact_ref: str = "artifact:T03",
    obligation_ref: str = "obligation:T03",
    supported_readiness_postures: list[str] | None = None,
) -> RepoPhaseBridgeContract:
    bridge_without_hash = RepoPhaseBridgeContract(
        schema=REPO_PHASE_BRIDGE_CONTRACT_SCHEMA,
        bridge_contract_ref=f"bridge:{transition_id}",
        circuit_id=catalog.circuit_id,
        circuit_version=catalog.circuit_version,
        circuit_hash=catalog.circuit_hash or canonical_hash(catalog, drop_keys={"circuit_hash"}),
        transition_id=transition_id,
        from_phase=from_phase,
        to_phase=to_phase,
        O_bridge=OBridge(
            required_objects=[
                RequiredObjectRow(
                    object_kind=object_kind,
                    required_artifact_ref=artifact_ref,
                    required_source_phase=from_phase,
                    required_authority_layer="support",
                    required_file_hash=f"sha256:file:{transition_id}",
                    required_canonical_payload_hash=f"sha256:payload:{transition_id}",
                    required_semantic_object_hash=f"sha256:semantic:{transition_id}",
                    required_evidence_boundary_hash=f"sha256:evidence:{transition_id}",
                    required_obligation_set_hash=f"sha256:obligation:{transition_id}",
                    required_object_identity_claim="same_visible_packet",
                    required_freshness_basis=["evidence_boundary_current"],
                )
            ],
            object_identity_checks=["same_visible_packet"],
            required_artifact_hash_checks=["file_hash", "canonical_payload_hash"],
            transformation_claims=[],
            stale_object_checks=["evidence_boundary_current"],
        ),
        E_bridge=EBridge(
            required_evidence=[f"evidence:{transition_id}"],
            forbidden_evidence=[],
            evidence_boundary_rules=["clean_first_pass_allowed"],
            warrant_requirements=[],
        ),
        D_bridge=DBridge(
            obligations_created=[],
            obligations_preserved=[obligation_ref],
            obligations_discharged=[],
            obligations_blocked_or_deferred=[],
            forbidden_silent_drops=True,
        ),
        U_bridge=UBridge(
            purpose=[transition_kind],
            next_allowed_phases=[to_phase],
            forbidden_promotions=[],
            failure_routes=["frontier:repair"],
            supported_readiness_postures=supported_readiness_postures or ["scoped_ready"],
            maximum_supported_posture=(supported_readiness_postures or ["scoped_ready"])[-1],
        ),
    )
    payload = bridge_without_hash.model_dump(mode="json", exclude_none=True)
    payload["bridge_hash"] = canonical_hash(bridge_without_hash, drop_keys={"bridge_hash"})
    return RepoPhaseBridgeContract.model_validate(payload)


def _claim(
    catalog: RepoPhaseCircuitCatalog,
    *,
    transition_id: str = "T03",
    from_phase: str = "blind_utility_descent",
    to_phase: str = "utility_program_reconciliation",
    transition_kind: str = "utility_reconciliation_input",
    artifact_ref: str = "artifact:T03",
    evidence_ref: str = "evidence:T03",
    obligation_ref: str = "obligation:T03",
) -> RepoPhaseTransitionClaim:
    payload: dict[str, object] = {
        "schema": REPO_PHASE_TRANSITION_CLAIM_SCHEMA,
        "transition_claim_ref": f"claim:{transition_id}",
        "claiming_actor_ref": "orchestrator:test",
        "claim_source": "orchestrator",
        "circuit_id": catalog.circuit_id,
        "circuit_version": catalog.circuit_version,
        "circuit_hash": catalog.circuit_hash or canonical_hash(catalog, drop_keys={"circuit_hash"}),
        "from_phase": from_phase,
        "to_phase": to_phase,
        "transition_id": transition_id,
        "claimed_transition_kind": transition_kind,
        "claimed_readiness_posture": "scoped_ready",
        "claimed_evidence_posture": "clean_first_pass_allowed",
        "claimed_promotion": "none",
        "artifact_refs": [artifact_ref],
        "evidence_refs": [evidence_ref],
        "obligation_transfer_refs": [obligation_ref],
        "intended_use": transition_kind,
    }
    claim_without_hash = RepoPhaseTransitionClaim.model_validate(payload)
    payload = claim_without_hash.model_dump(mode="json", exclude_none=True)
    payload["claim_hash"] = canonical_hash(claim_without_hash, drop_keys={"claim_hash"})
    return RepoPhaseTransitionClaim.model_validate(payload)


def _artifact(
    catalog: RepoPhaseCircuitCatalog,
    bridge: RepoPhaseBridgeContract,
    *,
    transition_id: str = "T03",
    from_phase: str = "blind_utility_descent",
    object_kind: str = "utility_obligation_set",
    artifact_ref: str = "artifact:T03",
) -> PhaseArtifactRow:
    return PhaseArtifactRow.model_validate(
        {
            "artifact_ref": artifact_ref,
            "artifact_kind": object_kind,
            "source_phase": from_phase,
            "authority_layer": "support",
            "file_hash": f"sha256:file:{transition_id}",
            "canonical_payload_hash": f"sha256:payload:{transition_id}",
            "semantic_object_hash": f"sha256:semantic:{transition_id}",
            "catalog_hash": catalog.circuit_hash
            or canonical_hash(catalog, drop_keys={"circuit_hash"}),
            "bridge_hash": bridge.bridge_hash or canonical_hash(bridge, drop_keys={"bridge_hash"}),
            "evidence_boundary_hash": f"sha256:evidence:{transition_id}",
            "obligation_set_hash": f"sha256:obligation:{transition_id}",
            "object_identity_claim": "same_visible_packet",
            "evidence_refs": [f"evidence:{transition_id}"],
            "freshness_basis": ["evidence_boundary_current"],
        }
    )


def _evidence(transition_id: str = "T03") -> dict[str, object]:
    return {
        "evidence_ref": f"evidence:{transition_id}",
        "evidence_kind": "visible_spec",
        "source_phase": "blind_utility_descent",
        "authority_layer": "support",
        "boundary_posture": "clean_first_pass_allowed",
        "clean_first_pass_posture": "clean",
        "evidence_hash": f"sha256:evidence-row:{transition_id}",
        "derived_from_evidence_refs": [],
        "contamination_tags": [],
    }


def _obligation(
    *,
    transition_id: str = "T03",
    source_phase: str = "blind_utility_descent",
    target_phase: str = "utility_program_reconciliation",
) -> dict[str, object]:
    return {
        "obligation_ref": f"obligation:{transition_id}",
        "source_phase": source_phase,
        "target_phase": target_phase,
        "transfer_status": "preserved",
        "preservation_required": True,
    }


def _valid_case(
    *,
    transition_id: str = "T03",
    from_phase: str = "blind_utility_descent",
    to_phase: str = "utility_program_reconciliation",
    transition_kind: str = "utility_reconciliation_input",
    object_kind: str = "utility_obligation_set",
    supported_readiness_postures: list[str] | None = None,
):
    catalog = _catalog()
    artifact_ref = f"artifact:{transition_id}"
    bridge = _bridge(
        catalog,
        transition_id=transition_id,
        from_phase=from_phase,
        to_phase=to_phase,
        transition_kind=transition_kind,
        object_kind=object_kind,
        artifact_ref=artifact_ref,
        obligation_ref=f"obligation:{transition_id}",
        supported_readiness_postures=supported_readiness_postures,
    )
    report = validate_transition(
        catalog=catalog,
        bridge=bridge,
        transition_claim=_claim(
            catalog,
            transition_id=transition_id,
            from_phase=from_phase,
            to_phase=to_phase,
            transition_kind=transition_kind,
            artifact_ref=artifact_ref,
            evidence_ref=f"evidence:{transition_id}",
            obligation_ref=f"obligation:{transition_id}",
        ),
        artifacts=[
            _artifact(
                catalog,
                bridge,
                transition_id=transition_id,
                from_phase=from_phase,
                object_kind=object_kind,
                artifact_ref=artifact_ref,
            )
        ],
        evidence=[_evidence(transition_id)],
        obligations=[
            _obligation(
                transition_id=transition_id,
                source_phase=from_phase,
                target_phase=to_phase,
            )
        ],
    )
    payload = report.model_dump(mode="json", exclude_none=True)
    payload["canonical_output_hash"] = canonical_hash(report, drop_keys={"canonical_output_hash"})
    return catalog, bridge, report.model_validate(payload)


def _closure() -> RepoPhaseTransitionClosureReport:
    catalog, bridge, report = _valid_case()
    return compute_transition_closure(
        catalog=catalog,
        bridge_contracts=[bridge],
        validation_reports=[report],
        known_risk_refs={"T03": "risk:scoped"},
    )


def test_valid_a_reports_produce_scoped_closure_rows() -> None:
    closure = _closure()

    assert closure.closure_rows[0].transition_id == "T03"
    assert closure.closure_rows[0].closure_status == "scoped_ready"
    assert closure.closure_rows[0].closure_basis == "scoped_ready_with_known_risk"
    assert closure.closure_rows[0].known_risk_ref == "risk:scoped"


def test_blocking_a_validation_report_blocks_closure() -> None:
    catalog, bridge, _report = _valid_case()
    blocked = validate_transition(
        catalog=catalog,
        bridge=bridge,
        transition_claim=_claim(catalog),
        artifacts=[],
        evidence=[_evidence()],
        obligations=[_obligation()],
    )
    closure = compute_transition_closure(
        catalog=catalog,
        bridge_contracts=[bridge],
        validation_reports=[blocked],
    )

    assert closure.closure_rows[0].closure_status == "blocked"
    assert closure.closure_rows[0].closure_basis == "blocked_by_A_validation"
    assert closure.frontier_summary_rows


def test_input_validation_report_hash_mismatch_fails_closed() -> None:
    catalog, bridge, report = _valid_case()

    with pytest.raises(ValueError, match="hash mismatch"):
        compute_transition_closure(
            catalog=catalog,
            bridge_contracts=[bridge],
            validation_reports=[report],
            input_validation_report_hashes={
                report.transition_validation_report_ref: "sha256:wrong",
            },
        )


def test_closure_posture_cannot_exceed_weakest_transition() -> None:
    closure = _closure()
    payload = deepcopy(closure.model_dump(mode="json", exclude_none=True))
    payload["closure_rows"][0]["readiness_posture"] = "gold_ready"
    payload.pop("canonical_output_hash", None)

    with pytest.raises(ValidationError):
        RepoPhaseTransitionClosureReport.model_validate(payload)


def test_representative_only_cannot_claim_gold_or_official_readiness() -> None:
    closure = _closure()
    payload = deepcopy(closure.model_dump(mode="json", exclude_none=True))
    payload["closure_rows"][0]["closure_status"] = "representative_only"
    payload["closure_rows"][0]["closure_basis"] = "representative_only"
    payload["closure_rows"][0]["readiness_posture"] = "official_ready"
    payload["closure_rows"][0]["maximum_supported_posture"] = "official_ready"
    payload["closure_rows"][0].pop("known_risk_ref", None)
    payload.pop("canonical_output_hash", None)

    with pytest.raises(ValidationError):
        RepoPhaseTransitionClosureReport.model_validate(payload)


def test_scoped_ready_without_known_risk_ref_fails_closed() -> None:
    catalog, bridge, report = _valid_case()

    with pytest.raises(ValidationError, match="known_risk_ref"):
        compute_transition_closure(
            catalog=catalog,
            bridge_contracts=[bridge],
            validation_reports=[report],
        )


def test_gate_plan_with_execution_authority_fails_closed() -> None:
    plan = plan_transition_gates(_closure())
    payload = deepcopy(plan.model_dump(mode="json", exclude_none=True))
    payload["gate_plan_rows"][0]["plan_authority_posture"] = "run_this_gate"
    payload.pop("canonical_output_hash", None)

    with pytest.raises(ValidationError):
        RepoPhaseGateExecutionPlan.model_validate(payload)


def test_worker_baton_with_dispatch_authority_fails_closed() -> None:
    baton = build_worker_baton_contract(_closure())
    payload = deepcopy(baton.model_dump(mode="json", exclude_none=True))
    payload["baton_authority_posture"] = "dispatch_worker"
    payload.pop("canonical_output_hash", None)

    with pytest.raises(ValidationError):
        RepoPhaseWorkerBatonContract.model_validate(payload)


def test_worker_baton_forbidden_input_fails_closed() -> None:
    with pytest.raises(ValidationError, match="forbidden_inputs"):
        RepoPhaseWorkerBatonContract(
            schema="repo_phase_worker_baton_contract@1",
            worker_baton_contract_ref="baton:bad",
            transition_id="T03",
            source_phase_refs=["blind_utility_descent"],
            target_phase="utility_program_reconciliation",
            allowed_inputs=["artifact:forbidden"],
            required_outputs=[
                BatonOutputRow(
                    output_kind="utility_program_reconciliation:closeout",
                    target_phase="utility_program_reconciliation",
                )
            ],
            forbidden_inputs=["artifact:forbidden"],
            forbidden_promotions=[],
            required_closeout_rows=["worker_closeout"],
            baton_authority_posture="baton_contract_only_not_dispatch_authority",
        )


def test_worker_baton_output_outside_target_phase_fails_closed() -> None:
    closure = _closure()

    with pytest.raises(ValidationError, match="outside target_phase"):
        build_worker_baton_contract(
            closure,
            required_outputs=[
                {
                    "output_kind": "implementation:closeout",
                    "target_phase": "implementation",
                }
            ],
        )


def test_evidence_posture_plan_without_equivalence_checks_fails_closed() -> None:
    with pytest.raises(ValidationError, match="equivalence checks"):
        RepoPhaseEvidencePosturePlan(
            schema="repo_phase_evidence_posture_plan@1",
            evidence_posture_plan_ref="evidence-plan:bad",
            transition_id="T03",
            current_evidence_posture="clean_first_pass_allowed",
            target_evidence_posture="official_like_pressure",
            required_equivalence_checks=[],
            forbidden_evidence_leaks=[],
            official_readiness_requirements=[],
            plan_authority_posture="plan_only_not_observed_evidence",
        )


def test_operationalization_report_remains_non_executing_and_non_authoritative() -> None:
    closure = _closure()
    gate_plan = plan_transition_gates(closure)
    baton = build_worker_baton_contract(closure)
    evidence_plan = plan_evidence_posture(closure)
    report = emit_operationalization_report(
        closure,
        gate_plan=gate_plan,
        baton_contract=baton,
        evidence_plan=evidence_plan,
    )

    assert (
        report.operationalization_authority_posture
        == "operationalization_summary_only_not_execution_authority"
    )
    assert "official_eval_authority_not_granted" in report.handoff_constraints
    assert "T03" in report.recommended_next_frontier


def test_shuffled_input_order_preserves_output_order_and_hashes() -> None:
    catalog = _catalog()
    catalog_a, bridge_a, report_a = _valid_case()
    catalog_b, bridge_b, report_b = _valid_case(
        transition_id="T04",
        from_phase="utility_program_reconciliation",
        to_phase="implementation",
        transition_kind="implementation_handoff_input",
        object_kind="program_ontology_patch",
    )
    assert catalog_a == catalog_b == catalog
    first = compute_transition_closure(
        catalog=catalog,
        bridge_contracts=[bridge_b, bridge_a],
        validation_reports=[report_b, report_a],
        known_risk_refs={"T03": "risk:T03", "T04": "risk:T04"},
    )
    second = compute_transition_closure(
        catalog=catalog,
        bridge_contracts=[bridge_a, bridge_b],
        validation_reports=[report_a, report_b],
        known_risk_refs={"T04": "risk:T04", "T03": "risk:T03"},
    )

    assert [row.transition_id for row in first.closure_rows] == ["T03", "T04"]
    assert first.canonical_output_hash == second.canonical_output_hash
