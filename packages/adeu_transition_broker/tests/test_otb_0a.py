from __future__ import annotations

from copy import deepcopy

import pytest
from adeu_transition_broker import (
    REPO_PHASE_BRIDGE_CONTRACT_SCHEMA,
    REPO_PHASE_CIRCUIT_CATALOG_SCHEMA,
    REPO_PHASE_TRANSITION_CLAIM_SCHEMA,
    DBridge,
    EBridge,
    OBridge,
    PhaseArtifactRow,
    RepoPhaseBridgeContract,
    RepoPhaseCircuitCatalog,
    RepoPhaseTransitionClaim,
    RequiredObjectRow,
    UBridge,
    canonical_hash,
    default_non_authority_guardrail,
    emit_legal_frontier,
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
            "valid_for_broker_frontier",
            "blocked",
            "invalid",
            "stale",
            "conflict_isolated",
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
            }
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
    forbidden_evidence: list[str] | None = None,
    next_allowed_phases: list[str] | None = None,
    forbidden_promotions: list[str] | None = None,
    supported_readiness_postures: list[str] | None = None,
) -> RepoPhaseBridgeContract:
    bridge_without_hash = RepoPhaseBridgeContract(
        schema=REPO_PHASE_BRIDGE_CONTRACT_SCHEMA,
        bridge_contract_ref="bridge:T03",
        circuit_id=catalog.circuit_id,
        circuit_version=catalog.circuit_version,
        circuit_hash=catalog.circuit_hash or canonical_hash(catalog, drop_keys={"circuit_hash"}),
        transition_id="T03",
        from_phase="blind_utility_descent",
        to_phase="utility_program_reconciliation",
        O_bridge=OBridge(
            required_objects=[
                RequiredObjectRow(
                    object_kind="utility_obligation_set",
                    required_artifact_ref="artifact:utility",
                    required_source_phase="blind_utility_descent",
                    required_authority_layer="support",
                    required_file_hash="sha256:file",
                    required_canonical_payload_hash="sha256:payload",
                    required_semantic_object_hash="sha256:semantic",
                    required_evidence_boundary_hash="sha256:evidence-boundary",
                    required_obligation_set_hash="sha256:obligation-set",
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
            required_evidence=["evidence:visible"],
            forbidden_evidence=forbidden_evidence or [],
            evidence_boundary_rules=["clean_first_pass_allowed"],
            warrant_requirements=[],
        ),
        D_bridge=DBridge(
            obligations_created=[],
            obligations_preserved=["obligation:utility-map"],
            obligations_discharged=[],
            obligations_blocked_or_deferred=[],
            forbidden_silent_drops=True,
        ),
        U_bridge=UBridge(
            purpose=["reconcile utility obligations"],
            next_allowed_phases=next_allowed_phases or ["utility_program_reconciliation"],
            forbidden_promotions=forbidden_promotions or [],
            failure_routes=["frontier:repair"],
            supported_readiness_postures=supported_readiness_postures or ["scoped_ready"],
            maximum_supported_posture=(
                supported_readiness_postures or ["scoped_ready"]
            )[-1],
        ),
    )
    payload = bridge_without_hash.model_dump(mode="json", exclude_none=True)
    payload["bridge_hash"] = canonical_hash(bridge_without_hash, drop_keys={"bridge_hash"})
    return RepoPhaseBridgeContract.model_validate(payload)


def _claim(catalog: RepoPhaseCircuitCatalog, **overrides: object) -> RepoPhaseTransitionClaim:
    payload: dict[str, object] = {
        "schema": REPO_PHASE_TRANSITION_CLAIM_SCHEMA,
        "transition_claim_ref": "claim:T03",
        "claiming_actor_ref": "orchestrator:test",
        "claim_source": "orchestrator",
        "circuit_id": catalog.circuit_id,
        "circuit_version": catalog.circuit_version,
        "circuit_hash": catalog.circuit_hash or canonical_hash(catalog, drop_keys={"circuit_hash"}),
        "from_phase": "blind_utility_descent",
        "to_phase": "utility_program_reconciliation",
        "transition_id": "T03",
        "claimed_transition_kind": "utility_reconciliation_input",
        "claimed_readiness_posture": "scoped_ready",
        "claimed_evidence_posture": "clean_first_pass_allowed",
        "claimed_promotion": "none",
        "artifact_refs": ["artifact:utility"],
        "evidence_refs": ["evidence:visible"],
        "obligation_transfer_refs": ["obligation:utility-map"],
        "intended_use": "map utility obligations into program ontology",
    }
    payload.update(overrides)
    claim_without_hash = RepoPhaseTransitionClaim.model_validate(payload)
    payload = claim_without_hash.model_dump(mode="json", exclude_none=True)
    payload["claim_hash"] = canonical_hash(claim_without_hash, drop_keys={"claim_hash"})
    return RepoPhaseTransitionClaim.model_validate(payload)


def _artifact(
    *,
    catalog: RepoPhaseCircuitCatalog | None = None,
    bridge: RepoPhaseBridgeContract | None = None,
    **overrides: object,
) -> PhaseArtifactRow:
    catalog = catalog or _catalog()
    bridge = bridge or _bridge(catalog)
    payload: dict[str, object] = {
        "artifact_ref": "artifact:utility",
        "artifact_kind": "utility_obligation_set",
        "source_phase": "blind_utility_descent",
        "authority_layer": "support",
        "file_hash": "sha256:file",
        "canonical_payload_hash": "sha256:payload",
        "semantic_object_hash": "sha256:semantic",
        "catalog_hash": catalog.circuit_hash or canonical_hash(catalog, drop_keys={"circuit_hash"}),
        "bridge_hash": bridge.bridge_hash or canonical_hash(bridge, drop_keys={"bridge_hash"}),
        "evidence_boundary_hash": "sha256:evidence-boundary",
        "obligation_set_hash": "sha256:obligation-set",
        "object_identity_claim": "same_visible_packet",
        "evidence_refs": ["evidence:visible"],
        "freshness_basis": ["evidence_boundary_current"],
    }
    payload.update(overrides)
    return PhaseArtifactRow.model_validate(payload)


def _visible_evidence(**overrides: object) -> dict[str, object]:
    payload: dict[str, object] = {
        "evidence_ref": "evidence:visible",
        "evidence_kind": "visible_spec",
        "source_phase": "blind_utility_descent",
        "authority_layer": "support",
        "boundary_posture": "clean_first_pass_allowed",
        "clean_first_pass_posture": "clean",
        "evidence_hash": "sha256:visible",
        "derived_from_evidence_refs": [],
        "contamination_tags": [],
    }
    payload.update(overrides)
    return payload


def _obligation(**overrides: object) -> dict[str, object]:
    payload: dict[str, object] = {
        "obligation_ref": "obligation:utility-map",
        "source_phase": "blind_utility_descent",
        "target_phase": "utility_program_reconciliation",
        "transfer_status": "preserved",
        "preservation_required": True,
    }
    payload.update(overrides)
    return payload


def _validate(
    *,
    catalog: RepoPhaseCircuitCatalog | None = None,
    bridge: RepoPhaseBridgeContract | None = None,
    claim: RepoPhaseTransitionClaim | None = None,
    artifacts: list[object] | None = None,
    evidence: list[object] | None = None,
    obligations: list[object] | None = None,
):
    catalog = catalog or _catalog()
    bridge = bridge or _bridge(catalog)
    claim = claim or _claim(catalog)
    return validate_transition(
        catalog=catalog,
        bridge=bridge,
        transition_claim=claim,
        artifacts=(
            artifacts if artifacts is not None else [_artifact(catalog=catalog, bridge=bridge)]
        ),
        evidence=evidence if evidence is not None else [_visible_evidence()],
        obligations=obligations if obligations is not None else [_obligation()],
    )


def test_valid_transition_emits_broker_frontier_status() -> None:
    report = _validate()
    frontier = emit_legal_frontier(report)

    assert report.validation_status == "valid_for_broker_frontier"
    assert report.bridge_consistency_status == "consistent"
    assert report.bridge_completeness_status == "complete"
    assert report.frontier_rows == []
    assert frontier.frontier_rows == []


def test_missing_required_object_fails_closed() -> None:
    report = _validate(artifacts=[])

    assert report.validation_status == "blocked"
    assert report.bridge_completeness_status == "missing_required_object"
    assert "MISSING_REQUIRED_OBJECT" in {row.diagnostic_code for row in report.diagnostic_rows}
    assert any(row.frontier_reason == "missing_object" for row in report.frontier_rows)


def test_artifact_hash_mismatch_is_stale() -> None:
    report = _validate(artifacts=[_artifact(file_hash="sha256:wrong")])

    assert report.validation_status == "stale"
    assert report.bridge_consistency_status == "hash_mismatch"
    assert "ARTIFACT_HASH_MISMATCH" in {row.diagnostic_code for row in report.diagnostic_rows}
    assert any(row.frontier_reason == "stale_artifact" for row in report.frontier_rows)


def test_artifact_catalog_hash_mismatch_is_stale() -> None:
    report = _validate(artifacts=[_artifact(catalog_hash="sha256:wrong-catalog")])

    assert report.validation_status == "stale"
    assert "ARTIFACT_CATALOG_HASH_MISMATCH" in {
        row.diagnostic_code for row in report.diagnostic_rows
    }


def test_artifact_bridge_hash_mismatch_is_stale() -> None:
    report = _validate(artifacts=[_artifact(bridge_hash="sha256:wrong-bridge")])

    assert report.validation_status == "stale"
    assert "ARTIFACT_BRIDGE_HASH_MISMATCH" in {
        row.diagnostic_code for row in report.diagnostic_rows
    }


def test_artifact_authority_layer_mismatch_fails_closed() -> None:
    report = _validate(artifacts=[_artifact(authority_layer="planning")])

    assert "ARTIFACT_AUTHORITY_LAYER_MISMATCH" in {
        row.diagnostic_code for row in report.diagnostic_rows
    }
    assert any(row.frontier_reason == "blocked_equivalence" for row in report.frontier_rows)


def test_duplicate_input_references_fail_closed() -> None:
    report = _validate(
        artifacts=[_artifact(), _artifact(file_hash="sha256:second")],
        evidence=[_visible_evidence(), _visible_evidence(evidence_hash="sha256:second")],
        obligations=[_obligation(), _obligation(preservation_required=False)],
    )

    assert {
        "DUPLICATE_ARTIFACT_REFERENCE",
        "DUPLICATE_EVIDENCE_REFERENCE",
        "DUPLICATE_OBLIGATION_REFERENCE",
    }.issubset({row.diagnostic_code for row in report.diagnostic_rows})


def test_direct_forbidden_evidence_fails_closed() -> None:
    catalog = _catalog()
    bridge = _bridge(catalog, forbidden_evidence=["post_eval_pressure"])
    claim = _claim(catalog, evidence_refs=["evidence:posteval"])
    report = _validate(
        catalog=catalog,
        bridge=bridge,
        claim=claim,
        evidence=[
            _visible_evidence(),
            _visible_evidence(
                evidence_ref="evidence:posteval",
                evidence_kind="post_eval_pressure",
                authority_layer="post_eval_pressure",
                boundary_posture="post_eval_pressure_only",
                clean_first_pass_posture="not_clean",
            ),
        ],
    )

    assert "FORBIDDEN_EVIDENCE_CONTAMINATION" in {
        row.diagnostic_code for row in report.diagnostic_rows
    }
    assert any(row.frontier_reason == "forbidden_evidence" for row in report.frontier_rows)


def test_transitive_forbidden_evidence_fails_closed() -> None:
    catalog = _catalog()
    bridge = _bridge(catalog, forbidden_evidence=["post_eval_pressure"])
    claim = _claim(catalog, evidence_refs=["evidence:summary"])
    report = _validate(
        catalog=catalog,
        bridge=bridge,
        claim=claim,
        evidence=[
            _visible_evidence(),
            _visible_evidence(
                evidence_ref="evidence:posteval",
                evidence_kind="post_eval_pressure",
                authority_layer="post_eval_pressure",
                boundary_posture="post_eval_pressure_only",
                clean_first_pass_posture="not_clean",
            ),
            _visible_evidence(
                evidence_ref="evidence:summary",
                evidence_kind="methodological_equivalence",
                evidence_hash="sha256:summary",
                derived_from_evidence_refs=["evidence:posteval"],
            ),
        ],
    )

    assert "FORBIDDEN_EVIDENCE_CONTAMINATION" in {
        row.diagnostic_code for row in report.diagnostic_rows
    }


def test_deep_transitive_forbidden_evidence_does_not_recurse() -> None:
    catalog = _catalog()
    bridge = _bridge(catalog, forbidden_evidence=["post_eval_pressure"])
    evidence = [
        _visible_evidence(
            evidence_ref="evidence:root",
            evidence_kind="methodological_equivalence",
            evidence_hash="sha256:root",
            derived_from_evidence_refs=["evidence:node-0000"],
        ),
        _visible_evidence(
            evidence_ref="evidence:posteval",
            evidence_kind="post_eval_pressure",
            authority_layer="post_eval_pressure",
            boundary_posture="post_eval_pressure_only",
            clean_first_pass_posture="not_clean",
            evidence_hash="sha256:posteval",
        ),
    ]
    for index in range(1100):
        parent_ref = f"evidence:node-{index + 1:04d}" if index < 1099 else "evidence:posteval"
        evidence.append(
            _visible_evidence(
                evidence_ref=f"evidence:node-{index:04d}",
                evidence_kind="methodological_equivalence",
                evidence_hash=f"sha256:node-{index:04d}",
                derived_from_evidence_refs=[parent_ref],
            )
        )
    claim = _claim(catalog, evidence_refs=["evidence:root"])
    report = _validate(catalog=catalog, bridge=bridge, claim=claim, evidence=evidence)

    assert "FORBIDDEN_EVIDENCE_CONTAMINATION" in {
        row.diagnostic_code for row in report.diagnostic_rows
    }


def test_required_artifact_evidence_is_validated_even_when_claim_omits_artifact() -> None:
    catalog = _catalog()
    bridge = _bridge(catalog, forbidden_evidence=["post_eval_pressure"])
    claim = _claim(catalog, artifact_refs=[], evidence_refs=["evidence:visible"])
    artifact = _artifact(
        catalog=catalog,
        bridge=bridge,
        evidence_refs=["evidence:posteval"],
    )
    report = _validate(
        catalog=catalog,
        bridge=bridge,
        claim=claim,
        artifacts=[artifact],
        evidence=[
            _visible_evidence(),
            _visible_evidence(
                evidence_ref="evidence:posteval",
                evidence_kind="post_eval_pressure",
                authority_layer="post_eval_pressure",
                boundary_posture="post_eval_pressure_only",
                clean_first_pass_posture="not_clean",
            ),
        ],
    )

    assert "FORBIDDEN_EVIDENCE_CONTAMINATION" in {
        row.diagnostic_code for row in report.diagnostic_rows
    }


def test_missing_evidence_boundary_posture_fails_closed() -> None:
    report = _validate(evidence=[_visible_evidence(boundary_posture=None)])

    assert "MISSING_EVIDENCE_BOUNDARY_POSTURE" in {
        row.diagnostic_code for row in report.diagnostic_rows
    }
    assert report.bridge_completeness_status == "missing_warrant"


def test_clean_first_pass_overclaim_fails_closed() -> None:
    report = _validate(
        evidence=[
            _visible_evidence(
                authority_layer="post_eval_pressure",
                boundary_posture="post_eval_pressure_only",
                clean_first_pass_posture="clean",
            )
        ]
    )

    assert "CLEAN_FIRST_PASS_POSTURE_OVERCLAIM" in {
        row.diagnostic_code for row in report.diagnostic_rows
    }


def test_silent_obligation_drop_fails_closed() -> None:
    report = _validate(obligations=[])

    assert "SILENT_OBLIGATION_DROP" in {row.diagnostic_code for row in report.diagnostic_rows}
    assert report.bridge_completeness_status == "missing_obligation_transfer"
    assert any(row.frontier_reason == "silent_obligation_drop" for row in report.frontier_rows)


def test_contract_created_obligation_transfer_is_required() -> None:
    catalog = _catalog()
    bridge = _bridge(catalog)
    payload = bridge.model_dump(mode="json", exclude_none=True)
    payload["D_bridge"]["obligations_created"] = ["obligation:new"]  # type: ignore[index]
    payload.pop("bridge_hash", None)
    bridge = RepoPhaseBridgeContract.model_validate(payload)
    report = _validate(catalog=catalog, bridge=bridge)

    assert "SILENT_OBLIGATION_DROP" in {row.diagnostic_code for row in report.diagnostic_rows}
    assert report.bridge_completeness_status == "missing_obligation_transfer"


def test_discharge_without_discharge_ref_fails_closed() -> None:
    report = _validate(obligations=[_obligation(transfer_status="discharged")])

    assert "DISCHARGE_REF_REQUIRED" in {row.diagnostic_code for row in report.diagnostic_rows}


def test_obligation_phase_mismatch_fails_closed() -> None:
    report = _validate(
        obligations=[
            _obligation(
                source_phase="implementation",
                target_phase="utility_program_reconciliation",
            )
        ]
    )

    assert "OBLIGATION_PHASE_MISMATCH" in {
        row.diagnostic_code for row in report.diagnostic_rows
    }
    assert report.bridge_completeness_status == "missing_equivalence"


def test_deferral_without_risk_posture_fails_closed() -> None:
    report = _validate(
        obligations=[
            _obligation(
                transfer_status="deferred",
                deferral_ref="deferral:utility",
            )
        ]
    )

    assert "DEFERRAL_RISK_POSTURE_REQUIRED" in {
        row.diagnostic_code for row in report.diagnostic_rows
    }
    assert report.bridge_completeness_status == "missing_deferral_risk"


def test_blocked_obligation_without_blocker_ref_fails_closed() -> None:
    report = _validate(obligations=[_obligation(transfer_status="blocked")])

    assert "BLOCKER_REF_REQUIRED" in {row.diagnostic_code for row in report.diagnostic_rows}
    assert report.bridge_completeness_status == "missing_warrant"


def test_target_phase_not_allowed_fails_closed() -> None:
    catalog = _catalog()
    bridge = _bridge(catalog, next_allowed_phases=["implementation"])
    report = _validate(catalog=catalog, bridge=bridge)

    assert "TARGET_PHASE_NOT_ALLOWED" in {row.diagnostic_code for row in report.diagnostic_rows}


def test_forbidden_promotion_fails_closed() -> None:
    catalog = _catalog()
    bridge = _bridge(catalog, forbidden_promotions=["scoped_to_official"])
    claim = _claim(catalog, claimed_promotion="scoped_to_official")
    report = _validate(catalog=catalog, bridge=bridge, claim=claim)

    assert "FORBIDDEN_PROMOTION" in {row.diagnostic_code for row in report.diagnostic_rows}
    assert any(row.frontier_reason == "illegal_promotion" for row in report.frontier_rows)


def test_transition_kind_mismatch_fails_closed() -> None:
    catalog = _catalog()
    claim = _claim(catalog, claimed_transition_kind="different_transition_kind")
    report = _validate(catalog=catalog, claim=claim)

    assert "TRANSITION_CLAIM_MISMATCH" in {
        row.diagnostic_code for row in report.diagnostic_rows
    }


def test_unsupported_posture_emits_downgrade_frontier() -> None:
    catalog = _catalog()
    bridge = _bridge(catalog, supported_readiness_postures=["scoped_method_test_only"])
    claim = _claim(catalog, claimed_readiness_posture="official_ready_candidate")
    report = _validate(catalog=catalog, bridge=bridge, claim=claim)

    assert "POSTURE_DOWNGRADE_REQUIRED" in {
        row.diagnostic_code for row in report.diagnostic_rows
    }
    assert any(
        row.frontier_reason == "posture_downgrade_required"
        and row.requested_posture == "official_ready_candidate"
        and row.maximum_supported_posture == "scoped_method_test_only"
        for row in report.frontier_rows
    )


def test_consistent_but_incomplete_bridge_is_not_promoted() -> None:
    catalog = _catalog()
    bridge = _bridge(catalog)
    payload = bridge.model_dump(mode="json", exclude_none=True)
    payload["E_bridge"]["required_evidence"] = ["evidence:missing"]
    payload.pop("bridge_hash", None)
    bridge = RepoPhaseBridgeContract.model_validate(payload)
    report = _validate(catalog=catalog, bridge=bridge)

    assert report.bridge_consistency_status == "consistent"
    assert report.bridge_completeness_status == "missing_required_evidence"
    assert report.validation_status == "blocked"


def test_unknown_status_vocabulary_fails_schema_validation() -> None:
    payload = _catalog_payload()
    payload["phase_rows"][0]["phase_kind"] = "probably_ok"  # type: ignore[index]

    with pytest.raises(ValidationError):
        RepoPhaseCircuitCatalog.model_validate(payload)


def test_shuffled_input_order_preserves_canonical_hash() -> None:
    catalog = _catalog()
    bridge = _bridge(catalog)
    claim = _claim(catalog)
    first = _validate(
        catalog=catalog,
        bridge=bridge,
        claim=claim,
        artifacts=[_artifact()],
        evidence=[_visible_evidence()],
        obligations=[_obligation()],
    )
    second = _validate(
        catalog=catalog,
        bridge=bridge,
        claim=claim,
        artifacts=list(reversed([_artifact()])),
        evidence=list(reversed([_visible_evidence()])),
        obligations=list(reversed([_obligation()])),
    )

    assert canonical_hash(first, drop_keys={"canonical_output_hash"}) == canonical_hash(
        second,
        drop_keys={"canonical_output_hash"},
    )


def test_legal_frontier_rows_deny_execution_authority() -> None:
    report = _validate(artifacts=[])
    frontier = emit_legal_frontier(report)

    assert frontier.frontier_rows
    assert {
        row.authority_posture for row in frontier.frontier_rows
    } == {"broker_validation_only_not_execution_authority"}


def test_non_authority_guardrail_denies_broker_overreach() -> None:
    guardrail = default_non_authority_guardrail()

    assert guardrail.semantic_authority_posture == "no_semantic_judgment_authority"
    assert guardrail.domain_ontology_authority_posture == "no_domain_ontology_authority"
    assert guardrail.hob_closure_authority_posture == "no_hob_closure_authority"
    assert guardrail.probe_generation_authority_posture == "no_probe_generation_authority"
    assert guardrail.probe_execution_authority_posture == "no_probe_execution_authority"
    assert guardrail.implementation_authority_posture == "no_implementation_authority"
    assert guardrail.worker_dispatch_authority_posture == "no_worker_dispatch_authority"
    assert guardrail.product_authority_posture == "no_product_authority"
    assert guardrail.official_eval_authority_posture == "no_official_eval_authority"
    assert guardrail.future_family_selection_posture == "no_future_family_selection_authority"


def test_canonical_hash_changes_when_claim_changes() -> None:
    catalog = _catalog()
    claim = _claim(catalog)
    payload = deepcopy(claim.model_dump(mode="json", exclude_none=True))
    payload["intended_use"] = "different intended use"
    payload.pop("claim_hash", None)
    changed = RepoPhaseTransitionClaim.model_validate(payload)

    assert canonical_hash(claim, drop_keys={"claim_hash"}) != canonical_hash(
        changed,
        drop_keys={"claim_hash"},
    )
