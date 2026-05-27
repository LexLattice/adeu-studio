from __future__ import annotations

import json
from pathlib import Path

from adeu_ir.repo import repo_root

from .otb_0a import (
    RepoPhaseBridgeContract,
    RepoPhaseCircuitCatalog,
    RepoPhaseLegalFrontierReport,
    RepoPhaseTransitionClaim,
    RepoPhaseTransitionValidationReport,
    RepoTransitionBrokerNonAuthorityGuardrail,
)
from .otb_0b import (
    RepoPhaseEvidencePosturePlan,
    RepoPhaseGateExecutionPlan,
    RepoPhaseOperationalizationReport,
    RepoPhaseTransitionClosureReport,
    RepoPhaseWorkerBatonContract,
)
from .otb_0c import (
    RepoPhaseStaleObjectInvalidationReport,
    RepoPhaseTransitionDeltaAttributionLedger,
    RepoTransitionBrokerFamilyCloseoutAlignment,
    RepoTransitionBrokerIntegrationHandoff,
)


def _write_schema(path: Path, schema: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(schema, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    mappings = [
        (
            RepoPhaseCircuitCatalog.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_circuit_catalog.v1.json",
            root / "spec" / "repo_phase_circuit_catalog.schema.json",
        ),
        (
            RepoPhaseBridgeContract.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_bridge_contract.v1.json",
            root / "spec" / "repo_phase_bridge_contract.schema.json",
        ),
        (
            RepoPhaseTransitionClaim.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_transition_claim.v1.json",
            root / "spec" / "repo_phase_transition_claim.schema.json",
        ),
        (
            RepoPhaseTransitionValidationReport.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_transition_validation_report.v1.json",
            root / "spec" / "repo_phase_transition_validation_report.schema.json",
        ),
        (
            RepoPhaseLegalFrontierReport.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_legal_frontier_report.v1.json",
            root / "spec" / "repo_phase_legal_frontier_report.schema.json",
        ),
        (
            RepoTransitionBrokerNonAuthorityGuardrail.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_transition_broker_non_authority_guardrail.v1.json",
            root / "spec" / "repo_transition_broker_non_authority_guardrail.schema.json",
        ),
        (
            RepoPhaseTransitionClosureReport.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_transition_closure_report.v1.json",
            root / "spec" / "repo_phase_transition_closure_report.schema.json",
        ),
        (
            RepoPhaseGateExecutionPlan.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_gate_execution_plan.v1.json",
            root / "spec" / "repo_phase_gate_execution_plan.schema.json",
        ),
        (
            RepoPhaseWorkerBatonContract.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_worker_baton_contract.v1.json",
            root / "spec" / "repo_phase_worker_baton_contract.schema.json",
        ),
        (
            RepoPhaseEvidencePosturePlan.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_evidence_posture_plan.v1.json",
            root / "spec" / "repo_phase_evidence_posture_plan.schema.json",
        ),
        (
            RepoPhaseOperationalizationReport.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_operationalization_report.v1.json",
            root / "spec" / "repo_phase_operationalization_report.schema.json",
        ),
        (
            RepoPhaseTransitionDeltaAttributionLedger.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_transition_delta_attribution_ledger.v1.json",
            root / "spec" / "repo_phase_transition_delta_attribution_ledger.schema.json",
        ),
        (
            RepoPhaseStaleObjectInvalidationReport.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_phase_stale_object_invalidation_report.v1.json",
            root / "spec" / "repo_phase_stale_object_invalidation_report.schema.json",
        ),
        (
            RepoTransitionBrokerIntegrationHandoff.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_transition_broker_integration_handoff.v1.json",
            root / "spec" / "repo_transition_broker_integration_handoff.schema.json",
        ),
        (
            RepoTransitionBrokerFamilyCloseoutAlignment.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_transition_broker"
            / "schema"
            / "repo_transition_broker_family_closeout_alignment.v1.json",
            root / "spec" / "repo_transition_broker_family_closeout_alignment.schema.json",
        ),
    ]
    for schema, authoritative_path, mirror_path in mappings:
        _write_schema(authoritative_path, schema)
        _write_schema(mirror_path, schema)


if __name__ == "__main__":
    main()
