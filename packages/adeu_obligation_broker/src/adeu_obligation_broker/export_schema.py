from __future__ import annotations

import json
from pathlib import Path

from adeu_ir.repo import repo_root

from .hob_0a import (
    RepoHierarchicalObligationCatalog,
    RepoInheritedObligationLedger,
    RepoObligationActivationAssessment,
    RepoObligationBrokerNonAuthorityGuardrail,
    RepoObligationTraversalValidationReport,
)
from .hob_0b import (
    RepoObligationClosureReport,
    RepoObligationImplementationBatchContract,
    RepoObligationNextFrontierReport,
    RepoObligationOperationalizationReport,
    RepoObligationProbeMatrixPlan,
)
from .hob_0c import (
    RepoObligationBrokerFamilyCloseoutAlignment,
    RepoObligationBrokerIntegrationHandoff,
    RepoObligationDeltaAttributionLedger,
    RepoObligationStaleLedgerInvalidationReport,
)


def _write_schema(path: Path, schema: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(schema, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    mappings = [
        (
            RepoHierarchicalObligationCatalog.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_hierarchical_obligation_catalog.v1.json",
            root / "spec" / "repo_hierarchical_obligation_catalog.schema.json",
        ),
        (
            RepoObligationActivationAssessment.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_obligation_activation_assessment.v1.json",
            root / "spec" / "repo_obligation_activation_assessment.schema.json",
        ),
        (
            RepoInheritedObligationLedger.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_inherited_obligation_ledger.v1.json",
            root / "spec" / "repo_inherited_obligation_ledger.schema.json",
        ),
        (
            RepoObligationTraversalValidationReport.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_obligation_traversal_validation_report.v1.json",
            root / "spec" / "repo_obligation_traversal_validation_report.schema.json",
        ),
        (
            RepoObligationBrokerNonAuthorityGuardrail.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_obligation_broker_non_authority_guardrail.v1.json",
            root / "spec" / "repo_obligation_broker_non_authority_guardrail.schema.json",
        ),
        (
            RepoObligationClosureReport.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_obligation_closure_report.v1.json",
            root / "spec" / "repo_obligation_closure_report.schema.json",
        ),
        (
            RepoObligationNextFrontierReport.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_obligation_next_frontier_report.v1.json",
            root / "spec" / "repo_obligation_next_frontier_report.schema.json",
        ),
        (
            RepoObligationProbeMatrixPlan.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_obligation_probe_matrix_plan.v1.json",
            root / "spec" / "repo_obligation_probe_matrix_plan.schema.json",
        ),
        (
            RepoObligationImplementationBatchContract.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_obligation_implementation_batch_contract.v1.json",
            root / "spec" / "repo_obligation_implementation_batch_contract.schema.json",
        ),
        (
            RepoObligationOperationalizationReport.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_obligation_operationalization_report.v1.json",
            root / "spec" / "repo_obligation_operationalization_report.schema.json",
        ),
        (
            RepoObligationDeltaAttributionLedger.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_obligation_delta_attribution_ledger.v1.json",
            root / "spec" / "repo_obligation_delta_attribution_ledger.schema.json",
        ),
        (
            RepoObligationStaleLedgerInvalidationReport.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_obligation_stale_ledger_invalidation_report.v1.json",
            root / "spec" / "repo_obligation_stale_ledger_invalidation_report.schema.json",
        ),
        (
            RepoObligationBrokerIntegrationHandoff.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_obligation_broker_integration_handoff.v1.json",
            root / "spec" / "repo_obligation_broker_integration_handoff.schema.json",
        ),
        (
            RepoObligationBrokerFamilyCloseoutAlignment.model_json_schema(by_alias=True),
            root
            / "packages"
            / "adeu_obligation_broker"
            / "schema"
            / "repo_obligation_broker_family_closeout_alignment.v1.json",
            root / "spec" / "repo_obligation_broker_family_closeout_alignment.schema.json",
        ),
    ]
    for schema, authoritative_path, mirror_path in mappings:
        _write_schema(authoritative_path, schema)
        _write_schema(mirror_path, schema)


if __name__ == "__main__":
    main()
