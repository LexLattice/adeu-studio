from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from adeu_ir.repo import repo_root

from .arc_series_cartography import (
    RepoArcMappingToolApplicabilityReport,
    RepoArcNamespaceMap,
    RepoArcSeriesCartography,
    RepoBranchPostureRegister,
    RepoEvidenceSurfaceIndex,
    RepoFamilyClosureRegister,
    RepoRecursiveCoordinateEmissionPlan,
    RepoSupportLineageRegister,
)
from .arc_series_cartography_derivation import (
    RepoArcCartographyDerivationManifest,
    RepoArcCartographyGapScanReport,
)
from .arc_series_cartography_tools import RepoArcCartographyToolRunEvidence
from .candidate_ratification_review import (
    RepoCandidateRatificationRequest,
    RepoRatificationAuthorityProfile,
    RepoRatificationRequestScopeBoundary,
)
from .candidate_review_adversarial import (
    RepoCandidateAdversarialReviewMatrix,
    RepoCandidateReviewConflictRegister,
    RepoCandidateReviewGapScan,
)
from .candidate_review_classification import (
    RepoCandidateEvidenceClassificationRecord,
    RepoCandidateEvidenceSourceIndex,
    RepoCandidateReviewBoundaryGuardrail,
)
from .candidate_review_summary import (
    RepoCandidatePreRatificationHandoff,
    RepoCandidateReviewClassificationSummary,
)
from .models import (
    RepoArcDependencyRegister,
    RepoArcDependencyRegisterV1,
    RepoDependencyGraph,
    RepoDescriptiveNormativeBindingFrame,
    RepoEntityCatalog,
    RepoOptimizationRegister,
    RepoSchemaFamilyRegistry,
    RepoSymbolCatalog,
    RepoTestIntentMatrix,
)
from .recursive_candidate_intake import (
    RepoCandidateNonAdoptionGuardrail,
    RepoCandidateSourceRegister,
    RepoRecursiveCandidateIntakeRecord,
)
from .recursive_candidate_intake_derivation import (
    RepoCandidateIntakeDerivationManifest,
    RepoCandidateIntakeGapScan,
)
from .recursive_candidate_intake_handoff import (
    RepoCandidateIntakePreV70Handoff,
    RepoOperatorIngressCandidateBinding,
    RepoRecursiveWorkflowResidueIntakeReport,
)

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _write_schema(path: Path, schema: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(schema, indent=2, sort_keys=True) + "\n"
    path.write_text(payload, encoding="utf-8")


def _assert_no_absolute_path_material(
    value: Any,
    *,
    repo_root_path: Path,
    node_path: str = "$",
) -> None:
    if isinstance(value, dict):
        for key in sorted(value):
            _assert_no_absolute_path_material(
                value[key],
                repo_root_path=repo_root_path,
                node_path=f"{node_path}.{key}",
            )
        return
    if isinstance(value, list):
        for index, item in enumerate(value):
            _assert_no_absolute_path_material(
                item,
                repo_root_path=repo_root_path,
                node_path=f"{node_path}[{index}]",
            )
        return
    if not isinstance(value, str):
        return

    normalized = value.replace("\\", "/")
    root_text = repo_root_path.as_posix()
    if root_text in normalized:
        raise RuntimeError(
            f"schema export contains repository absolute path material at {node_path}: {value!r}"
        )
    if _WINDOWS_ABSOLUTE_PATH_RE.search(value):
        raise RuntimeError(
            f"schema export contains Windows absolute path material at {node_path}: {value!r}"
        )
    if normalized.startswith("/home/") or normalized.startswith("/Users/"):
        raise RuntimeError(
            f"schema export contains user-home absolute path material at {node_path}: {value!r}"
        )


def main() -> None:
    root = repo_root(anchor=Path(__file__))
    dependency_register_v1_schema = RepoArcDependencyRegisterV1.model_json_schema(by_alias=True)
    dependency_register_schema = RepoArcDependencyRegister.model_json_schema(by_alias=True)
    dependency_graph_schema = RepoDependencyGraph.model_json_schema(by_alias=True)
    binding_frame_schema = RepoDescriptiveNormativeBindingFrame.model_json_schema(by_alias=True)
    optimization_register_schema = RepoOptimizationRegister.model_json_schema(by_alias=True)
    test_intent_matrix_schema = RepoTestIntentMatrix.model_json_schema(by_alias=True)
    registry_schema = RepoSchemaFamilyRegistry.model_json_schema(by_alias=True)
    catalog_schema = RepoEntityCatalog.model_json_schema(by_alias=True)
    symbol_catalog_schema = RepoSymbolCatalog.model_json_schema(by_alias=True)
    arc_series_cartography_schema = RepoArcSeriesCartography.model_json_schema(by_alias=True)
    arc_namespace_map_schema = RepoArcNamespaceMap.model_json_schema(by_alias=True)
    family_closure_register_schema = RepoFamilyClosureRegister.model_json_schema(by_alias=True)
    branch_posture_register_schema = RepoBranchPostureRegister.model_json_schema(by_alias=True)
    support_lineage_register_schema = RepoSupportLineageRegister.model_json_schema(by_alias=True)
    evidence_surface_index_schema = RepoEvidenceSurfaceIndex.model_json_schema(by_alias=True)
    tool_applicability_report_schema = RepoArcMappingToolApplicabilityReport.model_json_schema(
        by_alias=True
    )
    coordinate_emission_plan_schema = RepoRecursiveCoordinateEmissionPlan.model_json_schema(
        by_alias=True
    )
    cartography_derivation_manifest_schema = RepoArcCartographyDerivationManifest.model_json_schema(
        by_alias=True
    )
    cartography_gap_scan_report_schema = RepoArcCartographyGapScanReport.model_json_schema(
        by_alias=True
    )
    cartography_tool_run_evidence_schema = RepoArcCartographyToolRunEvidence.model_json_schema(
        by_alias=True
    )
    recursive_candidate_intake_schema = RepoRecursiveCandidateIntakeRecord.model_json_schema(
        by_alias=True
    )
    candidate_source_register_schema = RepoCandidateSourceRegister.model_json_schema(by_alias=True)
    candidate_non_adoption_guardrail_schema = RepoCandidateNonAdoptionGuardrail.model_json_schema(
        by_alias=True
    )
    candidate_intake_derivation_manifest_schema = (
        RepoCandidateIntakeDerivationManifest.model_json_schema(by_alias=True)
    )
    candidate_intake_gap_scan_schema = RepoCandidateIntakeGapScan.model_json_schema(by_alias=True)
    operator_ingress_candidate_binding_schema = (
        RepoOperatorIngressCandidateBinding.model_json_schema(by_alias=True)
    )
    recursive_workflow_residue_intake_report_schema = (
        RepoRecursiveWorkflowResidueIntakeReport.model_json_schema(by_alias=True)
    )
    candidate_intake_pre_v70_handoff_schema = RepoCandidateIntakePreV70Handoff.model_json_schema(
        by_alias=True
    )
    candidate_evidence_classification_record_schema = (
        RepoCandidateEvidenceClassificationRecord.model_json_schema(by_alias=True)
    )
    candidate_evidence_source_index_schema = RepoCandidateEvidenceSourceIndex.model_json_schema(
        by_alias=True
    )
    candidate_review_boundary_guardrail_schema = (
        RepoCandidateReviewBoundaryGuardrail.model_json_schema(by_alias=True)
    )
    candidate_adversarial_review_matrix_schema = (
        RepoCandidateAdversarialReviewMatrix.model_json_schema(by_alias=True)
    )
    candidate_review_conflict_register_schema = (
        RepoCandidateReviewConflictRegister.model_json_schema(by_alias=True)
    )
    candidate_review_gap_scan_schema = RepoCandidateReviewGapScan.model_json_schema(by_alias=True)
    candidate_review_classification_summary_schema = (
        RepoCandidateReviewClassificationSummary.model_json_schema(by_alias=True)
    )
    candidate_pre_ratification_handoff_schema = (
        RepoCandidatePreRatificationHandoff.model_json_schema(by_alias=True)
    )
    candidate_ratification_request_schema = RepoCandidateRatificationRequest.model_json_schema(
        by_alias=True
    )
    ratification_authority_profile_schema = RepoRatificationAuthorityProfile.model_json_schema(
        by_alias=True
    )
    ratification_request_scope_boundary_schema = (
        RepoRatificationRequestScopeBoundary.model_json_schema(by_alias=True)
    )

    _assert_no_absolute_path_material(dependency_register_v1_schema, repo_root_path=root)
    _assert_no_absolute_path_material(dependency_register_schema, repo_root_path=root)
    _assert_no_absolute_path_material(dependency_graph_schema, repo_root_path=root)
    _assert_no_absolute_path_material(binding_frame_schema, repo_root_path=root)
    _assert_no_absolute_path_material(optimization_register_schema, repo_root_path=root)
    _assert_no_absolute_path_material(test_intent_matrix_schema, repo_root_path=root)
    _assert_no_absolute_path_material(registry_schema, repo_root_path=root)
    _assert_no_absolute_path_material(catalog_schema, repo_root_path=root)
    _assert_no_absolute_path_material(symbol_catalog_schema, repo_root_path=root)
    _assert_no_absolute_path_material(arc_series_cartography_schema, repo_root_path=root)
    _assert_no_absolute_path_material(arc_namespace_map_schema, repo_root_path=root)
    _assert_no_absolute_path_material(family_closure_register_schema, repo_root_path=root)
    _assert_no_absolute_path_material(branch_posture_register_schema, repo_root_path=root)
    _assert_no_absolute_path_material(support_lineage_register_schema, repo_root_path=root)
    _assert_no_absolute_path_material(evidence_surface_index_schema, repo_root_path=root)
    _assert_no_absolute_path_material(tool_applicability_report_schema, repo_root_path=root)
    _assert_no_absolute_path_material(coordinate_emission_plan_schema, repo_root_path=root)
    _assert_no_absolute_path_material(cartography_derivation_manifest_schema, repo_root_path=root)
    _assert_no_absolute_path_material(cartography_gap_scan_report_schema, repo_root_path=root)
    _assert_no_absolute_path_material(cartography_tool_run_evidence_schema, repo_root_path=root)
    _assert_no_absolute_path_material(recursive_candidate_intake_schema, repo_root_path=root)
    _assert_no_absolute_path_material(candidate_source_register_schema, repo_root_path=root)
    _assert_no_absolute_path_material(candidate_non_adoption_guardrail_schema, repo_root_path=root)
    _assert_no_absolute_path_material(
        candidate_intake_derivation_manifest_schema, repo_root_path=root
    )
    _assert_no_absolute_path_material(candidate_intake_gap_scan_schema, repo_root_path=root)
    _assert_no_absolute_path_material(
        operator_ingress_candidate_binding_schema, repo_root_path=root
    )
    _assert_no_absolute_path_material(
        recursive_workflow_residue_intake_report_schema, repo_root_path=root
    )
    _assert_no_absolute_path_material(candidate_intake_pre_v70_handoff_schema, repo_root_path=root)
    _assert_no_absolute_path_material(
        candidate_evidence_classification_record_schema, repo_root_path=root
    )
    _assert_no_absolute_path_material(candidate_evidence_source_index_schema, repo_root_path=root)
    _assert_no_absolute_path_material(
        candidate_review_boundary_guardrail_schema, repo_root_path=root
    )
    _assert_no_absolute_path_material(
        candidate_adversarial_review_matrix_schema, repo_root_path=root
    )
    _assert_no_absolute_path_material(
        candidate_review_conflict_register_schema, repo_root_path=root
    )
    _assert_no_absolute_path_material(candidate_review_gap_scan_schema, repo_root_path=root)
    _assert_no_absolute_path_material(
        candidate_review_classification_summary_schema, repo_root_path=root
    )
    _assert_no_absolute_path_material(
        candidate_pre_ratification_handoff_schema, repo_root_path=root
    )
    _assert_no_absolute_path_material(candidate_ratification_request_schema, repo_root_path=root)
    _assert_no_absolute_path_material(ratification_authority_profile_schema, repo_root_path=root)
    _assert_no_absolute_path_material(
        ratification_request_scope_boundary_schema, repo_root_path=root
    )

    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_arc_dependency_register.v1.json",
        dependency_register_v1_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_arc_dependency_register.v2.json",
        dependency_register_schema,
    )
    _write_schema(
        root / "spec" / "repo_arc_dependency_register.schema.json",
        dependency_register_schema,
    )
    _write_schema(
        root / "packages" / "adeu_repo_description" / "schema" / "repo_dependency_graph.v1.json",
        dependency_graph_schema,
    )
    _write_schema(
        root / "spec" / "repo_dependency_graph.schema.json",
        dependency_graph_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_descriptive_normative_binding_frame.v1.json",
        binding_frame_schema,
    )
    _write_schema(
        root / "spec" / "repo_descriptive_normative_binding_frame.schema.json",
        binding_frame_schema,
    )
    _write_schema(
        root / "packages" / "adeu_repo_description" / "schema" / "repo_test_intent_matrix.v1.json",
        test_intent_matrix_schema,
    )
    _write_schema(
        root / "spec" / "repo_test_intent_matrix.schema.json",
        test_intent_matrix_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_optimization_register.v1.json",
        optimization_register_schema,
    )
    _write_schema(
        root / "spec" / "repo_optimization_register.schema.json",
        optimization_register_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_schema_family_registry.v1.json",
        registry_schema,
    )
    _write_schema(
        root / "spec" / "repo_schema_family_registry.schema.json",
        registry_schema,
    )
    _write_schema(
        root / "packages" / "adeu_repo_description" / "schema" / "repo_entity_catalog.v1.json",
        catalog_schema,
    )
    _write_schema(
        root / "spec" / "repo_entity_catalog.schema.json",
        catalog_schema,
    )
    _write_schema(
        root / "packages" / "adeu_repo_description" / "schema" / "repo_symbol_catalog.v1.json",
        symbol_catalog_schema,
    )
    _write_schema(
        root / "spec" / "repo_symbol_catalog.schema.json",
        symbol_catalog_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_arc_series_cartography.v1.json",
        arc_series_cartography_schema,
    )
    _write_schema(
        root / "spec" / "repo_arc_series_cartography.schema.json",
        arc_series_cartography_schema,
    )
    _write_schema(
        root / "packages" / "adeu_repo_description" / "schema" / "repo_arc_namespace_map.v1.json",
        arc_namespace_map_schema,
    )
    _write_schema(
        root / "spec" / "repo_arc_namespace_map.schema.json",
        arc_namespace_map_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_family_closure_register.v1.json",
        family_closure_register_schema,
    )
    _write_schema(
        root / "spec" / "repo_family_closure_register.schema.json",
        family_closure_register_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_branch_posture_register.v1.json",
        branch_posture_register_schema,
    )
    _write_schema(
        root / "spec" / "repo_branch_posture_register.schema.json",
        branch_posture_register_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_support_lineage_register.v1.json",
        support_lineage_register_schema,
    )
    _write_schema(
        root / "spec" / "repo_support_lineage_register.schema.json",
        support_lineage_register_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_evidence_surface_index.v1.json",
        evidence_surface_index_schema,
    )
    _write_schema(
        root / "spec" / "repo_evidence_surface_index.schema.json",
        evidence_surface_index_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_arc_mapping_tool_applicability_report.v1.json",
        tool_applicability_report_schema,
    )
    _write_schema(
        root / "spec" / "repo_arc_mapping_tool_applicability_report.schema.json",
        tool_applicability_report_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_recursive_coordinate_emission_plan.v1.json",
        coordinate_emission_plan_schema,
    )
    _write_schema(
        root / "spec" / "repo_recursive_coordinate_emission_plan.schema.json",
        coordinate_emission_plan_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_arc_cartography_derivation_manifest.v1.json",
        cartography_derivation_manifest_schema,
    )
    _write_schema(
        root / "spec" / "repo_arc_cartography_derivation_manifest.schema.json",
        cartography_derivation_manifest_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_arc_cartography_gap_scan_report.v1.json",
        cartography_gap_scan_report_schema,
    )
    _write_schema(
        root / "spec" / "repo_arc_cartography_gap_scan_report.schema.json",
        cartography_gap_scan_report_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_arc_cartography_tool_run_evidence.v1.json",
        cartography_tool_run_evidence_schema,
    )
    _write_schema(
        root / "spec" / "repo_arc_cartography_tool_run_evidence.schema.json",
        cartography_tool_run_evidence_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_recursive_candidate_intake_record.v1.json",
        recursive_candidate_intake_schema,
    )
    _write_schema(
        root / "spec" / "repo_recursive_candidate_intake_record.schema.json",
        recursive_candidate_intake_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_candidate_source_register.v1.json",
        candidate_source_register_schema,
    )
    _write_schema(
        root / "spec" / "repo_candidate_source_register.schema.json",
        candidate_source_register_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_candidate_non_adoption_guardrail.v1.json",
        candidate_non_adoption_guardrail_schema,
    )
    _write_schema(
        root / "spec" / "repo_candidate_non_adoption_guardrail.schema.json",
        candidate_non_adoption_guardrail_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_candidate_intake_derivation_manifest.v1.json",
        candidate_intake_derivation_manifest_schema,
    )
    _write_schema(
        root / "spec" / "repo_candidate_intake_derivation_manifest.schema.json",
        candidate_intake_derivation_manifest_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_candidate_intake_gap_scan.v1.json",
        candidate_intake_gap_scan_schema,
    )
    _write_schema(
        root / "spec" / "repo_candidate_intake_gap_scan.schema.json",
        candidate_intake_gap_scan_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_operator_ingress_candidate_binding.v1.json",
        operator_ingress_candidate_binding_schema,
    )
    _write_schema(
        root / "spec" / "repo_operator_ingress_candidate_binding.schema.json",
        operator_ingress_candidate_binding_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_recursive_workflow_residue_intake_report.v1.json",
        recursive_workflow_residue_intake_report_schema,
    )
    _write_schema(
        root / "spec" / "repo_recursive_workflow_residue_intake_report.schema.json",
        recursive_workflow_residue_intake_report_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_candidate_intake_pre_v70_handoff.v1.json",
        candidate_intake_pre_v70_handoff_schema,
    )
    _write_schema(
        root / "spec" / "repo_candidate_intake_pre_v70_handoff.schema.json",
        candidate_intake_pre_v70_handoff_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_candidate_evidence_classification_record.v1.json",
        candidate_evidence_classification_record_schema,
    )
    _write_schema(
        root / "spec" / "repo_candidate_evidence_classification_record.schema.json",
        candidate_evidence_classification_record_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_candidate_evidence_source_index.v1.json",
        candidate_evidence_source_index_schema,
    )
    _write_schema(
        root / "spec" / "repo_candidate_evidence_source_index.schema.json",
        candidate_evidence_source_index_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_candidate_review_boundary_guardrail.v1.json",
        candidate_review_boundary_guardrail_schema,
    )
    _write_schema(
        root / "spec" / "repo_candidate_review_boundary_guardrail.schema.json",
        candidate_review_boundary_guardrail_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_candidate_adversarial_review_matrix.v1.json",
        candidate_adversarial_review_matrix_schema,
    )
    _write_schema(
        root / "spec" / "repo_candidate_adversarial_review_matrix.schema.json",
        candidate_adversarial_review_matrix_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_candidate_review_conflict_register.v1.json",
        candidate_review_conflict_register_schema,
    )
    _write_schema(
        root / "spec" / "repo_candidate_review_conflict_register.schema.json",
        candidate_review_conflict_register_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_candidate_review_gap_scan.v1.json",
        candidate_review_gap_scan_schema,
    )
    _write_schema(
        root / "spec" / "repo_candidate_review_gap_scan.schema.json",
        candidate_review_gap_scan_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_candidate_review_classification_summary.v1.json",
        candidate_review_classification_summary_schema,
    )
    _write_schema(
        root / "spec" / "repo_candidate_review_classification_summary.schema.json",
        candidate_review_classification_summary_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_candidate_pre_ratification_handoff.v1.json",
        candidate_pre_ratification_handoff_schema,
    )
    _write_schema(
        root / "spec" / "repo_candidate_pre_ratification_handoff.schema.json",
        candidate_pre_ratification_handoff_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_candidate_ratification_request.v1.json",
        candidate_ratification_request_schema,
    )
    _write_schema(
        root / "spec" / "repo_candidate_ratification_request.schema.json",
        candidate_ratification_request_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_ratification_authority_profile.v1.json",
        ratification_authority_profile_schema,
    )
    _write_schema(
        root / "spec" / "repo_ratification_authority_profile.schema.json",
        ratification_authority_profile_schema,
    )
    _write_schema(
        root
        / "packages"
        / "adeu_repo_description"
        / "schema"
        / "repo_ratification_request_scope_boundary.v1.json",
        ratification_request_scope_boundary_schema,
    )
    _write_schema(
        root / "spec" / "repo_ratification_request_scope_boundary.schema.json",
        ratification_request_scope_boundary_schema,
    )


if __name__ == "__main__":
    main()
