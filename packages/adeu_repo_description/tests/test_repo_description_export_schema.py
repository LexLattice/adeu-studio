from __future__ import annotations

import json
import re
from pathlib import Path

from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_ACTION_EFFECT_ENVELOPE_SCHEMA,
    REPO_ADVERSARIAL_RELATION_REVIEW_SCHEMA,
    REPO_ARBITER_AUTHORITY_PROFILE_SCHEMA,
    REPO_ARBITER_RELATION_REGISTER_SCHEMA,
    REPO_ARC_DEPENDENCY_REGISTER_SCHEMA,
    REPO_ARC_DEPENDENCY_REGISTER_V1_SCHEMA,
    REPO_ARC_MAPPING_TOOL_APPLICABILITY_REPORT_SCHEMA,
    REPO_ARC_NAMESPACE_MAP_SCHEMA,
    REPO_ARC_SERIES_CARTOGRAPHY_SCHEMA,
    REPO_BRANCH_POSTURE_REGISTER_SCHEMA,
    REPO_CANDIDATE_ADVERSARIAL_REVIEW_MATRIX_SCHEMA,
    REPO_CANDIDATE_EVIDENCE_CLASSIFICATION_RECORD_SCHEMA,
    REPO_CANDIDATE_EVIDENCE_SOURCE_INDEX_SCHEMA,
    REPO_CANDIDATE_INTAKE_DERIVATION_MANIFEST_SCHEMA,
    REPO_CANDIDATE_INTAKE_GAP_SCAN_SCHEMA,
    REPO_CANDIDATE_INTAKE_PRE_V70_HANDOFF_SCHEMA,
    REPO_CANDIDATE_NON_ADOPTION_GUARDRAIL_SCHEMA,
    REPO_CANDIDATE_OUTCOME_OBSERVATION_RECORD_SCHEMA,
    REPO_CANDIDATE_OUTCOME_REVIEW_ENTRY_SCHEMA,
    REPO_CANDIDATE_PRE_RATIFICATION_HANDOFF_SCHEMA,
    REPO_CANDIDATE_RATIFICATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_CANDIDATE_RATIFICATION_RECORD_SCHEMA,
    REPO_CANDIDATE_RATIFICATION_REQUEST_SCHEMA,
    REPO_CANDIDATE_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA,
    REPO_CANDIDATE_REVIEW_CLASSIFICATION_SUMMARY_SCHEMA,
    REPO_CANDIDATE_REVIEW_CONFLICT_REGISTER_SCHEMA,
    REPO_CANDIDATE_REVIEW_GAP_SCAN_SCHEMA,
    REPO_CANDIDATE_SOURCE_REGISTER_SCHEMA,
    REPO_COMMAND_PREFLIGHT_CONTRACT_SCHEMA,
    REPO_COMMAND_SCOPE_AUTHORIZATION_BOUNDARY_SCHEMA,
    REPO_COMMIT_RELEASE_AUTHORITY_POSTURE_SCHEMA,
    REPO_CONNECTOR_ACCESS_REVIEW_BOUNDARY_SCHEMA,
    REPO_CONTAINED_INTEGRATION_CANDIDATE_PLAN_SCHEMA,
    REPO_CONTAINED_INTEGRATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_CONTAINED_INTEGRATION_TRIAL_RECORD_SCHEMA,
    REPO_CONTROLLED_EXECUTION_EXCEPTION_REGISTER_SCHEMA,
    REPO_CONTROLLED_EXECUTION_NON_EXECUTION_GUARDRAIL_SCHEMA,
    REPO_CONTROLLED_EXECUTION_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_CONTROLLED_EXECUTION_REVIEW_REQUEST_SCHEMA,
    REPO_CONTROLLED_EXECUTION_REVIEW_SUMMARY_SCHEMA,
    REPO_CONTROLLED_EXECUTION_SOURCE_INDEX_SCHEMA,
    REPO_CORPUS_BOUNDARY_CONTRACT_SCHEMA,
    REPO_CORPUS_DATA_HANDLING_AUTHORITY_REVIEW_SCHEMA,
    REPO_CORPUS_INGESTION_EXCEPTION_REGISTER_SCHEMA,
    REPO_CORPUS_INGESTION_NON_TRANSFER_GUARDRAIL_SCHEMA,
    REPO_CORPUS_INGESTION_PREFLIGHT_CONTRACT_SCHEMA,
    REPO_CORPUS_INGESTION_REVIEW_REQUEST_SCHEMA,
    REPO_CORPUS_INGESTION_SOURCE_INDEX_SCHEMA,
    REPO_CROSS_CORPUS_AUTHORITY_GAP_REGISTER_SCHEMA,
    REPO_CROSS_CORPUS_EXCEPTION_REGISTER_SCHEMA,
    REPO_CROSS_CORPUS_GOVERNANCE_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_CROSS_CORPUS_GOVERNANCE_REQUEST_SCHEMA,
    REPO_CROSS_CORPUS_GOVERNANCE_SUMMARY_SCHEMA,
    REPO_CROSS_CORPUS_NON_INGESTION_GUARDRAIL_SCHEMA,
    REPO_CROSS_CORPUS_SOURCE_INDEX_SCHEMA,
    REPO_DECISION_VISIBILITY_CONTRACT_SCHEMA,
    REPO_DEPENDENCY_GRAPH_SCHEMA,
    REPO_DESCRIPTIVE_NORMATIVE_BINDING_FRAME_SCHEMA,
    REPO_DISPATCH_RECONCILIATION_CONTRACT_SCHEMA,
    REPO_DISPATCH_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_ENTITY_CATALOG_SCHEMA,
    REPO_EVIDENCE_SURFACE_INDEX_SCHEMA,
    REPO_EXECUTION_EFFECT_MONITORING_CONTRACT_SCHEMA,
    REPO_EXECUTION_RUN_PLAN_SCHEMA,
    REPO_EXTERNAL_BRANCH_EXCEPTION_REGISTER_SCHEMA,
    REPO_EXTERNAL_BRANCH_NON_ACTIVATION_GUARDRAIL_SCHEMA,
    REPO_EXTERNAL_BRANCH_READINESS_SUMMARY_SCHEMA,
    REPO_EXTERNAL_BRANCH_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_EXTERNAL_BRANCH_REVIEW_REQUEST_SCHEMA,
    REPO_EXTERNAL_BRANCH_SOURCE_INDEX_SCHEMA,
    REPO_EXTERNAL_DATA_BOUNDARY_SCHEMA,
    REPO_EXTERNAL_RESULT_PROVENANCE_CONTRACT_SCHEMA,
    REPO_EXTERNAL_SUBMISSION_AUTHORITY_REVIEW_SCHEMA,
    REPO_EXTERNAL_TOOL_BOUNDARY_SCHEMA,
    REPO_FAMILY_CLOSURE_REGISTER_SCHEMA,
    REPO_IMPORTED_SUBSTRATE_PROVENANCE_REGISTER_SCHEMA,
    REPO_INTEGRATION_EFFECT_SURFACE_REGISTER_SCHEMA,
    REPO_INTEGRATION_NON_RELEASE_GUARDRAIL_SCHEMA,
    REPO_INTEGRATION_ROLLBACK_READINESS_SCHEMA,
    REPO_INTEGRATION_TARGET_BOUNDARY_SCHEMA,
    REPO_MODEL_OUTPUT_COMPARISON_PROJECTION_SCHEMA,
    REPO_OPERATOR_INGRESS_CANDIDATE_BINDING_SCHEMA,
    REPO_OPERATOR_PROJECTION_CASE_VIEW_SCHEMA,
    REPO_OPERATOR_PROJECTION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_OPERATOR_PROJECTION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    REPO_OPERATOR_PROJECTION_SOURCE_INDEX_SCHEMA,
    REPO_OPTIMIZATION_REGISTER_SCHEMA,
    REPO_OUTCOME_EVIDENCE_SOURCE_INDEX_SCHEMA,
    REPO_OUTCOME_REGRESSION_REGISTER_SCHEMA,
    REPO_OUTCOME_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA,
    REPO_POST_CONTROLLED_EXECUTION_REVIEW_HANDOFF_SCHEMA,
    REPO_POST_CROSS_CORPUS_REVIEW_HANDOFF_SCHEMA,
    REPO_POST_DISPATCH_REVIEW_HANDOFF_SCHEMA,
    REPO_POST_EXTERNAL_BRANCH_REVIEW_HANDOFF_SCHEMA,
    REPO_POST_INTEGRATION_OUTCOME_REVIEW_HANDOFF_SCHEMA,
    REPO_POST_PROJECTION_HANDOFF_SCHEMA,
    REPO_POST_RATIFICATION_HANDOFF_SCHEMA,
    REPO_POST_RECONCILIATION_HANDOFF_SCHEMA,
    REPO_POST_RUNTIME_PERMISSION_REVIEW_HANDOFF_SCHEMA,
    REPO_PRE_EXECUTION_AUTHORITY_REVIEW_HANDOFF_SCHEMA,
    REPO_PROJECTION_EXCEPTION_VISIBILITY_REGISTER_SCHEMA,
    REPO_RATIFICATION_AMENDMENT_SCOPE_BOUNDARY_SCHEMA,
    REPO_RATIFICATION_AUTHORITY_PROFILE_SCHEMA,
    REPO_RATIFICATION_DISSENT_REGISTER_SCHEMA,
    REPO_RATIFICATION_REQUEST_SCOPE_BOUNDARY_SCHEMA,
    REPO_RATIFICATION_REVIEW_WORKBENCH_PROJECTION_SCHEMA,
    REPO_RECONCILIATION_CLAIM_MAP_SCHEMA,
    REPO_RECONCILIATION_DISSENT_REGISTER_SCHEMA,
    REPO_RECONCILIATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_RECONCILIATION_GAP_SCAN_SCHEMA,
    REPO_RECONCILIATION_REVIEW_SUMMARY_SCHEMA,
    REPO_RECONCILIATION_SETTLEMENT_REQUEST_SCHEMA,
    REPO_RECURSIVE_CANDIDATE_INTAKE_RECORD_SCHEMA,
    REPO_RECURSIVE_COORDINATE_EMISSION_PLAN_SCHEMA,
    REPO_RECURSIVE_WORKFLOW_RESIDUE_INTAKE_REPORT_SCHEMA,
    REPO_REVIEW_SETTLEMENT_RECORD_SCHEMA,
    REPO_RUNTIME_AUTHORITY_EXCEPTION_REGISTER_SCHEMA,
    REPO_RUNTIME_AUTHORITY_NON_ACTION_GUARDRAIL_SCHEMA,
    REPO_RUNTIME_AUTHORITY_READINESS_SUMMARY_SCHEMA,
    REPO_RUNTIME_AUTHORITY_SOURCE_INDEX_SCHEMA,
    REPO_RUNTIME_EXECUTION_AUTHORITY_DECISION_SCHEMA,
    REPO_RUNTIME_EXECUTION_AUTHORITY_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_RUNTIME_EXECUTION_AUTHORITY_REQUEST_SCHEMA,
    REPO_RUNTIME_NON_EXECUTION_GUARDRAIL_SCHEMA,
    REPO_RUNTIME_PERMISSION_AUTHORITY_POSTURE_SCHEMA,
    REPO_RUNTIME_PERMISSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_RUNTIME_PERMISSION_REVIEW_REQUEST_SCHEMA,
    REPO_RUNTIME_PERMISSION_REVIEW_SUMMARY_SCHEMA,
    REPO_RUNTIME_PERMISSION_SOURCE_INDEX_SCHEMA,
    REPO_RUNTIME_ROLLBACK_CONTRACT_SCHEMA,
    REPO_RUNTIME_TELEMETRY_REQUIREMENT_SCHEMA,
    REPO_SCHEMA_FAMILY_REGISTRY_SCHEMA,
    REPO_SUPPORT_LINEAGE_REGISTER_SCHEMA,
    REPO_SYMBOL_CATALOG_SCHEMA,
    REPO_TEST_INTENT_MATRIX_SCHEMA,
    REPO_TOOL_FITNESS_DRIFT_REGISTER_SCHEMA,
    REPO_TOOL_INVOCATION_PLAN_SCHEMA,
    REPO_TOOL_USE_PERMISSION_ENVELOPE_SCHEMA,
    REPO_TYPED_ADJUDICATION_CASE_VIEW_SCHEMA,
    REPO_WORKER_OUTPUT_RECONCILIATION_PLAN_SCHEMA,
)
from adeu_repo_description.export_schema import main as export_schema_main

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _schema_pairs() -> dict[str, tuple[Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return {
        REPO_ARC_DEPENDENCY_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_arc_dependency_register.v2.json",
            root / "spec" / "repo_arc_dependency_register.schema.json",
        ),
        REPO_DEPENDENCY_GRAPH_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_dependency_graph.v1.json",
            root / "spec" / "repo_dependency_graph.schema.json",
        ),
        REPO_DESCRIPTIVE_NORMATIVE_BINDING_FRAME_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_descriptive_normative_binding_frame.v1.json",
            root / "spec" / "repo_descriptive_normative_binding_frame.schema.json",
        ),
        REPO_SCHEMA_FAMILY_REGISTRY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_schema_family_registry.v1.json",
            root / "spec" / "repo_schema_family_registry.schema.json",
        ),
        REPO_ENTITY_CATALOG_SCHEMA: (
            root / "packages" / "adeu_repo_description" / "schema" / "repo_entity_catalog.v1.json",
            root / "spec" / "repo_entity_catalog.schema.json",
        ),
        REPO_SYMBOL_CATALOG_SCHEMA: (
            root / "packages" / "adeu_repo_description" / "schema" / "repo_symbol_catalog.v1.json",
            root / "spec" / "repo_symbol_catalog.schema.json",
        ),
        REPO_TEST_INTENT_MATRIX_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_test_intent_matrix.v1.json",
            root / "spec" / "repo_test_intent_matrix.schema.json",
        ),
        REPO_OPTIMIZATION_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_optimization_register.v1.json",
            root / "spec" / "repo_optimization_register.schema.json",
        ),
        REPO_ARC_SERIES_CARTOGRAPHY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_arc_series_cartography.v1.json",
            root / "spec" / "repo_arc_series_cartography.schema.json",
        ),
        REPO_ARC_NAMESPACE_MAP_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_arc_namespace_map.v1.json",
            root / "spec" / "repo_arc_namespace_map.schema.json",
        ),
        REPO_FAMILY_CLOSURE_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_family_closure_register.v1.json",
            root / "spec" / "repo_family_closure_register.schema.json",
        ),
        REPO_BRANCH_POSTURE_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_branch_posture_register.v1.json",
            root / "spec" / "repo_branch_posture_register.schema.json",
        ),
        REPO_SUPPORT_LINEAGE_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_support_lineage_register.v1.json",
            root / "spec" / "repo_support_lineage_register.schema.json",
        ),
        REPO_EVIDENCE_SURFACE_INDEX_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_evidence_surface_index.v1.json",
            root / "spec" / "repo_evidence_surface_index.schema.json",
        ),
        REPO_ARC_MAPPING_TOOL_APPLICABILITY_REPORT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_arc_mapping_tool_applicability_report.v1.json",
            root / "spec" / "repo_arc_mapping_tool_applicability_report.schema.json",
        ),
        REPO_RECURSIVE_COORDINATE_EMISSION_PLAN_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_recursive_coordinate_emission_plan.v1.json",
            root / "spec" / "repo_recursive_coordinate_emission_plan.schema.json",
        ),
        REPO_RECURSIVE_CANDIDATE_INTAKE_RECORD_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_recursive_candidate_intake_record.v1.json",
            root / "spec" / "repo_recursive_candidate_intake_record.schema.json",
        ),
        REPO_CANDIDATE_SOURCE_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_source_register.v1.json",
            root / "spec" / "repo_candidate_source_register.schema.json",
        ),
        REPO_CANDIDATE_NON_ADOPTION_GUARDRAIL_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_non_adoption_guardrail.v1.json",
            root / "spec" / "repo_candidate_non_adoption_guardrail.schema.json",
        ),
        REPO_CANDIDATE_INTAKE_DERIVATION_MANIFEST_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_intake_derivation_manifest.v1.json",
            root / "spec" / "repo_candidate_intake_derivation_manifest.schema.json",
        ),
        REPO_CANDIDATE_INTAKE_GAP_SCAN_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_intake_gap_scan.v1.json",
            root / "spec" / "repo_candidate_intake_gap_scan.schema.json",
        ),
        REPO_OPERATOR_INGRESS_CANDIDATE_BINDING_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_operator_ingress_candidate_binding.v1.json",
            root / "spec" / "repo_operator_ingress_candidate_binding.schema.json",
        ),
        REPO_RECURSIVE_WORKFLOW_RESIDUE_INTAKE_REPORT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_recursive_workflow_residue_intake_report.v1.json",
            root / "spec" / "repo_recursive_workflow_residue_intake_report.schema.json",
        ),
        REPO_CANDIDATE_INTAKE_PRE_V70_HANDOFF_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_intake_pre_v70_handoff.v1.json",
            root / "spec" / "repo_candidate_intake_pre_v70_handoff.schema.json",
        ),
        REPO_CANDIDATE_EVIDENCE_CLASSIFICATION_RECORD_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_evidence_classification_record.v1.json",
            root / "spec" / "repo_candidate_evidence_classification_record.schema.json",
        ),
        REPO_CANDIDATE_EVIDENCE_SOURCE_INDEX_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_evidence_source_index.v1.json",
            root / "spec" / "repo_candidate_evidence_source_index.schema.json",
        ),
        REPO_CANDIDATE_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_review_boundary_guardrail.v1.json",
            root / "spec" / "repo_candidate_review_boundary_guardrail.schema.json",
        ),
        REPO_CANDIDATE_ADVERSARIAL_REVIEW_MATRIX_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_adversarial_review_matrix.v1.json",
            root / "spec" / "repo_candidate_adversarial_review_matrix.schema.json",
        ),
        REPO_CANDIDATE_REVIEW_CONFLICT_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_review_conflict_register.v1.json",
            root / "spec" / "repo_candidate_review_conflict_register.schema.json",
        ),
        REPO_CANDIDATE_REVIEW_GAP_SCAN_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_review_gap_scan.v1.json",
            root / "spec" / "repo_candidate_review_gap_scan.schema.json",
        ),
        REPO_CANDIDATE_REVIEW_CLASSIFICATION_SUMMARY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_review_classification_summary.v1.json",
            root / "spec" / "repo_candidate_review_classification_summary.schema.json",
        ),
        REPO_CANDIDATE_PRE_RATIFICATION_HANDOFF_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_pre_ratification_handoff.v1.json",
            root / "spec" / "repo_candidate_pre_ratification_handoff.schema.json",
        ),
        REPO_CANDIDATE_RATIFICATION_REQUEST_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_ratification_request.v1.json",
            root / "spec" / "repo_candidate_ratification_request.schema.json",
        ),
        REPO_RATIFICATION_AUTHORITY_PROFILE_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_ratification_authority_profile.v1.json",
            root / "spec" / "repo_ratification_authority_profile.schema.json",
        ),
        REPO_RATIFICATION_REQUEST_SCOPE_BOUNDARY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_ratification_request_scope_boundary.v1.json",
            root / "spec" / "repo_ratification_request_scope_boundary.schema.json",
        ),
        REPO_CANDIDATE_RATIFICATION_RECORD_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_ratification_record.v1.json",
            root / "spec" / "repo_candidate_ratification_record.schema.json",
        ),
        REPO_REVIEW_SETTLEMENT_RECORD_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_review_settlement_record.v1.json",
            root / "spec" / "repo_review_settlement_record.schema.json",
        ),
        REPO_RATIFICATION_DISSENT_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_ratification_dissent_register.v1.json",
            root / "spec" / "repo_ratification_dissent_register.schema.json",
        ),
        REPO_RATIFICATION_AMENDMENT_SCOPE_BOUNDARY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_ratification_amendment_scope_boundary.v1.json",
            root / "spec" / "repo_ratification_amendment_scope_boundary.schema.json",
        ),
        REPO_POST_RATIFICATION_HANDOFF_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_post_ratification_handoff.v1.json",
            root / "spec" / "repo_post_ratification_handoff.schema.json",
        ),
        REPO_CANDIDATE_RATIFICATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_ratification_family_closeout_alignment.v1.json",
            root / "spec" / "repo_candidate_ratification_family_closeout_alignment.schema.json",
        ),
        REPO_CONTAINED_INTEGRATION_CANDIDATE_PLAN_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_contained_integration_candidate_plan.v1.json",
            root / "spec" / "repo_contained_integration_candidate_plan.schema.json",
        ),
        REPO_INTEGRATION_TARGET_BOUNDARY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_integration_target_boundary.v1.json",
            root / "spec" / "repo_integration_target_boundary.schema.json",
        ),
        REPO_INTEGRATION_NON_RELEASE_GUARDRAIL_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_integration_non_release_guardrail.v1.json",
            root / "spec" / "repo_integration_non_release_guardrail.schema.json",
        ),
        REPO_CONTAINED_INTEGRATION_TRIAL_RECORD_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_contained_integration_trial_record.v1.json",
            root / "spec" / "repo_contained_integration_trial_record.schema.json",
        ),
        REPO_INTEGRATION_EFFECT_SURFACE_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_integration_effect_surface_register.v1.json",
            root / "spec" / "repo_integration_effect_surface_register.schema.json",
        ),
        REPO_INTEGRATION_ROLLBACK_READINESS_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_integration_rollback_readiness.v1.json",
            root / "spec" / "repo_integration_rollback_readiness.schema.json",
        ),
        REPO_COMMIT_RELEASE_AUTHORITY_POSTURE_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_commit_release_authority_posture.v1.json",
            root / "spec" / "repo_commit_release_authority_posture.schema.json",
        ),
        REPO_POST_INTEGRATION_OUTCOME_REVIEW_HANDOFF_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_post_integration_outcome_review_handoff.v1.json",
            root / "spec" / "repo_post_integration_outcome_review_handoff.schema.json",
        ),
        REPO_CONTAINED_INTEGRATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_contained_integration_family_closeout_alignment.v1.json",
            root / "spec" / "repo_contained_integration_family_closeout_alignment.schema.json",
        ),
        REPO_CANDIDATE_OUTCOME_REVIEW_ENTRY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_outcome_review_entry.v1.json",
            root / "spec" / "repo_candidate_outcome_review_entry.schema.json",
        ),
        REPO_OUTCOME_EVIDENCE_SOURCE_INDEX_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_outcome_evidence_source_index.v1.json",
            root / "spec" / "repo_outcome_evidence_source_index.schema.json",
        ),
        REPO_OUTCOME_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_outcome_review_boundary_guardrail.v1.json",
            root / "spec" / "repo_outcome_review_boundary_guardrail.schema.json",
        ),
        REPO_CANDIDATE_OUTCOME_OBSERVATION_RECORD_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_candidate_outcome_observation_record.v1.json",
            root / "spec" / "repo_candidate_outcome_observation_record.schema.json",
        ),
        REPO_OUTCOME_REGRESSION_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_outcome_regression_register.v1.json",
            root / "spec" / "repo_outcome_regression_register.schema.json",
        ),
        REPO_TOOL_FITNESS_DRIFT_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_tool_fitness_drift_register.v1.json",
            root / "spec" / "repo_tool_fitness_drift_register.schema.json",
        ),
        REPO_OPERATOR_PROJECTION_CASE_VIEW_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_operator_projection_case_view.v1.json",
            root / "spec" / "repo_operator_projection_case_view.schema.json",
        ),
        REPO_OPERATOR_PROJECTION_SOURCE_INDEX_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_operator_projection_source_index.v1.json",
            root / "spec" / "repo_operator_projection_source_index.schema.json",
        ),
        REPO_OPERATOR_PROJECTION_NON_AUTHORITY_GUARDRAIL_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_operator_projection_non_authority_guardrail.v1.json",
            root / "spec" / "repo_operator_projection_non_authority_guardrail.schema.json",
        ),
        REPO_TYPED_ADJUDICATION_CASE_VIEW_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_typed_adjudication_case_view.v1.json",
            root / "spec" / "repo_typed_adjudication_case_view.schema.json",
        ),
        REPO_MODEL_OUTPUT_COMPARISON_PROJECTION_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_model_output_comparison_projection.v1.json",
            root / "spec" / "repo_model_output_comparison_projection.schema.json",
        ),
        REPO_PROJECTION_EXCEPTION_VISIBILITY_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_projection_exception_visibility_register.v1.json",
            root / "spec" / "repo_projection_exception_visibility_register.schema.json",
        ),
        REPO_DECISION_VISIBILITY_CONTRACT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_decision_visibility_contract.v1.json",
            root / "spec" / "repo_decision_visibility_contract.schema.json",
        ),
        REPO_RATIFICATION_REVIEW_WORKBENCH_PROJECTION_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_ratification_review_workbench_projection.v1.json",
            root / "spec" / "repo_ratification_review_workbench_projection.schema.json",
        ),
        REPO_POST_PROJECTION_HANDOFF_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_post_projection_handoff.v1.json",
            root / "spec" / "repo_post_projection_handoff.schema.json",
        ),
        REPO_OPERATOR_PROJECTION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_operator_projection_family_closeout_alignment.v1.json",
            root / "spec" / "repo_operator_projection_family_closeout_alignment.schema.json",
        ),
        REPO_WORKER_OUTPUT_RECONCILIATION_PLAN_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_worker_output_reconciliation_plan.v1.json",
            root / "spec" / "repo_worker_output_reconciliation_plan.schema.json",
        ),
        REPO_DISPATCH_RECONCILIATION_CONTRACT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_dispatch_reconciliation_contract.v1.json",
            root / "spec" / "repo_dispatch_reconciliation_contract.schema.json",
        ),
        REPO_POST_DISPATCH_REVIEW_HANDOFF_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_post_dispatch_review_handoff.v1.json",
            root / "spec" / "repo_post_dispatch_review_handoff.schema.json",
        ),
        REPO_DISPATCH_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_dispatch_review_family_closeout_alignment.v1.json",
            root / "spec" / "repo_dispatch_review_family_closeout_alignment.schema.json",
        ),
        REPO_RECONCILIATION_CLAIM_MAP_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_reconciliation_claim_map.v1.json",
            root / "spec" / "repo_reconciliation_claim_map.schema.json",
        ),
        REPO_ARBITER_RELATION_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_arbiter_relation_register.v1.json",
            root / "spec" / "repo_arbiter_relation_register.schema.json",
        ),
        REPO_RECONCILIATION_DISSENT_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_reconciliation_dissent_register.v1.json",
            root / "spec" / "repo_reconciliation_dissent_register.schema.json",
        ),
        REPO_ARBITER_AUTHORITY_PROFILE_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_arbiter_authority_profile.v1.json",
            root / "spec" / "repo_arbiter_authority_profile.schema.json",
        ),
        REPO_RECONCILIATION_SETTLEMENT_REQUEST_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_reconciliation_settlement_request.v1.json",
            root / "spec" / "repo_reconciliation_settlement_request.schema.json",
        ),
        REPO_ADVERSARIAL_RELATION_REVIEW_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_adversarial_relation_review.v1.json",
            root / "spec" / "repo_adversarial_relation_review.schema.json",
        ),
        REPO_RECONCILIATION_GAP_SCAN_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_reconciliation_gap_scan.v1.json",
            root / "spec" / "repo_reconciliation_gap_scan.schema.json",
        ),
        REPO_RECONCILIATION_REVIEW_SUMMARY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_reconciliation_review_summary.v1.json",
            root / "spec" / "repo_reconciliation_review_summary.schema.json",
        ),
        REPO_POST_RECONCILIATION_HANDOFF_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_post_reconciliation_handoff.v1.json",
            root / "spec" / "repo_post_reconciliation_handoff.schema.json",
        ),
        REPO_RECONCILIATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_reconciliation_family_closeout_alignment.v1.json",
            root / "spec" / "repo_reconciliation_family_closeout_alignment.schema.json",
        ),
        REPO_RUNTIME_PERMISSION_SOURCE_INDEX_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_runtime_permission_source_index.v1.json",
            root / "spec" / "repo_runtime_permission_source_index.schema.json",
        ),
        REPO_RUNTIME_PERMISSION_REVIEW_REQUEST_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_runtime_permission_review_request.v1.json",
            root / "spec" / "repo_runtime_permission_review_request.schema.json",
        ),
        REPO_RUNTIME_NON_EXECUTION_GUARDRAIL_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_runtime_non_execution_guardrail.v1.json",
            root / "spec" / "repo_runtime_non_execution_guardrail.schema.json",
        ),
        REPO_COMMAND_PREFLIGHT_CONTRACT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_command_preflight_contract.v1.json",
            root / "spec" / "repo_command_preflight_contract.schema.json",
        ),
        REPO_ACTION_EFFECT_ENVELOPE_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_action_effect_envelope.v1.json",
            root / "spec" / "repo_action_effect_envelope.schema.json",
        ),
        REPO_RUNTIME_TELEMETRY_REQUIREMENT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_runtime_telemetry_requirement.v1.json",
            root / "spec" / "repo_runtime_telemetry_requirement.schema.json",
        ),
        REPO_RUNTIME_ROLLBACK_CONTRACT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_runtime_rollback_contract.v1.json",
            root / "spec" / "repo_runtime_rollback_contract.schema.json",
        ),
        REPO_RUNTIME_PERMISSION_AUTHORITY_POSTURE_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_runtime_permission_authority_posture.v1.json",
            root / "spec" / "repo_runtime_permission_authority_posture.schema.json",
        ),
        REPO_RUNTIME_PERMISSION_REVIEW_SUMMARY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_runtime_permission_review_summary.v1.json",
            root / "spec" / "repo_runtime_permission_review_summary.schema.json",
        ),
        REPO_POST_RUNTIME_PERMISSION_REVIEW_HANDOFF_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_post_runtime_permission_review_handoff.v1.json",
            root / "spec" / "repo_post_runtime_permission_review_handoff.schema.json",
        ),
        REPO_RUNTIME_PERMISSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_runtime_permission_family_closeout_alignment.v1.json",
            root / "spec" / "repo_runtime_permission_family_closeout_alignment.schema.json",
        ),
        REPO_RUNTIME_AUTHORITY_SOURCE_INDEX_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_runtime_authority_source_index.v1.json",
            root / "spec" / "repo_runtime_authority_source_index.schema.json",
        ),
        REPO_RUNTIME_EXECUTION_AUTHORITY_REQUEST_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_runtime_execution_authority_request.v1.json",
            root / "spec" / "repo_runtime_execution_authority_request.schema.json",
        ),
        REPO_RUNTIME_AUTHORITY_NON_ACTION_GUARDRAIL_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_runtime_authority_non_action_guardrail.v1.json",
            root / "spec" / "repo_runtime_authority_non_action_guardrail.schema.json",
        ),
        REPO_RUNTIME_EXECUTION_AUTHORITY_DECISION_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_runtime_execution_authority_decision.v1.json",
            root / "spec" / "repo_runtime_execution_authority_decision.schema.json",
        ),
        REPO_TOOL_USE_PERMISSION_ENVELOPE_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_tool_use_permission_envelope.v1.json",
            root / "spec" / "repo_tool_use_permission_envelope.schema.json",
        ),
        REPO_COMMAND_SCOPE_AUTHORIZATION_BOUNDARY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_command_scope_authorization_boundary.v1.json",
            root / "spec" / "repo_command_scope_authorization_boundary.schema.json",
        ),
        REPO_RUNTIME_AUTHORITY_EXCEPTION_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_runtime_authority_exception_register.v1.json",
            root / "spec" / "repo_runtime_authority_exception_register.schema.json",
        ),
        REPO_RUNTIME_AUTHORITY_READINESS_SUMMARY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_runtime_authority_readiness_summary.v1.json",
            root / "spec" / "repo_runtime_authority_readiness_summary.schema.json",
        ),
        REPO_PRE_EXECUTION_AUTHORITY_REVIEW_HANDOFF_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_pre_execution_authority_review_handoff.v1.json",
            root / "spec" / "repo_pre_execution_authority_review_handoff.schema.json",
        ),
        REPO_RUNTIME_EXECUTION_AUTHORITY_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_runtime_execution_authority_family_closeout_alignment.v1.json",
            root
            / "spec"
            / "repo_runtime_execution_authority_family_closeout_alignment.schema.json",
        ),
        REPO_CONTROLLED_EXECUTION_SOURCE_INDEX_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_controlled_execution_source_index.v1.json",
            root / "spec" / "repo_controlled_execution_source_index.schema.json",
        ),
        REPO_CONTROLLED_EXECUTION_REVIEW_REQUEST_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_controlled_execution_review_request.v1.json",
            root / "spec" / "repo_controlled_execution_review_request.schema.json",
        ),
        REPO_CONTROLLED_EXECUTION_NON_EXECUTION_GUARDRAIL_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_controlled_execution_non_execution_guardrail.v1.json",
            root / "spec" / "repo_controlled_execution_non_execution_guardrail.schema.json",
        ),
        REPO_EXECUTION_RUN_PLAN_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_execution_run_plan.v1.json",
            root / "spec" / "repo_execution_run_plan.schema.json",
        ),
        REPO_TOOL_INVOCATION_PLAN_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_tool_invocation_plan.v1.json",
            root / "spec" / "repo_tool_invocation_plan.schema.json",
        ),
        REPO_EXECUTION_EFFECT_MONITORING_CONTRACT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_execution_effect_monitoring_contract.v1.json",
            root / "spec" / "repo_execution_effect_monitoring_contract.schema.json",
        ),
        REPO_CONTROLLED_EXECUTION_EXCEPTION_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_controlled_execution_exception_register.v1.json",
            root / "spec" / "repo_controlled_execution_exception_register.schema.json",
        ),
        REPO_CONTROLLED_EXECUTION_REVIEW_SUMMARY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_controlled_execution_review_summary.v1.json",
            root / "spec" / "repo_controlled_execution_review_summary.schema.json",
        ),
        REPO_POST_CONTROLLED_EXECUTION_REVIEW_HANDOFF_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_post_controlled_execution_review_handoff.v1.json",
            root / "spec" / "repo_post_controlled_execution_review_handoff.schema.json",
        ),
        REPO_CONTROLLED_EXECUTION_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_controlled_execution_review_family_closeout_alignment.v1.json",
            root
            / "spec"
            / "repo_controlled_execution_review_family_closeout_alignment.schema.json",
        ),
        REPO_EXTERNAL_BRANCH_SOURCE_INDEX_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_external_branch_source_index.v1.json",
            root / "spec" / "repo_external_branch_source_index.schema.json",
        ),
        REPO_EXTERNAL_BRANCH_REVIEW_REQUEST_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_external_branch_review_request.v1.json",
            root / "spec" / "repo_external_branch_review_request.schema.json",
        ),
        REPO_EXTERNAL_BRANCH_NON_ACTIVATION_GUARDRAIL_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_external_branch_non_activation_guardrail.v1.json",
            root / "spec" / "repo_external_branch_non_activation_guardrail.schema.json",
        ),
        REPO_EXTERNAL_DATA_BOUNDARY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_external_data_boundary.v1.json",
            root / "spec" / "repo_external_data_boundary.schema.json",
        ),
        REPO_EXTERNAL_TOOL_BOUNDARY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_external_tool_boundary.v1.json",
            root / "spec" / "repo_external_tool_boundary.schema.json",
        ),
        REPO_EXTERNAL_SUBMISSION_AUTHORITY_REVIEW_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_external_submission_authority_review.v1.json",
            root / "spec" / "repo_external_submission_authority_review.schema.json",
        ),
        REPO_EXTERNAL_RESULT_PROVENANCE_CONTRACT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_external_result_provenance_contract.v1.json",
            root / "spec" / "repo_external_result_provenance_contract.schema.json",
        ),
        REPO_EXTERNAL_BRANCH_EXCEPTION_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_external_branch_exception_register.v1.json",
            root / "spec" / "repo_external_branch_exception_register.schema.json",
        ),
        REPO_EXTERNAL_BRANCH_READINESS_SUMMARY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_external_branch_readiness_summary.v1.json",
            root / "spec" / "repo_external_branch_readiness_summary.schema.json",
        ),
        REPO_POST_EXTERNAL_BRANCH_REVIEW_HANDOFF_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_post_external_branch_review_handoff.v1.json",
            root / "spec" / "repo_post_external_branch_review_handoff.schema.json",
        ),
        REPO_EXTERNAL_BRANCH_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_external_branch_review_family_closeout_alignment.v1.json",
            root / "spec" / "repo_external_branch_review_family_closeout_alignment.schema.json",
        ),
        REPO_CROSS_CORPUS_SOURCE_INDEX_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_cross_corpus_source_index.v1.json",
            root / "spec" / "repo_cross_corpus_source_index.schema.json",
        ),
        REPO_CROSS_CORPUS_GOVERNANCE_REQUEST_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_cross_corpus_governance_request.v1.json",
            root / "spec" / "repo_cross_corpus_governance_request.schema.json",
        ),
        REPO_CROSS_CORPUS_NON_INGESTION_GUARDRAIL_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_cross_corpus_non_ingestion_guardrail.v1.json",
            root / "spec" / "repo_cross_corpus_non_ingestion_guardrail.schema.json",
        ),
        REPO_CORPUS_BOUNDARY_CONTRACT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_corpus_boundary_contract.v1.json",
            root / "spec" / "repo_corpus_boundary_contract.schema.json",
        ),
        REPO_IMPORTED_SUBSTRATE_PROVENANCE_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_imported_substrate_provenance_register.v1.json",
            root / "spec" / "repo_imported_substrate_provenance_register.schema.json",
        ),
        REPO_CROSS_CORPUS_AUTHORITY_GAP_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_cross_corpus_authority_gap_register.v1.json",
            root / "spec" / "repo_cross_corpus_authority_gap_register.schema.json",
        ),
        REPO_CROSS_CORPUS_EXCEPTION_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_cross_corpus_exception_register.v1.json",
            root / "spec" / "repo_cross_corpus_exception_register.schema.json",
        ),
        REPO_CROSS_CORPUS_GOVERNANCE_SUMMARY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_cross_corpus_governance_summary.v1.json",
            root / "spec" / "repo_cross_corpus_governance_summary.schema.json",
        ),
        REPO_POST_CROSS_CORPUS_REVIEW_HANDOFF_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_post_cross_corpus_review_handoff.v1.json",
            root / "spec" / "repo_post_cross_corpus_review_handoff.schema.json",
        ),
        REPO_CROSS_CORPUS_GOVERNANCE_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_cross_corpus_governance_family_closeout_alignment.v1.json",
            root / "spec" / "repo_cross_corpus_governance_family_closeout_alignment.schema.json",
        ),
        REPO_CORPUS_INGESTION_SOURCE_INDEX_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_corpus_ingestion_source_index.v1.json",
            root / "spec" / "repo_corpus_ingestion_source_index.schema.json",
        ),
        REPO_CORPUS_INGESTION_REVIEW_REQUEST_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_corpus_ingestion_review_request.v1.json",
            root / "spec" / "repo_corpus_ingestion_review_request.schema.json",
        ),
        REPO_CORPUS_INGESTION_NON_TRANSFER_GUARDRAIL_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_corpus_ingestion_non_transfer_guardrail.v1.json",
            root / "spec" / "repo_corpus_ingestion_non_transfer_guardrail.schema.json",
        ),
        REPO_CORPUS_INGESTION_PREFLIGHT_CONTRACT_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_corpus_ingestion_preflight_contract.v1.json",
            root / "spec" / "repo_corpus_ingestion_preflight_contract.schema.json",
        ),
        REPO_CONNECTOR_ACCESS_REVIEW_BOUNDARY_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_connector_access_review_boundary.v1.json",
            root / "spec" / "repo_connector_access_review_boundary.schema.json",
        ),
        REPO_CORPUS_DATA_HANDLING_AUTHORITY_REVIEW_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_corpus_data_handling_authority_review.v1.json",
            root / "spec" / "repo_corpus_data_handling_authority_review.schema.json",
        ),
        REPO_CORPUS_INGESTION_EXCEPTION_REGISTER_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_corpus_ingestion_exception_register.v1.json",
            root / "spec" / "repo_corpus_ingestion_exception_register.schema.json",
        ),
    }


def _historical_schema_paths() -> dict[str, Path]:
    root = repo_root(anchor=Path(__file__))
    return {
        REPO_ARC_DEPENDENCY_REGISTER_V1_SCHEMA: (
            root
            / "packages"
            / "adeu_repo_description"
            / "schema"
            / "repo_arc_dependency_register.v1.json"
        ),
    }


def test_authoritative_and_mirror_schema_are_byte_identical() -> None:
    for authoritative, mirror in _schema_pairs().values():
        assert authoritative.read_bytes() == mirror.read_bytes()


def test_schema_export_rerun_is_clean_and_deterministic() -> None:
    pairs = _schema_pairs()
    before = {
        schema: (authoritative.read_bytes(), mirror.read_bytes())
        for schema, (authoritative, mirror) in pairs.items()
    }
    export_schema_main()
    after_first = {
        schema: (authoritative.read_bytes(), mirror.read_bytes())
        for schema, (authoritative, mirror) in pairs.items()
    }
    export_schema_main()
    after_second = {
        schema: (authoritative.read_bytes(), mirror.read_bytes())
        for schema, (authoritative, mirror) in pairs.items()
    }
    assert before == after_first == after_second


def test_exported_schema_has_stable_contract_markers() -> None:
    for expected_schema, (authoritative, _mirror) in _schema_pairs().items():
        payload = json.loads(authoritative.read_text(encoding="utf-8"))
        assert payload["properties"]["schema"]["const"] == expected_schema
    for expected_schema, authoritative in _historical_schema_paths().items():
        payload = json.loads(authoritative.read_text(encoding="utf-8"))
        assert payload["properties"]["schema"]["const"] == expected_schema


def test_exported_schema_has_no_absolute_path_material() -> None:
    root = repo_root(anchor=Path(__file__))
    root_text = root.as_posix()

    def _check_node(node: object) -> None:
        if isinstance(node, dict):
            for value in node.values():
                _check_node(value)
            return
        if isinstance(node, list):
            for item in node:
                _check_node(item)
            return
        if not isinstance(node, str):
            return
        normalized = node.replace("\\", "/")
        assert root_text not in normalized
        assert not normalized.startswith("/home/")
        assert not normalized.startswith("/Users/")
        assert _WINDOWS_ABSOLUTE_PATH_RE.search(node) is None

    for authoritative, mirror in _schema_pairs().values():
        _check_node(json.loads(authoritative.read_text(encoding="utf-8")))
        _check_node(json.loads(mirror.read_text(encoding="utf-8")))
    for authoritative in _historical_schema_paths().values():
        _check_node(json.loads(authoritative.read_text(encoding="utf-8")))
    (REPO_POST_RUNTIME_PERMISSION_REVIEW_HANDOFF_SCHEMA,)
