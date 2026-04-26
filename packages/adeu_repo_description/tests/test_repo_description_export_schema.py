from __future__ import annotations

import json
import re
from pathlib import Path

from adeu_ir.repo import repo_root
from adeu_repo_description import (
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
    REPO_CANDIDATE_PRE_RATIFICATION_HANDOFF_SCHEMA,
    REPO_CANDIDATE_RATIFICATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_CANDIDATE_RATIFICATION_RECORD_SCHEMA,
    REPO_CANDIDATE_RATIFICATION_REQUEST_SCHEMA,
    REPO_CANDIDATE_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA,
    REPO_CANDIDATE_REVIEW_CLASSIFICATION_SUMMARY_SCHEMA,
    REPO_CANDIDATE_REVIEW_CONFLICT_REGISTER_SCHEMA,
    REPO_CANDIDATE_REVIEW_GAP_SCAN_SCHEMA,
    REPO_CANDIDATE_SOURCE_REGISTER_SCHEMA,
    REPO_CONTAINED_INTEGRATION_CANDIDATE_PLAN_SCHEMA,
    REPO_DEPENDENCY_GRAPH_SCHEMA,
    REPO_DESCRIPTIVE_NORMATIVE_BINDING_FRAME_SCHEMA,
    REPO_ENTITY_CATALOG_SCHEMA,
    REPO_EVIDENCE_SURFACE_INDEX_SCHEMA,
    REPO_FAMILY_CLOSURE_REGISTER_SCHEMA,
    REPO_INTEGRATION_NON_RELEASE_GUARDRAIL_SCHEMA,
    REPO_INTEGRATION_TARGET_BOUNDARY_SCHEMA,
    REPO_OPERATOR_INGRESS_CANDIDATE_BINDING_SCHEMA,
    REPO_OPTIMIZATION_REGISTER_SCHEMA,
    REPO_POST_RATIFICATION_HANDOFF_SCHEMA,
    REPO_RATIFICATION_AMENDMENT_SCOPE_BOUNDARY_SCHEMA,
    REPO_RATIFICATION_AUTHORITY_PROFILE_SCHEMA,
    REPO_RATIFICATION_DISSENT_REGISTER_SCHEMA,
    REPO_RATIFICATION_REQUEST_SCOPE_BOUNDARY_SCHEMA,
    REPO_RECURSIVE_CANDIDATE_INTAKE_RECORD_SCHEMA,
    REPO_RECURSIVE_COORDINATE_EMISSION_PLAN_SCHEMA,
    REPO_RECURSIVE_WORKFLOW_RESIDUE_INTAKE_REPORT_SCHEMA,
    REPO_REVIEW_SETTLEMENT_RECORD_SCHEMA,
    REPO_SCHEMA_FAMILY_REGISTRY_SCHEMA,
    REPO_SUPPORT_LINEAGE_REGISTER_SCHEMA,
    REPO_SYMBOL_CATALOG_SCHEMA,
    REPO_TEST_INTENT_MATRIX_SCHEMA,
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
