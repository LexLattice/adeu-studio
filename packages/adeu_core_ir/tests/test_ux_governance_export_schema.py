from __future__ import annotations

import json
import re
from pathlib import Path

from adeu_core_ir import (
    ADEU_BROKERED_REFLEXIVE_EXECUTION_PLAN_SCHEMA,
    ADEU_BROKERED_REFLEXIVE_PAYLOAD_SCHEMA,
    EXTERNAL_CONTRIBUTION_ALIGNMENT_PACKET_SCHEMA,
    META_CONTROL_UPDATE_CANDIDATE_SCHEMA,
    META_CONTROL_UPDATE_MANIFEST_SCHEMA,
    META_LOOP_CHECKPOINT_RESULT_MANIFEST_SCHEMA,
    META_LOOP_CONFORMANCE_REPORT_SCHEMA,
    META_LOOP_DRIFT_DIAGNOSTICS_SCHEMA,
    META_LOOP_RUN_TRACE_SCHEMA,
    META_LOOP_SEQUENCE_CONTRACT_SCHEMA,
    META_MODULE_CATALOG_SCHEMA,
    META_TESTING_INTENT_PACKET_SCHEMA,
    MODULE_CONFORMANCE_REPORT_SCHEMA,
    UX_CONFORMANCE_REPORT_SCHEMA,
    UX_DOMAIN_PACKET_SCHEMA,
    UX_INTERACTION_CONTRACT_SCHEMA,
    UX_MORPH_DIAGNOSTICS_SCHEMA,
    UX_MORPH_IR_SCHEMA,
    UX_SURFACE_COMPILER_EXPORT_SCHEMA,
    UX_SURFACE_COMPILER_VARIANT_MANIFEST_SCHEMA,
    UX_SURFACE_PROJECTION_SCHEMA,
    V36A_APPROVED_PROFILE_TABLE_SCHEMA,
    V36A_SAME_CONTEXT_GLOSSARY_SCHEMA,
)
from adeu_core_ir.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\\\")


def _schema_paths() -> list[tuple[Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return [
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "adeu_brokered_reflexive_payload.v1.json",
            root / "spec" / "adeu_brokered_reflexive_payload.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "adeu_brokered_reflexive_execution_plan.v1.json",
            root / "spec" / "adeu_brokered_reflexive_execution_plan.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "external_contribution_alignment_packet.v1.json",
            root / "spec" / "external_contribution_alignment_packet.schema.json",
        ),
        (
            root / "packages" / "adeu_core_ir" / "schema" / "module_conformance_report.v1.json",
            root / "spec" / "module_conformance_report.schema.json",
        ),
        (
            root / "packages" / "adeu_core_ir" / "schema" / "ux_domain_packet.v1.json",
            root / "spec" / "ux_domain_packet.schema.json",
        ),
        (
            root / "packages" / "adeu_core_ir" / "schema" / "ux_morph_ir.v1.json",
            root / "spec" / "ux_morph_ir.schema.json",
        ),
        (
            root / "packages" / "adeu_core_ir" / "schema" / "ux_surface_projection.v1.json",
            root / "spec" / "ux_surface_projection.schema.json",
        ),
        (
            root / "packages" / "adeu_core_ir" / "schema" / "ux_interaction_contract.v1.json",
            root / "spec" / "ux_interaction_contract.schema.json",
        ),
        (
            root / "packages" / "adeu_core_ir" / "schema" / "ux_morph_diagnostics.v1.json",
            root / "spec" / "ux_morph_diagnostics.schema.json",
        ),
        (
            root / "packages" / "adeu_core_ir" / "schema" / "ux_conformance_report.v1.json",
            root / "spec" / "ux_conformance_report.schema.json",
        ),
        (
            root / "packages" / "adeu_core_ir" / "schema" / "ux_surface_compiler_export.v1.json",
            root / "spec" / "ux_surface_compiler_export.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "ux_surface_compiler_variant_manifest.v1.json",
            root / "spec" / "ux_surface_compiler_variant_manifest.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "v36a_first_family_approved_profile_table.v1.json",
            root / "spec" / "v36a_first_family_approved_profile_table.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "v36a_same_context_reachability_glossary.v1.json",
            root / "spec" / "v36a_same_context_reachability_glossary.schema.json",
        ),
        (
            root / "packages" / "adeu_core_ir" / "schema" / "meta_testing_intent_packet.v1.json",
            root / "spec" / "meta_testing_intent_packet.schema.json",
        ),
        (
            root / "packages" / "adeu_core_ir" / "schema" / "meta_module_catalog.v1.json",
            root / "spec" / "meta_module_catalog.schema.json",
        ),
        (
            root / "packages" / "adeu_core_ir" / "schema" / "meta_loop_sequence_contract.v1.json",
            root / "spec" / "meta_loop_sequence_contract.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "meta_loop_checkpoint_result_manifest.v1.json",
            root / "spec" / "meta_loop_checkpoint_result_manifest.schema.json",
        ),
        (
            root / "packages" / "adeu_core_ir" / "schema" / "meta_loop_run_trace.v1.json",
            root / "spec" / "meta_loop_run_trace.schema.json",
        ),
        (
            root / "packages" / "adeu_core_ir" / "schema" / "meta_loop_drift_diagnostics.v1.json",
            root / "spec" / "meta_loop_drift_diagnostics.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "meta_loop_conformance_report.v1.json",
            root / "spec" / "meta_loop_conformance_report.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "meta_control_update_candidate.v1.json",
            root / "spec" / "meta_control_update_candidate.schema.json",
        ),
        (
            root
            / "packages"
            / "adeu_core_ir"
            / "schema"
            / "meta_control_update_manifest.v1.json",
            root / "spec" / "meta_control_update_manifest.schema.json",
        ),
    ]


def test_authoritative_and_mirror_schema_files_are_byte_identical() -> None:
    for authoritative, mirror in _schema_paths():
        assert authoritative.read_bytes() == mirror.read_bytes()


def test_schema_export_rerun_is_clean_and_deterministic() -> None:
    before = [
        (authoritative.read_bytes(), mirror.read_bytes())
        for authoritative, mirror in _schema_paths()
    ]

    export_schema_main()
    after_first = [
        (authoritative.read_bytes(), mirror.read_bytes())
        for authoritative, mirror in _schema_paths()
    ]

    export_schema_main()
    after_second = [
        (authoritative.read_bytes(), mirror.read_bytes())
        for authoritative, mirror in _schema_paths()
    ]

    assert before == after_first == after_second


def test_exported_schema_files_have_stable_contract_markers() -> None:
    expected_consts = {
        "adeu_brokered_reflexive_payload.v1.json": ADEU_BROKERED_REFLEXIVE_PAYLOAD_SCHEMA,
        "adeu_brokered_reflexive_execution_plan.v1.json": (
            ADEU_BROKERED_REFLEXIVE_EXECUTION_PLAN_SCHEMA
        ),
        "external_contribution_alignment_packet.v1.json": (
            EXTERNAL_CONTRIBUTION_ALIGNMENT_PACKET_SCHEMA
        ),
        "module_conformance_report.v1.json": MODULE_CONFORMANCE_REPORT_SCHEMA,
        "ux_domain_packet.v1.json": UX_DOMAIN_PACKET_SCHEMA,
        "ux_morph_ir.v1.json": UX_MORPH_IR_SCHEMA,
        "ux_surface_projection.v1.json": UX_SURFACE_PROJECTION_SCHEMA,
        "ux_interaction_contract.v1.json": UX_INTERACTION_CONTRACT_SCHEMA,
        "ux_morph_diagnostics.v1.json": UX_MORPH_DIAGNOSTICS_SCHEMA,
        "ux_conformance_report.v1.json": UX_CONFORMANCE_REPORT_SCHEMA,
        "ux_surface_compiler_export.v1.json": UX_SURFACE_COMPILER_EXPORT_SCHEMA,
        "ux_surface_compiler_variant_manifest.v1.json": UX_SURFACE_COMPILER_VARIANT_MANIFEST_SCHEMA,
        "v36a_first_family_approved_profile_table.v1.json": V36A_APPROVED_PROFILE_TABLE_SCHEMA,
        "v36a_same_context_reachability_glossary.v1.json": V36A_SAME_CONTEXT_GLOSSARY_SCHEMA,
        "meta_testing_intent_packet.v1.json": META_TESTING_INTENT_PACKET_SCHEMA,
        "meta_module_catalog.v1.json": META_MODULE_CATALOG_SCHEMA,
        "meta_loop_sequence_contract.v1.json": META_LOOP_SEQUENCE_CONTRACT_SCHEMA,
        "meta_loop_checkpoint_result_manifest.v1.json": META_LOOP_CHECKPOINT_RESULT_MANIFEST_SCHEMA,
        "meta_loop_run_trace.v1.json": META_LOOP_RUN_TRACE_SCHEMA,
        "meta_loop_drift_diagnostics.v1.json": META_LOOP_DRIFT_DIAGNOSTICS_SCHEMA,
        "meta_loop_conformance_report.v1.json": META_LOOP_CONFORMANCE_REPORT_SCHEMA,
        "meta_control_update_candidate.v1.json": META_CONTROL_UPDATE_CANDIDATE_SCHEMA,
        "meta_control_update_manifest.v1.json": META_CONTROL_UPDATE_MANIFEST_SCHEMA,
    }

    for authoritative, _mirror in _schema_paths():
        payload = json.loads(authoritative.read_text(encoding="utf-8"))
        assert payload["properties"]["schema"]["const"] == expected_consts[authoritative.name]


def test_exported_schema_files_have_no_absolute_path_material() -> None:
    root = repo_root(anchor=Path(__file__))
    root_text = root.as_posix()

    def _check_node(node: object) -> None:
        if isinstance(node, dict):
            for key in sorted(node):
                _check_node(node[key])
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

    for authoritative, mirror in _schema_paths():
        for path in (authoritative, mirror):
            payload = json.loads(path.read_text(encoding="utf-8"))
            _check_node(payload)
