from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest
from adeu_core_ir import (
    UXConformanceReport,
    UXDomainPacket,
    UXInteractionContract,
    UXMorphDiagnostics,
    UXMorphIR,
    UXSurfaceCompilerExport,
    UXSurfaceCompilerVariantManifest,
    UXSurfaceProjection,
    V36AFirstFamilyApprovedProfileTable,
    V36ASameContextReachabilityGlossary,
    assert_v36e_reference_bundle_consistent,
    canonicalize_ux_surface_compiler_export_payload,
    canonicalize_ux_surface_compiler_variant_manifest_payload,
)
from adeu_ir.repo import repo_root
from pydantic import ValidationError
from urm_runtime.hashing import sha256_canonical_json


def _fixtures_root(version: str) -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "ux_governance" / version


def _evidence_root(version: str) -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "artifacts" / "agent_harness" / version / "evidence_inputs"


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v36a_bundle() -> tuple[
    UXDomainPacket,
    UXMorphIR,
    V36AFirstFamilyApprovedProfileTable,
    V36ASameContextReachabilityGlossary,
]:
    root = _fixtures_root("vnext_plus61")
    return (
        UXDomainPacket.model_validate(
            _load_json(root / "ux_domain_packet_artifact_inspector_reference.json")
        ),
        UXMorphIR.model_validate(
            _load_json(root / "ux_morph_ir_artifact_inspector_reference.json")
        ),
        V36AFirstFamilyApprovedProfileTable.model_validate(
            _load_json(root / "v36a_first_family_approved_profile_table.json")
        ),
        V36ASameContextReachabilityGlossary.model_validate(
            _load_json(root / "v36a_same_context_reachability_glossary.json")
        ),
    )


def _load_v36b_pair() -> tuple[UXSurfaceProjection, UXInteractionContract]:
    root = _fixtures_root("vnext_plus62")
    return (
        UXSurfaceProjection.model_validate(
            _load_json(root / "ux_surface_projection_artifact_inspector_reference.json")
        ),
        UXInteractionContract.model_validate(
            _load_json(root / "ux_interaction_contract_artifact_inspector_reference.json")
        ),
    )


def _load_v36c_bundle() -> tuple[
    dict[str, object], dict[str, object], dict[str, object], dict[str, object]
]:
    fixture_root = _fixtures_root("vnext_plus63")
    evidence_root = _evidence_root("v63")
    return (
        _load_json(fixture_root / "v36c_rendered_reference_surface_contract.json"),
        _load_json(evidence_root / "v36c_artifact_inspector_reference_surface_snapshot_v63.json"),
        _load_json(
            evidence_root / "v36c_artifact_inspector_reference_surface_binding_manifest_v63.json"
        ),
        _load_json(evidence_root / "v36c_artifact_inspector_reference_surface_evidence_v63.json"),
    )


def _load_v36d_pair() -> tuple[UXMorphDiagnostics, UXConformanceReport]:
    root = _fixtures_root("vnext_plus64")
    return (
        UXMorphDiagnostics.model_validate(
            _load_json(root / "ux_morph_diagnostics_artifact_inspector_reference.json")
        ),
        UXConformanceReport.model_validate(
            _load_json(root / "ux_conformance_report_artifact_inspector_reference.json")
        ),
    )


def _load_v36e_bundle() -> tuple[
    dict[str, object],
    dict[str, object],
    dict[str, object],
    dict[str, object],
    dict[str, object],
]:
    root = _fixtures_root("vnext_plus65")
    return (
        _load_json(root / "ux_morph_diagnostics_artifact_inspector_alternate.json"),
        _load_json(root / "ux_conformance_report_artifact_inspector_alternate.json"),
        _load_json(root / "ux_surface_compiler_export_artifact_inspector_reference.json"),
        _load_json(root / "ux_surface_compiler_export_artifact_inspector_alternate.json"),
        _load_json(root / "ux_surface_compiler_variant_manifest_artifact_inspector.json"),
    )


def test_v36e_reference_fixtures_validate_and_bind_to_released_substrate() -> None:
    domain_packet, morph_ir, approved_profile_table, same_context_glossary = _load_v36a_bundle()
    surface_projection, interaction_contract = _load_v36b_pair()
    (
        rendered_surface_contract,
        rendered_surface_snapshot,
        rendered_surface_binding_manifest,
        rendered_reference_surface_evidence,
    ) = _load_v36c_bundle()
    diagnostics, conformance_report = _load_v36d_pair()
    (
        _alternate_diagnostics_payload,
        _alternate_conformance_payload,
        canonical_export_payload,
        alternate_export_payload,
        manifest_payload,
    ) = _load_v36e_bundle()

    canonical_export = UXSurfaceCompilerExport.model_validate(canonical_export_payload)
    alternate_export = UXSurfaceCompilerExport.model_validate(alternate_export_payload)
    variant_manifest = UXSurfaceCompilerVariantManifest.model_validate(manifest_payload)

    assert_v36e_reference_bundle_consistent(
        domain_packet=domain_packet,
        morph_ir=morph_ir,
        approved_profile_table=approved_profile_table,
        same_context_glossary=same_context_glossary,
        surface_projection=surface_projection,
        interaction_contract=interaction_contract,
        rendered_surface_contract=rendered_surface_contract,
        rendered_surface_snapshot=rendered_surface_snapshot,
        rendered_surface_binding_manifest=rendered_surface_binding_manifest,
        rendered_reference_surface_evidence=rendered_reference_surface_evidence,
        diagnostics=diagnostics,
        conformance_report=conformance_report,
        canonical_export=canonical_export,
        alternate_export=alternate_export,
        variant_manifest=variant_manifest,
    )


def test_canonicalize_v36e_reference_artifacts_round_trip_without_drift() -> None:
    (
        _alternate_diagnostics_payload,
        _alternate_conformance_payload,
        canonical_export_payload,
        alternate_export_payload,
        manifest_payload,
    ) = _load_v36e_bundle()

    assert canonicalize_ux_surface_compiler_export_payload(canonical_export_payload) == (
        canonical_export_payload
    )
    assert canonicalize_ux_surface_compiler_export_payload(alternate_export_payload) == (
        alternate_export_payload
    )
    assert canonicalize_ux_surface_compiler_variant_manifest_payload(manifest_payload) == (
        manifest_payload
    )


def test_v36e_export_rejects_non_pass_conformance_gate() -> None:
    (
        _alternate_diagnostics_payload,
        _alternate_conformance_payload,
        _canonical_export_payload,
        alternate_export_payload,
        _manifest_payload,
    ) = _load_v36e_bundle()
    broken_payload = copy.deepcopy(alternate_export_payload)
    broken_payload["conformance_gating_snapshot"]["overall_judgment"] = "needs_review"  # type: ignore[index]

    with pytest.raises(
        ValidationError,
        match="conformance report overall judgment must follow the frozen aggregation rule",
    ):
        UXSurfaceCompilerExport.model_validate(broken_payload)


def test_v36e_bundle_rejects_missing_binding_coverage() -> None:
    domain_packet, morph_ir, approved_profile_table, same_context_glossary = _load_v36a_bundle()
    surface_projection, interaction_contract = _load_v36b_pair()
    (
        rendered_surface_contract,
        rendered_surface_snapshot,
        rendered_surface_binding_manifest,
        rendered_reference_surface_evidence,
    ) = _load_v36c_bundle()
    diagnostics, conformance_report = _load_v36d_pair()
    (
        _alternate_diagnostics_payload,
        _alternate_conformance_payload,
        canonical_export_payload,
        alternate_export_payload,
        manifest_payload,
    ) = _load_v36e_bundle()
    canonical_export_payload["exported_implementation_binding_map"] = canonical_export_payload[
        "exported_implementation_binding_map"
    ][:-1]  # type: ignore[index]

    canonical_export = UXSurfaceCompilerExport.model_validate(canonical_export_payload)
    alternate_export = UXSurfaceCompilerExport.model_validate(alternate_export_payload)
    variant_manifest = UXSurfaceCompilerVariantManifest.model_validate(manifest_payload)

    with pytest.raises(
        ValueError,
        match="surface compiler export must preserve the full released v36b binding set",
    ):
        assert_v36e_reference_bundle_consistent(
            domain_packet=domain_packet,
            morph_ir=morph_ir,
            approved_profile_table=approved_profile_table,
            same_context_glossary=same_context_glossary,
            surface_projection=surface_projection,
            interaction_contract=interaction_contract,
            rendered_surface_contract=rendered_surface_contract,
            rendered_surface_snapshot=rendered_surface_snapshot,
            rendered_surface_binding_manifest=rendered_surface_binding_manifest,
            rendered_reference_surface_evidence=rendered_reference_surface_evidence,
            diagnostics=diagnostics,
            conformance_report=conformance_report,
            canonical_export=canonical_export,
            alternate_export=alternate_export,
            variant_manifest=variant_manifest,
        )


def test_v36e_bundle_rejects_out_of_table_alternate_profile_drift() -> None:
    (
        _alternate_diagnostics_payload,
        _alternate_conformance_payload,
        _canonical_export_payload,
        alternate_export_payload,
        manifest_payload,
    ) = _load_v36e_bundle()

    alternate_export_payload["approved_profile_id"] = "artifact_inspector_reference"  # type: ignore[index]
    alternate_export_payload["diagnostics_gating_snapshot"]["approved_profile_id"] = (  # type: ignore[index]
        "artifact_inspector_reference"
    )
    alternate_export_payload["conformance_gating_snapshot"]["approved_profile_id"] = (  # type: ignore[index]
        "artifact_inspector_reference"
    )
    manifest_payload["profile_variants"][1]["approved_profile_id"] = "artifact_inspector_reference"  # type: ignore[index]

    with pytest.raises(
        ValidationError,
        match="implementation target payload export_ref must bind to bundle approved_profile_id",
    ):
        UXSurfaceCompilerExport.model_validate(alternate_export_payload)

    with pytest.raises(
        ValidationError,
        match=(
            "profile_variants must enumerate canonical profile first and alternate profile second"
        ),
    ):
        UXSurfaceCompilerVariantManifest.model_validate(manifest_payload)


def test_v36e_manifest_source_hashes_match_actual_source_artifacts() -> None:
    (
        _alternate_diagnostics_payload,
        _alternate_conformance_payload,
        _canonical_export_payload,
        _alternate_export_payload,
        manifest_payload,
    ) = _load_v36e_bundle()
    variant_manifest = UXSurfaceCompilerVariantManifest.model_validate(manifest_payload)
    root = repo_root(anchor=Path(__file__))

    for profile in variant_manifest.profile_variants:
        for row in profile.source_artifact_hashes:
            payload = _load_json(root / row.artifact_ref)
            assert row.artifact_hash == sha256_canonical_json(payload)


def test_v36e_export_rejects_side_channel_prompt_inputs() -> None:
    (
        _alternate_diagnostics_payload,
        _alternate_conformance_payload,
        _canonical_export_payload,
        alternate_export_payload,
        _manifest_payload,
    ) = _load_v36e_bundle()
    alternate_export_payload["derivation_metadata"]["side_channel_prompt_inputs_rejected"] = (  # type: ignore[index]
        False
    )

    with pytest.raises(ValidationError):
        UXSurfaceCompilerExport.model_validate(alternate_export_payload)
