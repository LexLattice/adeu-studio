from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_core_ir import (
    UXConformanceReport,
    UXDomainPacket,
    UXInteractionContract,
    UXMorphDiagnostics,
    UXMorphIR,
    UXSurfaceProjection,
    V36AFirstFamilyApprovedProfileTable,
    V36ASameContextReachabilityGlossary,
    assert_v36d_reference_bundle_consistent,
    canonicalize_ux_conformance_report_payload,
    canonicalize_ux_morph_diagnostics_payload,
    derive_v36d_overall_judgment,
)
from adeu_ir.repo import repo_root
from pydantic import ValidationError


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


def _load_v36d_pair() -> tuple[dict[str, object], dict[str, object]]:
    root = _fixtures_root("vnext_plus64")
    return (
        _load_json(root / "ux_morph_diagnostics_artifact_inspector_reference.json"),
        _load_json(root / "ux_conformance_report_artifact_inspector_reference.json"),
    )


def _warning_finding() -> dict[str, object]:
    return {
        "conformance_impact": "needs_review",
        "finding_id": "finding-provisional-authoritative-styling",
        "provenance_pointers": [
            {
                "source_path": (
                    "artifacts/agent_harness/v63/evidence_inputs/"
                    "v36c_artifact_inspector_reference_surface_snapshot_v63.json"
                ),
                "source_schema": "v36c_rendered_reference_surface_semantic_snapshot@1",
                "target_ref": "artifact_inspector_reference_main:provisional-status-surface",
            }
        ],
        "rendered_surface_assertion_inputs_used": [
            "v36c_rendered_reference_surface_contract@1",
            "v36c_rendered_reference_surface_semantic_snapshot@1",
        ],
        "severity": "warning",
        "supporting_evidence_refs": [
            (
                "artifacts/agent_harness/v63/evidence_inputs/"
                "v36c_artifact_inspector_reference_surface_snapshot_v63.json"
            )
        ],
        "violation_family": "provisional_data_rendered_with_authoritative_styling",
    }


def test_v36d_reference_fixtures_validate_and_bind_to_released_substrate() -> None:
    domain_packet, morph_ir, approved_profile_table, same_context_glossary = _load_v36a_bundle()
    surface_projection, interaction_contract = _load_v36b_pair()
    (
        rendered_surface_contract,
        rendered_surface_snapshot,
        rendered_surface_binding_manifest,
        rendered_reference_surface_evidence,
    ) = _load_v36c_bundle()
    diagnostics_payload, conformance_payload = _load_v36d_pair()

    diagnostics = UXMorphDiagnostics.model_validate(diagnostics_payload)
    conformance_report = UXConformanceReport.model_validate(conformance_payload)

    assert_v36d_reference_bundle_consistent(
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
    )
    assert conformance_report.overall_judgment == "pass"
    assert derive_v36d_overall_judgment(diagnostics.findings) == "pass"


def test_canonicalize_v36d_reference_pair_round_trips_without_drift() -> None:
    diagnostics_payload, conformance_payload = _load_v36d_pair()

    assert canonicalize_ux_morph_diagnostics_payload(diagnostics_payload) == diagnostics_payload
    assert canonicalize_ux_conformance_report_payload(conformance_payload) == conformance_payload


def test_diagnostics_reject_event_stream_truth_substitution() -> None:
    diagnostics_payload, _conformance_payload = _load_v36d_pair()
    finding = _warning_finding()
    finding["supporting_evidence_refs"] = [
        (
            "artifacts/agent_harness/v63/runtime/evidence/codex/copilot/"
            "v63-closeout-main-1/urm_events.ndjson"
        )
    ]
    diagnostics_payload["findings"] = [finding]

    with pytest.raises(
        ValidationError,
        match="must not treat event streams or worker prose as authoritative grounds",
    ):
        UXMorphDiagnostics.model_validate(diagnostics_payload)


def test_diagnostics_reject_provenance_source_path_outside_canonical_stack() -> None:
    diagnostics_payload, _conformance_payload = _load_v36d_pair()
    finding = _warning_finding()
    finding["provenance_pointers"][0]["source_path"] = "docs/LOCKED_CONTINUATION_vNEXT_PLUS64.md"  # type: ignore[index]
    diagnostics_payload["findings"] = [finding]

    with pytest.raises(
        ValidationError,
        match="provenance_pointers.source_path must resolve to the frozen canonical artifact stack",
    ):
        UXMorphDiagnostics.model_validate(diagnostics_payload)


def test_conformance_report_rejects_route_local_heuristics() -> None:
    _diagnostics_payload, conformance_payload = _load_v36d_pair()
    conformance_payload["derivation_metadata"]["fresh_route_local_heuristics_introduced"] = True  # type: ignore[index]

    with pytest.raises(ValidationError):
        UXConformanceReport.model_validate(conformance_payload)


def test_v36d_bundle_rejects_non_deterministic_aggregation() -> None:
    domain_packet, morph_ir, approved_profile_table, same_context_glossary = _load_v36a_bundle()
    surface_projection, interaction_contract = _load_v36b_pair()
    (
        rendered_surface_contract,
        rendered_surface_snapshot,
        rendered_surface_binding_manifest,
        rendered_reference_surface_evidence,
    ) = _load_v36c_bundle()
    diagnostics_payload, conformance_payload = _load_v36d_pair()
    diagnostics_payload["findings"] = [_warning_finding()]
    conformance_payload["overall_judgment"] = "pass"
    conformance_payload["severity_counts"] = {"advisory": 0, "error": 0, "warning": 1}
    conformance_payload["supporting_finding_ids"] = ["finding-provisional-authoritative-styling"]
    conformance_payload["warning_rule_families"] = [
        "provisional_data_rendered_with_authoritative_styling"
    ]

    diagnostics = UXMorphDiagnostics.model_validate(diagnostics_payload)
    conformance_report = UXConformanceReport.model_validate(conformance_payload)

    with pytest.raises(
        ValueError,
        match="conformance report overall judgment must follow the frozen aggregation rule",
    ):
        assert_v36d_reference_bundle_consistent(
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
        )


def test_v36d_bundle_rejects_mismatched_rendered_reference_tuple() -> None:
    domain_packet, morph_ir, approved_profile_table, same_context_glossary = _load_v36a_bundle()
    surface_projection, interaction_contract = _load_v36b_pair()
    (
        rendered_surface_contract,
        rendered_surface_snapshot,
        rendered_surface_binding_manifest,
        rendered_reference_surface_evidence,
    ) = _load_v36c_bundle()
    diagnostics_payload, conformance_payload = _load_v36d_pair()
    rendered_surface_contract["reference_instance_id"] = "artifact_inspector_reference_other"

    diagnostics = UXMorphDiagnostics.model_validate(diagnostics_payload)
    conformance_report = UXConformanceReport.model_validate(conformance_payload)

    with pytest.raises(
        ValueError, match="rendered_surface_contract mismatch for reference_instance_id"
    ):
        assert_v36d_reference_bundle_consistent(
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
        )


def test_v36d_bundle_rejects_supporting_finding_id_drift() -> None:
    domain_packet, morph_ir, approved_profile_table, same_context_glossary = _load_v36a_bundle()
    surface_projection, interaction_contract = _load_v36b_pair()
    (
        rendered_surface_contract,
        rendered_surface_snapshot,
        rendered_surface_binding_manifest,
        rendered_reference_surface_evidence,
    ) = _load_v36c_bundle()
    diagnostics_payload, conformance_payload = _load_v36d_pair()
    diagnostics_payload["findings"] = [_warning_finding()]
    conformance_payload["overall_judgment"] = "needs_review"
    conformance_payload["severity_counts"] = {"advisory": 0, "error": 0, "warning": 1}
    conformance_payload["supporting_finding_ids"] = []
    conformance_payload["warning_rule_families"] = [
        "provisional_data_rendered_with_authoritative_styling"
    ]

    diagnostics = UXMorphDiagnostics.model_validate(diagnostics_payload)
    conformance_report = UXConformanceReport.model_validate(conformance_payload)

    with pytest.raises(
        ValueError, match="conformance report must be derived from the diagnostics finding ids"
    ):
        assert_v36d_reference_bundle_consistent(
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
        )


def test_v36d_bundle_rejects_unbound_provenance_target_ref() -> None:
    domain_packet, morph_ir, approved_profile_table, same_context_glossary = _load_v36a_bundle()
    surface_projection, interaction_contract = _load_v36b_pair()
    (
        rendered_surface_contract,
        rendered_surface_snapshot,
        rendered_surface_binding_manifest,
        rendered_reference_surface_evidence,
    ) = _load_v36c_bundle()
    diagnostics_payload, conformance_payload = _load_v36d_pair()
    diagnostics_payload["findings"] = [_warning_finding()]
    diagnostics_payload["findings"][0]["provenance_pointers"][0]["target_ref"] = (  # type: ignore[index]
        "artifact_inspector_reference_main:typoed-surface"
    )
    conformance_payload["overall_judgment"] = "needs_review"
    conformance_payload["severity_counts"] = {"advisory": 0, "error": 0, "warning": 1}
    conformance_payload["supporting_finding_ids"] = ["finding-provisional-authoritative-styling"]
    conformance_payload["warning_rule_families"] = [
        "provisional_data_rendered_with_authoritative_styling"
    ]

    diagnostics = UXMorphDiagnostics.model_validate(diagnostics_payload)
    conformance_report = UXConformanceReport.model_validate(conformance_payload)

    with pytest.raises(
        ValueError,
        match="provenance target_ref must bind to the released v36b/v36c target set",
    ):
        assert_v36d_reference_bundle_consistent(
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
        )
