from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_core_ir import (
    V36A_CANONICAL_REFERENCE_PROFILE_ID,
    UXDomainPacket,
    UXInteractionContract,
    UXMorphIR,
    UXSurfaceProjection,
    V36AFirstFamilyApprovedProfileTable,
    V36ASameContextReachabilityGlossary,
    assert_v36b_projection_interaction_binding,
    assert_v36b_reference_bundle_consistent,
    build_v36b_stable_binding_id,
    build_v36b_stable_provenance_hook_id,
    canonicalize_ux_interaction_contract_payload,
    canonicalize_ux_surface_projection_payload,
)
from adeu_ir.repo import repo_root
from pydantic import ValidationError


def _fixtures_root(version: str) -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "ux_governance" / version


def _load_json(version: str, name: str) -> dict[str, object]:
    return json.loads((_fixtures_root(version) / name).read_text(encoding="utf-8"))


def _load_v36a_bundle() -> tuple[
    UXDomainPacket,
    UXMorphIR,
    V36AFirstFamilyApprovedProfileTable,
    V36ASameContextReachabilityGlossary,
]:
    return (
        UXDomainPacket.model_validate(
            _load_json("vnext_plus61", "ux_domain_packet_artifact_inspector_reference.json")
        ),
        UXMorphIR.model_validate(
            _load_json("vnext_plus61", "ux_morph_ir_artifact_inspector_reference.json")
        ),
        V36AFirstFamilyApprovedProfileTable.model_validate(
            _load_json("vnext_plus61", "v36a_first_family_approved_profile_table.json")
        ),
        V36ASameContextReachabilityGlossary.model_validate(
            _load_json("vnext_plus61", "v36a_same_context_reachability_glossary.json")
        ),
    )


def _load_v36b_pair() -> tuple[UXSurfaceProjection, UXInteractionContract]:
    return (
        UXSurfaceProjection.model_validate(
            _load_json("vnext_plus62", "ux_surface_projection_artifact_inspector_reference.json")
        ),
        UXInteractionContract.model_validate(
            _load_json("vnext_plus62", "ux_interaction_contract_artifact_inspector_reference.json")
        ),
    )


def test_v36b_reference_fixtures_validate_and_bind_to_v36a_substrate() -> None:
    domain_packet, morph_ir, approved_profile_table, same_context_glossary = _load_v36a_bundle()
    surface_projection, interaction_contract = _load_v36b_pair()

    assert_v36b_reference_bundle_consistent(
        domain_packet=domain_packet,
        morph_ir=morph_ir,
        approved_profile_table=approved_profile_table,
        same_context_glossary=same_context_glossary,
        surface_projection=surface_projection,
        interaction_contract=interaction_contract,
    )
    assert surface_projection.approved_profile_id == V36A_CANONICAL_REFERENCE_PROFILE_ID
    assert interaction_contract.approved_profile_id == V36A_CANONICAL_REFERENCE_PROFILE_ID


def test_canonicalize_v36b_reference_pair_round_trips_without_drift() -> None:
    projection_payload = _load_json(
        "vnext_plus62",
        "ux_surface_projection_artifact_inspector_reference.json",
    )
    interaction_payload = _load_json(
        "vnext_plus62",
        "ux_interaction_contract_artifact_inspector_reference.json",
    )

    assert canonicalize_ux_surface_projection_payload(projection_payload) == projection_payload
    assert canonicalize_ux_interaction_contract_payload(interaction_payload) == interaction_payload


def test_v36b_binding_rejects_mismatched_reference_instance_id() -> None:
    surface_projection, _interaction_contract = _load_v36b_pair()
    payload = _load_json(
        "vnext_plus62", "ux_interaction_contract_artifact_inspector_reference.json"
    )
    payload["reference_instance_id"] = "artifact_inspector_reference_other"
    for hook in payload["stable_provenance_hooks"]:  # type: ignore[index]
        _reference_instance_id, suffix = hook["target_ref"].split(":", 1)
        hook["target_ref"] = f"artifact_inspector_reference_other:{suffix}"
        hook["hook_id"] = build_v36b_stable_provenance_hook_id(
            reference_instance_id="artifact_inspector_reference_other",
            target_kind=hook["target_kind"],
            target_ref=hook["target_ref"],
        )
    for binding in payload["implementation_observable_bindings"]:  # type: ignore[index]
        _reference_instance_id, suffix = binding["target_ref"].split(":", 1)
        binding["target_ref"] = f"artifact_inspector_reference_other:{suffix}"
        binding["binding_id"] = build_v36b_stable_binding_id(
            reference_instance_id="artifact_inspector_reference_other",
            target_kind=binding["target_kind"],
            target_ref=binding["target_ref"],
        )
    interaction_contract = UXInteractionContract.model_validate(payload)

    with pytest.raises(
        ValueError, match="projection/interaction binding mismatch for reference_instance_id"
    ):
        assert_v36b_projection_interaction_binding(
            surface_projection=surface_projection,
            interaction_contract=interaction_contract,
        )


def test_surface_projection_rejects_provenance_hook_from_different_reference_instance() -> None:
    payload = _load_json("vnext_plus62", "ux_surface_projection_artifact_inspector_reference.json")
    hook = payload["stable_provenance_hooks"][0]  # type: ignore[index]
    _reference_instance_id, suffix = hook["target_ref"].split(":", 1)
    hook["target_ref"] = f"artifact_inspector_reference_other:{suffix}"
    hook["hook_id"] = build_v36b_stable_provenance_hook_id(
        reference_instance_id="artifact_inspector_reference_other",
        target_kind=hook["target_kind"],
        target_ref=hook["target_ref"],
    )

    with pytest.raises(
        ValidationError,
        match="stable_provenance_hooks target_ref must bind to bundle reference_instance_id",
    ):
        UXSurfaceProjection.model_validate(payload)


def test_interaction_contract_rejects_binding_from_different_reference_instance() -> None:
    payload = _load_json(
        "vnext_plus62", "ux_interaction_contract_artifact_inspector_reference.json"
    )
    binding = payload["implementation_observable_bindings"][0]  # type: ignore[index]
    _reference_instance_id, suffix = binding["target_ref"].split(":", 1)
    binding["target_ref"] = f"artifact_inspector_reference_other:{suffix}"
    binding["binding_id"] = build_v36b_stable_binding_id(
        reference_instance_id="artifact_inspector_reference_other",
        target_kind=binding["target_kind"],
        target_ref=binding["target_ref"],
    )

    with pytest.raises(
        ValidationError,
        match=(
            "implementation_observable_bindings target_ref must bind to bundle "
            "reference_instance_id"
        ),
    ):
        UXInteractionContract.model_validate(payload)


def test_v36b_bundle_rejects_detached_v36a_profile_binding() -> None:
    domain_packet, morph_ir, approved_profile_table, same_context_glossary = _load_v36a_bundle()
    interaction_payload = _load_json(
        "vnext_plus62", "ux_interaction_contract_artifact_inspector_reference.json"
    )
    interaction_payload["approved_profile_id"] = "artifact_inspector_alternate"
    interaction_contract = UXInteractionContract.model_validate(interaction_payload)
    projection_payload = _load_json(
        "vnext_plus62", "ux_surface_projection_artifact_inspector_reference.json"
    )
    projection_payload["approved_profile_id"] = "artifact_inspector_alternate"
    surface_projection = UXSurfaceProjection.model_validate(projection_payload)

    with pytest.raises(
        ValueError, match="v36b reference bundle must match released v36a reference pair"
    ):
        assert_v36b_reference_bundle_consistent(
            domain_packet=domain_packet,
            morph_ir=morph_ir,
            approved_profile_table=approved_profile_table,
            same_context_glossary=same_context_glossary,
            surface_projection=surface_projection,
            interaction_contract=interaction_contract,
        )


def test_surface_projection_rejects_region_lane_membership_mismatch() -> None:
    payload = _load_json("vnext_plus62", "ux_surface_projection_artifact_inspector_reference.json")
    payload["regions"][1]["lane_ids"] = payload["regions"][1]["lane_ids"][1:]  # type: ignore[index]

    with pytest.raises(ValidationError, match="region/lane membership mismatch"):
        UXSurfaceProjection.model_validate(payload)


def test_interaction_contract_rejects_forbidden_authoritative_gate_source() -> None:
    payload = _load_json(
        "vnext_plus62", "ux_interaction_contract_artifact_inspector_reference.json"
    )
    payload["interaction_entries"][1]["authoritative_gate_source"][  # type: ignore[index]
        "source_kind"
    ] = "page_local_constants"

    with pytest.raises(ValidationError):
        UXInteractionContract.model_validate(payload)


def test_interaction_contract_requires_gate_source_for_gated_entry() -> None:
    payload = _load_json(
        "vnext_plus62", "ux_interaction_contract_artifact_inspector_reference.json"
    )
    payload["interaction_entries"][1]["authoritative_gate_source"] = None  # type: ignore[index]

    with pytest.raises(ValidationError, match="requires authoritative_gate_source"):
        UXInteractionContract.model_validate(payload)


def test_interaction_contract_rejects_overstated_runtime_visible_consequence() -> None:
    payload = _load_json(
        "vnext_plus62", "ux_interaction_contract_artifact_inspector_reference.json"
    )
    payload["interaction_entries"][3]["runtime_visible_consequence"] = {  # type: ignore[index]
        "outcome_kind": "bounded_context_focus_visible",
        "truth_posture": "request_only",
    }

    with pytest.raises(
        ValidationError,
        match="runtime_visible_consequence must remain epistemic and must not overstate success",
    ):
        UXInteractionContract.model_validate(payload)


def test_v36b_bundle_rejects_missing_minimum_binding_coverage() -> None:
    domain_packet, morph_ir, approved_profile_table, same_context_glossary = _load_v36a_bundle()
    payload = _load_json("vnext_plus62", "ux_surface_projection_artifact_inspector_reference.json")
    payload["implementation_observable_bindings"] = [
        binding
        for binding in payload["implementation_observable_bindings"]  # type: ignore[index]
        if binding["target_kind"] != "diagnostic_surface"
    ]
    surface_projection = UXSurfaceProjection.model_validate(payload)
    interaction_contract = UXInteractionContract.model_validate(
        _load_json("vnext_plus62", "ux_interaction_contract_artifact_inspector_reference.json")
    )

    with pytest.raises(
        ValueError,
        match="implementation_observable_bindings missing required target kinds",
    ):
        assert_v36b_reference_bundle_consistent(
            domain_packet=domain_packet,
            morph_ir=morph_ir,
            approved_profile_table=approved_profile_table,
            same_context_glossary=same_context_glossary,
            surface_projection=surface_projection,
            interaction_contract=interaction_contract,
        )


def test_v36b_bundle_rejects_missing_minimum_provenance_hook_coverage() -> None:
    domain_packet, morph_ir, approved_profile_table, same_context_glossary = _load_v36a_bundle()
    payload = _load_json(
        "vnext_plus62", "ux_interaction_contract_artifact_inspector_reference.json"
    )
    payload["stable_provenance_hooks"] = [
        hook
        for hook in payload["stable_provenance_hooks"]  # type: ignore[index]
        if hook["target_kind"] != "authority_bearing_control"
    ]
    interaction_contract = UXInteractionContract.model_validate(payload)
    surface_projection = UXSurfaceProjection.model_validate(
        _load_json("vnext_plus62", "ux_surface_projection_artifact_inspector_reference.json")
    )

    with pytest.raises(
        ValueError,
        match="stable_provenance_hooks missing required target kinds",
    ):
        assert_v36b_reference_bundle_consistent(
            domain_packet=domain_packet,
            morph_ir=morph_ir,
            approved_profile_table=approved_profile_table,
            same_context_glossary=same_context_glossary,
            surface_projection=surface_projection,
            interaction_contract=interaction_contract,
        )
