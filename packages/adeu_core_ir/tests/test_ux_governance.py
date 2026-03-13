from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest
from adeu_core_ir import (
    V36A_CANONICAL_REFERENCE_PROFILE_ID,
    UXDomainPacket,
    UXMorphIR,
    V36AFirstFamilyApprovedProfileTable,
    V36ASameContextReachabilityGlossary,
    approved_profile_combination_allowed,
    assert_v36a_reference_bundle_consistent,
    assert_v36a_reference_instance_binding,
    canonicalize_ux_domain_packet_payload,
    canonicalize_ux_morph_ir_payload,
    canonicalize_v36a_approved_profile_table_payload,
    canonicalize_v36a_same_context_glossary_payload,
)
from adeu_ir.repo import repo_root
from pydantic import ValidationError


def _fixtures_root() -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "ux_governance" / "vnext_plus61"


def _load_json(name: str) -> dict[str, object]:
    return json.loads((_fixtures_root() / name).read_text(encoding="utf-8"))


def test_reference_bundle_fixtures_validate_and_bind() -> None:
    domain_packet = UXDomainPacket.model_validate(
        _load_json("ux_domain_packet_artifact_inspector_reference.json")
    )
    morph_ir = UXMorphIR.model_validate(_load_json("ux_morph_ir_artifact_inspector_reference.json"))
    approved_profile_table = V36AFirstFamilyApprovedProfileTable.model_validate(
        _load_json("v36a_first_family_approved_profile_table.json")
    )
    same_context_glossary = V36ASameContextReachabilityGlossary.model_validate(
        _load_json("v36a_same_context_reachability_glossary.json")
    )

    assert_v36a_reference_bundle_consistent(
        domain_packet=domain_packet,
        morph_ir=morph_ir,
        approved_profile_table=approved_profile_table,
        same_context_glossary=same_context_glossary,
    )
    assert domain_packet.reference_instance_id == "artifact_inspector_reference_main"
    assert domain_packet.approved_profile_id == V36A_CANONICAL_REFERENCE_PROFILE_ID
    assert (
        approved_profile_table.canonical_reference_profile_id == V36A_CANONICAL_REFERENCE_PROFILE_ID
    )
    assert len(approved_profile_table.profiles) == 2


def test_canonicalize_reference_bundle_fixtures_round_trips_without_drift() -> None:
    domain_payload = _load_json("ux_domain_packet_artifact_inspector_reference.json")
    morph_payload = _load_json("ux_morph_ir_artifact_inspector_reference.json")
    profile_payload = _load_json("v36a_first_family_approved_profile_table.json")
    glossary_payload = _load_json("v36a_same_context_reachability_glossary.json")

    assert canonicalize_ux_domain_packet_payload(domain_payload) == domain_payload
    assert canonicalize_ux_morph_ir_payload(morph_payload) == morph_payload
    assert canonicalize_v36a_approved_profile_table_payload(profile_payload) == profile_payload
    assert canonicalize_v36a_same_context_glossary_payload(glossary_payload) == glossary_payload


def test_reference_instance_binding_rejects_mismatched_binding_field() -> None:
    domain_packet = UXDomainPacket.model_validate(
        _load_json("ux_domain_packet_artifact_inspector_reference.json")
    )
    morph_payload = _load_json("ux_morph_ir_artifact_inspector_reference.json")
    morph_payload["reference_instance_id"] = "artifact_inspector_reference_other"
    morph_ir = UXMorphIR.model_validate(morph_payload)

    with pytest.raises(
        ValueError, match="reference instance binding mismatch for reference_instance_id"
    ):
        assert_v36a_reference_instance_binding(domain_packet=domain_packet, morph_ir=morph_ir)


def test_approved_profile_combination_policy_rejects_non_enumerated_combination() -> None:
    domain_packet = UXDomainPacket.model_validate(
        _load_json("ux_domain_packet_artifact_inspector_reference.json")
    )
    morph_payload = _load_json("ux_morph_ir_artifact_inspector_reference.json")
    morph_payload["morph_axes"]["density"] = "medium"  # type: ignore[index]
    morph_ir = UXMorphIR.model_validate(morph_payload)
    approved_profile_table = V36AFirstFamilyApprovedProfileTable.model_validate(
        _load_json("v36a_first_family_approved_profile_table.json")
    )
    same_context_glossary = V36ASameContextReachabilityGlossary.model_validate(
        _load_json("v36a_same_context_reachability_glossary.json")
    )

    assert not approved_profile_combination_allowed(
        approved_profile_table,
        morph_axes=morph_ir.morph_axes,
    )
    with pytest.raises(ValueError, match="approved profile binding mismatch for morph axes"):
        assert_v36a_reference_bundle_consistent(
            domain_packet=domain_packet,
            morph_ir=morph_ir,
            approved_profile_table=approved_profile_table,
            same_context_glossary=same_context_glossary,
        )


def test_same_context_glossary_rejects_non_frozen_sequence() -> None:
    payload = _load_json("v36a_same_context_reachability_glossary.json")
    swapped = copy.deepcopy(payload)
    swapped["same_context_reachable"] = [
        "bounded_workbench_position_shift",
        "bounded_workbench_focus_shift",
        "bounded_workbench_state_reveal",
    ]

    with pytest.raises(
        ValidationError, match="same_context_reachable must equal the frozen sequence"
    ):
        V36ASameContextReachabilityGlossary.model_validate(swapped)


def test_authority_boundary_policy_is_frozen_true() -> None:
    payload = _load_json("ux_domain_packet_artifact_inspector_reference.json")
    payload["authority_boundary_policy"]["ui_artifacts_may_express_but_may_not_mint_authority"] = (
        False  # type: ignore[index]
    )

    with pytest.raises(ValidationError):
        UXDomainPacket.model_validate(payload)
