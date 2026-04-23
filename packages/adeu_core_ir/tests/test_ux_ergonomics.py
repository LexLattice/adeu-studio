from __future__ import annotations

import copy
import json
import re
from pathlib import Path

import pytest
from adeu_core_ir import (
    FROZEN_V67A_CANDIDATE_PROFILE_IDS,
    FROZEN_V67A_CLASS_IDS,
    FROZEN_V67A_COMPONENT_REF_SEQUENCE,
    UXComponentErgonomicRegistry,
    UXComponentVisibilityContract,
    UXErgonomicAdjudicationRequest,
    UXErgonomicAdjudicationResult,
    UXErgonomicCandidateProjectionProfileTable,
    UXErgonomicCaseEnvelope,
    UXErgonomicRuleAuthorityStack,
    UXInteractionContract,
    UXSurfaceProjection,
    V36AFirstFamilyApprovedProfileTable,
    V36ASameContextReachabilityGlossary,
    assert_ux_adjudication_result_consistent_with_request,
    assert_ux_ergonomic_bundle_source_binding_consistent,
    assert_ux_ergonomic_candidate_projection_table_bound_to_approved_profiles,
    assert_ux_ergonomic_candidate_projection_table_bound_to_surface_projection,
    assert_ux_visibility_contract_complete_for_projection,
    canonicalize_ux_component_ergonomic_registry_payload,
    canonicalize_ux_component_visibility_contract_payload,
    canonicalize_ux_ergonomic_adjudication_request_payload,
    canonicalize_ux_ergonomic_adjudication_result_payload,
    canonicalize_ux_ergonomic_candidate_projection_profile_table_payload,
    canonicalize_ux_ergonomic_case_envelope_payload,
    canonicalize_ux_ergonomic_rule_authority_stack_payload,
)
from adeu_ir.repo import repo_root
from pydantic import ValidationError


def _fixtures_root() -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "ux_ergonomics" / "vnext_plus185"


def _ux_governance_root(version: str) -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "ux_governance" / version


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def test_v67a_reference_fixtures_validate_and_bind_to_released_ux_governance() -> None:
    fixtures_root = _fixtures_root()
    governance61 = _ux_governance_root("vnext_plus61")
    governance62 = _ux_governance_root("vnext_plus62")
    rule_stack_path = (
        fixtures_root / "ux_ergonomic_rule_authority_stack_artifact_inspector_reference.json"
    )
    registry_path = (
        fixtures_root / "ux_component_ergonomic_registry_artifact_inspector_reference.json"
    )
    visibility_contract_path = (
        fixtures_root / "ux_component_visibility_contract_artifact_inspector_reference.json"
    )
    candidate_table_path = (
        fixtures_root
        / "ux_ergonomic_candidate_projection_profile_table_artifact_inspector_reference.json"
    )
    case_envelope_path = (
        fixtures_root
        / "ux_ergonomic_case_envelope_artifact_inspector_desktop_maximized_reference.json"
    )
    request_path = (
        fixtures_root
        / "ux_ergonomic_adjudication_request_artifact_inspector_desktop_maximized_reference.json"
    )
    result_path = (
        fixtures_root
        / "ux_ergonomic_adjudication_result_artifact_inspector_desktop_maximized_reference.json"
    )

    rule_authority_stack = UXErgonomicRuleAuthorityStack.model_validate(
        _load_json(rule_stack_path)
    )
    registry = UXComponentErgonomicRegistry.model_validate(_load_json(registry_path))
    visibility_contract = UXComponentVisibilityContract.model_validate(
        _load_json(visibility_contract_path)
    )
    candidate_projection_table = UXErgonomicCandidateProjectionProfileTable.model_validate(
        _load_json(candidate_table_path)
    )
    case_envelope = UXErgonomicCaseEnvelope.model_validate(_load_json(case_envelope_path))
    request = UXErgonomicAdjudicationRequest.model_validate(_load_json(request_path))
    result = UXErgonomicAdjudicationResult.model_validate(_load_json(result_path))

    approved_profile_table = V36AFirstFamilyApprovedProfileTable.model_validate(
        _load_json(governance61 / "v36a_first_family_approved_profile_table.json")
    )
    same_context_glossary = V36ASameContextReachabilityGlossary.model_validate(
        _load_json(governance61 / "v36a_same_context_reachability_glossary.json")
    )
    surface_projection = UXSurfaceProjection.model_validate(
        _load_json(governance62 / "ux_surface_projection_artifact_inspector_reference.json")
    )
    interaction_contract = UXInteractionContract.model_validate(
        _load_json(governance62 / "ux_interaction_contract_artifact_inspector_reference.json")
    )

    assert [row.class_id for row in registry.class_rows] == list(FROZEN_V67A_CLASS_IDS)
    assert [row.component_ref for row in visibility_contract.component_rows] == sorted(
        FROZEN_V67A_COMPONENT_REF_SEQUENCE
    )
    assert [row.candidate_profile_id for row in candidate_projection_table.candidate_rows] == list(
        FROZEN_V67A_CANDIDATE_PROFILE_IDS
    )

    assert_ux_ergonomic_candidate_projection_table_bound_to_approved_profiles(
        candidate_projection_table=candidate_projection_table,
        approved_profile_table=approved_profile_table,
    )
    assert_ux_ergonomic_candidate_projection_table_bound_to_surface_projection(
        candidate_projection_table=candidate_projection_table,
        surface_projection=surface_projection,
        interaction_contract=interaction_contract,
        same_context_glossary=same_context_glossary,
    )
    assert_ux_visibility_contract_complete_for_projection(
        visibility_contract=visibility_contract,
        surface_projection=surface_projection,
    )
    assert_ux_ergonomic_bundle_source_binding_consistent(
        rule_authority_stack=rule_authority_stack,
        registry=registry,
        visibility_contract=visibility_contract,
        candidate_projection_table=candidate_projection_table,
        case_envelope=case_envelope,
        request=request,
        result=result,
    )
    assert_ux_adjudication_result_consistent_with_request(
        result=result,
        request=request,
        candidate_projection_table=candidate_projection_table,
    )


def test_v67a_reference_fixtures_round_trip_without_drift() -> None:
    fixtures_root = _fixtures_root()
    rule_stack_path = (
        fixtures_root / "ux_ergonomic_rule_authority_stack_artifact_inspector_reference.json"
    )
    registry_path = (
        fixtures_root / "ux_component_ergonomic_registry_artifact_inspector_reference.json"
    )
    visibility_contract_path = (
        fixtures_root / "ux_component_visibility_contract_artifact_inspector_reference.json"
    )
    candidate_table_path = (
        fixtures_root
        / "ux_ergonomic_candidate_projection_profile_table_artifact_inspector_reference.json"
    )
    case_envelope_path = (
        fixtures_root
        / "ux_ergonomic_case_envelope_artifact_inspector_desktop_maximized_reference.json"
    )
    request_path = (
        fixtures_root
        / "ux_ergonomic_adjudication_request_artifact_inspector_desktop_maximized_reference.json"
    )
    result_path = (
        fixtures_root
        / "ux_ergonomic_adjudication_result_artifact_inspector_desktop_maximized_reference.json"
    )

    assert canonicalize_ux_ergonomic_rule_authority_stack_payload(
        _load_json(rule_stack_path)
    ) == _load_json(rule_stack_path)
    assert canonicalize_ux_component_ergonomic_registry_payload(
        _load_json(registry_path)
    ) == _load_json(registry_path)
    assert canonicalize_ux_component_visibility_contract_payload(
        _load_json(visibility_contract_path)
    ) == _load_json(visibility_contract_path)
    assert canonicalize_ux_ergonomic_candidate_projection_profile_table_payload(
        _load_json(candidate_table_path)
    ) == _load_json(candidate_table_path)
    assert canonicalize_ux_ergonomic_case_envelope_payload(
        _load_json(case_envelope_path)
    ) == _load_json(case_envelope_path)
    assert canonicalize_ux_ergonomic_adjudication_request_payload(
        _load_json(request_path)
    ) == _load_json(request_path)
    assert canonicalize_ux_ergonomic_adjudication_result_payload(
        _load_json(result_path)
    ) == _load_json(result_path)


def test_v67a_source_hash_mismatch_reports_artifact_ref() -> None:
    fixtures_root = _fixtures_root()
    governance61 = _ux_governance_root("vnext_plus61")
    governance62 = _ux_governance_root("vnext_plus62")
    bad_hash = "0" * 64
    rule_authority_stack = UXErgonomicRuleAuthorityStack.model_validate(
        _load_json(
            fixtures_root
            / "ux_ergonomic_rule_authority_stack_artifact_inspector_reference.json"
        )
    )
    registry = UXComponentErgonomicRegistry.model_validate(
        _load_json(
            fixtures_root
            / "ux_component_ergonomic_registry_artifact_inspector_reference.json"
        )
    )
    visibility_payload = copy.deepcopy(
        _load_json(
            fixtures_root
            / "ux_component_visibility_contract_artifact_inspector_reference.json"
        )
    )
    bad_ref = visibility_payload["source_artifact_hashes"][0]["artifact_ref"]  # type: ignore[index]
    visibility_payload["source_artifact_hashes"][0]["artifact_hash"] = bad_hash  # type: ignore[index]
    visibility_contract = UXComponentVisibilityContract.model_validate(visibility_payload)
    candidate_payload = copy.deepcopy(
        _load_json(
            fixtures_root
            / "ux_ergonomic_candidate_projection_profile_table_artifact_inspector_reference.json"
        )
    )
    candidate_payload["source_artifact_hashes"][0]["artifact_hash"] = bad_hash  # type: ignore[index]
    candidate_projection_table = UXErgonomicCandidateProjectionProfileTable.model_validate(
        candidate_payload
    )
    case_envelope = UXErgonomicCaseEnvelope.model_validate(
        _load_json(
            fixtures_root
            / "ux_ergonomic_case_envelope_artifact_inspector_desktop_maximized_reference.json"
        )
    )
    request_payload = copy.deepcopy(
        _load_json(
            fixtures_root
            / (
                "ux_ergonomic_adjudication_request_"
                "artifact_inspector_desktop_maximized_reference.json"
            )
        )
    )
    request_payload["source_artifact_hashes"][0]["artifact_hash"] = bad_hash  # type: ignore[index]
    request = UXErgonomicAdjudicationRequest.model_validate(request_payload)
    result_payload = copy.deepcopy(
        _load_json(
            fixtures_root
            / "ux_ergonomic_adjudication_result_artifact_inspector_desktop_maximized_reference.json"
        )
    )
    result_payload["source_artifact_hashes"][0]["artifact_hash"] = bad_hash  # type: ignore[index]
    result = UXErgonomicAdjudicationResult.model_validate(result_payload)

    approved_profile_table = V36AFirstFamilyApprovedProfileTable.model_validate(
        _load_json(governance61 / "v36a_first_family_approved_profile_table.json")
    )
    same_context_glossary = V36ASameContextReachabilityGlossary.model_validate(
        _load_json(governance61 / "v36a_same_context_reachability_glossary.json")
    )
    surface_projection = UXSurfaceProjection.model_validate(
        _load_json(
            governance62 / "ux_surface_projection_artifact_inspector_reference.json"
        )
    )
    interaction_contract = UXInteractionContract.model_validate(
        _load_json(
            governance62 / "ux_interaction_contract_artifact_inspector_reference.json"
        )
    )

    assert_ux_ergonomic_candidate_projection_table_bound_to_approved_profiles(
        candidate_projection_table=candidate_projection_table,
        approved_profile_table=approved_profile_table,
    )
    assert_ux_ergonomic_candidate_projection_table_bound_to_surface_projection(
        candidate_projection_table=candidate_projection_table,
        surface_projection=surface_projection,
        interaction_contract=interaction_contract,
        same_context_glossary=same_context_glossary,
    )
    assert_ux_visibility_contract_complete_for_projection(
        visibility_contract=visibility_contract,
        surface_projection=surface_projection,
    )

    with pytest.raises(
        ValueError,
        match=rf"artifact_ref {re.escape(bad_ref)}",
    ):
        assert_ux_ergonomic_bundle_source_binding_consistent(
            rule_authority_stack=rule_authority_stack,
            registry=registry,
            visibility_contract=visibility_contract,
            candidate_projection_table=candidate_projection_table,
            case_envelope=case_envelope,
            request=request,
            result=result,
        )


def test_v67a_reject_rule_authority_stack_platform_preset_requires_repo_adoption() -> None:
    reject_path = (
        _fixtures_root()
        / (
            "reject_ux_ergonomic_rule_authority_stack_"
            "platform_preset_hard_law_without_repo_adoption.json"
        )
    )
    payload = _load_json(reject_path)

    with pytest.raises(
        ValidationError,
        match="must not treat platform preset as hard law without repo adoption",
    ):
        UXErgonomicRuleAuthorityStack.model_validate(payload)


def test_v67a_reject_rule_authority_stack_user_preference_cannot_lower_hard_floor() -> None:
    payload = _load_json(
        _fixtures_root()
        / "reject_ux_ergonomic_rule_authority_stack_user_preference_lowers_hard_floor.json"
    )

    with pytest.raises(
        ValidationError, match="must not allow user preference to lower hard floors"
    ):
        UXErgonomicRuleAuthorityStack.model_validate(payload)


def test_v67a_reject_candidate_projection_profile_table_unknown_lane_ref() -> None:
    fixtures_root = _fixtures_root()
    governance61 = _ux_governance_root("vnext_plus61")
    governance62 = _ux_governance_root("vnext_plus62")
    reject_path = (
        fixtures_root
        / "reject_ux_ergonomic_candidate_projection_profile_table_unknown_lane_ref.json"
    )

    payload = _load_json(reject_path)
    candidate_projection_table = UXErgonomicCandidateProjectionProfileTable.model_validate(payload)
    interaction_contract = UXInteractionContract.model_validate(
        _load_json(governance62 / "ux_interaction_contract_artifact_inspector_reference.json")
    )
    surface_projection = UXSurfaceProjection.model_validate(
        _load_json(governance62 / "ux_surface_projection_artifact_inspector_reference.json")
    )
    same_context_glossary = V36ASameContextReachabilityGlossary.model_validate(
        _load_json(governance61 / "v36a_same_context_reachability_glossary.json")
    )

    with pytest.raises(ValueError, match="references unknown lane"):
        assert_ux_ergonomic_candidate_projection_table_bound_to_surface_projection(
            candidate_projection_table=candidate_projection_table,
            surface_projection=surface_projection,
            interaction_contract=interaction_contract,
            same_context_glossary=same_context_glossary,
        )
