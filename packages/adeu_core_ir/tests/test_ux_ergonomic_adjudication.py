from __future__ import annotations

import copy
import json
from pathlib import Path

from adeu_core_ir import (
    UXComponentErgonomicRegistry,
    UXComponentVisibilityContract,
    UXErgonomicAdjudicationRequest,
    UXErgonomicAdjudicationResult,
    UXErgonomicAmbiguityRow,
    UXErgonomicCandidateProjectionProfileTable,
    UXErgonomicCaseEnvelope,
    UXErgonomicFeasibleCandidateRow,
    UXErgonomicRuleAuthorityStack,
    UXInteractionContract,
    UXSurfaceProjection,
    V36AFirstFamilyApprovedProfileTable,
    V36ASameContextReachabilityGlossary,
    canonicalize_computed_ux_ergonomic_adjudication_result_payload,
    derive_ux_ergonomic_overall_judgment,
    evaluate_ux_ergonomic_adjudication_request,
)
from adeu_ir.repo import repo_root


def _ux_ergonomics_root(version: str) -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "ux_ergonomics" / version


def _ux_governance_root(version: str) -> Path:
    root = repo_root(anchor=Path(__file__))
    return root / "apps" / "api" / "fixtures" / "ux_governance" / version


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_reference_inputs() -> dict[str, object]:
    ergonomics_root = _ux_ergonomics_root("vnext_plus185")
    governance61 = _ux_governance_root("vnext_plus61")
    governance62 = _ux_governance_root("vnext_plus62")
    return {
        "rule_authority_stack": UXErgonomicRuleAuthorityStack.model_validate(
            _load_json(
                ergonomics_root
                / "ux_ergonomic_rule_authority_stack_artifact_inspector_reference.json"
            )
        ),
        "registry": UXComponentErgonomicRegistry.model_validate(
            _load_json(
                ergonomics_root
                / "ux_component_ergonomic_registry_artifact_inspector_reference.json"
            )
        ),
        "visibility_contract": UXComponentVisibilityContract.model_validate(
            _load_json(
                ergonomics_root
                / "ux_component_visibility_contract_artifact_inspector_reference.json"
            )
        ),
        "candidate_projection_table": UXErgonomicCandidateProjectionProfileTable.model_validate(
            _load_json(
                ergonomics_root
                / (
                    "ux_ergonomic_candidate_projection_profile_table_"
                    "artifact_inspector_reference.json"
                )
            )
        ),
        "case_envelope": UXErgonomicCaseEnvelope.model_validate(
            _load_json(
                ergonomics_root
                / "ux_ergonomic_case_envelope_artifact_inspector_desktop_maximized_reference.json"
            )
        ),
        "request": UXErgonomicAdjudicationRequest.model_validate(
            _load_json(
                ergonomics_root
                / (
                    "ux_ergonomic_adjudication_request_"
                    "artifact_inspector_desktop_maximized_reference.json"
                )
            )
        ),
        "approved_profile_table": V36AFirstFamilyApprovedProfileTable.model_validate(
            _load_json(governance61 / "v36a_first_family_approved_profile_table.json")
        ),
        "same_context_glossary": V36ASameContextReachabilityGlossary.model_validate(
            _load_json(governance61 / "v36a_same_context_reachability_glossary.json")
        ),
        "surface_projection": UXSurfaceProjection.model_validate(
            _load_json(governance62 / "ux_surface_projection_artifact_inspector_reference.json")
        ),
        "interaction_contract": UXInteractionContract.model_validate(
            _load_json(governance62 / "ux_interaction_contract_artifact_inspector_reference.json")
        ),
    }


def test_v67b_reference_adjudication_matches_computed_fixture() -> None:
    payload = canonicalize_computed_ux_ergonomic_adjudication_result_payload(
        **_load_reference_inputs()
    )
    expected = _load_json(
        _ux_ergonomics_root("vnext_plus186")
        / (
            "ux_ergonomic_adjudication_result_"
            "artifact_inspector_desktop_maximized_computed_reference.json"
        )
    )

    assert payload == expected


def test_v67b_invalid_request_basis_mismatch_returns_invalid_result() -> None:
    inputs = _load_reference_inputs()
    request_payload = copy.deepcopy(inputs["request"].model_dump(mode="json"))
    request_payload["source_artifact_hashes"][0]["artifact_hash"] = "0" * 64  # type: ignore[index]
    inputs["request"] = UXErgonomicAdjudicationRequest.model_validate(request_payload)

    result = evaluate_ux_ergonomic_adjudication_request(**inputs)

    assert result.report_status == "invalid_request_basis_mismatch"
    assert result.overall_judgment == "fail"
    assert result.blocked_candidate_rows == []
    assert result.feasible_candidate_rows == []


def test_v67b_hard_floor_composition_blocks_sub_floor_commit_targets() -> None:
    result = evaluate_ux_ergonomic_adjudication_request(**_load_reference_inputs())

    blocked = {
        row.candidate_profile_id: row for row in result.blocked_candidate_rows
    }
    feasible = {
        row.candidate_profile_id: row for row in result.feasible_candidate_rows
    }

    assert "artifact_inspector_maximized_split_reference" in feasible
    assert "artifact_inspector_half_screen_split_reference" in feasible
    assert blocked["artifact_inspector_narrow_stacked_same_context"].blocking_reason_codes == [
        "erg_block_target_floor_violation"
    ]
    assert (
        blocked[
            "artifact_inspector_quarter_screen_inspector_safe_buffered"
        ].blocking_reason_codes
        == ["erg_block_target_floor_violation"]
    )
    assert blocked["artifact_inspector_narrow_stacked_same_context"].authority_layers_triggered == [
        "repo_local_policy",
        "user_declared_preference",
    ]


def test_v67b_overall_judgment_marks_top_tier_tie_as_needs_review() -> None:
    judgment = derive_ux_ergonomic_overall_judgment(
        report_status="valid",
        feasible_candidate_rows=[
            UXErgonomicFeasibleCandidateRow.model_validate(
                {
                    "candidate_profile_id": "artifact_inspector_half_screen_split_reference",
                    "preference_tier": "preferred",
                    "supporting_reason_codes": [
                        "erg_support_commit_gate_gated_and_targetable"
                    ],
                }
            ),
            UXErgonomicFeasibleCandidateRow.model_validate(
                {
                    "candidate_profile_id": "artifact_inspector_maximized_split_reference",
                    "preference_tier": "preferred",
                    "supporting_reason_codes": [
                        "erg_support_commit_gate_gated_and_targetable"
                    ],
                }
            ),
        ],
        ambiguity_rows=[
            UXErgonomicAmbiguityRow.model_validate(
                {
                    "ambiguity_id": "top_tier_candidate_tie",
                    "ambiguity_kind": "deterministic_tie_unresolved",
                    "affected_candidate_ids": [
                        "artifact_inspector_half_screen_split_reference",
                        "artifact_inspector_maximized_split_reference",
                    ],
                    "severity": "warning",
                    "reason_codes": ["erg_review_top_tier_candidate_tie"],
                }
            )
        ],
        measurement_obligation_rows=[],
    )

    assert judgment == "needs_review"


def test_v67b_css_only_case_does_not_over_block_on_missing_physical_chain() -> None:
    result = evaluate_ux_ergonomic_adjudication_request(**_load_reference_inputs())

    for row in result.blocked_candidate_rows:
        assert "erg_block_physical_chain_required_but_inadmissible" not in row.blocking_reason_codes
        assert "erg_block_visual_angle_required_but_inadmissible" not in row.blocking_reason_codes

    assert result.report_status == "valid"
    assert isinstance(result, UXErgonomicAdjudicationResult)


def test_v67b_invalid_units_do_not_count_as_physical_size_admissible() -> None:
    inputs = _load_reference_inputs()
    case_envelope = inputs["case_envelope"].model_copy(deep=True)
    case_envelope.device_pixel_ratio_or_none = copy.deepcopy(case_envelope.zoom_scale_or_none)
    assert case_envelope.device_pixel_ratio_or_none is not None
    case_envelope.device_pixel_ratio_or_none.admissibility = "physical_size_admissible"
    case_envelope.device_pixel_ratio_or_none.numeric_value = 2.0
    case_envelope.device_pixel_ratio_or_none.unit = "mm"
    case_envelope.physical_screen_ppi_or_none = copy.deepcopy(
        case_envelope.preferred_text_min_css_px_or_none
    )
    assert case_envelope.physical_screen_ppi_or_none is not None
    case_envelope.physical_screen_ppi_or_none.admissibility = "physical_size_admissible"
    case_envelope.physical_screen_ppi_or_none.numeric_value = 110.0
    case_envelope.physical_screen_ppi_or_none.unit = "ratio"
    inputs["case_envelope"] = case_envelope

    result = evaluate_ux_ergonomic_adjudication_request(**inputs)

    assert result.report_status == "valid"
    ambiguity_reasons = {
        reason
        for row in result.ambiguity_rows
        for reason in row.reason_codes
    }
    assert "erg_review_physical_size_inadmissible_but_not_required" in ambiguity_reasons


def test_v67b_declared_viewport_geometry_keeps_result_in_review() -> None:
    inputs = _load_reference_inputs()
    case_envelope = inputs["case_envelope"].model_copy(deep=True)
    case_envelope.viewport_css_geometry.admissibility = "planning_declared_css_geometry"
    case_envelope.available_surface_css_geometry.admissibility = "css_geometry_admissible"
    inputs["case_envelope"] = case_envelope

    result = evaluate_ux_ergonomic_adjudication_request(**inputs)

    assert result.report_status == "valid"
    assert result.overall_judgment == "needs_review"
    half_screen = next(
        row
        for row in result.measurement_obligation_rows
        if row.candidate_profile_id == "artifact_inspector_half_screen_split_reference"
    )
    assert half_screen.reason_codes == ["erg_review_declared_geometry_not_runtime_measured"]


def test_v67b_case_envelope_admissibility_failure_stays_structural() -> None:
    inputs = _load_reference_inputs()
    case_envelope = inputs["case_envelope"].model_copy(deep=True)
    case_envelope.physical_size_reasoning_required = True
    case_envelope.device_pixel_ratio_or_none = copy.deepcopy(case_envelope.zoom_scale_or_none)
    assert case_envelope.device_pixel_ratio_or_none is not None
    case_envelope.device_pixel_ratio_or_none.admissibility = "none"
    case_envelope.device_pixel_ratio_or_none.numeric_value = 2.0
    case_envelope.device_pixel_ratio_or_none.provenance_state = "verified_device_inventory"
    case_envelope.device_pixel_ratio_or_none.source_kind = "device_inventory"
    inputs["case_envelope"] = case_envelope

    result = evaluate_ux_ergonomic_adjudication_request(**inputs)

    assert result.report_status == "invalid_case_envelope_admissibility"
    assert result.overall_judgment == "fail"
    assert result.feasible_candidate_rows == []
    assert result.measurement_obligation_rows == []
