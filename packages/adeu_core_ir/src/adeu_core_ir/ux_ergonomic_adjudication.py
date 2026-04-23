from __future__ import annotations

from dataclasses import dataclass, field
from typing import Literal

from .ux_ergonomics import (
    FROZEN_V67A_REQUIRED_EVIDENCE_COMPONENT_REFS,
    UXComponentErgonomicRegistry,
    UXComponentVisibilityContract,
    UXErgonomicAdjudicationRequest,
    UXErgonomicAdjudicationResult,
    UXErgonomicAmbiguityRow,
    UXErgonomicBlockedCandidateRow,
    UXErgonomicCandidateProjectionProfileRow,
    UXErgonomicCandidateProjectionProfileTable,
    UXErgonomicCaseEnvelope,
    UXErgonomicFeasibleCandidateRow,
    UXErgonomicMeasurementObligationRow,
    UXErgonomicOverallJudgment,
    UXErgonomicPreferenceTier,
    UXErgonomicReportStatus,
    UXErgonomicRuleAuthorityStack,
    assert_ux_case_envelope_admissibility_consistent,
    assert_ux_ergonomic_bundle_source_binding_consistent,
    assert_ux_ergonomic_candidate_projection_table_bound_to_approved_profiles,
    assert_ux_ergonomic_candidate_projection_table_bound_to_surface_projection,
    assert_ux_visibility_contract_complete_for_projection,
)
from .ux_governance import (
    UXInteractionContract,
    UXSurfaceProjection,
    V36AFirstFamilyApprovedProfileTable,
    V36ASameContextReachabilityGlossary,
)

_ALLOWED_CSS_ADMISSIBILITY = {"css_geometry_admissible", "planning_declared_css_geometry"}
_WINDOW_MODE_ORDER: tuple[str, ...] = (
    "quarter_screen_inspector_safe_buffered",
    "narrow_stacked_same_context",
    "half_screen_split_reference",
    "maximized_split_reference",
)
_ACTION_REF_TO_CLASS_ID: dict[str, str] = {
    "open-commit-review": "erg_comparison_action_cluster",
    "run-advisory-action": "erg_advisory_action_cluster",
    "submit-commit-request": "erg_commit_gate_action_cluster",
}
_TASK_CRITICAL_ACTIONS: dict[str, tuple[str, ...]] = {
    "compare_candidate_variant": ("open-commit-review",),
    "inspect_evidence_before_commit": ("open-commit-review", "submit-commit-request"),
    "source_review": ("submit-commit-request",),
}

_BLOCKING_REASON_CODES: tuple[str, ...] = (
    "erg_block_basis_hash_mismatch",
    "erg_block_unknown_projection_ref",
    "erg_block_unknown_approved_profile_id",
    "erg_block_unknown_same_context_reveal_term",
    "erg_block_missing_visibility_contract_row",
    "erg_block_missing_required_evidence_visibility",
    "erg_block_required_evidence_not_same_context_reachable",
    "erg_block_trust_boundary_not_visible",
    "erg_block_commit_gate_not_targetable",
    "erg_block_user_preference_lowers_hard_floor",
    "erg_block_platform_preset_claimed_as_hard_without_repo_adoption",
    "erg_block_target_floor_violation",
    "erg_block_text_floor_violation",
    "erg_block_physical_chain_required_but_inadmissible",
    "erg_block_visual_angle_required_but_inadmissible",
    "erg_block_scalar_preference_score_present",
)
_REVIEW_REASON_CODES: tuple[str, ...] = (
    "erg_review_declared_geometry_not_runtime_measured",
    "erg_review_unknown_input_mode_with_high_risk_action",
    "erg_review_unknown_task_posture",
    "erg_review_user_acuity_reduced_but_unscaled",
    "erg_review_physical_size_inadmissible_but_not_required",
    "erg_review_visual_angle_inadmissible_but_not_required",
    "erg_review_top_tier_candidate_tie",
)
_SUPPORTING_REASON_CODES: tuple[str, ...] = (
    "erg_support_preserves_required_evidence_visibility",
    "erg_support_preserves_trust_boundary_visibility",
    "erg_support_commit_gate_gated_and_targetable",
    "erg_support_same_context_reveal_validated",
    "erg_support_css_geometry_admissible",
)


@dataclass(slots=True)
class _MeasurementAdmissibility:
    css_geometry_available: bool
    physical_size_available: bool
    visual_angle_available: bool
    runtime_geometry_measured: bool


@dataclass(slots=True)
class _CandidateEvaluation:
    candidate_profile_id: str
    blocked_reason_codes: set[str] = field(default_factory=set)
    authority_layers_triggered: set[str] = field(default_factory=set)
    supporting_reason_codes: set[str] = field(default_factory=set)
    review_reason_codes: set[str] = field(default_factory=set)
    measurement_obligation_rows: list[UXErgonomicMeasurementObligationRow] = field(
        default_factory=list
    )
    residual_ambiguity_or_none: str | None = None
    preference_tier: UXErgonomicPreferenceTier | None = None


def derive_ux_ergonomic_measurement_admissibility(
    *,
    case_envelope: UXErgonomicCaseEnvelope,
) -> _MeasurementAdmissibility:
    css_geometry_available = (
        case_envelope.viewport_css_geometry.admissibility in _ALLOWED_CSS_ADMISSIBILITY
        and case_envelope.available_surface_css_geometry.admissibility in _ALLOWED_CSS_ADMISSIBILITY
    )
    runtime_geometry_measured = (
        case_envelope.available_surface_css_geometry.admissibility == "css_geometry_admissible"
    )
    device_pixel_ratio = case_envelope.device_pixel_ratio_or_none
    physical_screen_ppi = case_envelope.physical_screen_ppi_or_none
    viewing_distance_mm = case_envelope.viewing_distance_mm_or_none
    physical_size_available = (
        device_pixel_ratio is not None
        and device_pixel_ratio.admissibility == "physical_size_admissible"
        and physical_screen_ppi is not None
        and physical_screen_ppi.admissibility == "physical_size_admissible"
    )
    visual_angle_available = (
        physical_size_available
        and viewing_distance_mm is not None
        and viewing_distance_mm.admissibility == "visual_angle_admissible"
    )
    return _MeasurementAdmissibility(
        css_geometry_available=css_geometry_available,
        physical_size_available=physical_size_available,
        visual_angle_available=visual_angle_available,
        runtime_geometry_measured=runtime_geometry_measured,
    )


def _invalid_result(
    *,
    request: UXErgonomicAdjudicationRequest,
    report_status: UXErgonomicReportStatus,
) -> UXErgonomicAdjudicationResult:
    return UXErgonomicAdjudicationResult.model_validate(
        {
            "schema": "ux_ergonomic_adjudication_result@1",
            "result_id": f"{request.request_id}_computed_invalid",
            "request_ref": request.request_id,
            "source_artifact_refs": request.source_artifact_refs,
            "source_artifact_hashes": [
                row.model_dump(mode="json") for row in request.source_artifact_hashes
            ],
            "report_status": report_status,
            "overall_judgment": "fail",
        }
    )


def _candidate_rows_by_ref(
    *,
    candidate: UXErgonomicCandidateProjectionProfileRow,
) -> tuple[dict[str, object], dict[str, object]]:
    visibility_by_ref = {
        row.component_ref: row for row in candidate.component_visibility_claims
    }
    action_by_ref = {row.action_ref: row for row in candidate.action_targeting_claims}
    return visibility_by_ref, action_by_ref


def _applicable_hard_floor_minimum(
    *,
    rule_authority_stack: UXErgonomicRuleAuthorityStack,
    class_id: str,
    input_mode: str,
    metric: Literal["min_target_size_css_px", "min_text_size_css_px"],
) -> tuple[float | None, set[str]]:
    minimum: float | None = None
    authority_layers: set[str] = set()
    for rule in rule_authority_stack.rules:
        if (
            rule.force != "hard_floor"
            or rule.constraint.metric != metric
            or class_id not in rule.applies_to_component_classes
            or input_mode not in rule.applies_to_input_modes
            or rule.constraint.minimum_or_none is None
        ):
            continue
        minimum = max(minimum or 0.0, rule.constraint.minimum_or_none)
        authority_layers.add(rule.authority_layer)
    return minimum, authority_layers


def _window_mode_distance(
    case_mode: str,
    candidate_mode: str,
) -> int:
    return abs(_WINDOW_MODE_ORDER.index(case_mode) - _WINDOW_MODE_ORDER.index(candidate_mode))


def _tier_from_distance(distance: int) -> UXErgonomicPreferenceTier:
    if distance <= 0:
        return "preferred"
    if distance == 1:
        return "acceptable"
    if distance == 2:
        return "marginal"
    return "discouraged"


def evaluate_ux_ergonomic_candidate_row(
    *,
    candidate: UXErgonomicCandidateProjectionProfileRow,
    rule_authority_stack: UXErgonomicRuleAuthorityStack,
    registry: UXComponentErgonomicRegistry,
    visibility_contract: UXComponentVisibilityContract,
    case_envelope: UXErgonomicCaseEnvelope,
    measurement_admissibility: _MeasurementAdmissibility,
) -> _CandidateEvaluation:
    del registry
    visibility_by_ref, action_by_ref = _candidate_rows_by_ref(candidate=candidate)
    evaluation = _CandidateEvaluation(candidate_profile_id=candidate.candidate_profile_id)

    required_visibility_refs = {
        row.component_ref
        for row in visibility_contract.component_rows
        if row.continuous_visibility_required
    }
    for component_ref in required_visibility_refs:
        claim = visibility_by_ref.get(component_ref)
        if claim is None:
            evaluation.blocked_reason_codes.add("erg_block_missing_required_evidence_visibility")
            continue
        if claim.visibility_state == "continuously_visible":
            continue
        if component_ref == "lane:trust-boundary-lane":
            evaluation.blocked_reason_codes.add("erg_block_trust_boundary_not_visible")
        elif claim.visibility_state == "same_context_reachable":
            evaluation.blocked_reason_codes.add(
                "erg_block_required_evidence_not_same_context_reachable"
            )
        else:
            evaluation.blocked_reason_codes.add("erg_block_missing_required_evidence_visibility")

    critical_actions = _TASK_CRITICAL_ACTIONS[case_envelope.task_posture]
    for action_ref in critical_actions:
        claim = action_by_ref.get(action_ref)
        action_class_id = _ACTION_REF_TO_CLASS_ID[action_ref]
        minimum, authority_layers = _applicable_hard_floor_minimum(
            rule_authority_stack=rule_authority_stack,
            class_id=action_class_id,
            input_mode=case_envelope.input_mode,
            metric="min_target_size_css_px",
        )
        if claim is None:
            if action_ref == "submit-commit-request":
                evaluation.blocked_reason_codes.add("erg_block_commit_gate_not_targetable")
            else:
                evaluation.blocked_reason_codes.add("erg_block_target_floor_violation")
            evaluation.authority_layers_triggered.update(authority_layers)
            continue
        if action_ref == "submit-commit-request" and not claim.gate_visible_before_action:
            evaluation.blocked_reason_codes.add("erg_block_commit_gate_not_targetable")
            evaluation.authority_layers_triggered.update(authority_layers)
        if minimum is not None and claim.min_target_size_css_px < minimum:
            evaluation.blocked_reason_codes.add("erg_block_target_floor_violation")
            evaluation.authority_layers_triggered.update(authority_layers)

    if (
        case_envelope.physical_size_reasoning_required
        and not measurement_admissibility.physical_size_available
    ):
        evaluation.blocked_reason_codes.add("erg_block_physical_chain_required_but_inadmissible")
    elif (
        not case_envelope.physical_size_reasoning_required
        and not measurement_admissibility.physical_size_available
        and (
            case_envelope.device_pixel_ratio_or_none is not None
            or case_envelope.physical_screen_ppi_or_none is not None
        )
    ):
        evaluation.review_reason_codes.add("erg_review_physical_size_inadmissible_but_not_required")

    if (
        case_envelope.visual_angle_reasoning_required
        and not measurement_admissibility.visual_angle_available
    ):
        evaluation.blocked_reason_codes.add("erg_block_visual_angle_required_but_inadmissible")
    elif (
        not case_envelope.visual_angle_reasoning_required
        and not measurement_admissibility.visual_angle_available
        and case_envelope.viewing_distance_mm_or_none is not None
    ):
        evaluation.review_reason_codes.add("erg_review_visual_angle_inadmissible_but_not_required")

    if evaluation.blocked_reason_codes:
        if not evaluation.authority_layers_triggered:
            evaluation.authority_layers_triggered.update(
                {"constitutional_surface_invariant", "repo_local_policy"}
            )
        return evaluation

    if all(
        visibility_by_ref.get(component_ref) is not None
        and visibility_by_ref[component_ref].visibility_state == "continuously_visible"
        for component_ref in FROZEN_V67A_REQUIRED_EVIDENCE_COMPONENT_REFS
    ):
        evaluation.supporting_reason_codes.add("erg_support_preserves_required_evidence_visibility")
    trust_boundary = visibility_by_ref.get("lane:trust-boundary-lane")
    if trust_boundary is not None and trust_boundary.visibility_state == "continuously_visible":
        evaluation.supporting_reason_codes.add("erg_support_preserves_trust_boundary_visibility")
    commit_claim = action_by_ref.get("submit-commit-request")
    if commit_claim is not None and commit_claim.gate_visible_before_action:
        evaluation.supporting_reason_codes.add("erg_support_commit_gate_gated_and_targetable")
    if any(
        claim.visibility_state == "same_context_reachable" and claim.reveal_transition_or_none
        for claim in visibility_by_ref.values()
    ):
        evaluation.supporting_reason_codes.add("erg_support_same_context_reveal_validated")
    if measurement_admissibility.css_geometry_available:
        evaluation.supporting_reason_codes.add("erg_support_css_geometry_admissible")

    distance = _window_mode_distance(
        case_envelope.window_occupancy_mode,
        candidate.target_envelope,
    )
    evaluation.preference_tier = _tier_from_distance(distance)

    if (
        case_envelope.available_surface_css_geometry.admissibility
        == "planning_declared_css_geometry"
        and distance > 0
    ):
        evaluation.review_reason_codes.add("erg_review_declared_geometry_not_runtime_measured")
        evaluation.measurement_obligation_rows.append(
            UXErgonomicMeasurementObligationRow.model_validate(
                {
                    "obligation_id": f"{candidate.candidate_profile_id}_targetability_measurement",
                    "candidate_profile_id": candidate.candidate_profile_id,
                    "measurement_kind": "runtime_targetability_measurement",
                    "required_for": "needs_review",
                    "reason_codes": ["erg_review_declared_geometry_not_runtime_measured"],
                }
            )
        )
        if evaluation.preference_tier in {"marginal", "discouraged"}:
            evaluation.measurement_obligation_rows.append(
                UXErgonomicMeasurementObligationRow.model_validate(
                    {
                        "obligation_id": f"{candidate.candidate_profile_id}_visibility_measurement",
                        "candidate_profile_id": candidate.candidate_profile_id,
                        "measurement_kind": "runtime_visibility_measurement",
                        "required_for": "needs_review",
                        "reason_codes": ["erg_review_declared_geometry_not_runtime_measured"],
                    }
                )
            )
            evaluation.residual_ambiguity_or_none = (
                "same-context posture requires runtime visibility confirmation"
            )

    return evaluation


def derive_ux_ergonomic_overall_judgment(
    *,
    report_status: UXErgonomicReportStatus,
    feasible_candidate_rows: list[UXErgonomicFeasibleCandidateRow],
    ambiguity_rows: list[UXErgonomicAmbiguityRow],
    measurement_obligation_rows: list[UXErgonomicMeasurementObligationRow],
) -> UXErgonomicOverallJudgment:
    if report_status != "valid":
        return "fail"
    if not feasible_candidate_rows:
        return "fail"
    if any(row.severity == "warning" for row in ambiguity_rows):
        return "needs_review"
    if any(row.required_for == "needs_review" for row in measurement_obligation_rows):
        return "needs_review"
    return "pass"


def evaluate_ux_ergonomic_adjudication_request(
    *,
    rule_authority_stack: UXErgonomicRuleAuthorityStack,
    registry: UXComponentErgonomicRegistry,
    visibility_contract: UXComponentVisibilityContract,
    candidate_projection_table: UXErgonomicCandidateProjectionProfileTable,
    case_envelope: UXErgonomicCaseEnvelope,
    request: UXErgonomicAdjudicationRequest,
    approved_profile_table: V36AFirstFamilyApprovedProfileTable,
    same_context_glossary: V36ASameContextReachabilityGlossary,
    surface_projection: UXSurfaceProjection,
    interaction_contract: UXInteractionContract,
) -> UXErgonomicAdjudicationResult:
    try:
        assert_ux_visibility_contract_complete_for_projection(
            visibility_contract=visibility_contract,
            surface_projection=surface_projection,
        )
    except ValueError:
        return _invalid_result(
            request=request,
            report_status="invalid_visibility_contract_basis_mismatch",
        )
    try:
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
    except ValueError:
        return _invalid_result(
            request=request,
            report_status="invalid_candidate_table_basis_mismatch",
        )
    try:
        assert_ux_case_envelope_admissibility_consistent(case_envelope=case_envelope)
    except ValueError:
        return _invalid_result(
            request=request,
            report_status="invalid_case_envelope_admissibility",
        )
    try:
        assert_ux_ergonomic_bundle_source_binding_consistent(
            rule_authority_stack=rule_authority_stack,
            registry=registry,
            visibility_contract=visibility_contract,
            candidate_projection_table=candidate_projection_table,
            case_envelope=case_envelope,
            request=request,
        )
    except ValueError:
        return _invalid_result(
            request=request,
            report_status="invalid_request_basis_mismatch",
        )

    measurement_admissibility = derive_ux_ergonomic_measurement_admissibility(
        case_envelope=case_envelope
    )
    evaluations = [
        evaluate_ux_ergonomic_candidate_row(
            candidate=candidate,
            rule_authority_stack=rule_authority_stack,
            registry=registry,
            visibility_contract=visibility_contract,
            case_envelope=case_envelope,
            measurement_admissibility=measurement_admissibility,
        )
        for candidate in candidate_projection_table.candidate_rows
    ]

    blocked_rows = sorted(
        (
            UXErgonomicBlockedCandidateRow.model_validate(
                {
                    "candidate_profile_id": evaluation.candidate_profile_id,
                    "blocking_reason_codes": sorted(evaluation.blocked_reason_codes),
                    "authority_layers_triggered": sorted(evaluation.authority_layers_triggered),
                }
            )
            for evaluation in evaluations
            if evaluation.blocked_reason_codes
        ),
        key=lambda row: row.candidate_profile_id,
    )
    feasible_rows = sorted(
        (
            UXErgonomicFeasibleCandidateRow.model_validate(
                {
                    "candidate_profile_id": evaluation.candidate_profile_id,
                    "preference_tier": evaluation.preference_tier,
                    "supporting_reason_codes": sorted(evaluation.supporting_reason_codes),
                    "residual_ambiguity_or_none": evaluation.residual_ambiguity_or_none,
                }
            )
            for evaluation in evaluations
            if not evaluation.blocked_reason_codes and evaluation.preference_tier is not None
        ),
        key=lambda row: row.candidate_profile_id,
    )
    measurement_rows = sorted(
        (
            obligation
            for evaluation in evaluations
            for obligation in evaluation.measurement_obligation_rows
        ),
        key=lambda row: row.obligation_id,
    )
    ambiguity_rows = sorted(
        (
            UXErgonomicAmbiguityRow.model_validate(
                {
                    "ambiguity_id": f"{evaluation.candidate_profile_id}_review",
                    "ambiguity_kind": "runtime_confirmation_pending",
                    "affected_candidate_ids": [evaluation.candidate_profile_id],
                    "severity": "warning",
                    "reason_codes": sorted(evaluation.review_reason_codes),
                }
            )
            for evaluation in evaluations
            if evaluation.review_reason_codes and not evaluation.blocked_reason_codes
        ),
        key=lambda row: row.ambiguity_id,
    )

    preferred_ids = [
        row.candidate_profile_id for row in feasible_rows if row.preference_tier == "preferred"
    ]
    if len(preferred_ids) > 1:
        ambiguity_rows.append(
            UXErgonomicAmbiguityRow.model_validate(
                {
                    "ambiguity_id": "top_tier_candidate_tie",
                    "ambiguity_kind": "deterministic_tie_unresolved",
                    "affected_candidate_ids": sorted(preferred_ids),
                    "severity": "warning",
                    "reason_codes": ["erg_review_top_tier_candidate_tie"],
                }
            )
        )
        ambiguity_rows = sorted(ambiguity_rows, key=lambda row: row.ambiguity_id)

    overall_judgment = derive_ux_ergonomic_overall_judgment(
        report_status="valid",
        feasible_candidate_rows=feasible_rows,
        ambiguity_rows=ambiguity_rows,
        measurement_obligation_rows=measurement_rows,
    )
    return UXErgonomicAdjudicationResult.model_validate(
        {
            "schema": "ux_ergonomic_adjudication_result@1",
            "result_id": f"{request.request_id}_computed_v67b",
            "request_ref": request.request_id,
            "source_artifact_refs": request.source_artifact_refs,
            "source_artifact_hashes": [
                row.model_dump(mode="json") for row in request.source_artifact_hashes
            ],
            "report_status": "valid",
            "overall_judgment": overall_judgment,
            "blocked_candidate_rows": [row.model_dump(mode="json") for row in blocked_rows],
            "feasible_candidate_rows": [row.model_dump(mode="json") for row in feasible_rows],
            "ambiguity_rows": [row.model_dump(mode="json") for row in ambiguity_rows],
            "measurement_obligation_rows": [
                row.model_dump(mode="json") for row in measurement_rows
            ],
        }
    )


def canonicalize_computed_ux_ergonomic_adjudication_result_payload(
    **kwargs: object,
) -> dict[str, object]:
    result = evaluate_ux_ergonomic_adjudication_request(**kwargs)
    return result.model_dump(mode="json", exclude_none=True)
