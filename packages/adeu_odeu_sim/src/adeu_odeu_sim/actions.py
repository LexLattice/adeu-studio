from __future__ import annotations

from .models import (
    ActionTemplate,
    ActionType,
    DeonticStatus,
    LaneCrossingContract,
    LaneCrossingContractKind,
    LaneDelta,
    LaneName,
)

FROZEN_ACTION_TYPE_ORDER: tuple[ActionType, ...] = (
    ActionType.CONTRIBUTE,
    ActionType.DEFECT,
    ActionType.SHARE_CLAIM,
    ActionType.MISREPORT,
    ActionType.VERIFY,
    ActionType.AUDIT,
    ActionType.SANCTION,
    ActionType.APPEAL,
    ActionType.INVEST_E,
    ActionType.INVEST_D,
    ActionType.DO_NOTHING,
)

ACTION_ORDER_INDEX: dict[ActionType, int] = {
    action_type: index for index, action_type in enumerate(FROZEN_ACTION_TYPE_ORDER)
}

LANE_CROSSING_CONTRACT_LIBRARY: dict[LaneCrossingContractKind, LaneCrossingContract] = {
    LaneCrossingContractKind.O_TO_E_TRACE: LaneCrossingContract(
        contract_kind=LaneCrossingContractKind.O_TO_E_TRACE,
        source_lane=LaneName.O,
        target_lane=LaneName.E,
        trigger_surface="material_state_change",
        effect_surface="observation_and_evidence_trace",
        diagnostic_posture="typed_trace_required",
    ),
    LaneCrossingContractKind.E_TO_D_LEGITIMACY: LaneCrossingContract(
        contract_kind=LaneCrossingContractKind.E_TO_D_LEGITIMACY,
        source_lane=LaneName.E,
        target_lane=LaneName.D,
        trigger_surface="verified_claim_or_public_report",
        effect_surface="legitimacy_belief_and_norm_commitment_update",
        diagnostic_posture="typed_legitimacy_drift_visible",
    ),
    LaneCrossingContractKind.D_TO_O_ALLOCATION: LaneCrossingContract(
        contract_kind=LaneCrossingContractKind.D_TO_O_ALLOCATION,
        source_lane=LaneName.D,
        target_lane=LaneName.O,
        trigger_surface="deontic_or_role_commitment",
        effect_surface="commons_allocation_and_material_action_selection",
        diagnostic_posture="typed_allocation_commitment_visible",
    ),
    LaneCrossingContractKind.U_TO_D_PRESSURE: LaneCrossingContract(
        contract_kind=LaneCrossingContractKind.U_TO_D_PRESSURE,
        source_lane=LaneName.U,
        target_lane=LaneName.D,
        trigger_surface="utility_pressure",
        effect_surface="deontic_contestation_or_compliance_shift",
        diagnostic_posture="typed_pressure_trace_visible",
    ),
}

ACTION_LIBRARY: dict[ActionType, ActionTemplate] = {
    ActionType.CONTRIBUTE: ActionTemplate(
        action_type=ActionType.CONTRIBUTE,
        actor_eligibility=("all",),
        material_cost=1.0,
        observability=0.8,
        evidence_emission="commons_contribution_trace",
        base_deontic_status=DeonticStatus.PERMITTED,
        lane_impact=LaneDelta(O=0.8, E=0.1, D=0.1, U=-0.1),
    ),
    ActionType.DEFECT: ActionTemplate(
        action_type=ActionType.DEFECT,
        actor_eligibility=("all",),
        material_cost=0.0,
        observability=0.45,
        evidence_emission="hidden_extraction_trace",
        base_deontic_status=DeonticStatus.FORBIDDEN,
        lane_impact=LaneDelta(O=-0.9, E=-0.2, D=-0.25, U=0.9),
    ),
    ActionType.SHARE_CLAIM: ActionTemplate(
        action_type=ActionType.SHARE_CLAIM,
        actor_eligibility=("all",),
        material_cost=0.2,
        observability=1.0,
        evidence_emission="claim_publication",
        base_deontic_status=DeonticStatus.PERMITTED,
        lane_impact=LaneDelta(O=0.0, E=0.35, D=0.05, U=0.05),
    ),
    ActionType.MISREPORT: ActionTemplate(
        action_type=ActionType.MISREPORT,
        actor_eligibility=("all",),
        material_cost=0.1,
        observability=0.5,
        evidence_emission="misreport_signal",
        base_deontic_status=DeonticStatus.FORBIDDEN,
        lane_impact=LaneDelta(O=0.0, E=-0.7, D=-0.25, U=0.35),
    ),
    ActionType.VERIFY: ActionTemplate(
        action_type=ActionType.VERIFY,
        actor_eligibility=("all",),
        material_cost=0.8,
        observability=0.9,
        evidence_emission="verification_record",
        base_deontic_status=DeonticStatus.PERMITTED,
        lane_impact=LaneDelta(O=-0.1, E=0.8, D=0.15, U=-0.05),
    ),
    ActionType.AUDIT: ActionTemplate(
        action_type=ActionType.AUDIT,
        actor_eligibility=("auditor", "official"),
        material_cost=1.0,
        observability=1.0,
        evidence_emission="audit_result",
        base_deontic_status=DeonticStatus.PERMITTED,
        lane_impact=LaneDelta(O=-0.1, E=0.85, D=0.35, U=-0.05),
    ),
    ActionType.SANCTION: ActionTemplate(
        action_type=ActionType.SANCTION,
        actor_eligibility=("official",),
        material_cost=0.6,
        observability=1.0,
        evidence_emission="sanction_event",
        base_deontic_status=DeonticStatus.REQUIRED,
        lane_impact=LaneDelta(O=-0.1, E=0.15, D=0.75, U=-0.15),
    ),
    ActionType.APPEAL: ActionTemplate(
        action_type=ActionType.APPEAL,
        actor_eligibility=("all",),
        material_cost=0.4,
        observability=1.0,
        evidence_emission="appeal_record",
        base_deontic_status=DeonticStatus.PERMITTED,
        lane_impact=LaneDelta(O=-0.05, E=0.15, D=0.3, U=0.0),
    ),
    ActionType.INVEST_E: ActionTemplate(
        action_type=ActionType.INVEST_E,
        actor_eligibility=("all",),
        material_cost=1.3,
        observability=1.0,
        evidence_emission="public_epistemics_investment",
        base_deontic_status=DeonticStatus.PERMITTED,
        lane_impact=LaneDelta(O=0.2, E=0.8, D=0.15, U=-0.2),
    ),
    ActionType.INVEST_D: ActionTemplate(
        action_type=ActionType.INVEST_D,
        actor_eligibility=("all",),
        material_cost=1.3,
        observability=1.0,
        evidence_emission="institutional_investment",
        base_deontic_status=DeonticStatus.PERMITTED,
        lane_impact=LaneDelta(O=0.2, E=0.1, D=0.8, U=-0.2),
    ),
    ActionType.DO_NOTHING: ActionTemplate(
        action_type=ActionType.DO_NOTHING,
        actor_eligibility=("all",),
        material_cost=0.0,
        observability=0.2,
        evidence_emission="silence",
        base_deontic_status=DeonticStatus.PERMITTED,
        lane_impact=LaneDelta(O=0.0, E=-0.05, D=-0.02, U=0.05),
    ),
}

ACTION_CONTRACT_KINDS: dict[ActionType, tuple[LaneCrossingContractKind, ...]] = {
    ActionType.CONTRIBUTE: (LaneCrossingContractKind.D_TO_O_ALLOCATION,),
    ActionType.DEFECT: (
        LaneCrossingContractKind.U_TO_D_PRESSURE,
        LaneCrossingContractKind.D_TO_O_ALLOCATION,
    ),
    ActionType.SHARE_CLAIM: (LaneCrossingContractKind.O_TO_E_TRACE,),
    ActionType.MISREPORT: (
        LaneCrossingContractKind.O_TO_E_TRACE,
        LaneCrossingContractKind.U_TO_D_PRESSURE,
    ),
    ActionType.VERIFY: (
        LaneCrossingContractKind.O_TO_E_TRACE,
        LaneCrossingContractKind.E_TO_D_LEGITIMACY,
    ),
    ActionType.AUDIT: (
        LaneCrossingContractKind.O_TO_E_TRACE,
        LaneCrossingContractKind.E_TO_D_LEGITIMACY,
    ),
    ActionType.SANCTION: (LaneCrossingContractKind.D_TO_O_ALLOCATION,),
    ActionType.APPEAL: (LaneCrossingContractKind.E_TO_D_LEGITIMACY,),
    ActionType.INVEST_E: (
        LaneCrossingContractKind.D_TO_O_ALLOCATION,
        LaneCrossingContractKind.O_TO_E_TRACE,
    ),
    ActionType.INVEST_D: (LaneCrossingContractKind.D_TO_O_ALLOCATION,),
    ActionType.DO_NOTHING: (),
}


def get_action_template(action_type: ActionType) -> ActionTemplate:
    return ACTION_LIBRARY[action_type]


def get_action_contracts(action_type: ActionType) -> tuple[LaneCrossingContract, ...]:
    return tuple(
        LANE_CROSSING_CONTRACT_LIBRARY[kind] for kind in ACTION_CONTRACT_KINDS[action_type]
    )
