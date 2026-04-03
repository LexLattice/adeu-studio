from __future__ import annotations

from .models import ActionTemplate, ActionType, DeonticStatus, LaneDelta


ACTION_LIBRARY: dict[ActionType, ActionTemplate] = {
    ActionType.CONTRIBUTE: ActionTemplate(
        action_type=ActionType.CONTRIBUTE,
        actor_eligibility=["all"],
        material_cost=1.0,
        observability=0.8,
        evidence_emission="commons_contribution_trace",
        base_deontic_status=DeonticStatus.PERMITTED,
        lane_impact=LaneDelta(O=0.8, E=0.1, D=0.1, U=-0.1),
    ),
    ActionType.DEFECT: ActionTemplate(
        action_type=ActionType.DEFECT,
        actor_eligibility=["all"],
        material_cost=0.0,
        observability=0.45,
        evidence_emission="hidden_extraction_trace",
        base_deontic_status=DeonticStatus.FORBIDDEN,
        lane_impact=LaneDelta(O=-0.9, E=-0.2, D=-0.2, U=0.9),
    ),
    ActionType.SHARE_CLAIM: ActionTemplate(
        action_type=ActionType.SHARE_CLAIM,
        actor_eligibility=["all"],
        material_cost=0.2,
        observability=1.0,
        evidence_emission="claim_publication",
        base_deontic_status=DeonticStatus.PERMITTED,
        lane_impact=LaneDelta(O=0.0, E=0.4, D=0.05, U=0.1),
    ),
    ActionType.MISREPORT: ActionTemplate(
        action_type=ActionType.MISREPORT,
        actor_eligibility=["all"],
        material_cost=0.1,
        observability=0.5,
        evidence_emission="misreport_signal",
        base_deontic_status=DeonticStatus.FORBIDDEN,
        lane_impact=LaneDelta(O=0.0, E=-0.7, D=-0.25, U=0.35),
    ),
    ActionType.VERIFY: ActionTemplate(
        action_type=ActionType.VERIFY,
        actor_eligibility=["all"],
        material_cost=0.8,
        observability=0.9,
        evidence_emission="verification_record",
        base_deontic_status=DeonticStatus.PERMITTED,
        lane_impact=LaneDelta(O=-0.1, E=0.8, D=0.15, U=-0.05),
    ),
    ActionType.AUDIT: ActionTemplate(
        action_type=ActionType.AUDIT,
        actor_eligibility=["auditor", "official"],
        material_cost=1.0,
        observability=1.0,
        evidence_emission="audit_result",
        base_deontic_status=DeonticStatus.PERMITTED,
        lane_impact=LaneDelta(O=-0.1, E=0.9, D=0.4, U=-0.1),
    ),
    ActionType.SANCTION: ActionTemplate(
        action_type=ActionType.SANCTION,
        actor_eligibility=["official"],
        material_cost=0.6,
        observability=1.0,
        evidence_emission="sanction_event",
        base_deontic_status=DeonticStatus.REQUIRED,
        lane_impact=LaneDelta(O=-0.1, E=0.2, D=0.7, U=-0.1),
    ),
    ActionType.APPEAL: ActionTemplate(
        action_type=ActionType.APPEAL,
        actor_eligibility=["all"],
        material_cost=0.4,
        observability=1.0,
        evidence_emission="appeal_record",
        base_deontic_status=DeonticStatus.PERMITTED,
        lane_impact=LaneDelta(O=-0.05, E=0.2, D=0.35, U=0.0),
    ),
    ActionType.INVEST_E: ActionTemplate(
        action_type=ActionType.INVEST_E,
        actor_eligibility=["all"],
        material_cost=1.3,
        observability=1.0,
        evidence_emission="public_epistemics_investment",
        base_deontic_status=DeonticStatus.PERMITTED,
        lane_impact=LaneDelta(O=0.25, E=0.8, D=0.2, U=-0.2),
    ),
    ActionType.INVEST_D: ActionTemplate(
        action_type=ActionType.INVEST_D,
        actor_eligibility=["all"],
        material_cost=1.3,
        observability=1.0,
        evidence_emission="institutional_investment",
        base_deontic_status=DeonticStatus.PERMITTED,
        lane_impact=LaneDelta(O=0.25, E=0.15, D=0.8, U=-0.2),
    ),
    ActionType.DO_NOTHING: ActionTemplate(
        action_type=ActionType.DO_NOTHING,
        actor_eligibility=["all"],
        material_cost=0.0,
        observability=0.2,
        evidence_emission="silence",
        base_deontic_status=DeonticStatus.PERMITTED,
        lane_impact=LaneDelta(O=0.0, E=-0.05, D=-0.02, U=0.05),
    ),
}


def get_action_template(action_type: ActionType) -> ActionTemplate:
    return ACTION_LIBRARY[action_type]
