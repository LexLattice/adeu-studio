from __future__ import annotations

from statistics import mean, pstdev

from .models import ActionType, MetricPoint, WorldState
from .regimes import classify_regime


def clamp(value: float, low: float = 0.0, high: float = 1.0) -> float:
    return max(low, min(high, value))


def gini(values: list[float]) -> float:
    if not values:
        return 0.0
    sorted_vals = sorted(max(v, 0.0) for v in values)
    n = len(sorted_vals)
    total = sum(sorted_vals)
    if total == 0:
        return 0.0
    weighted_sum = sum((idx + 1) * val for idx, val in enumerate(sorted_vals))
    return (2 * weighted_sum) / (n * total) - (n + 1) / n


def compute_epistemic_integrity(world: WorldState, cooperation_rate: float, belief_accuracy: float) -> float:
    report_truth = mean([1.0 if report.truthful else 0.0 for report in world.public_reports[-5:]]) if world.public_reports else 0.55
    verification_rate = sum(1 for action in world.planned_actions if action.action_type == ActionType.VERIFY)
    verification_rate = verification_rate / max(1, len(world.planned_actions))
    evidence_density = len([e for e in world.evidence_records if e.turn >= max(0, world.turn - 3)]) / max(1, len(world.agents) * 2)
    evidence_density = clamp(evidence_density, 0.0, 1.0)
    misinformation_penalty = world.config.misinformation * 0.55
    score = (
        0.28 * belief_accuracy
        + 0.2 * world.institution.archive_capacity
        + 0.18 * world.institution.public_epistemics_level
        + 0.14 * report_truth
        + 0.1 * verification_rate
        + 0.1 * evidence_density
        - misinformation_penalty
    )
    return clamp(score)


def compute_metrics(world: WorldState) -> MetricPoint:
    coop_actions = [a for a in world.planned_actions if a.action_type == ActionType.CONTRIBUTE]
    defect_actions = [a for a in world.planned_actions if a.action_type == ActionType.DEFECT]
    action_denom = max(1, len(coop_actions) + len(defect_actions))
    cooperation_rate = len(coop_actions) / action_denom

    commons_health = clamp(world.resource_pool.stock / world.resource_pool.capacity)
    belief_errors = []
    for agent in world.agents:
        stock_error = abs(agent.e_state.belief_commons - world.resource_pool.stock) / max(1.0, world.resource_pool.capacity)
        legitimacy_error = abs(agent.d_state.legitimacy_belief - world.institution.legitimacy)
        blended_error = 0.65 * stock_error + 0.35 * legitimacy_error
        belief_errors.append(blended_error)
    average_belief_accuracy = clamp(1.0 - mean(belief_errors))

    epistemic_integrity = compute_epistemic_integrity(world, cooperation_rate, average_belief_accuracy)
    symbolic_gap = clamp(world.institution.formal_presence - world.institution.operativity)
    utility_concentration = clamp(gini([agent.o_state.resources for agent in world.agents]))
    trust_vals = [agent.e_state.trust_institution for agent in world.agents]
    trust_ai_vals = [agent.e_state.trust_ai for agent in world.agents]
    belief_vals = [agent.e_state.belief_commons / max(1.0, world.resource_pool.capacity) for agent in world.agents]
    trust_fragmentation = clamp(0.9 * pstdev(trust_vals) + 0.7 * pstdev(trust_ai_vals) + 0.8 * pstdev(belief_vals))

    point = MetricPoint(
        turn=world.turn,
        cooperation_rate=cooperation_rate,
        commons_health=commons_health,
        average_belief_accuracy=average_belief_accuracy,
        epistemic_integrity=epistemic_integrity,
        institution_legitimacy=clamp(world.institution.legitimacy),
        institution_operativity=clamp(world.institution.operativity),
        symbolic_gap=symbolic_gap,
        sanction_consistency=clamp(world.institution.sanction_consistency),
        utility_concentration=utility_concentration,
        trust_fragmentation=trust_fragmentation,
        regime_label="",
    )
    point.regime_label = classify_regime(point, world)
    return point
