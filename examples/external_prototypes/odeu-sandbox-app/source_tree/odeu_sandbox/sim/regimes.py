from __future__ import annotations

from .models import AIBiasMode, MetricPoint, WorldState


def classify_regime(metrics: MetricPoint, world: WorldState) -> str:
    if (
        metrics.cooperation_rate >= 0.6
        and metrics.epistemic_integrity >= 0.52
        and metrics.institution_legitimacy >= 0.65
        and metrics.institution_operativity >= 0.62
    ):
        return "Cooperative Legible Order"
    if (
        metrics.cooperation_rate >= 0.58
        and metrics.epistemic_integrity < 0.48
        and metrics.institution_operativity >= 0.72
        and world.institution.enforcement_capacity >= 0.75
        and world.institution.appeal_availability <= 0.45
    ):
        return "Coercive Truth-Poor Order"
    if (
        world.config.ai_mode == AIBiasMode.SYCOPHANTIC
        and metrics.epistemic_integrity < 0.5
        and metrics.average_belief_accuracy < 0.82
        and metrics.utility_concentration > 0.45
    ):
        return "Epistemic Capture Collapse"
    if (
        metrics.epistemic_integrity < 0.36
        and (metrics.commons_health < 0.6 or world.config.misinformation > 0.4)
        and metrics.institution_operativity < 0.7
    ):
        return "Epistemic Capture Collapse"
    if metrics.symbolic_gap >= 0.45 and metrics.institution_operativity < 0.62:
        return "Symbolic Institution Drift"
    if metrics.utility_concentration > 0.38 and metrics.cooperation_rate < 0.5:
        return "Fragmented Opportunism"
    return "Contested Mixed Regime"
