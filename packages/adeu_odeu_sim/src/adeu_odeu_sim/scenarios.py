from __future__ import annotations

from .models import AIBiasMode, ScenarioConfig

CANONICAL_REPLAY_SEED = 7
CANONICAL_REPLAY_HORIZON = 25

SCENARIOS: dict[str, ScenarioConfig] = {
    "healthy_baseline": ScenarioConfig(
        name="healthy_baseline",
        description=(
            "Moderate scarcity with decent evidence, decent institutions, "
            "and mixed archetypes."
        ),
        scarcity=0.35,
        regeneration_rate=0.12,
        misinformation=0.12,
        verification_capacity=0.62,
        enforcement_capacity=0.65,
        sanction_severity=1.25,
        initial_legitimacy=0.7,
        initial_operativity=0.68,
        sanction_consistency=0.75,
        archive_capacity=0.62,
        appeal_availability=0.75,
        public_epistemics_level=0.62,
        ai_mode=AIBiasMode.NONE,
        ai_reliability=0.0,
    ),
    "weak_d": ScenarioConfig(
        name="weak_d",
        description=(
            "Norms still exist, but enforcement throughput and consistency "
            "are too weak to stay operative."
        ),
        scarcity=0.35,
        regeneration_rate=0.12,
        misinformation=0.12,
        verification_capacity=0.62,
        enforcement_capacity=0.2,
        sanction_severity=0.8,
        initial_legitimacy=0.58,
        initial_operativity=0.32,
        sanction_consistency=0.3,
        archive_capacity=0.62,
        appeal_availability=0.7,
        public_epistemics_level=0.58,
        ai_mode=AIBiasMode.NONE,
        ai_reliability=0.0,
    ),
}

DEFAULT_SCENARIO_NAME = "healthy_baseline"


def get_scenario(name: str) -> ScenarioConfig:
    if name not in SCENARIOS:
        raise ValueError(f"unsupported V51-A scenario: {name}")
    return SCENARIOS[name].model_copy(deep=True)


def list_scenarios() -> list[ScenarioConfig]:
    return [SCENARIOS[name].model_copy(deep=True) for name in sorted(SCENARIOS)]
