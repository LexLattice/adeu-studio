from __future__ import annotations

from odeu_sandbox.sim.engine import ODEUSimulation


def run_scenario(name: str, *, seed: int = 7, steps: int = 25, overrides: dict | None = None):
    sim = ODEUSimulation()
    sim.reset(name, seed=seed, overrides=overrides)
    for _ in range(steps):
        sim.step()
    return sim.get_state().metrics_history[-1]


def test_deterministic_seed_reproducibility() -> None:
    first = run_scenario("healthy_baseline", seed=7, steps=18)
    second = run_scenario("healthy_baseline", seed=7, steps=18)

    assert first.model_dump() == second.model_dump()


def test_regime_signatures_cover_target_modes() -> None:
    healthy = run_scenario("healthy_baseline", seed=7, steps=25)
    weak_d = run_scenario("weak_d", seed=7, steps=25)
    coercive = run_scenario("coercive_truth_poor_order", seed=7, steps=25)
    ai_capture = run_scenario(
        "ai_mediated_epistemics",
        seed=7,
        steps=25,
        overrides={
            "ai_mode": "sycophantic",
            "ai_reliability": 0.88,
            "misinformation": 0.36,
            "verification_capacity": 0.3,
            "archive_capacity": 0.22,
            "public_epistemics_level": 0.2,
        },
    )

    assert healthy.regime_label == "Cooperative Legible Order"
    assert healthy.institution_legitimacy > 0.9

    assert weak_d.regime_label == "Symbolic Institution Drift"
    assert weak_d.symbolic_gap > 0.4

    assert coercive.regime_label == "Coercive Truth-Poor Order"
    assert coercive.epistemic_integrity < 0.48
    assert coercive.institution_operativity > 0.9

    assert ai_capture.regime_label == "Epistemic Capture Collapse"
    assert ai_capture.utility_concentration > 0.45


def test_weak_e_reduces_epistemic_integrity_relative_to_baseline() -> None:
    healthy = run_scenario("healthy_baseline", seed=9, steps=20)
    weak_e = run_scenario("weak_e", seed=9, steps=20)

    assert weak_e.epistemic_integrity < healthy.epistemic_integrity
