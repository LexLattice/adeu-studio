from __future__ import annotations

import json
from pathlib import Path

from adeu_odeu_sim.engine import (
    ODEUSimulation,
    run_canonical_scenario,
    summarize_action_counts,
    summarize_lane_state,
)
from adeu_odeu_sim.models import EvidenceRecord
from adeu_odeu_sim.scenarios import CANONICAL_REPLAY_HORIZON, CANONICAL_REPLAY_SEED


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v51a" / name


def _summary(world) -> dict[str, object]:
    return {
        "scenario": world.scenario,
        "seed": world.seed,
        "turn": world.turn,
        "resource_pool_stock": round(world.resource_pool.stock, 6),
        "institution_legitimacy": round(world.institution.legitimacy, 6),
        "institution_operativity": round(world.institution.operativity, 6),
        "last_metric": world.metrics_history[-1].model_dump(mode="json", by_alias=True),
        "action_counts": summarize_action_counts(world),
        "lane_summary": summarize_lane_state(world),
        "event_record_count": len(world.event_records),
        "evidence_record_count": len(world.evidence_records),
        "sanction_event_count": len(world.sanction_events),
    }


def test_canonical_replay_is_byte_identical_for_healthy_baseline() -> None:
    first = run_canonical_scenario(
        "healthy_baseline",
        seed=CANONICAL_REPLAY_SEED,
        steps=CANONICAL_REPLAY_HORIZON,
    )
    second = run_canonical_scenario(
        "healthy_baseline",
        seed=CANONICAL_REPLAY_SEED,
        steps=CANONICAL_REPLAY_HORIZON,
    )
    assert first.model_dump(mode="json", by_alias=True) == second.model_dump(
        mode="json", by_alias=True
    )


def test_regime_signatures_match_starter_scenarios() -> None:
    healthy = run_canonical_scenario("healthy_baseline")
    weak_d = run_canonical_scenario("weak_d")
    assert healthy.metrics_history[-1].regime_label == "Cooperative Legible Order"
    assert weak_d.metrics_history[-1].regime_label == "Symbolic Institution Drift"


def test_replay_fixture_healthy_baseline_matches_reference() -> None:
    summary = _summary(run_canonical_scenario("healthy_baseline"))
    fixture = json.loads(_fixture_path("reference_healthy_baseline_summary.json").read_text())
    assert summary == fixture


def test_replay_fixture_weak_d_matches_reference() -> None:
    summary = _summary(run_canonical_scenario("weak_d"))
    fixture = json.loads(_fixture_path("reference_weak_d_summary.json").read_text())
    assert summary == fixture


def test_agent_iteration_order_is_frozen_by_agent_id() -> None:
    baseline = ODEUSimulation()
    baseline_world = baseline.reset("healthy_baseline", seed=CANONICAL_REPLAY_SEED)
    baseline._update_ontology(baseline_world)
    baseline._observe_world(baseline_world)
    baseline_actions = baseline.plan_actions(baseline_world)

    reordered = ODEUSimulation()
    world = reordered.reset("healthy_baseline", seed=CANONICAL_REPLAY_SEED)
    reordered._update_ontology(world)
    reordered._observe_world(world)
    unsorted_world = world.model_copy(deep=True)
    object.__setattr__(unsorted_world, "agents", list(reversed(unsorted_world.agents)))
    reordered_actions = reordered.plan_actions(unsorted_world)

    assert [action.actor_id for action in baseline_actions] == [
        action.actor_id for action in reordered_actions
    ]
    assert baseline_actions[0].model_dump(
        mode="json", by_alias=True
    ) == reordered_actions[0].model_dump(mode="json", by_alias=True)


def test_sanction_target_tiebreak_is_deterministic() -> None:
    simulation = ODEUSimulation()
    world = simulation.reset("weak_d", seed=CANONICAL_REPLAY_SEED)
    world.turn = 3
    world.evidence_records = [
        EvidenceRecord(
            id="ev_a",
            turn=3,
            kind="suspected_violation",
            proposition="norm_violation",
            value=1.0,
            confidence=0.75,
            source_ids=("act_01",),
            target_agent_id="agent_10",
        ),
        EvidenceRecord(
            id="ev_b",
            turn=3,
            kind="suspected_violation",
            proposition="norm_violation",
            value=1.0,
            confidence=0.75,
            source_ids=("act_02",),
            target_agent_id="agent_02",
        ),
    ]
    assert simulation._select_sanction_target(world) == "agent_02"
