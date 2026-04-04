from __future__ import annotations

import pytest
from adeu_odeu_sim.scenarios import get_scenario, list_scenarios


def test_v51a_scenario_set_is_frozen() -> None:
    assert [scenario.name for scenario in list_scenarios()] == [
        "healthy_baseline",
        "weak_d",
    ]


def test_get_scenario_returns_deep_copy() -> None:
    scenario = get_scenario("healthy_baseline")
    scenario.description = "changed"
    assert get_scenario("healthy_baseline").description != "changed"


def test_get_scenario_rejects_unknown_name() -> None:
    with pytest.raises(ValueError, match="unsupported V51-A scenario"):
        get_scenario("weak_e")
