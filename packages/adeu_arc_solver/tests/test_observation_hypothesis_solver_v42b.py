from __future__ import annotations

import json
from pathlib import Path

from adeu_arc_solver import derive_v42b_observation_and_hypothesis
from adeu_ir.repo import repo_root


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def test_solver_helper_replays_v90_reference_pair() -> None:
    root = _repo_root()
    task_packet = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus89"
        / "adeu_arc_task_packet_v89_reference.json"
    )
    observation = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus90"
        / "adeu_arc_observation_frame_v90_reference.json"
    )
    hypothesis = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus90"
        / "adeu_arc_hypothesis_frame_v90_reference.json"
    )

    derived_observation, derived_hypothesis = derive_v42b_observation_and_hypothesis(
        task_packet=task_packet,
        task_packet_ref="apps/api/fixtures/arc_agi/vnext_plus89/adeu_arc_task_packet_v89_reference.json",
        observation_inputs={
            "ontology_register": observation["ontology_register"],
            "entity_inventory": observation["entity_inventory"],
            "relation_inventory": observation["relation_inventory"],
            "state_partition_register": observation["state_partition_register"],
            "ontology_uncertainty_register": observation["ontology_uncertainty_register"],
            "observation_entries": observation["observation_entries"],
            "required_dimension_set": observation["required_dimension_set"],
            "missing_dimension_register": observation["missing_dimension_register"],
        },
        hypothesis_inputs={
            "hypothesis_register": hypothesis["hypothesis_register"],
            "ambiguity_register": hypothesis["ambiguity_register"],
            "claim_posture_register": hypothesis["claim_posture_register"],
            "deontic_admissibility_register": hypothesis["deontic_admissibility_register"],
            "utility_pressure_register": hypothesis["utility_pressure_register"],
            "working_hypothesis_posture": hypothesis["working_hypothesis_posture"],
        },
        observation_frame_ref="apps/api/fixtures/arc_agi/vnext_plus90/adeu_arc_observation_frame_v90_reference.json",
    )

    assert derived_observation == observation
    assert derived_hypothesis == hypothesis
