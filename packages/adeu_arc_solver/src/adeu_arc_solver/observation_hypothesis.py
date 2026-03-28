from __future__ import annotations

from copy import deepcopy
from typing import Any

from adeu_arc_agi import derive_v42b_arc_hypothesis_frame, derive_v42b_arc_observation_frame


def derive_v42b_observation_and_hypothesis(
    *,
    task_packet: dict[str, Any],
    task_packet_ref: str,
    observation_inputs: dict[str, Any],
    hypothesis_inputs: dict[str, Any],
    observation_frame_ref: str,
) -> tuple[dict[str, Any], dict[str, Any]]:
    observation_frame = derive_v42b_arc_observation_frame(
        task_packet=deepcopy(task_packet),
        task_packet_ref=task_packet_ref,
        ontology_register=deepcopy(observation_inputs["ontology_register"]),
        entity_inventory=deepcopy(observation_inputs["entity_inventory"]),
        relation_inventory=deepcopy(observation_inputs["relation_inventory"]),
        state_partition_register=deepcopy(observation_inputs["state_partition_register"]),
        ontology_uncertainty_register=deepcopy(
            observation_inputs.get("ontology_uncertainty_register", [])
        ),
        observation_entries=deepcopy(observation_inputs["observation_entries"]),
        required_dimension_set=deepcopy(observation_inputs.get("required_dimension_set")),
        missing_dimension_register=deepcopy(observation_inputs.get("missing_dimension_register")),
    )
    hypothesis_frame = derive_v42b_arc_hypothesis_frame(
        task_packet=deepcopy(task_packet),
        task_packet_ref=task_packet_ref,
        observation_frame=deepcopy(observation_frame),
        observation_frame_ref=observation_frame_ref,
        hypothesis_register=deepcopy(hypothesis_inputs["hypothesis_register"]),
        ambiguity_register=deepcopy(hypothesis_inputs.get("ambiguity_register", [])),
        claim_posture_register=deepcopy(hypothesis_inputs["claim_posture_register"]),
        deontic_admissibility_register=deepcopy(
            hypothesis_inputs["deontic_admissibility_register"]
        ),
        utility_pressure_register=deepcopy(hypothesis_inputs["utility_pressure_register"]),
        working_hypothesis_posture=deepcopy(hypothesis_inputs["working_hypothesis_posture"]),
    )
    return observation_frame, hypothesis_frame
