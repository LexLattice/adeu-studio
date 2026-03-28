from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from adeu_arc_solver import derive_v42e_scorecard_manifest
from adeu_ir.repo import repo_root


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def test_solver_helper_replays_v93_reference_scorecard_manifest() -> None:
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
    action = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus91"
        / "adeu_arc_action_proposal_v91_reference.json"
    )
    rollout = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus91"
        / "adeu_arc_rollout_trace_v91_reference.json"
    )
    local_eval = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus92"
        / "adeu_arc_local_eval_record_v92_reference.json"
    )
    scorecard = _load_json(
        root
        / "apps"
        / "api"
        / "fixtures"
        / "arc_agi"
        / "vnext_plus93"
        / "adeu_arc_scorecard_manifest_v93_reference.json"
    )

    derived = derive_v42e_scorecard_manifest(
        task_packet=task_packet,
        task_packet_ref=scorecard["task_packet_ref"],
        observation_frame=observation,
        observation_frame_ref=scorecard["observation_frame_ref"],
        hypothesis_frame=hypothesis,
        hypothesis_frame_ref=scorecard["hypothesis_frame_ref"],
        action_proposal=action,
        action_proposal_ref=scorecard["action_proposal_ref"],
        rollout_trace=rollout,
        rollout_trace_ref=scorecard["rollout_trace_ref"],
        local_eval_record=local_eval,
        local_eval_record_ref=scorecard["local_eval_record_ref"],
        environment_ref=scorecard["environment_ref"],
        session_ref=scorecard["session_ref"],
        competition_scope_ref=scorecard["competition_scope_ref"],
        scorecard_scope=scorecard["scorecard_scope"],
        scorecard_profile=scorecard["scorecard_profile"],
        model_id=scorecard["model_id"],
        run_id=scorecard["run_id"],
        scorecard_source_kind=scorecard["scorecard_source_kind"],
        authority_posture=scorecard["authority_posture"],
        authority_scope=scorecard["authority_scope"],
        authority_source_kind=scorecard["authority_source_kind"],
        authority_validity=scorecard["authority_validity"],
        authority_limitations=scorecard["authority_limitations"],
        competition_mode_posture=scorecard["competition_mode_posture"],
        local_replay_lineage_refs=scorecard["local_replay_lineage_refs"],
        external_replay_authority_refs=scorecard["external_replay_authority_refs"],
        scorecard_facing_metrics=scorecard["scorecard_facing_metrics"],
        official_scorecard_outcome_metrics=scorecard["official_scorecard_outcome_metrics"],
        scorecard_outcome_summary=scorecard["scorecard_outcome_summary"],
        settlement_posture_carry=scorecard["settlement_posture_carry"],
        authority_basis_refs=scorecard["authority_basis_refs"],
        deferred_authority_assertions=scorecard["deferred_authority_assertions"],
        evidence_refs=scorecard["evidence_refs"],
    )

    assert derived == scorecard
