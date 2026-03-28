from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_arc_agi import (
    ADEU_ARC_SCORECARD_MANIFEST_SCHEMA,
    AdeuArcScorecardManifest,
    compute_adeu_arc_scorecard_manifest_id,
    derive_v42e_arc_scorecard_manifest,
)
from adeu_arc_solver import derive_v42e_scorecard_manifest
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v89_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus89"


def _v90_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus90"


def _v91_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus91"


def _v92_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus92"


def _v93_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "arc_agi" / "vnext_plus93"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_v89(name: str) -> dict[str, Any]:
    return _load_json(_v89_root() / name)


def _load_v90(name: str) -> dict[str, Any]:
    return _load_json(_v90_root() / name)


def _load_v91(name: str) -> dict[str, Any]:
    return _load_json(_v91_root() / name)


def _load_v92(name: str) -> dict[str, Any]:
    return _load_json(_v92_root() / name)


def _load_v93(name: str) -> dict[str, Any]:
    return _load_json(_v93_root() / name)


def _scorecard_schema_validator() -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_arc_agi"
            / "schema"
            / "adeu_arc_scorecard_manifest.v1.json"
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v93_reference_fixture_replays_and_validates() -> None:
    task_packet = _load_v89("adeu_arc_task_packet_v89_reference.json")
    observation = _load_v90("adeu_arc_observation_frame_v90_reference.json")
    hypothesis = _load_v90("adeu_arc_hypothesis_frame_v90_reference.json")
    action = _load_v91("adeu_arc_action_proposal_v91_reference.json")
    rollout = _load_v91("adeu_arc_rollout_trace_v91_reference.json")
    local_eval = _load_v92("adeu_arc_local_eval_record_v92_reference.json")
    scorecard = _load_v93("adeu_arc_scorecard_manifest_v93_reference.json")

    validated = AdeuArcScorecardManifest.model_validate(scorecard)
    assert validated.schema == ADEU_ARC_SCORECARD_MANIFEST_SCHEMA
    assert validated.task_packet_id == task_packet["task_packet_id"]
    assert validated.observation_frame_id == observation["observation_frame_id"]
    assert validated.hypothesis_frame_id == hypothesis["hypothesis_frame_id"]
    assert validated.action_proposal_id == action["action_proposal_id"]
    assert validated.rollout_trace_id == rollout["rollout_trace_id"]
    assert validated.local_eval_record_id == local_eval["local_eval_record_id"]

    derived = derive_v42e_arc_scorecard_manifest(
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


def test_v93_solver_helper_replays_reference_fixture() -> None:
    task_packet = _load_v89("adeu_arc_task_packet_v89_reference.json")
    observation = _load_v90("adeu_arc_observation_frame_v90_reference.json")
    hypothesis = _load_v90("adeu_arc_hypothesis_frame_v90_reference.json")
    action = _load_v91("adeu_arc_action_proposal_v91_reference.json")
    rollout = _load_v91("adeu_arc_rollout_trace_v91_reference.json")
    local_eval = _load_v92("adeu_arc_local_eval_record_v92_reference.json")
    scorecard = _load_v93("adeu_arc_scorecard_manifest_v93_reference.json")

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


def test_v93_id_is_deterministic() -> None:
    payload = _load_v93("adeu_arc_scorecard_manifest_v93_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("scorecard_manifest_id")
    assert compute_adeu_arc_scorecard_manifest_id(without_id) == payload["scorecard_manifest_id"]


def test_v93_exported_schema_accepts_reference_fixture() -> None:
    _scorecard_schema_validator().validate(
        _load_v93("adeu_arc_scorecard_manifest_v93_reference.json")
    )


def test_v93_accepts_authority_class_matrix() -> None:
    fixture_names = [
        "adeu_arc_scorecard_manifest_v93_case_local_shadow_only.json",
        "adeu_arc_scorecard_manifest_v93_case_competition_posture_declared_no_official_scorecard.json",
        "adeu_arc_scorecard_manifest_v93_case_official_imported.json",
    ]
    seen: set[str] = set()
    for fixture_name in fixture_names:
        payload = _load_v93(fixture_name)
        validated = AdeuArcScorecardManifest.model_validate(payload)
        seen.add(validated.scorecard_source_kind)
    assert seen == {
        "local_shadow_only",
        "competition_posture_declared_no_official_scorecard",
        "official_imported",
    }


def test_v93_rejects_missing_replay_lineage_binding_fixture() -> None:
    payload = _load_v93(
        "adeu_arc_scorecard_manifest_v93_reject_missing_replay_lineage_binding.json"
    )
    with pytest.raises(ValidationError, match="must include all released"):
        AdeuArcScorecardManifest.model_validate(payload)


def test_v93_rejects_local_as_official_authority_fixture() -> None:
    payload = _load_v93("adeu_arc_scorecard_manifest_v93_reject_local_as_official_authority.json")
    with pytest.raises(ValidationError, match="requires scorecard_source_kind=official_imported"):
        AdeuArcScorecardManifest.model_validate(payload)


def test_v93_rejects_leaderboard_overclaim_fixture() -> None:
    payload = _load_v93(
        "adeu_arc_scorecard_manifest_v93_reject_leaderboard_competition_overclaim_local_only.json"
    )
    with pytest.raises(ValidationError, match="forbidden term"):
        AdeuArcScorecardManifest.model_validate(payload)


def test_v93_rejects_missing_authority_posture_typing_fixture() -> None:
    payload = _load_v93(
        "adeu_arc_scorecard_manifest_v93_reject_missing_authority_posture_typing.json"
    )
    with pytest.raises(ValidationError, match="authority_posture must not be empty"):
        AdeuArcScorecardManifest.model_validate(payload)


def test_v93_rejects_settlement_posture_erasure_fixture() -> None:
    payload = _load_v93("adeu_arc_scorecard_manifest_v93_reject_settlement_posture_erasure.json")
    with pytest.raises(ValidationError, match="claim_posture_preserved must be true"):
        AdeuArcScorecardManifest.model_validate(payload)


def test_v93_rejects_submission_tournament_operator_authority_leakage_fixture() -> None:
    payload = _load_v93(
        "adeu_arc_scorecard_manifest_v93_reject_submission_tournament_operator_leakage.json"
    )
    with pytest.raises(ValidationError, match="forbidden term"):
        AdeuArcScorecardManifest.model_validate(payload)


def test_v93_rejects_forbidden_necessity_phrase_with_whitespace_variant() -> None:
    payload = deepcopy(_load_v93("adeu_arc_scorecard_manifest_v93_reference.json"))
    payload["scorecard_outcome_summary"] = "This outcome means all solutions must mirror this move."
    with pytest.raises(ValidationError, match="forbidden term 'all solutions must'"):
        AdeuArcScorecardManifest.model_validate(payload)


def test_v93_derive_rejects_local_eval_ref_mismatch() -> None:
    task_packet = _load_v89("adeu_arc_task_packet_v89_reference.json")
    observation = _load_v90("adeu_arc_observation_frame_v90_reference.json")
    hypothesis = _load_v90("adeu_arc_hypothesis_frame_v90_reference.json")
    action = _load_v91("adeu_arc_action_proposal_v91_reference.json")
    rollout = _load_v91("adeu_arc_rollout_trace_v91_reference.json")
    local_eval = _load_v92("adeu_arc_local_eval_record_v92_reference.json")
    scorecard = _load_v93("adeu_arc_scorecard_manifest_v93_reference.json")

    local_eval["observation_frame_ref"] = "fixture://tampered-observation-ref"

    with pytest.raises(
        ValueError,
        match="local_eval_record must preserve released observation_frame_ref",
    ):
        derive_v42e_arc_scorecard_manifest(
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
