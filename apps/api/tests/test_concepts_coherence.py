from __future__ import annotations

from copy import deepcopy

from adeu_api.concepts_coherence import (
    COHERENCE_SCHEMA_VERSION,
    build_concepts_coherence_artifact,
)


def _question_artifact_base() -> dict:
    return {
        "question_rank_version": "concepts.qrank.v3",
        "solver_trust": "solver_backed",
        "mapping_trust": None,
        "bridge_loss_signals": [],
        "evidence_refs": [
            {"kind": "event", "ref": "event:run#1"},
            {"kind": "event", "ref": "event:run#2"},
        ],
        "questions": [
            {
                "question_id": "q_alpha",
                "anchors": [
                    {"object_id": "amb_bank", "json_path": "/ambiguity/0"},
                    {"object_id": "cl_1", "json_path": "/claims/0"},
                ],
            },
            {
                "question_id": "q_beta",
                "anchors": [
                    {"object_id": "ln_1", "json_path": "/links/0"},
                ],
            },
        ],
    }


def _tournament_artifact_base() -> dict:
    return {
        "tournament_score_version": "concepts.tscore.v3",
        "solver_trust": "solver_backed",
        "mapping_trust": None,
        "bridge_loss_signals": [],
        "score_metadata": {
            "score_version": "concepts.tscore.v3",
            "objective_vector_version": "concepts.tobjective.v3",
            "tie_break_version": "concepts.ttiebreak.v1",
            "tie_break_order": "objective_vector_desc_then_stable_id_asc",
        },
        "candidates": [
            {
                "candidate_id": "cand_alpha",
                "question_id": "q_alpha",
                "score_version": "concepts.tscore.v3",
                "tie_break_provenance": {
                    "stable_id": "cand_alpha",
                    "objective_vector_version": "concepts.tobjective.v3",
                    "tie_break_version": "concepts.ttiebreak.v1",
                    "tie_break_order": "objective_vector_desc_then_stable_id_asc",
                },
            },
            {
                "candidate_id": "cand_beta",
                "question_id": "q_beta",
                "score_version": "concepts.tscore.v3",
                "tie_break_provenance": {
                    "stable_id": "cand_beta",
                    "objective_vector_version": "concepts.tobjective.v3",
                    "tie_break_version": "concepts.ttiebreak.v1",
                    "tie_break_order": "objective_vector_desc_then_stable_id_asc",
                },
            },
        ],
    }


def test_concepts_coherence_artifact_is_deterministic_and_clean() -> None:
    question = _question_artifact_base()
    tournament = _tournament_artifact_base()
    bridge_loss_report = {"entries": [{"status": "preserved"}]}
    patch_apply_summary = {"entity_ids": ["amb_bank", "cl_1", "ln_1"]}

    left = build_concepts_coherence_artifact(
        run_id="run_001",
        question_artifact=question,
        tournament_artifact=tournament,
        bridge_loss_report=bridge_loss_report,
        patch_apply_summary=patch_apply_summary,
    )
    right = build_concepts_coherence_artifact(
        run_id="run_001",
        question_artifact=question,
        tournament_artifact=tournament,
        bridge_loss_report=bridge_loss_report,
        patch_apply_summary=patch_apply_summary,
    )

    assert left == right
    assert left["schema_version"] == COHERENCE_SCHEMA_VERSION
    assert left["coherence_alert_count"] == 0
    assert left["coherence_alerts"] == []
    assert left["coherence_counts_by_code"] == {}


def test_concepts_coherence_artifact_is_permutation_invariant() -> None:
    left_question = _question_artifact_base()
    left_tournament = _tournament_artifact_base()
    right_question = deepcopy(left_question)
    right_tournament = deepcopy(left_tournament)

    right_question["evidence_refs"] = list(reversed(right_question["evidence_refs"]))
    right_question["questions"] = list(reversed(right_question["questions"]))
    right_question["questions"][0]["anchors"] = list(
        reversed(right_question["questions"][0]["anchors"])
    )
    right_tournament["candidates"] = list(reversed(right_tournament["candidates"]))

    left = build_concepts_coherence_artifact(
        run_id="run_perm",
        question_artifact=left_question,
        tournament_artifact=left_tournament,
        bridge_loss_report={"entries": [{"status": "preserved"}]},
        patch_apply_summary={"entity_ids": ["amb_bank", "cl_1", "ln_1"]},
    )
    right = build_concepts_coherence_artifact(
        run_id="run_perm",
        question_artifact=right_question,
        tournament_artifact=right_tournament,
        bridge_loss_report={"entries": [{"status": "preserved"}]},
        patch_apply_summary={"entity_ids": ["ln_1", "cl_1", "amb_bank"]},
    )

    assert left == right


def test_concepts_coherence_artifact_emits_expected_alerts_for_mismatches() -> None:
    question = _question_artifact_base()
    question["question_rank_version"] = "concepts.qrank.v2"
    question["solver_trust"] = "kernel_only"
    question["mapping_trust"] = "derived_bridge"
    question["evidence_refs"] = []
    question["bridge_loss_signals"] = []
    question["questions"] = [
        {
            "question_id": "q_alpha",
            "anchors": [{"object_id": "amb_bank", "json_path": "/ambiguity/0"}],
        }
    ]

    tournament = _tournament_artifact_base()
    tournament["tournament_score_version"] = "concepts.tscore.v2"
    tournament["solver_trust"] = "solver_backed"
    tournament["mapping_trust"] = "derived_alignment"
    tournament["score_metadata"]["objective_vector_version"] = "concepts.tobjective.v2"
    tournament["score_metadata"]["tie_break_version"] = "concepts.ttiebreak.v0"
    tournament["score_metadata"]["score_version"] = "concepts.tscore.v3"
    tournament["candidates"] = [
        {
            "candidate_id": "cand_missing",
            "question_id": "q_missing",
            "score_version": "concepts.tscore.v3",
            "tie_break_provenance": {
                "stable_id": "cand_missing",
                "objective_vector_version": "concepts.tobjective.v2",
                "tie_break_version": "concepts.ttiebreak.v0",
                "tie_break_order": "objective_vector_desc_then_stable_id_asc",
            },
        }
    ]
    tournament["bridge_loss_signals"] = []

    artifact = build_concepts_coherence_artifact(
        run_id="run_mismatch",
        question_artifact=question,
        tournament_artifact=tournament,
        bridge_loss_report={"entries": [{"status": "not_modeled"}]},
        patch_apply_summary={"entity_ids": []},
    )

    codes = {item["code"] for item in artifact["coherence_alerts"]}
    assert "question_rank_version_mismatch" in codes
    assert "tournament_score_version_mismatch" in codes
    assert "missing_required_cross_artifact_references" in codes
    assert "inconsistent_question_id_references" in codes
    assert "objective_vector_version_mismatch" in codes
    assert "tie_break_version_mismatch" in codes
    assert "candidate_score_version_mismatch" in codes
    assert "candidate_objective_vector_version_mismatch" in codes
    assert "candidate_tie_break_version_mismatch" in codes
    assert "contradictory_status_labels" in codes
    assert "inconsistent_entity_id_references" in codes
    assert "missing_bridge_loss_references" in codes
    assert artifact["coherence_alert_count"] == len(artifact["coherence_alerts"])
    assert artifact["coherence_counts_by_code"]["contradictory_status_labels"] == 2
