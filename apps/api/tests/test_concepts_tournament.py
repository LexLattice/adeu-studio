from __future__ import annotations

import json
from pathlib import Path

import adeu_api.main as api_main
import pytest
from adeu_api.main import (
    ConceptQuestionsRequest,
    ConceptTournamentCandidateInput,
    ConceptTournamentRequest,
    concept_questions_endpoint,
    concept_tournament_endpoint,
)
from adeu_concepts import ConceptIR
from adeu_ir.models import JsonPatchOp
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode
from fastapi import HTTPException


def _fixture_ir(*, fixture: str, name: str) -> ConceptIR:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / fixture / "proposals" / name
    return ConceptIR.model_validate(json.loads(path.read_text(encoding="utf-8")))


def _fixture_source(*, fixture: str) -> str:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / fixture / "source.txt"
    return path.read_text(encoding="utf-8").strip()


def _no_op_candidate(concept: ConceptIR) -> ConceptTournamentCandidateInput:
    return ConceptTournamentCandidateInput(
        question_id="q_noop",
        patch_ops=[
            JsonPatchOp(
                op="test",
                path="/claims/0/sense_id",
                value=concept.claims[0].sense_id,
            )
        ],
    )


def _first_patch_candidate(
    *,
    concept: ConceptIR,
    source_text: str,
) -> ConceptTournamentCandidateInput:
    questions = concept_questions_endpoint(
        ConceptQuestionsRequest(
            ir=concept,
            source_text=source_text,
            mode=KernelMode.LAX,
            include_forced_details=True,
        )
    )
    for question in questions.questions:
        for answer in question.answers:
            if answer.patch:
                return ConceptTournamentCandidateInput(
                    question_id=question.question_id,
                    patch_ops=answer.patch,
                )
    raise AssertionError("expected at least one patch answer from /concepts/questions")


def test_tournament_replay_is_deterministic_and_picks_improvement() -> None:
    concept = _fixture_ir(fixture="bank_sense_coherence", name="var2.json")
    source = _fixture_source(fixture="bank_sense_coherence")
    improving = _first_patch_candidate(concept=concept, source_text=source)
    noop = _no_op_candidate(concept)

    req = ConceptTournamentRequest(
        ir=concept,
        source_text=source,
        mode=KernelMode.LAX,
        tournament_mode="replay_candidates",
        provider="mock",
        candidates=[noop, improving],
    )
    left = concept_tournament_endpoint(req)
    right = concept_tournament_endpoint(req)

    assert left == right
    assert left.tournament_score_version == "concepts.tscore.v2"
    assert left.score_metadata.score_version == "concepts.tscore.v2"
    assert (
        left.score_metadata.tie_break_order
        == "objective_vector_desc_then_stable_id_asc"
    )
    assert left.score_metadata.objective_dimensions
    assert left.no_safe_improvement is False
    assert left.selected_candidate_id is not None
    assert left.candidates
    top = left.candidates[0]
    assert top.candidate_id == left.selected_candidate_id
    assert top.improved is True
    assert tuple(top.objective_vector) > tuple(left.base_objective_vector)
    assert top.score_version == "concepts.tscore.v2"
    assert top.tie_break_provenance.stable_id == top.candidate_id
    assert (
        top.tie_break_provenance.tie_break_order
        == "objective_vector_desc_then_stable_id_asc"
    )
    assert top.tie_break_provenance.objective_dimensions
    assert top.bridge_loss_signals == []
    assert left.bridge_loss_signals == []
    assert left.budget_report.budget_version == "budget.v1"
    assert left.budget_report.max_solver_calls == api_main.MAX_TOURNAMENT_SOLVER_CALLS_TOTAL
    assert left.budget_report.max_dry_runs == api_main.MAX_TOURNAMENT_DRY_RUN_EVALS_TOTAL
    assert 0 <= left.budget_report.used_solver_calls <= left.budget_report.max_solver_calls
    assert 0 <= left.budget_report.used_dry_runs <= left.budget_report.max_dry_runs
    assert left.mapping_trust is None
    assert left.solver_trust == "solver_backed"
    assert left.proof_trust is None


def test_tournament_replay_returns_no_safe_improvement() -> None:
    concept = _fixture_ir(fixture="bank_sense_coherence", name="var2.json")
    source = _fixture_source(fixture="bank_sense_coherence")
    req = ConceptTournamentRequest(
        ir=concept,
        source_text=source,
        mode=KernelMode.LAX,
        tournament_mode="replay_candidates",
        provider="mock",
        candidates=[_no_op_candidate(concept)],
    )
    response = concept_tournament_endpoint(req)

    assert response.no_safe_improvement is True
    assert response.selected_candidate_id is None
    assert response.candidates
    assert response.candidates[0].improved is False


def test_tournament_replay_requires_candidates() -> None:
    concept = _fixture_ir(fixture="bank_sense_coherence", name="var2.json")
    source = _fixture_source(fixture="bank_sense_coherence")

    with pytest.raises(HTTPException) as exc_info:
        concept_tournament_endpoint(
            ConceptTournamentRequest(
                ir=concept,
                source_text=source,
                mode=KernelMode.LAX,
                tournament_mode="replay_candidates",
                provider="mock",
                candidates=None,
            )
        )

    assert exc_info.value.status_code == 400
    assert exc_info.value.detail["code"] == "TOURNAMENT_NO_CANDIDATES"


def test_tournament_stale_ir_hash_error_code() -> None:
    concept = _fixture_ir(fixture="bank_sense_coherence", name="var2.json")
    source = _fixture_source(fixture="bank_sense_coherence")

    with pytest.raises(HTTPException) as exc_info:
        concept_tournament_endpoint(
            ConceptTournamentRequest(
                ir=concept,
                source_text=source,
                mode=KernelMode.LAX,
                tournament_mode="replay_candidates",
                provider="mock",
                candidates=[_no_op_candidate(concept)],
                expected_ir_hash="deadbeef",
            )
        )

    detail = exc_info.value.detail
    assert exc_info.value.status_code == 409
    assert detail["code"] == "TOURNAMENT_STALE_IR_HASH_MISMATCH"
    assert detail["legacy_code"] == "STALE_IR"
    assert detail["provided_ir_hash"] == "deadbeef"
    assert isinstance(detail["expected_ir_hash"], str)


def test_tournament_live_generation_provider_error() -> None:
    concept = _fixture_ir(fixture="bank_sense_coherence", name="var2.json")
    source = _fixture_source(fixture="bank_sense_coherence")

    with pytest.raises(HTTPException) as exc_info:
        concept_tournament_endpoint(
            ConceptTournamentRequest(
                ir=concept,
                source_text=source,
                mode=KernelMode.LAX,
                tournament_mode="live_generation",
                provider="openai",
            )
        )

    assert exc_info.value.status_code == 502
    assert exc_info.value.detail["code"] == "TOURNAMENT_PROVIDER_ERROR"


def test_tournament_budget_report_truncates_on_dry_run_cap() -> None:
    concept = _fixture_ir(fixture="bank_sense_coherence", name="var2.json")
    source = _fixture_source(fixture="bank_sense_coherence")
    noop = _no_op_candidate(concept)
    req = ConceptTournamentRequest(
        ir=concept,
        source_text=source,
        mode=KernelMode.LAX,
        tournament_mode="replay_candidates",
        provider="mock",
        candidates=[
            noop,
            noop.model_copy(update={"question_id": "q_noop_2"}),
            noop.model_copy(update={"question_id": "q_noop_3"}),
        ],
        max_dry_runs=1,
        max_solver_calls=10,
    )
    response = concept_tournament_endpoint(req)

    assert response.candidate_count == 3
    assert response.evaluated_count == 1
    assert len(response.candidates) == 1
    assert response.budget_report.max_dry_runs == 1
    assert response.budget_report.used_dry_runs == 1
    assert response.budget_report.truncated is True
    assert (
        response.budget_report.truncation_reason
        == api_main.QUESTION_TRUNCATION_REASON_DRY_RUN_CAP
    )
