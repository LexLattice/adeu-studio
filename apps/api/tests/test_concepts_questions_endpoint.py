from __future__ import annotations

import json
from pathlib import Path

import adeu_api.main as api_main
import pytest
from adeu_api.main import (
    ConceptApplyAmbiguityOptionRequest,
    ConceptApplyPatchRequest,
    ConceptQuestionsRequest,
    apply_concept_ambiguity_option_endpoint,
    apply_concept_patch_endpoint,
    concept_questions_endpoint,
)
from adeu_concepts import (
    AmbiguityOption,
    ConceptIR,
    ConceptQuestion,
    ConceptQuestionAnchor,
    analyze_concept,
    build_concept_questions,
    pick_latest_run,
    unavailable_analysis,
)
from adeu_concepts.analysis import AnalysisAtomRef, MicResult
from adeu_ir.models import JsonPatchOp
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode


def _fixture_ir(*, fixture: str, name: str) -> ConceptIR:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / fixture / "proposals" / name
    return ConceptIR.model_validate(json.loads(path.read_text(encoding="utf-8")))


def _fixture_source(*, fixture: str) -> str:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / fixture / "source.txt"
    return path.read_text(encoding="utf-8").strip()


def _question_key(question: ConceptQuestion, option_id: str) -> str:
    anchor_object_ids = sorted(
        {anchor.object_id for anchor in question.anchors if anchor.object_id is not None}
    )
    anchor_json_paths = sorted(
        {anchor.json_path for anchor in question.anchors if anchor.json_path is not None}
    )
    payload = {
        "signal_kind": question.signal,
        "anchor_object_ids": anchor_object_ids,
        "anchor_json_paths": anchor_json_paths,
        "selected_answer_option_id": option_id,
    }
    return json.dumps(payload, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def test_concepts_questions_endpoint_is_deterministic_and_capped() -> None:
    concept = _fixture_ir(fixture="bank_sense_coherence", name="var2.json")
    source = _fixture_source(fixture="bank_sense_coherence")

    left = concept_questions_endpoint(
        ConceptQuestionsRequest(
            ir=concept,
            source_text=source,
            mode=KernelMode.LAX,
            include_forced_details=True,
        )
    )
    right = concept_questions_endpoint(
        ConceptQuestionsRequest(
            ir=concept,
            source_text=source,
            mode=KernelMode.LAX,
            include_forced_details=True,
        )
    )

    assert left == right
    assert left.question_count == len(left.questions)
    assert left.question_count <= left.max_questions == 10
    assert left.max_answers_per_question == 4
    assert all(0 < len(item.answers) <= 4 for item in left.questions)
    assert left.question_rank_version == "concepts.qrank.v2"
    assert left.rationale_version == "concepts.rationale.v1"
    assert left.budget_report.budget_version == "budget.v1"
    assert left.budget_report.max_solver_calls == api_main.MAX_QUESTION_SOLVER_CALLS_TOTAL
    assert left.budget_report.max_dry_runs == api_main.MAX_QUESTION_DRY_RUN_EVALS_TOTAL
    assert 0 <= left.budget_report.used_solver_calls <= left.budget_report.max_solver_calls
    assert 0 <= left.budget_report.used_dry_runs <= left.budget_report.max_dry_runs
    assert left.mapping_trust is None
    assert left.solver_trust == "solver_backed"
    assert left.proof_trust is None
    for question in left.questions:
        assert question.rationale_code in {
            "mic_conflict",
            "forced_nonentailment",
            "disconnected_cluster",
        }
        assert question.rationale.strip()


def test_concepts_questions_endpoint_enforces_expected_ir_hash() -> None:
    concept = _fixture_ir(fixture="bank_sense_coherence", name="var2.json")
    source = _fixture_source(fixture="bank_sense_coherence")

    with pytest.raises(api_main.HTTPException) as exc_info:
        concept_questions_endpoint(
            ConceptQuestionsRequest(
                ir=concept,
                source_text=source,
                mode=KernelMode.LAX,
                include_forced_details=True,
                expected_ir_hash="deadbeef",
            )
        )

    detail = exc_info.value.detail
    assert exc_info.value.status_code == 409
    assert isinstance(detail, dict)
    assert detail["code"] == "STALE_IR"
    assert detail["provided_ir_hash"] == "deadbeef"
    assert isinstance(detail["expected_ir_hash"], str)


def test_concepts_questions_answers_are_apply_endpoint_compatible() -> None:
    concept = _fixture_ir(fixture="bank_sense_coherence", name="var2.json")
    analysis = unavailable_analysis().model_copy(
        update={
            "mic": MicResult(
                status="COMPLETE",
                constraint_count=1,
                constraints=[
                    AnalysisAtomRef(
                        atom_name="atom_ambiguity",
                        object_id="amb_bank",
                        json_path="/ambiguity/0/exactly_one",
                        label="ambiguity",
                    )
                ],
                shrink_iters=0,
                solver_calls=1,
                details=None,
            )
        }
    )

    questions = build_concept_questions(concept, analysis)
    ambiguity_questions = [
        item for item in questions if item.question_id.startswith("mic_ambiguity_")
    ]
    assert ambiguity_questions
    answer = ambiguity_questions[0].answers[0]

    payload = concept.model_dump(mode="json")
    payload["ambiguity"][0]["option_details_by_id"] = {
        answer.option_id: answer.model_dump(mode="json", by_alias=True, exclude_none=True)
    }
    prepared = ConceptIR.model_validate(payload)

    resp = apply_concept_ambiguity_option_endpoint(
        ConceptApplyAmbiguityOptionRequest(
            ir=prepared,
            ambiguity_id="amb_bank",
            option_id=answer.option_id,
            mode=KernelMode.LAX,
        )
    )

    assert resp.patched_ir.model_dump(mode="json") != prepared.model_dump(mode="json")


def test_concepts_questions_apply_patch_updates_question_space() -> None:
    concept = _fixture_ir(fixture="bank_sense_coherence", name="var2.json")
    source = _fixture_source(fixture="bank_sense_coherence")

    before = concept_questions_endpoint(
        ConceptQuestionsRequest(
            ir=concept,
            source_text=source,
            mode=KernelMode.LAX,
            include_forced_details=True,
        )
    )
    ambiguity_question = next(
        question
        for question in before.questions
        if question.question_id.startswith("mic_ambiguity_")
    )
    answer = ambiguity_question.answers[0]
    assert answer.patch
    chosen_key = _question_key(ambiguity_question, answer.option_id)

    applied = apply_concept_patch_endpoint(
        ConceptApplyPatchRequest(
            ir=concept,
            ir_hash=api_main._concept_ir_hash(concept),
            patch_ops=answer.patch,
            source_text=source,
            mode=KernelMode.LAX,
        )
    )

    after = concept_questions_endpoint(
        ConceptQuestionsRequest(
            ir=applied.patched_ir,
            source_text=source,
            mode=KernelMode.LAX,
            include_forced_details=True,
        )
    )

    keys_after = {
        _question_key(question, option.option_id)
        for question in after.questions
        for option in question.answers
    }
    assert chosen_key not in keys_after


def test_questions_rank_and_dedupe_prefers_mic_and_is_stable() -> None:
    concept = _fixture_ir(fixture="bank_sense_coherence", name="var2.json")
    source = _fixture_source(fixture="bank_sense_coherence")
    report, records = api_main.check_concept_with_validator_runs(
        concept,
        mode=KernelMode.LAX,
        source_text=source,
    )
    run_inputs = [api_main._validator_run_input_from_record(record) for record in records]
    concept_runs = [api_main._concept_run_ref_from_input(run) for run in run_inputs]
    analysis = analyze_concept(concept, run=pick_latest_run(concept_runs))

    answers = [
        AmbiguityOption(
            option_id="set_sense",
            label="Set sense",
            patch=[
                JsonPatchOp(
                    op="replace", path="/claims/0/sense_id", value=concept.claims[0].sense_id
                )
            ],
        )
    ]
    mic = ConceptQuestion(
        question_id="q_mic",
        signal="mic",
        rationale_code="mic_conflict",
        rationale="MIC rationale",
        prompt="MIC question",
        anchors=[
            ConceptQuestionAnchor(
                object_id="amb_bank",
                json_path="/ambiguity/0",
                label="ambiguity",
            )
        ],
        answers=answers,
    )
    mic_duplicate = ConceptQuestion(
        question_id="q_mic_dup",
        signal="mic",
        rationale_code="mic_conflict",
        rationale="MIC rationale",
        prompt="MIC question duplicate text",
        anchors=[
            ConceptQuestionAnchor(
                object_id="amb_bank",
                json_path="/ambiguity/0",
                label="ambiguity",
            )
        ],
        answers=answers,
    )
    disconnect = ConceptQuestion(
        question_id="q_disconnect",
        signal="disconnected_clusters",
        rationale_code="disconnected_cluster",
        rationale="Disconnect rationale",
        prompt="Disconnect question",
        anchors=[
            ConceptQuestionAnchor(object_id=concept.terms[0].id, label="disconnected_clusters")
        ],
        answers=answers,
    )

    ranked_left = api_main._rank_and_dedupe_questions(
        questions=[disconnect, mic_duplicate, mic],
        analysis=analysis,
        report=report,
        ir=concept,
    )
    ranked_right = api_main._rank_and_dedupe_questions(
        questions=[disconnect, mic_duplicate, mic],
        analysis=analysis,
        report=report,
        ir=concept,
    )

    assert ranked_left == ranked_right
    assert [item.signal for item in ranked_left] == ["mic", "disconnected_clusters"]


def test_do_no_harm_filter_suppresses_non_improving_answers(monkeypatch) -> None:
    concept = _fixture_ir(fixture="bank_sense_coherence", name="var2.json")
    source = _fixture_source(fixture="bank_sense_coherence")
    report, records = api_main.check_concept_with_validator_runs(
        concept,
        mode=KernelMode.LAX,
        source_text=source,
    )
    run_inputs = [api_main._validator_run_input_from_record(record) for record in records]
    concept_runs = [api_main._concept_run_ref_from_input(run) for run in run_inputs]
    analysis = analyze_concept(concept, run=pick_latest_run(concept_runs))

    question = ConceptQuestion(
        question_id="q_mic",
        signal="mic",
        rationale_code="mic_conflict",
        rationale="MIC rationale",
        prompt="MIC question",
        anchors=[
            ConceptQuestionAnchor(
                object_id="amb_bank",
                json_path="/ambiguity/0",
                label="ambiguity",
            )
        ],
        answers=[
            AmbiguityOption(
                option_id="keep",
                label="keep",
                patch=[
                    JsonPatchOp(
                        op="add",
                        path="/links/-",
                        value={
                            "id": "q_keep",
                            "kind": "commitment",
                            "src_sense_id": concept.senses[0].id,
                            "dst_sense_id": concept.senses[0].id,
                        },
                    )
                ],
            ),
            AmbiguityOption(
                option_id="drop",
                label="drop",
                patch=[
                    JsonPatchOp(
                        op="add",
                        path="/links/-",
                        value={
                            "id": "q_drop",
                            "kind": "commitment",
                            "src_sense_id": concept.senses[0].id,
                            "dst_sense_id": concept.senses[0].id,
                        },
                    )
                ],
            ),
        ],
    )

    def _fake_eval(*, patch_ops, **kwargs):
        link_id = str((patch_ops[0].value or {}).get("id"))
        if link_id == "q_drop":
            return False, 1
        return True, 1

    monkeypatch.setattr(api_main, "_evaluate_question_answer_dry_run", _fake_eval)

    filtered = api_main._filter_question_answers_do_no_harm(
        req=ConceptQuestionsRequest(ir=concept, source_text=source, mode=KernelMode.LAX),
        report=report,
        analysis=analysis,
        questions=[question],
    )

    assert filtered.questions
    assert [answer.option_id for answer in filtered.questions[0].answers] == ["keep"]


def test_do_no_harm_filter_respects_dry_run_budget(monkeypatch) -> None:
    concept = _fixture_ir(fixture="bank_sense_coherence", name="var2.json")
    source = _fixture_source(fixture="bank_sense_coherence")
    report, records = api_main.check_concept_with_validator_runs(
        concept,
        mode=KernelMode.LAX,
        source_text=source,
    )
    run_inputs = [api_main._validator_run_input_from_record(record) for record in records]
    concept_runs = [api_main._concept_run_ref_from_input(run) for run in run_inputs]
    analysis = analyze_concept(concept, run=pick_latest_run(concept_runs))

    questions: list[ConceptQuestion] = []
    for idx in range(api_main.MAX_QUESTION_DRY_RUN_EVALS_TOTAL + 5):
        questions.append(
            ConceptQuestion(
                question_id=f"q_{idx}",
                signal="mic",
                rationale_code="mic_conflict",
                rationale="MIC rationale",
                prompt=f"q_{idx}",
                anchors=[
                    ConceptQuestionAnchor(
                        object_id="amb_bank",
                        json_path="/ambiguity/0",
                        label="ambiguity",
                    )
                ],
                answers=[
                    AmbiguityOption(
                        option_id=f"opt_{idx}",
                        label=f"opt_{idx}",
                        patch=[
                            JsonPatchOp(
                                op="add",
                                path="/links/-",
                                value={
                                    "id": f"budget_{idx}",
                                    "kind": "commitment",
                                    "src_sense_id": concept.senses[0].id,
                                    "dst_sense_id": concept.senses[0].id,
                                },
                            )
                        ],
                    )
                ],
            )
        )

    calls = {"count": 0}

    def _fake_eval(**kwargs):
        calls["count"] += 1
        return True, 1

    monkeypatch.setattr(api_main, "_evaluate_question_answer_dry_run", _fake_eval)

    filtered = api_main._filter_question_answers_do_no_harm(
        req=ConceptQuestionsRequest(ir=concept, source_text=source, mode=KernelMode.LAX),
        report=report,
        analysis=analysis,
        questions=questions,
    )

    assert len(filtered.questions) == api_main.MAX_QUESTION_DRY_RUN_EVALS_TOTAL
    assert calls["count"] == api_main.MAX_QUESTION_DRY_RUN_EVALS_TOTAL
    assert filtered.truncated is True
    assert filtered.truncation_reason == api_main.QUESTION_TRUNCATION_REASON_DRY_RUN_CAP


def test_concepts_questions_endpoint_is_read_only(monkeypatch) -> None:
    concept = _fixture_ir(fixture="bank_sense_coherence", name="var2.json")
    source = _fixture_source(fixture="bank_sense_coherence")
    monkeypatch.setenv("ADEU_PERSIST_VALIDATOR_RUNS", "1")
    calls = {"count": 0}

    def _should_not_persist(*, runs, artifact_id):
        calls["count"] += 1

    monkeypatch.setattr(api_main, "_persist_validator_runs", _should_not_persist)

    response = concept_questions_endpoint(
        ConceptQuestionsRequest(
            ir=concept,
            source_text=source,
            mode=KernelMode.LAX,
            include_forced_details=True,
        )
    )

    assert response.question_count >= 0
    assert calls["count"] == 0
