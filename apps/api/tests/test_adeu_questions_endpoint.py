from __future__ import annotations

import json
from pathlib import Path

import adeu_api.main as api_main
import pytest
from adeu_api.adeu_concept_bridge import BRIDGE_MAPPING_VERSION, compute_mapping_hash
from adeu_api.main import AdeuQuestionsRequest, adeu_questions_endpoint
from adeu_concepts import AmbiguityOption, ConceptQuestion, ConceptQuestionAnchor
from adeu_ir import AdeuIR
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode
from fastapi import HTTPException


def _fixture_ir(*, fixture: str, name: str) -> AdeuIR:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "fixtures" / fixture / "proposals" / name
    return AdeuIR.model_validate(json.loads(path.read_text(encoding="utf-8")))


def _fixture_source(*, fixture: str) -> str:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "fixtures" / fixture / "clause.txt"
    return path.read_text(encoding="utf-8").strip()


def _permuted_ir(ir: AdeuIR) -> AdeuIR:
    return ir.model_copy(
        update={
            "O": ir.O.model_copy(
                update={
                    "entities": list(reversed(ir.O.entities)),
                    "definitions": list(reversed(ir.O.definitions)),
                }
            ),
            "D_norm": ir.D_norm.model_copy(
                update={
                    "statements": list(reversed(ir.D_norm.statements)),
                    "exceptions": list(reversed(ir.D_norm.exceptions)),
                }
            ),
        }
    )


def _synthetic_build_questions(concept_ir, analysis, *, max_questions, max_answers_per_question):
    del analysis, max_questions, max_answers_per_question
    if not concept_ir.claims:
        return []
    claim = concept_ir.claims[0]
    return [
        ConceptQuestion(
            question_id="q_adeu_anchor",
            signal="mic",
            prompt="Resolve the legal claim anchor",
            anchors=[
                ConceptQuestionAnchor(
                    object_id=claim.id,
                    json_path="/claims/0/sense_id",
                    label="claim_implication",
                )
            ],
            answers=[
                AmbiguityOption(
                    option_id="keep",
                    label="Keep",
                    variant_ir_id="variant_keep",
                )
            ],
        )
    ]


def test_adeu_questions_endpoint_is_deterministic_and_emits_trust_metadata() -> None:
    ir = _fixture_ir(fixture="exception_priority_resolves_conflict", name="var2.json")
    source = _fixture_source(fixture="exception_priority_resolves_conflict")

    left = adeu_questions_endpoint(
        AdeuQuestionsRequest(
            ir=ir,
            source_text=source,
            mode=KernelMode.LAX,
            include_validator_runs=True,
        )
    )
    right = adeu_questions_endpoint(
        AdeuQuestionsRequest(
            ir=ir,
            source_text=source,
            mode=KernelMode.LAX,
            include_validator_runs=True,
        )
    )

    assert left == right
    assert left.question_rank_version == "adeu.qrank.v1"
    assert left.bridge_mapping_version == BRIDGE_MAPPING_VERSION
    assert left.mapping_hash == compute_mapping_hash()
    assert left.mapping_trust == "derived_bridge"
    assert left.solver_trust in {"kernel_only", "solver_backed"}
    assert left.proof_trust is None
    assert left.question_count == len(left.questions)
    assert left.max_questions == api_main.DEFAULT_MAX_QUESTIONS
    assert left.max_answers_per_question == api_main.DEFAULT_MAX_ANSWERS_PER_QUESTION
    if left.validator_runs:
        assert left.solver_trust == "solver_backed"
    else:
        assert left.solver_trust == "kernel_only"
    assert left.analysis is None
    assert left.budget_report.budget_version == "budget.v1"
    assert left.budget_report.max_solver_calls == api_main.MAX_QUESTION_SOLVER_CALLS_TOTAL
    assert left.budget_report.max_dry_runs == api_main.MAX_QUESTION_DRY_RUN_EVALS_TOTAL
    assert 0 <= left.budget_report.used_solver_calls <= left.budget_report.max_solver_calls
    assert 0 <= left.budget_report.used_dry_runs <= left.budget_report.max_dry_runs

    for question in left.questions:
        assert question.anchors
        for anchor in question.anchors:
            assert isinstance(anchor.object_id, str)
            assert anchor.object_id
            assert isinstance(anchor.json_path, str)
            assert anchor.json_path.startswith("/")
            if anchor.span is not None:
                assert 0 <= anchor.span.start < anchor.span.end <= len(source)


def test_adeu_questions_endpoint_is_invariant_to_adeu_input_order() -> None:
    base = _fixture_ir(fixture="exception_priority_resolves_conflict", name="var2.json")
    permuted = _permuted_ir(base)
    source = _fixture_source(fixture="exception_priority_resolves_conflict")

    left = adeu_questions_endpoint(
        AdeuQuestionsRequest(ir=base, source_text=source, mode=KernelMode.LAX)
    )
    right = adeu_questions_endpoint(
        AdeuQuestionsRequest(ir=permuted, source_text=source, mode=KernelMode.LAX)
    )

    assert left.questions == right.questions
    assert left.bridge_manifest == right.bridge_manifest
    assert left.mapping_hash == right.mapping_hash
    assert left.question_count == right.question_count
    assert left.budget_report == right.budget_report


def test_adeu_questions_endpoint_projects_concept_anchors_to_adeu_refs(monkeypatch) -> None:
    ir = _fixture_ir(fixture="exception_priority_resolves_conflict", name="var2.json")
    source = _fixture_source(fixture="exception_priority_resolves_conflict") + "  "
    monkeypatch.setattr(api_main, "build_concept_questions", _synthetic_build_questions)

    response = adeu_questions_endpoint(
        AdeuQuestionsRequest(
            ir=ir,
            source_text=source,
            mode=KernelMode.LAX,
            include_analysis_details=True,
        )
    )

    assert response.question_count == 1
    assert response.analysis is not None
    anchor = response.questions[0].anchors[0]
    assert anchor.object_id is not None
    assert anchor.object_id.startswith("dn_")
    assert anchor.json_path is not None
    assert anchor.json_path.startswith("/D_norm/statements/")
    if anchor.span is not None:
        assert 0 <= anchor.span.start < anchor.span.end <= len(source)


def test_adeu_questions_endpoint_enforces_expected_ir_hash() -> None:
    ir = _fixture_ir(fixture="exception_priority_resolves_conflict", name="var2.json")

    with pytest.raises(HTTPException) as exc_info:
        adeu_questions_endpoint(
            AdeuQuestionsRequest(
                ir=ir,
                mode=KernelMode.LAX,
                expected_ir_hash="deadbeef",
            )
        )

    detail = exc_info.value.detail
    assert exc_info.value.status_code == 409
    assert isinstance(detail, dict)
    assert detail["code"] == "STALE_IR"
    assert detail["provided_ir_hash"] == "deadbeef"
    assert isinstance(detail["expected_ir_hash"], str)


def test_adeu_questions_endpoint_is_read_only(monkeypatch) -> None:
    ir = _fixture_ir(fixture="exception_priority_resolves_conflict", name="var2.json")
    source = _fixture_source(fixture="exception_priority_resolves_conflict")
    monkeypatch.setenv("ADEU_PERSIST_VALIDATOR_RUNS", "1")
    calls = {"count": 0}

    def _should_not_persist(*, runs, artifact_id):
        calls["count"] += 1

    monkeypatch.setattr(api_main, "_persist_validator_runs", _should_not_persist)

    response = adeu_questions_endpoint(
        AdeuQuestionsRequest(
            ir=ir,
            source_text=source,
            mode=KernelMode.LAX,
        )
    )

    assert response.question_count >= 0
    assert calls["count"] == 0


def test_adeu_questions_endpoint_rejects_out_of_bounds_anchor_spans(monkeypatch) -> None:
    ir = _fixture_ir(fixture="exception_priority_resolves_conflict", name="var2.json")
    monkeypatch.setattr(api_main, "build_concept_questions", _synthetic_build_questions)

    with pytest.raises(HTTPException) as exc_info:
        adeu_questions_endpoint(
            AdeuQuestionsRequest(
                ir=ir,
                source_text="short",
                mode=KernelMode.LAX,
            )
        )

    detail = exc_info.value.detail
    assert exc_info.value.status_code == 400
    assert isinstance(detail, dict)
    assert detail["code"] == "ADEU_QUESTIONS_ANCHOR_UNRESOLVED"
