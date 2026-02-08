from __future__ import annotations

import json
from pathlib import Path

from adeu_api.main import (
    ConceptApplyAmbiguityOptionRequest,
    ConceptQuestionsRequest,
    apply_concept_ambiguity_option_endpoint,
    concept_questions_endpoint,
)
from adeu_concepts import ConceptIR, build_concept_questions, unavailable_analysis
from adeu_concepts.analysis import AnalysisAtomRef, MicResult
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
    assert left.mapping_trust is None
    assert left.solver_trust == "solver_backed"
    assert left.proof_trust is None


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
