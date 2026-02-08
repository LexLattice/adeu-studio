from __future__ import annotations

import json
from pathlib import Path

from adeu_concepts import (
    ConceptIR,
    ConceptRunRef,
    analyze_concept,
    build_concept_questions,
    check_with_validator_runs,
    unavailable_analysis,
)
from adeu_concepts.analysis import ForcedCountermodel, ForcedResult
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode


def _fixture_payload(*, fixture: str, name: str) -> dict:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / fixture / "proposals" / name
    return json.loads(path.read_text(encoding="utf-8"))


def _fixture_source(*, fixture: str) -> str:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / fixture / "source.txt"
    return path.read_text(encoding="utf-8").strip()


def _run_ref_from_record(record) -> ConceptRunRef:
    return ConceptRunRef(
        run_id=None,
        created_at=None,
        status=record.result.status,
        request_hash=record.result.request_hash,
        formula_hash=record.result.formula_hash,
        evidence_model=record.result.evidence.model,
        evidence_unsat_core=record.result.evidence.unsat_core,
        evidence_error=record.result.evidence.error,
        atom_map_json={
            atom.assertion_name: {
                "object_id": atom.object_id,
                "json_path": atom.json_path,
            }
            for atom in record.request.payload.atom_map
        },
    )


def test_build_concept_questions_is_deterministic_and_capped() -> None:
    concept = ConceptIR.model_validate(
        _fixture_payload(fixture="bank_sense_coherence", name="var2.json")
    )
    report, runs = check_with_validator_runs(
        concept,
        mode=KernelMode.STRICT,
        source_text=_fixture_source(fixture="bank_sense_coherence"),
    )
    assert report.status == "REFUSE"
    assert runs

    analysis = analyze_concept(concept, run=_run_ref_from_record(runs[0]))

    left = build_concept_questions(concept, analysis)
    right = build_concept_questions(concept, analysis)

    assert left
    assert left == right
    assert len(left) <= 10
    assert any(item.signal == "mic" for item in left)
    assert all(0 < len(item.answers) <= 4 for item in left)
    assert len({item.question_id for item in left}) == len(left)
    assert all(answer.patch for item in left for answer in item.answers)


def test_build_concept_questions_includes_forced_countermodel_signal() -> None:
    concept = ConceptIR.model_validate(
        _fixture_payload(fixture="bank_sense_coherence", name="var1.json")
    )
    analysis = unavailable_analysis().model_copy(
        update={
            "forced": ForcedResult(
                status="COMPLETE",
                candidate_count=1,
                forced_count=0,
                forced_edges=[],
                countermodel_count=1,
                countermodels=[
                    ForcedCountermodel(
                        src_sense_id="s_credit",
                        dst_sense_id="s_bank_river",
                        kind="commitment",
                        solver_status="SAT",
                        assignments=[],
                    )
                ],
                solver_calls=1,
                details=None,
            )
        }
    )

    questions = build_concept_questions(concept, analysis)
    forced = [item for item in questions if item.signal == "forced_countermodel"]
    assert forced
    assert forced[0].answers
    assert forced[0].answers[0].patch[0].path == "/links/-"


def test_build_concept_questions_includes_disconnect_signal() -> None:
    base = ConceptIR.model_validate(
        _fixture_payload(fixture="bank_sense_coherence", name="var1.json")
    )
    payload = base.model_dump(mode="json")
    payload["links"] = []
    concept = ConceptIR.model_validate(payload)

    questions = build_concept_questions(
        concept,
        unavailable_analysis(),
    )
    disconnected = [item for item in questions if item.signal == "disconnected_clusters"]
    assert disconnected
    assert disconnected[0].answers
    assert disconnected[0].answers[0].patch[0].path == "/links/-"
