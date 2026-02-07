from __future__ import annotations

import json
from pathlib import Path

from adeu_concepts import (
    ConceptIR,
    ConceptRunRef,
    analyze_concept,
    check_with_validator_runs,
    pick_latest_run,
    strip_analysis_details,
    unavailable_analysis,
)
from adeu_concepts.analysis import _constraint_label
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


def test_analyze_concept_sat_populates_closure_and_no_mic() -> None:
    concept = ConceptIR.model_validate(
        _fixture_payload(fixture="bank_sense_coherence", name="var1.json")
    )
    report, runs = check_with_validator_runs(
        concept,
        mode=KernelMode.STRICT,
        source_text=_fixture_source(fixture="bank_sense_coherence"),
    )

    assert report.status == "PASS"
    assert runs

    analysis = analyze_concept(concept, run=_run_ref_from_record(runs[0]))
    assert analysis.closure.status == "COMPLETE"
    assert analysis.closure.edge_count == len(analysis.closure.edges)
    assert analysis.mic.status == "UNAVAILABLE"
    assert any(
        edge.src_sense_id == "s_bank_fin"
        and edge.dst_sense_id == "s_credit"
        and edge.kind == "commitment"
        for edge in analysis.closure.edges
    )


def test_analyze_concept_unsat_populates_mic_and_no_closure() -> None:
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
    assert analysis.closure.status == "UNAVAILABLE"
    assert analysis.mic.status == "COMPLETE"
    assert analysis.mic.constraint_count > 0
    assert all(item.label is not None for item in analysis.mic.constraints)


def test_analyze_concept_mic_reports_partial_when_shrink_caps_hit() -> None:
    concept = ConceptIR.model_validate(
        _fixture_payload(fixture="bank_sense_coherence", name="var2.json")
    )
    _, runs = check_with_validator_runs(
        concept,
        mode=KernelMode.STRICT,
        source_text=_fixture_source(fixture="bank_sense_coherence"),
    )
    assert runs

    analysis = analyze_concept(
        concept,
        run=_run_ref_from_record(runs[0]),
        max_shrink_iters=0,
        max_solver_calls=60,
    )
    assert analysis.mic.status == "PARTIAL"
    assert analysis.mic.details == "max_shrink_iters reached"
    assert analysis.mic.shrink_iters == 0
    assert analysis.mic.solver_calls == 0


def test_pick_latest_run_prefers_created_at_then_list_order() -> None:
    first = ConceptRunRef(run_id="r1", created_at="2026-02-10T10:00:00Z", status="SAT")
    second = ConceptRunRef(run_id="r2", created_at="2026-02-10T11:00:00Z", status="UNSAT")
    third = ConceptRunRef(run_id="r3", created_at=None, status="SAT")

    assert pick_latest_run([first, second, third]) == second

    no_ts_a = ConceptRunRef(run_id="aa", created_at=None, status="SAT")
    no_ts_b = ConceptRunRef(run_id="zz", created_at=None, status="UNSAT")
    assert pick_latest_run([no_ts_a, no_ts_b]) == no_ts_b


def test_strip_and_unavailable_analysis_contract() -> None:
    empty = unavailable_analysis(details="no runs")
    assert empty.closure.status == "UNAVAILABLE"
    assert empty.mic.status == "UNAVAILABLE"

    stripped = strip_analysis_details(empty)
    assert stripped.closure.edges == []
    assert stripped.closure.details is None
    assert stripped.mic.constraints == []
    assert stripped.mic.details is None


def test_constraint_label_matches_only_expected_pointer_shapes() -> None:
    assert _constraint_label("/claims/0/active") == "claim_activation"
    assert _constraint_label("/claims/0/sense_id") == "claim_implication"
    assert _constraint_label("/ambiguity/0/exactly_one") == "ambiguity"
    assert _constraint_label("/links/0") == "link"

    assert _constraint_label("/claims/0/meta/active") is None
    assert _constraint_label("/claims/0/sense_id/extra") is None
