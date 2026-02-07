from __future__ import annotations

import json
from pathlib import Path

import adeu_api.main as api_main
from adeu_api.main import ConceptAnalyzeRequest, analyze_concept_variant
from adeu_concepts import ConceptIR
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


def _coherent_ir() -> ConceptIR:
    return ConceptIR.model_validate(
        _fixture_payload(fixture="bank_sense_coherence", name="var1.json")
    )


def _incoherent_ir() -> ConceptIR:
    return ConceptIR.model_validate(
        _fixture_payload(fixture="bank_sense_coherence", name="var2.json")
    )


def test_concepts_analyze_inline_runs_override_recompute(monkeypatch) -> None:
    def _unexpected_recompute(*args, **kwargs):
        raise AssertionError("recompute should not be called when inline runs are provided")

    monkeypatch.setattr(api_main, "check_concept_with_validator_runs", _unexpected_recompute)

    resp = analyze_concept_variant(
        ConceptAnalyzeRequest(
            ir=_coherent_ir(),
            validator_runs=[
                {
                    "run_id": "inline-1",
                    "created_at": "2026-03-01T10:00:00Z",
                    "request_hash": "req-inline",
                    "formula_hash": "formula-inline",
                    "status": "SAT",
                    "evidence_json": {"model": {}, "unsat_core": []},
                    "atom_map_json": {},
                }
            ],
            include_validator_runs=True,
        )
    )

    assert resp.check_report.status == "PASS"
    assert resp.analysis.closure.status == "COMPLETE"
    assert resp.analysis.mic.status == "UNAVAILABLE"
    assert resp.validator_runs is not None and len(resp.validator_runs) == 1


def test_concepts_analyze_recompute_populates_analysis_and_runs() -> None:
    resp = analyze_concept_variant(
        ConceptAnalyzeRequest(
            ir=_coherent_ir(),
            source_text=_fixture_source(fixture="bank_sense_coherence"),
            include_validator_runs=True,
            mode=KernelMode.LAX,
        )
    )

    assert resp.check_report.status == "PASS"
    assert resp.analysis.closure.status == "COMPLETE"
    assert resp.analysis.closure.edge_count >= 0
    assert resp.validator_runs is not None and len(resp.validator_runs) == 1


def test_concepts_analyze_hides_details_when_requested() -> None:
    resp = analyze_concept_variant(
        ConceptAnalyzeRequest(
            ir=_incoherent_ir(),
            source_text=_fixture_source(fixture="bank_sense_coherence"),
            include_analysis_details=False,
            mode=KernelMode.STRICT,
        )
    )

    assert resp.check_report.status == "REFUSE"
    assert resp.analysis.closure.edges == []
    assert resp.analysis.closure.details is None
    assert resp.analysis.mic.constraints == []
    assert resp.analysis.mic.details is None


def test_concepts_analyze_picks_latest_inline_run_by_created_at() -> None:
    resp = analyze_concept_variant(
        ConceptAnalyzeRequest(
            ir=_incoherent_ir(),
            validator_runs=[
                {
                    "run_id": "older-sat",
                    "created_at": "2026-03-01T09:00:00Z",
                    "request_hash": "req-shared",
                    "formula_hash": "formula-shared",
                    "status": "SAT",
                    "evidence_json": {"model": {}, "unsat_core": []},
                    "atom_map_json": {},
                },
                {
                    "run_id": "newer-unsat",
                    "created_at": "2026-03-01T10:00:00Z",
                    "request_hash": "req-shared",
                    "formula_hash": "formula-shared",
                    "status": "UNSAT",
                    "evidence_json": {
                        "model": {},
                        "unsat_core": ["a:cl_credit:0f4f4a56813d"],
                    },
                    "atom_map_json": {
                        "a:cl_credit:0f4f4a56813d": {
                            "object_id": "cl_credit",
                            "json_path": "/claims/0/active",
                        }
                    },
                },
            ],
            mode=KernelMode.LAX,
        )
    )

    assert resp.check_report.status == "REFUSE"
    assert resp.analysis.closure.status == "UNAVAILABLE"
    assert resp.analysis.mic.status in {"COMPLETE", "PARTIAL"}


def test_concepts_analyze_empty_inline_runs_returns_unavailable_analysis() -> None:
    resp = analyze_concept_variant(
        ConceptAnalyzeRequest(
            ir=_coherent_ir(),
            validator_runs=[],
        )
    )

    assert resp.check_report.status == "PASS"
    assert resp.analysis.closure.status == "UNAVAILABLE"
    assert resp.analysis.mic.status == "UNAVAILABLE"


def test_concepts_analyze_normalizes_inline_atom_map_list_to_map() -> None:
    resp = analyze_concept_variant(
        ConceptAnalyzeRequest(
            ir=_coherent_ir(),
            include_validator_runs=True,
            validator_runs=[
                {
                    "run_id": "inline-list-map",
                    "created_at": "2026-03-01T10:00:00Z",
                    "request_hash": "req-inline-list",
                    "formula_hash": "formula-inline-list",
                    "status": "SAT",
                    "evidence_json": {"model": {}, "unsat_core": []},
                    "atom_map_json": [
                        {
                            "assertion_name": "a:claim_1:abc123def456",
                            "object_id": "claim_1",
                            "json_path": "/claims/0/active",
                        }
                    ],
                }
            ],
        )
    )

    assert resp.validator_runs is not None
    assert isinstance(resp.validator_runs[0].atom_map_json, dict)
