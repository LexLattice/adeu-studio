from __future__ import annotations

import json
from pathlib import Path

import adeu_api.main as api_main
from adeu_api.main import (
    ExplainFlipAdeuRequest,
    ExplainFlipConceptsRequest,
    explain_flip_endpoint,
)
from adeu_concepts import ConceptIR
from adeu_ir import AdeuIR
from adeu_ir.repo import repo_root


def _left_ir() -> AdeuIR:
    return AdeuIR.model_validate(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_left",
            "context": {
                "doc_id": "doc:test:flip",
                "jurisdiction": "US-CA",
                "time_eval": "2026-02-06T00:00:00Z",
            },
            "D_norm": {
                "statements": [
                    {
                        "id": "stmt_a",
                        "kind": "obligation",
                        "subject": {"ref_type": "text", "text": "Supplier"},
                        "action": {"verb": "deliver"},
                        "scope": {"jurisdiction": "US-CA", "time_about": {"kind": "unspecified"}},
                        "provenance": {
                            "doc_ref": "doc:test:flip#sec1",
                            "span": {"start": 0, "end": 12},
                        },
                    }
                ]
            },
        }
    )


def _right_ir() -> AdeuIR:
    return AdeuIR.model_validate(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_right",
            "context": {
                "doc_id": "doc:test:flip",
                "jurisdiction": "US-CA",
                "time_eval": "2026-02-06T00:00:00Z",
            },
            "D_norm": {
                "statements": [
                    {
                        "id": "stmt_a",
                        "kind": "prohibition",
                        "subject": {"ref_type": "text", "text": "Supplier"},
                        "action": {"verb": "deliver"},
                        "scope": {"jurisdiction": "US-CA", "time_about": {"kind": "unspecified"}},
                        "provenance": {
                            "doc_ref": "doc:test:flip#sec1",
                            "span": {"start": 0, "end": 12},
                        },
                    }
                ]
            },
        }
    )


def _concept_fixture(name: str) -> ConceptIR:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / "bank_sense_coherence" / "proposals" / name
    return ConceptIR.model_validate(json.loads(path.read_text(encoding="utf-8")))


def test_explain_flip_endpoint_adeu_inline_runs() -> None:
    req = ExplainFlipAdeuRequest(
        domain="adeu",
        left_ir=_left_ir(),
        right_ir=_right_ir(),
        left_validator_runs=[
            {
                "request_hash": "req-inline",
                "formula_hash": "f-inline",
                "status": "UNSAT",
                "evidence_json": {"unsat_core": ["atom_stmt"], "model": {}},
                "atom_map_json": {
                    "atom_stmt": {"object_id": "stmt_a", "json_path": "/D_norm/statements/0/kind"}
                },
            }
        ],
        right_validator_runs=[
            {
                "request_hash": "req-inline",
                "formula_hash": "f-inline",
                "status": "SAT",
                "evidence_json": {"unsat_core": [], "model": {"atom_stmt": "True"}},
                "atom_map_json": {
                    "atom_stmt": {"object_id": "stmt_a", "json_path": "/D_norm/statements/0/kind"}
                },
            }
        ],
    )
    resp = explain_flip_endpoint(req)
    assert resp.diff_report.solver.status_flip == "UNSAT→SAT"
    assert resp.flip_explanation.solver_status_flip == "UNSAT→SAT"
    assert "→" in resp.flip_explanation.check_status_flip
    assert resp.flip_explanation.cause_chain
    assert resp.analysis_delta is None


def test_explain_flip_endpoint_concepts_analysis_delta_toggle() -> None:
    left = _concept_fixture("var1.json")
    right = _concept_fixture("var1.json").model_copy(
        update={
            "concept_id": "concept_right_variant",
            "claims": [
                _concept_fixture("var1.json").claims[0].model_copy(
                    update={"id": "claim_1", "sense_id": "s_bank_river"}
                )
            ],
        }
    )

    req_without = ExplainFlipConceptsRequest(
        domain="concepts",
        left_ir=left,
        right_ir=right,
        include_analysis_delta=False,
        left_validator_runs=[
            {
                "request_hash": "req-c",
                "formula_hash": "f-c",
                "status": "SAT",
                "evidence_json": {"unsat_core": [], "model": {}},
                "atom_map_json": {},
            }
        ],
        right_validator_runs=[
            {
                "request_hash": "req-c",
                "formula_hash": "f-c",
                "status": "SAT",
                "evidence_json": {"unsat_core": [], "model": {}},
                "atom_map_json": {},
            }
        ],
    )
    resp_without = explain_flip_endpoint(req_without)
    assert resp_without.analysis_delta is None

    req_with = req_without.model_copy(
        update={
            "include_analysis_delta": True,
            "additional_solver_call_budget": 0,
        }
    )
    resp_with = explain_flip_endpoint(req_with)
    assert resp_with.analysis_delta is not None
    assert isinstance(resp_with.analysis_delta.mic_atoms_added, list)
    assert isinstance(resp_with.analysis_delta.forced_edges_added, list)


def test_explain_flip_endpoint_recompute_failure_is_missing(monkeypatch) -> None:
    def _explode(*args, **kwargs):
        raise RuntimeError("boom")

    monkeypatch.setattr(api_main, "check_with_validator_runs", _explode)

    req = ExplainFlipAdeuRequest(
        domain="adeu",
        left_ir=_left_ir(),
        right_ir=_right_ir(),
    )
    resp = explain_flip_endpoint(req)
    assert resp.diff_report.solver.status_flip == "NO_RUNS"
    assert resp.diff_report.summary.run_source == "recomputed"
