from __future__ import annotations

import adeu_api.main as api_main
from adeu_api.main import DiffRequest, diff_endpoint
from adeu_ir import AdeuIR
from adeu_kernel import KernelMode


def _left_ir() -> AdeuIR:
    return AdeuIR.model_validate(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_left",
            "context": {
                "doc_id": "doc:test:diff",
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
                            "doc_ref": "doc:test:diff#sec1",
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
                "doc_id": "doc:test:diff",
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
                            "doc_ref": "doc:test:diff#sec1",
                            "span": {"start": 0, "end": 12},
                        },
                    }
                ]
            },
        }
    )


def test_diff_endpoint_uses_inline_runs_and_reports_solver_flip() -> None:
    req = DiffRequest(
        left_ir=_left_ir(),
        right_ir=_right_ir(),
        left_validator_runs=[
            {
                "request_hash": "req-1",
                "formula_hash": "f-1",
                "status": "UNSAT",
                "evidence_json": {"unsat_core": ["atom_stmt"], "model": {}},
                "atom_map_json": {
                    "atom_stmt": {"object_id": "stmt_a", "json_path": "/D_norm/statements/0"}
                },
            }
        ],
        right_validator_runs=[
            {
                "request_hash": "req-1",
                "formula_hash": "f-1",
                "status": "SAT",
                "evidence_json": {"unsat_core": [], "model": {"atom_stmt": "True"}},
                "atom_map_json": [
                    {
                        "assertion_name": "atom_stmt",
                        "object_id": "stmt_a",
                        "json_path": "/D_norm/statements/0",
                    }
                ],
            }
        ],
    )
    resp = diff_endpoint(req)
    assert resp.left_id == "ir_left"
    assert resp.right_id == "ir_right"
    assert resp.solver.status_flip == "UNSAT→SAT"
    assert resp.summary.run_source == "provided"
    assert resp.solver.core_delta.removed_atoms == ["atom_stmt"]
    assert resp.causal_slice.touched_atoms == ["atom_stmt"]
    assert resp.causal_slice.explanation_items[0].span is not None


def test_diff_endpoint_recomputes_runs_when_inline_runs_missing() -> None:
    req = DiffRequest(
        left_ir=_left_ir(),
        right_ir=_right_ir(),
        left_artifact_id="artifact-left",
        right_artifact_id="artifact-right",
    )
    resp = diff_endpoint(req)
    assert resp.solver.status_flip == "SAT→SAT"
    assert resp.solver.left_runs
    assert resp.solver.right_runs
    assert resp.summary.run_source == "recomputed"
    assert resp.summary.recompute_mode == "LAX"
    assert resp.summary.left_backend == "z3"
    assert resp.summary.right_backend == "z3"


def test_diff_endpoint_uses_requested_recompute_mode() -> None:
    req = DiffRequest(left_ir=_left_ir(), right_ir=_right_ir(), mode=KernelMode.STRICT)
    resp = diff_endpoint(req)
    assert resp.summary.recompute_mode == "STRICT"


def test_diff_endpoint_recompute_failure_is_missing_not_error(monkeypatch) -> None:
    def _explode(*args, **kwargs):
        raise RuntimeError("boom")

    monkeypatch.setattr(api_main, "check_with_validator_runs", _explode)
    req = DiffRequest(left_ir=_left_ir(), right_ir=_right_ir())
    resp = diff_endpoint(req)
    assert resp.solver.status_flip == "NO_RUNS"
    assert resp.solver.left_runs == []
    assert resp.solver.right_runs == []
    assert resp.summary.run_source == "recomputed"
