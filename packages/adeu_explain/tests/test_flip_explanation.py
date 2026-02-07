from __future__ import annotations

from adeu_explain import build_diff_report, build_flip_explanation


def _left_ir() -> dict:
    return {
        "ir_id": "left_ir",
        "D_norm": {
            "statements": [
                {
                    "id": "stmt_a",
                    "kind": "obligation",
                    "action": {"verb": "pay"},
                    "scope": {"jurisdiction": "US-CA", "time_about": {"kind": "unspecified"}},
                    "provenance": {"doc_ref": "doc:test#1", "span": {"start": 1, "end": 9}},
                }
            ]
        },
    }


def _right_ir() -> dict:
    return {
        "ir_id": "right_ir",
        "D_norm": {
            "statements": [
                {
                    "id": "stmt_a",
                    "kind": "prohibition",
                    "action": {"verb": "pay"},
                    "scope": {"jurisdiction": "US-CA", "time_about": {"kind": "unspecified"}},
                    "provenance": {"doc_ref": "doc:test#1", "span": {"start": 1, "end": 9}},
                }
            ]
        },
    }


def test_build_flip_explanation_reports_status_and_cause_chain() -> None:
    diff = build_diff_report(
        _left_ir(),
        _right_ir(),
        left_id="left_ir",
        right_id="right_ir",
        left_runs=[
            {
                "request_hash": "req-1",
                "formula_hash": "f-1",
                "status": "UNSAT",
                "evidence_json": {"unsat_core": ["atom_stmt"], "model": {}},
                "atom_map_json": {
                    "atom_stmt": {"object_id": "stmt_a", "json_path": "/D_norm/statements/0/kind"}
                },
            }
        ],
        right_runs=[
            {
                "request_hash": "req-1",
                "formula_hash": "f-1",
                "status": "SAT",
                "evidence_json": {"unsat_core": [], "model": {"atom_stmt": "True"}},
                "atom_map_json": {
                    "atom_stmt": {"object_id": "stmt_a", "json_path": "/D_norm/statements/0/kind"}
                },
            }
        ],
    )
    explanation = build_flip_explanation(
        _left_ir(),
        _right_ir(),
        diff_report=diff,
        left_check_status="REFUSE",
        right_check_status="WARN",
    )

    assert explanation.flip_kind == "UNSAT→SAT"
    assert explanation.check_status_flip == "REFUSE→WARN"
    assert explanation.solver_status_flip == "UNSAT→SAT"
    assert explanation.primary_changes
    assert explanation.evidence_changes
    assert explanation.cause_chain
    first = explanation.cause_chain[0]
    assert first.left_span is not None
    assert first.right_span is not None
    assert first.object_kind == "statement"


def test_build_flip_explanation_is_deterministic() -> None:
    diff = build_diff_report(
        _left_ir(),
        _right_ir(),
        left_id="left_ir",
        right_id="right_ir",
        left_runs=[
            {
                "request_hash": "req-2",
                "formula_hash": "f-2",
                "status": "SAT",
                "evidence_json": {"unsat_core": [], "model": {"atom_stmt": "False"}},
                "atom_map_json": {
                    "atom_stmt": {"object_id": "stmt_a", "json_path": "/D_norm/statements/0/kind"}
                },
            }
        ],
        right_runs=[
            {
                "request_hash": "req-2",
                "formula_hash": "f-2",
                "status": "SAT",
                "evidence_json": {"unsat_core": [], "model": {"atom_stmt": "True"}},
                "atom_map_json": {
                    "atom_stmt": {"object_id": "stmt_a", "json_path": "/D_norm/statements/0/kind"}
                },
            }
        ],
    )
    first = build_flip_explanation(
        _left_ir(),
        _right_ir(),
        diff_report=diff,
        left_check_status="WARN",
        right_check_status="WARN",
    )
    second = build_flip_explanation(
        _left_ir(),
        _right_ir(),
        diff_report=diff,
        left_check_status="WARN",
        right_check_status="WARN",
    )
    assert first.model_dump(mode="json") == second.model_dump(mode="json")
