from __future__ import annotations

from adeu_explain import build_diff_report


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
                },
                {
                    "id": "stmt_b",
                    "kind": "prohibition",
                    "action": {"verb": "share"},
                    "scope": {"jurisdiction": "US-CA", "time_about": {"kind": "unspecified"}},
                },
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
                },
                {
                    "id": "stmt_b",
                    "kind": "prohibition",
                    "action": {"verb": "share"},
                    "scope": {"jurisdiction": "US-CA", "time_about": {"kind": "unspecified"}},
                },
            ],
            "exceptions": [
                {
                    "id": "ex_high",
                    "label": "unless approved",
                }
            ],
        },
    }


def test_structural_diff_is_deterministic() -> None:
    first = build_diff_report(_left_ir(), _right_ir(), left_id="left_ir", right_id="right_ir")
    second = build_diff_report(_left_ir(), _right_ir(), left_id="left_ir", right_id="right_ir")
    assert first.model_dump(mode="json") == second.model_dump(mode="json")

    patch_keys = [(patch.path, patch.op) for patch in first.structural.json_patches]
    assert patch_keys == sorted(patch_keys)
    assert "/D_norm/statements/0/kind" in first.structural.changed_paths
    assert "stmt_a" in first.structural.changed_object_ids
    assert "ex_high" in first.structural.changed_object_ids


def test_solver_diff_pairing_and_status_flip_are_deterministic() -> None:
    left_runs = [
        {
            "run_id": "left-run-0",
            "created_at": "2026-02-06T10:00:00Z",
            "request_hash": "req-1",
            "formula_hash": "f-1",
            "status": "UNSAT",
            "evidence_json": {"unsat_core": ["atom_conflict"], "model": {}},
            "atom_map_json": {
                "atom_conflict": {
                    "object_id": "stmt_a",
                    "json_path": "/D_norm/statements/0",
                }
            },
        }
    ]
    right_runs = [
        {
            "run_id": "right-run-0",
            "created_at": "2026-02-06T10:01:00Z",
            "request_hash": "req-1",
            "formula_hash": "f-1",
            "status": "SAT",
            "evidence_json": {"unsat_core": [], "model": {"atom_conflict": "True"}},
            "atom_map_json": [
                {
                    "assertion_name": "atom_conflict",
                    "object_id": "stmt_a",
                    "json_path": "/D_norm/statements/0",
                }
            ],
        }
    ]

    report = build_diff_report(
        _left_ir(),
        _right_ir(),
        left_id="left_ir",
        right_id="right_ir",
        left_runs=left_runs,
        right_runs=right_runs,
    )
    assert report.solver.status_flip == "UNSAT→SAT"
    assert report.solver.request_hash_changed is False
    assert report.solver.formula_hash_changed is False
    assert report.solver.core_delta.removed_atoms == ["atom_conflict"]
    assert report.solver.model_delta.added_assignments[0].atom == "atom_conflict"

    rerun = build_diff_report(
        _left_ir(),
        _right_ir(),
        left_id="left_ir",
        right_id="right_ir",
        left_runs=left_runs,
        right_runs=right_runs,
    )
    assert report.model_dump(mode="json") == rerun.model_dump(mode="json")


def test_causal_slice_intersects_structural_and_solver_deltas() -> None:
    left_runs = [
        {
            "request_hash": "req-2",
            "formula_hash": "f-2",
            "status": "UNSAT",
            "evidence_json": {"unsat_core": ["atom_stmt_b"], "model": {}},
            "atom_map_json": {
                "atom_stmt_b": {
                    "object_id": "stmt_b",
                    "json_path": "/D_norm/statements/1",
                }
            },
        }
    ]
    right_runs = [
        {
            "request_hash": "req-2",
            "formula_hash": "f-2",
            "status": "UNSAT",
            "evidence_json": {"unsat_core": ["atom_stmt_a"], "model": {}},
            "atom_map_json": {
                "atom_stmt_a": {
                    "object_id": "stmt_a",
                    "json_path": "/D_norm/statements/0",
                }
            },
        }
    ]

    report = build_diff_report(
        _left_ir(),
        _right_ir(),
        left_id="left_ir",
        right_id="right_ir",
        left_runs=left_runs,
        right_runs=right_runs,
    )
    assert report.causal_slice.touched_atoms == ["atom_stmt_a"]
    assert report.causal_slice.touched_object_ids == ["stmt_a"]
    assert report.causal_slice.touched_json_paths == ["/D_norm/statements/0"]


def test_missing_pairable_runs_are_reported_as_no_runs() -> None:
    left_runs = [
        {
            "request_hash": "req-left",
            "formula_hash": "f-left",
            "status": "SAT",
            "evidence_json": {"unsat_core": [], "model": {}},
            "atom_map_json": {},
        }
    ]
    right_runs = [
        {
            "request_hash": "req-right",
            "formula_hash": "f-right",
            "status": "UNSAT",
            "evidence_json": {"unsat_core": ["a"], "model": {}},
            "atom_map_json": {"a": {"object_id": "stmt_a", "json_path": "/D_norm/statements/0"}},
        }
    ]
    report = build_diff_report(
        _left_ir(),
        _right_ir(),
        left_id="left_ir",
        right_id="right_ir",
        left_runs=left_runs,
        right_runs=right_runs,
    )
    assert report.solver.status_flip == "NO_RUNS"
    assert report.solver.unpaired_left_hashes == ["req-left:f-left"]
    assert report.solver.unpaired_right_hashes == ["req-right:f-right"]


def test_solver_diff_handles_mixed_and_missing_timestamps_across_pairs() -> None:
    left_runs = [
        {
            "request_hash": "req-a",
            "formula_hash": "f-a",
            "created_at": None,
            "status": "UNSAT",
            "evidence_json": {"unsat_core": ["atom_a"], "model": {}},
            "atom_map_json": {
                "atom_a": {"object_id": "stmt_a", "json_path": "/D_norm/statements/0"}
            },
        },
        {
            "request_hash": "req-b",
            "formula_hash": "f-b",
            "created_at": "2026-02-06T10:00:00Z",
            "status": "SAT",
            "evidence_json": {"unsat_core": [], "model": {"atom_b": "True"}},
            "atom_map_json": {
                "atom_b": {"object_id": "stmt_b", "json_path": "/D_norm/statements/1"}
            },
        },
    ]
    right_runs = [
        {
            "request_hash": "req-a",
            "formula_hash": "f-a",
            "created_at": None,
            "status": "SAT",
            "evidence_json": {"unsat_core": [], "model": {"atom_a": "True"}},
            "atom_map_json": {
                "atom_a": {"object_id": "stmt_a", "json_path": "/D_norm/statements/0"}
            },
        },
        {
            "request_hash": "req-b",
            "formula_hash": "f-b",
            "created_at": "2026-02-06T10:01:00Z",
            "status": "UNSAT",
            "evidence_json": {"unsat_core": ["atom_b"], "model": {}},
            "atom_map_json": {
                "atom_b": {"object_id": "stmt_b", "json_path": "/D_norm/statements/1"}
            },
        },
    ]
    report = build_diff_report(
        _left_ir(),
        _right_ir(),
        left_id="left_ir",
        right_id="right_ir",
        left_runs=left_runs,
        right_runs=right_runs,
    )
    assert report.solver.status_flip == "SAT→UNSAT"


def test_solver_diff_handles_mixed_timestamps_within_same_pair() -> None:
    left_runs = [
        {
            "request_hash": "req-c",
            "formula_hash": "f-c",
            "created_at": None,
            "status": "UNSAT",
            "evidence_json": {"unsat_core": ["atom_c"], "model": {}},
            "atom_map_json": {
                "atom_c": {"object_id": "stmt_a", "json_path": "/D_norm/statements/0"}
            },
        },
        {
            "request_hash": "req-c",
            "formula_hash": "f-c",
            "created_at": "2026-02-06T11:00:00Z",
            "status": "SAT",
            "evidence_json": {"unsat_core": [], "model": {"atom_c": "True"}},
            "atom_map_json": {
                "atom_c": {"object_id": "stmt_a", "json_path": "/D_norm/statements/0"}
            },
        },
    ]
    right_runs = [
        {
            "request_hash": "req-c",
            "formula_hash": "f-c",
            "created_at": "2026-02-06T11:01:00Z",
            "status": "UNSAT",
            "evidence_json": {"unsat_core": ["atom_c"], "model": {}},
            "atom_map_json": {
                "atom_c": {"object_id": "stmt_a", "json_path": "/D_norm/statements/0"}
            },
        }
    ]
    report = build_diff_report(
        _left_ir(),
        _right_ir(),
        left_id="left_ir",
        right_id="right_ir",
        left_runs=left_runs,
        right_runs=right_runs,
    )
    assert report.solver.status_flip == "SAT→UNSAT"


def test_causal_slice_enriches_span_from_object_id() -> None:
    left = _left_ir()
    left["D_norm"]["statements"][0]["provenance"] = {
        "doc_ref": "doc:test:diff#sec1",
        "span": {"start": 3, "end": 12},
    }
    right = _right_ir()
    right["D_norm"]["statements"][0]["provenance"] = {
        "doc_ref": "doc:test:diff#sec1",
        "span": {"start": 3, "end": 12},
    }

    report = build_diff_report(
        left,
        right,
        left_id="left_ir",
        right_id="right_ir",
        left_runs=[
            {
                "request_hash": "req-span-id",
                "formula_hash": "f-span-id",
                "status": "UNSAT",
                "evidence_json": {"unsat_core": ["atom_stmt_a"], "model": {}},
                "atom_map_json": {
                    "atom_stmt_a": {"object_id": "stmt_a", "json_path": "/D_norm/statements/0/kind"}
                },
            }
        ],
        right_runs=[
            {
                "request_hash": "req-span-id",
                "formula_hash": "f-span-id",
                "status": "SAT",
                "evidence_json": {"unsat_core": [], "model": {"atom_stmt_a": "True"}},
                "atom_map_json": {
                    "atom_stmt_a": {"object_id": "stmt_a", "json_path": "/D_norm/statements/0/kind"}
                },
            }
        ],
    )

    assert report.causal_slice.explanation_items
    span = report.causal_slice.explanation_items[0].span
    assert span is not None
    assert span.start == 3
    assert span.end == 12


def test_causal_slice_enriches_span_from_json_path_when_object_id_missing() -> None:
    left = {
        "concept_id": "left_concept",
        "claims": [
            {
                "id": "claim_1",
                "sense_id": "s_a",
                "provenance": {"doc_ref": "doc:concept#1", "span": {"start": 1, "end": 9}},
            }
        ],
    }
    right = {
        "concept_id": "right_concept",
        "claims": [
            {
                "id": "claim_1",
                "sense_id": "s_b",
                "provenance": {"doc_ref": "doc:concept#1", "span": {"start": 1, "end": 9}},
            }
        ],
    }
    report = build_diff_report(
        left,
        right,
        left_id="left_concept",
        right_id="right_concept",
        left_runs=[
            {
                "request_hash": "req-span-path",
                "formula_hash": "f-span-path",
                "status": "UNSAT",
                "evidence_json": {"unsat_core": ["atom_claim"], "model": {}},
                "atom_map_json": {
                    "atom_claim": {"object_id": None, "json_path": "/claims/0/sense_id"}
                },
            }
        ],
        right_runs=[
            {
                "request_hash": "req-span-path",
                "formula_hash": "f-span-path",
                "status": "SAT",
                "evidence_json": {"unsat_core": [], "model": {"atom_claim": "True"}},
                "atom_map_json": {
                    "atom_claim": {"object_id": None, "json_path": "/claims/0/sense_id"}
                },
            }
        ],
    )
    assert report.causal_slice.explanation_items
    span = report.causal_slice.explanation_items[0].span
    assert span is not None
    assert span.start == 1
    assert span.end == 9


def test_pointer_segments_keep_empty_token_for_empty_object_keys() -> None:
    left = {"": {"id": "obj_empty", "value": 1}}
    right = {"": {"id": "obj_empty", "value": 2}}
    report = build_diff_report(left, right, left_id="left_empty", right_id="right_empty")
    assert "//value" in report.structural.changed_paths
    assert "obj_empty" in report.structural.changed_object_ids
