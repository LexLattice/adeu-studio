from __future__ import annotations

from adeu_explain import (
    EXPLAIN_DIFF_SCHEMA,
    build_explain_diff_packet,
    validate_explain_diff_packet,
)


def _sample_diff_report_payload() -> dict[str, object]:
    return {
        "left_id": "left",
        "right_id": "right",
        "structural": {
            "json_patches": [
                {"op": "replace", "path": "/b", "value": 2},
                {"op": "replace", "path": "/a", "value": 1},
            ],
            "changed_paths": ["/z", "/a"],
            "changed_object_ids": ["obj-z", "obj-a"],
        },
        "solver": {
            "left_runs": [
                {
                    "run_id": "run-b",
                    "request_hash": "req-b",
                    "formula_hash": "form-b",
                    "created_at": "2026-02-15T00:00:00+00:00",
                },
                {
                    "run_id": "run-a",
                    "request_hash": "req-a",
                    "formula_hash": "form-a",
                    "created_at": "2026-02-14T00:00:00+00:00",
                },
            ],
            "right_runs": [],
            "status_flip": "UNSAT→SAT",
            "core_delta": {
                "added_atoms": ["atom-z", "atom-a"],
                "removed_atoms": ["atom-c", "atom-b"],
            },
            "model_delta": {
                "added_assignments": [
                    {"atom": "z", "value": "true"},
                    {"atom": "a", "value": "false"},
                ],
                "removed_assignments": [],
                "changed_assignments": [
                    {"atom": "k", "left_value": "false", "right_value": "true"},
                    {"atom": "a", "left_value": "false", "right_value": "true"},
                ],
                "changed_atoms": ["k", "a"],
            },
            "request_hash_changed": False,
            "formula_hash_changed": False,
            "unpaired_left_hashes": ["z", "a"],
            "unpaired_right_hashes": ["r", "b"],
        },
        "causal_slice": {
            "touched_atoms": ["atom-z", "atom-a"],
            "touched_object_ids": ["obj-z", "obj-a"],
            "touched_json_paths": ["/z", "/a"],
            "explanation_items": [
                {"atom_name": "atom-z", "object_id": "obj-z", "json_path": "/z"},
                {"atom_name": "atom-a", "object_id": "obj-a", "json_path": "/a"},
            ],
        },
        "summary": {
            "status_flip": "UNSAT→SAT",
            "solver_pairing_state": "PAIRED",
            "mapping_trust": "derived_bridge",
            "solver_trust": "solver_backed",
            "proof_trust": None,
            "unpaired_left_keys": ["z", "a"],
            "unpaired_right_keys": ["r", "b"],
            "structural_patch_count": "2",
            "solver_touched_atom_count": "2",
            "causal_atom_count": "2",
            "run_source": "provided",
            "recompute_mode": "LAX",
            "left_backend": "z3",
            "right_backend": "z3",
            "left_timeout_ms": 5000,
            "right_timeout_ms": 5000,
        },
    }


def test_build_explain_diff_packet_is_deterministic_and_canonical() -> None:
    packet = build_explain_diff_packet(
        explain_kind="semantic_diff",
        input_artifact_refs=["artifact:b", "artifact:a"],
        diff_report=_sample_diff_report_payload(),
        diff_refs=["artifact:diff:z", "artifact:diff:a"],
        witness_refs=["artifact:witness:z", "artifact:witness:a"],
        validator_evidence_packet_refs=["artifact:validator:r2", "artifact:validator:r1"],
    )

    assert packet["schema"] == EXPLAIN_DIFF_SCHEMA
    assert packet["input_artifact_refs"] == ["artifact:a", "artifact:b"]
    assert packet["diff_refs"] == ["artifact:diff:a", "artifact:diff:z"]
    assert packet["witness_refs"] == ["artifact:witness:a", "artifact:witness:z"]
    assert packet["validator_evidence_packet_refs"] == [
        "artifact:validator:r1",
        "artifact:validator:r2",
    ]

    structural = packet["sections"]["diff_report"]["structural"]
    assert structural["changed_paths"] == ["/a", "/z"]
    assert structural["changed_object_ids"] == ["obj-a", "obj-z"]

    validate_explain_diff_packet(packet)


def test_explain_hash_excludes_nonsemantic_diagnostics() -> None:
    base_kwargs = {
        "explain_kind": "flip_explain",
        "input_artifact_refs": ["artifact:a"],
        "diff_report": _sample_diff_report_payload(),
        "flip_explanation": {
            "flip_kind": "status_change",
            "check_status_flip": "REFUSE→WARN",
            "solver_status_flip": "UNSAT→SAT",
            "primary_changes": [],
            "evidence_changes": [],
            "cause_chain": [],
            "repair_hints": [],
        },
    }

    first = build_explain_diff_packet(
        **base_kwargs,
        run_ir_mismatch=False,
        left_mismatch=False,
        right_mismatch=False,
        nonsemantic_fields={"client_request_id": "req-a", "operator_note": "first"},
    )
    second = build_explain_diff_packet(
        **base_kwargs,
        run_ir_mismatch=True,
        left_mismatch=True,
        right_mismatch=True,
        nonsemantic_fields={"client_request_id": "req-b", "operator_note": "second"},
    )

    assert first["explain_hash"] == second["explain_hash"]
    validate_explain_diff_packet(first)
    validate_explain_diff_packet(second)


def test_validate_explain_diff_packet_rejects_invalid_ref() -> None:
    packet = build_explain_diff_packet(
        explain_kind="semantic_diff",
        input_artifact_refs=["artifact:a"],
        diff_report=_sample_diff_report_payload(),
    )
    packet["input_artifact_refs"] = ["validator:run-1"]

    try:
        validate_explain_diff_packet(packet)
        assert False, "expected invalid ref failure"
    except ValueError as exc:
        assert "invalid explain ref format" in str(exc)
