from __future__ import annotations

import json
from pathlib import Path

from adeu_explain import build_explain_diff_packet
from jsonschema import Draft202012Validator


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("Repository root not found")


def _load_schema() -> dict[str, object]:
    schema_path = _repo_root() / "spec" / "explain_diff.schema.json"
    return json.loads(schema_path.read_text(encoding="utf-8"))


def _diff_report() -> dict[str, object]:
    return {
        "left_id": "left",
        "right_id": "right",
        "structural": {
            "json_patches": [],
            "changed_paths": [],
            "changed_object_ids": [],
        },
        "solver": {
            "left_runs": [],
            "right_runs": [],
            "status_flip": "NO_RUNS",
            "core_delta": {"added_atoms": [], "removed_atoms": []},
            "model_delta": {
                "added_assignments": [],
                "removed_assignments": [],
                "changed_assignments": [],
                "changed_atoms": [],
            },
            "request_hash_changed": False,
            "formula_hash_changed": False,
            "unpaired_left_hashes": [],
            "unpaired_right_hashes": [],
        },
        "causal_slice": {
            "touched_atoms": [],
            "touched_object_ids": [],
            "touched_json_paths": [],
            "explanation_items": [],
        },
        "summary": {
            "status_flip": "NO_RUNS",
            "solver_pairing_state": "NO_RUNS",
            "mapping_trust": "derived_bridge",
            "solver_trust": "kernel_only",
            "proof_trust": None,
            "unpaired_left_keys": [],
            "unpaired_right_keys": [],
            "structural_patch_count": "0",
            "solver_touched_atom_count": "0",
            "causal_atom_count": "0",
            "run_source": "recomputed",
            "recompute_mode": "LAX",
            "left_backend": None,
            "right_backend": None,
            "left_timeout_ms": None,
            "right_timeout_ms": None,
        },
    }


def test_explain_diff_schema_accepts_normalized_payload() -> None:
    payload = build_explain_diff_packet(
        explain_kind="semantic_diff",
        input_artifact_refs=["artifact:a"],
        diff_report=_diff_report(),
        diff_refs=["artifact:diff:a"],
        witness_refs=["artifact:witness:a"],
    )
    validator = Draft202012Validator(_load_schema())
    errors = sorted(validator.iter_errors(payload), key=lambda err: err.path)
    assert errors == []


def test_explain_diff_hash_is_stable_when_nonsemantic_fields_change() -> None:
    first = build_explain_diff_packet(
        explain_kind="flip_explain",
        input_artifact_refs=["artifact:a"],
        diff_report=_diff_report(),
        flip_explanation={
            "flip_kind": "none",
            "check_status_flip": "PASS→PASS",
            "solver_status_flip": "NO_RUNS",
            "primary_changes": [],
            "evidence_changes": [],
            "cause_chain": [],
            "repair_hints": [],
        },
        run_ir_mismatch=False,
        left_mismatch=False,
        right_mismatch=False,
        nonsemantic_fields={"client_request_id": "req-a"},
    )
    second = build_explain_diff_packet(
        explain_kind="flip_explain",
        input_artifact_refs=["artifact:a"],
        diff_report=_diff_report(),
        flip_explanation={
            "flip_kind": "none",
            "check_status_flip": "PASS→PASS",
            "solver_status_flip": "NO_RUNS",
            "primary_changes": [],
            "evidence_changes": [],
            "cause_chain": [],
            "repair_hints": [],
        },
        run_ir_mismatch=True,
        left_mismatch=True,
        right_mismatch=True,
        nonsemantic_fields={"client_request_id": "req-b"},
    )

    assert first["explain_hash"] == second["explain_hash"]
