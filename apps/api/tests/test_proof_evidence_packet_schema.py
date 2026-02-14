from __future__ import annotations

import json
from pathlib import Path

from adeu_kernel import build_proof_evidence_packet
from jsonschema import Draft202012Validator


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("Repository root not found")


def _load_schema() -> dict[str, object]:
    return json.loads(
        (_repo_root() / "spec" / "proof_evidence.schema.json").read_text(encoding="utf-8")
    )


def test_proof_evidence_schema_accepts_normalized_payload() -> None:
    packet = build_proof_evidence_packet(
        proof_id="proof_a",
        artifact_id="artifact_a",
        created_at="2026-02-14T00:00:00+00:00",
        backend="lean",
        theorem_id="thm_alpha",
        status="proved",
        proof_hash="a" * 64,
        inputs=[
            {"object_id": "x", "json_path": "/action", "formula_hash": "f" * 64},
        ],
        details={"semantics_version": "adeu.lean.core.v1"},
    )
    validator = Draft202012Validator(_load_schema())
    errors = sorted(validator.iter_errors(packet), key=lambda err: err.path)
    assert errors == []


def test_proof_evidence_hash_is_stable_across_binding_key_change() -> None:
    base_kwargs = dict(
        artifact_id="artifact_a",
        created_at="2026-02-14T00:00:00+00:00",
        backend="lean",
        theorem_id="thm_alpha",
        status="proved",
        proof_hash="a" * 64,
        inputs=[],
        details={"semantics_version": "adeu.lean.core.v1"},
    )
    first = build_proof_evidence_packet(proof_id="proof_a", **base_kwargs)
    second = build_proof_evidence_packet(proof_id="proof_b", **base_kwargs)
    assert first["proof_id"] != second["proof_id"]
    assert first["proof_evidence_hash"] == second["proof_evidence_hash"]
