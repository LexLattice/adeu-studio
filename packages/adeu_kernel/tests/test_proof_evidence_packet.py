from __future__ import annotations

from adeu_ir import ProofInput
from adeu_kernel import PROOF_EVIDENCE_SCHEMA, build_proof_evidence_packet


def test_proof_evidence_packet_is_deterministic_for_identical_inputs() -> None:
    first = build_proof_evidence_packet(
        proof_id="proof_a",
        artifact_id="artifact_a",
        created_at="2026-02-14T00:00:00+00:00",
        backend="lean",
        theorem_id="thm_alpha",
        status="proved",
        proof_hash="a" * 64,
        inputs=[
            ProofInput(object_id="policy_context", json_path="/action_hash", formula_hash="h2"),
            ProofInput(object_id="adeu.get_app_state", json_path="/action_kind", formula_hash="h1"),
        ],
        details={"z": 2, "a": 1},
    )
    second = build_proof_evidence_packet(
        proof_id="proof_a",
        artifact_id="artifact_a",
        created_at="2026-02-14T00:00:00+00:00",
        backend="lean",
        theorem_id="thm_alpha",
        status="proved",
        proof_hash="a" * 64,
        inputs=[
            {"object_id": "adeu.get_app_state", "json_path": "/action_kind", "formula_hash": "h1"},
            {"object_id": "policy_context", "json_path": "/action_hash", "formula_hash": "h2"},
        ],
        details={"a": 1, "z": 2},
    )

    assert first == second
    assert first["schema"] == PROOF_EVIDENCE_SCHEMA
    assert first["inputs"] == [
        {"object_id": "adeu.get_app_state", "json_path": "/action_kind", "formula_hash": "h1"},
        {"object_id": "policy_context", "json_path": "/action_hash", "formula_hash": "h2"},
    ]


def test_proof_evidence_hash_excludes_proof_id_and_created_at() -> None:
    packet_a = build_proof_evidence_packet(
        proof_id="proof_a",
        artifact_id="artifact_a",
        created_at="2026-02-14T00:00:00+00:00",
        backend="lean",
        theorem_id="thm_alpha",
        status="proved",
        proof_hash="a" * 64,
        inputs=[],
        details={},
    )
    packet_b = build_proof_evidence_packet(
        proof_id="proof_b",
        artifact_id="artifact_a",
        created_at="2027-02-14T00:00:00+00:00",
        backend="lean",
        theorem_id="thm_alpha",
        status="proved",
        proof_hash="a" * 64,
        inputs=[],
        details={},
    )

    assert packet_a["proof_id"] != packet_b["proof_id"]
    assert packet_a["proof_evidence_hash"] == packet_b["proof_evidence_hash"]


def test_failed_packet_sets_deterministic_failed_reason() -> None:
    packet = build_proof_evidence_packet(
        proof_id="proof_timeout",
        artifact_id="artifact_a",
        created_at="2026-02-14T00:00:00+00:00",
        backend="lean",
        theorem_id="thm_alpha",
        status="failed",
        proof_hash="b" * 64,
        inputs=[],
        details={"error": "timed out while waiting for Lean backend"},
    )
    assert packet["failed"] == {"reason": "timeout"}
