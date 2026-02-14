from __future__ import annotations

import json
from pathlib import Path

from adeu_ir import SolverEvidence
from adeu_kernel import build_validator_evidence_packet
from jsonschema import Draft202012Validator


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("repository root not found")


def _load_schema() -> dict[str, object]:
    return json.loads(
        (_repo_root() / "spec" / "validator_evidence_packet.schema.json").read_text(
            encoding="utf-8"
        )
    )


def test_validator_evidence_packet_schema_accepts_normalized_payload() -> None:
    packet = build_validator_evidence_packet(
        validator_run_id="run-1",
        backend="z3",
        backend_version="4.13.3",
        timeout_ms=3000,
        options={"seed": 7},
        request_hash="a" * 64,
        formula_hash="b" * 64,
        status="UNSAT",
        evidence=SolverEvidence(
            unsat_core=["a:dn2:bbbb2222bbbb", "a:dn1:aaaa1111aaaa"],
            stats={"num_assertions": 2, "solver_time_s": 1.5},
        ),
        atom_map={
            "a:dn1:aaaa1111aaaa": {
                "object_id": "dn1",
                "json_path": "/D_norm/statements/0",
            },
            "a:dn2:bbbb2222bbbb": {
                "object_id": "dn2",
                "json_path": "/D_norm/statements/1",
            },
        },
        assurance="solver_backed",
    )
    validator = Draft202012Validator(_load_schema())
    errors = sorted(validator.iter_errors(packet), key=lambda err: str(err.path))
    assert errors == []


def test_validator_evidence_packet_hash_is_stable_across_run_id_changes() -> None:
    base_kwargs = {
        "backend": "z3",
        "backend_version": "4.13.3",
        "timeout_ms": 3000,
        "options": {"seed": 7},
        "request_hash": "a" * 64,
        "formula_hash": "b" * 64,
        "status": "SAT",
        "evidence": SolverEvidence(model={"x": "true"}, stats={"num_assertions": 1}),
        "atom_map": {},
        "assurance": "solver_backed",
    }
    first = build_validator_evidence_packet(validator_run_id="run-1", **base_kwargs)
    second = build_validator_evidence_packet(validator_run_id="run-2", **base_kwargs)
    assert first["evidence_packet_hash"] == second["evidence_packet_hash"]
