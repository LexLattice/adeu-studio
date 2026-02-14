from __future__ import annotations

from adeu_ir import SolverEvidence
from adeu_kernel import (
    SEMANTICS_DIAGNOSTICS_SCHEMA,
    build_semantics_diagnostics,
    build_validator_evidence_packet,
)


def test_semantics_diagnostics_is_deterministic_and_sorted() -> None:
    packet_unsat = build_validator_evidence_packet(
        validator_run_id="run-b",
        backend="z3",
        backend_version="4.13.3",
        timeout_ms=3000,
        options={"seed": 2},
        request_hash="b" * 64,
        formula_hash="b" * 64,
        status="UNSAT",
        evidence={
            "unsat_core": ["a:dn2:bbbb2222bbbb", "a:dn1:aaaa1111aaaa"],
            "core_trace": [
                {
                    "assertion_name": "a:dn2:bbbb2222bbbb",
                    "object_id": "dn2",
                    "json_path": "/D_norm/statements/1",
                },
                {
                    "assertion_name": "a:dn1:aaaa1111aaaa",
                    "object_id": "dn1",
                    "json_path": "/D_norm/statements/0",
                },
            ],
            "stats": {"num_assertions": 2},
        },
        atom_map={
            "a:dn1:aaaa1111aaaa": {"object_id": "dn1", "json_path": "/D_norm/statements/0"},
            "a:dn2:bbbb2222bbbb": {"object_id": "dn2", "json_path": "/D_norm/statements/1"},
        },
        assurance="solver_backed",
    )
    packet_error = build_validator_evidence_packet(
        validator_run_id="run-a",
        backend="z3",
        backend_version="4.13.3",
        timeout_ms=3000,
        options={"seed": 1},
        request_hash="a" * 64,
        formula_hash="a" * 64,
        status="ERROR",
        evidence=SolverEvidence(error="backend failed", stats={"num_assertions": 0}),
        atom_map={},
    )

    first = build_semantics_diagnostics(
        artifact_ref="artifact:abc",
        validator_evidence_packets=[packet_unsat, packet_error],
    )
    second = build_semantics_diagnostics(
        artifact_ref="artifact:abc",
        validator_evidence_packets=[packet_error, packet_unsat],
    )

    assert first == second
    assert first["schema"] == SEMANTICS_DIAGNOSTICS_SCHEMA
    assert [record["validator_run_id"] for record in first["records"]] == ["run-a", "run-b"]
    assert first["records"][0]["assurance"] == "kernel_only"
    assert [ref["assertion_name"] for ref in first["records"][1]["witness_refs"]] == [
        "a:dn1:aaaa1111aaaa",
        "a:dn2:bbbb2222bbbb",
    ]
    assert len(str(first["semantics_diagnostics_hash"])) == 64
