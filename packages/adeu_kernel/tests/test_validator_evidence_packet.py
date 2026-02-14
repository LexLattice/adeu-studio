from __future__ import annotations

from adeu_ir import SolverEvidence, ValidatorAtomRef
from adeu_kernel import VALIDATOR_EVIDENCE_PACKET_SCHEMA, build_validator_evidence_packet


def test_validator_evidence_packet_is_deterministic_for_identical_inputs() -> None:
    atom_map = {
        "a:dn1:aaaa1111aaaa": {"object_id": "dn1", "json_path": "/D_norm/statements/0"},
        "a:dn2:bbbb2222bbbb": {"object_id": "dn2", "json_path": "/D_norm/statements/1"},
    }
    evidence = SolverEvidence(
        unsat_core=["a:dn2:bbbb2222bbbb", "a:dn1:aaaa1111aaaa"],
        stats={
            "num_assertions": 2,
            "solver_time_s": 1.5,
            "backend_payload": {"b": 2, "a": 1},
        },
    )

    first = build_validator_evidence_packet(
        validator_run_id="run-alpha",
        backend="z3",
        backend_version="4.13.3",
        timeout_ms=3000,
        options={"seed": 7, "mbqi": False},
        request_hash="a" * 64,
        formula_hash="b" * 64,
        status="UNSAT",
        evidence=evidence,
        atom_map=atom_map,
        assurance="solver_backed",
    )
    second = build_validator_evidence_packet(
        validator_run_id="run-alpha",
        backend="z3",
        backend_version="4.13.3",
        timeout_ms=3000,
        options={"mbqi": False, "seed": 7},
        request_hash="a" * 64,
        formula_hash="b" * 64,
        status="UNSAT",
        evidence=evidence,
        atom_map=atom_map,
        assurance="solver_backed",
    )

    assert first == second
    assert first["schema"] == VALIDATOR_EVIDENCE_PACKET_SCHEMA
    assert first["evidence"]["unsat_core"] == [
        "a:dn1:aaaa1111aaaa",
        "a:dn2:bbbb2222bbbb",
    ]
    assert [item["assertion_name"] for item in first["evidence"]["core_trace"]] == [
        "a:dn1:aaaa1111aaaa",
        "a:dn2:bbbb2222bbbb",
    ]
    assert first["evidence"]["stats"] == {
        "backend_payload": '{"a":1,"b":2}',
        "num_assertions": 2,
        "solver_time_s": "1.5",
    }


def test_validator_evidence_packet_hash_excludes_validator_run_id() -> None:
    packet_a = build_validator_evidence_packet(
        validator_run_id="run-alpha",
        backend="z3",
        backend_version="4.13.3",
        timeout_ms=3000,
        options={"seed": 7},
        request_hash="a" * 64,
        formula_hash="b" * 64,
        status="SAT",
        evidence=SolverEvidence(
            model={"|x|": "true"},
            stats={"num_assertions": 1},
        ),
        atom_map=[
            ValidatorAtomRef(
                assertion_name="a:dn1:aaaa1111aaaa",
                object_id="dn1",
                json_path="/D_norm/statements/0",
            )
        ],
        assurance="solver_backed",
    )
    packet_b = build_validator_evidence_packet(
        validator_run_id="run-beta",
        backend="z3",
        backend_version="4.13.3",
        timeout_ms=3000,
        options={"seed": 7},
        request_hash="a" * 64,
        formula_hash="b" * 64,
        status="SAT",
        evidence=SolverEvidence(
            model={"|x|": "true"},
            stats={"num_assertions": 1},
        ),
        atom_map=[
            ValidatorAtomRef(
                assertion_name="a:dn1:aaaa1111aaaa",
                object_id="dn1",
                json_path="/D_norm/statements/0",
            )
        ],
        assurance="solver_backed",
    )

    assert packet_a["validator_run_id"] != packet_b["validator_run_id"]
    assert packet_a["evidence_packet_hash"] == packet_b["evidence_packet_hash"]
