from __future__ import annotations

import json
from pathlib import Path

from adeu_api.main import (
    get_artifact_semantics_diagnostics_endpoint,
    get_concept_artifact_semantics_diagnostics_endpoint,
)
from adeu_api.storage import create_artifact, create_concept_artifact, create_validator_run
from jsonschema import Draft202012Validator


def _repo_root() -> Path:
    current_path = Path(__file__).resolve()
    for parent in current_path.parents:
        if (parent / ".git").exists():
            return parent
    raise FileNotFoundError("repository root not found")


def _load_schema() -> dict[str, object]:
    return json.loads(
        (_repo_root() / "spec" / "semantics_diagnostics.schema.json").read_text(encoding="utf-8")
    )


def test_artifact_semantics_diagnostics_endpoint_is_deterministic_and_schema_valid(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))

    artifact = create_artifact(
        clause_text="x",
        doc_id="doc:test",
        jurisdiction="US-CA",
        status="PASS",
        num_errors=0,
        num_warns=0,
        ir_json={},
        check_report_json={},
    )

    create_validator_run(
        artifact_id=artifact.artifact_id,
        concept_artifact_id=None,
        backend="z3",
        backend_version="4.13.3",
        timeout_ms=3000,
        options_json={"seed": 2},
        request_hash="b" * 64,
        formula_hash="b" * 64,
        status="UNSAT",
        assurance=None,
        evidence_json={
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
        atom_map_json={
            "a:dn1:aaaa1111aaaa": {"object_id": "dn1", "json_path": "/D_norm/statements/0"},
            "a:dn2:bbbb2222bbbb": {"object_id": "dn2", "json_path": "/D_norm/statements/1"},
        },
    )
    create_validator_run(
        artifact_id=artifact.artifact_id,
        concept_artifact_id=None,
        backend="z3",
        backend_version="4.13.3",
        timeout_ms=3000,
        options_json={"seed": 1},
        request_hash="a" * 64,
        formula_hash="a" * 64,
        status="ERROR",
        assurance=None,
        evidence_json={"error": "backend failed", "stats": {"num_assertions": 0}},
        atom_map_json={},
    )

    first = get_artifact_semantics_diagnostics_endpoint(artifact.artifact_id).model_dump(
        mode="json"
    )
    second = get_artifact_semantics_diagnostics_endpoint(artifact.artifact_id).model_dump(
        mode="json"
    )

    assert first == second
    assert first["schema"] == "semantics_diagnostics@1"
    assert first["artifact_ref"] == f"artifact:{artifact.artifact_id}"
    assert first["records"][0]["formula_hash"] == "a" * 64
    assert first["records"][0]["assurance"] == "kernel_only"
    assert first["records"][1]["formula_hash"] == "b" * 64
    assert first["records"][1]["assurance"] == "solver_backed"
    assert [ref["assertion_name"] for ref in first["records"][1]["witness_refs"]] == [
        "a:dn1:aaaa1111aaaa",
        "a:dn2:bbbb2222bbbb",
    ]

    validator = Draft202012Validator(_load_schema())
    errors = sorted(validator.iter_errors(first), key=lambda err: str(err.path))
    assert errors == []


def test_concept_artifact_semantics_diagnostics_endpoint_returns_deterministic_payload(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))

    concept_artifact = create_concept_artifact(
        schema_version="adeu.concepts.v0",
        artifact_version=1,
        source_text="x",
        doc_id="doc:test",
        status="PASS",
        num_errors=0,
        num_warns=0,
        ir_json={},
        check_report_json={},
        analysis_json=None,
    )
    run = create_validator_run(
        artifact_id=None,
        concept_artifact_id=concept_artifact.artifact_id,
        backend="z3",
        backend_version="4.13.3",
        timeout_ms=3000,
        options_json={},
        request_hash="c" * 64,
        formula_hash="d" * 64,
        status="SAT",
        assurance="solver_backed",
        evidence_json={"model": {"x": "true"}, "stats": {"num_assertions": 1}},
        atom_map_json={},
    )

    payload = get_concept_artifact_semantics_diagnostics_endpoint(
        concept_artifact.artifact_id
    ).model_dump(mode="json")

    assert payload["artifact_ref"] == f"concept_artifact:{concept_artifact.artifact_id}"
    assert len(payload["records"]) == 1
    assert payload["records"][0]["validator_run_id"] == run.run_id
    assert payload["records"][0]["status"] == "SAT"
    assert payload["records"][0]["assurance"] == "solver_backed"
