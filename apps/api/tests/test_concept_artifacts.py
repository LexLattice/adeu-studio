from __future__ import annotations

import json
import sqlite3
from pathlib import Path

import adeu_api.main as api_main
import pytest
from adeu_api.main import (
    ConceptAnalyzeRequest,
    ConceptArtifactCreateRequest,
    ConceptArtifactCreateResponse,
    ConceptArtifactListResponse,
    ConceptCheckRequest,
    ConceptProposeRequest,
    analyze_concept_variant,
    check_concept_variant,
    create_concept_artifact_endpoint,
    get_concept_artifact_endpoint,
    list_concept_artifact_validator_runs_endpoint,
    list_concept_artifacts_endpoint,
    propose_concept,
)
from adeu_api.storage import create_validator_run
from adeu_concepts import ConceptIR
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode
from fastapi import HTTPException


def _fixture_payload(name: str) -> dict:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / "bank_sense_coherence" / "proposals" / name
    return json.loads(path.read_text(encoding="utf-8"))


def _fixture_source() -> str:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / "bank_sense_coherence" / "source.txt"
    return path.read_text(encoding="utf-8").strip()


def _coherent_ir() -> ConceptIR:
    return ConceptIR.model_validate(_fixture_payload("var1.json"))


def _fetch_validator_rows(db_path: Path) -> list[sqlite3.Row]:
    with sqlite3.connect(db_path) as con:
        con.row_factory = sqlite3.Row
        return con.execute(
            """
            SELECT artifact_id, concept_artifact_id, backend, status
            FROM validator_runs
            ORDER BY created_at ASC
            """
        ).fetchall()


def _table_count(db_path: Path, table: str) -> int:
    with sqlite3.connect(db_path) as con:
        row = con.execute(f"SELECT COUNT(*) FROM {table}").fetchone()
    return int(row[0]) if row is not None else 0


def test_create_concept_artifact_persists_validator_runs_even_if_flag_disabled(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.setenv("ADEU_PERSIST_VALIDATOR_RUNS", "0")

    created: ConceptArtifactCreateResponse = create_concept_artifact_endpoint(
        ConceptArtifactCreateRequest(
            source_text=_fixture_source(),
            ir=_coherent_ir(),
            mode=KernelMode.LAX,
        )
    )

    assert created.check_report.status in {"PASS", "WARN"}
    assert created.analysis is not None
    assert created.analysis.forced.status in {"COMPLETE", "PARTIAL", "UNAVAILABLE"}

    rows = _fetch_validator_rows(db_path)
    assert len(rows) == 1
    assert rows[0]["artifact_id"] is None
    assert rows[0]["concept_artifact_id"] == created.artifact_id
    assert rows[0]["backend"] == "z3"


def test_create_concept_artifact_rolls_back_all_rows_when_validator_insert_fails(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))
    monkeypatch.delenv("ADEU_PERSIST_VALIDATOR_RUNS", raising=False)

    def _explode_persist(*args, **kwargs):
        raise RuntimeError("synthetic-concept-run-insert-failure")

    monkeypatch.setattr(api_main, "_persist_validator_runs", _explode_persist)

    with pytest.raises(RuntimeError, match="synthetic-concept-run-insert-failure"):
        create_concept_artifact_endpoint(
            ConceptArtifactCreateRequest(
                source_text=_fixture_source(),
                ir=_coherent_ir(),
                mode=KernelMode.LAX,
            )
        )

    assert _table_count(db_path, "concept_artifacts") == 0
    assert _table_count(db_path, "validator_runs") == 0


def test_concept_artifacts_get_and_list_order(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))

    first = create_concept_artifact_endpoint(
        ConceptArtifactCreateRequest(
            source_text=_fixture_source(),
            ir=_coherent_ir().model_copy(update={"concept_id": "concept_first"}),
            mode=KernelMode.LAX,
        )
    )
    second = create_concept_artifact_endpoint(
        ConceptArtifactCreateRequest(
            source_text=_fixture_source(),
            ir=_coherent_ir().model_copy(update={"concept_id": "concept_second"}),
            mode=KernelMode.LAX,
        )
    )

    listed: ConceptArtifactListResponse = list_concept_artifacts_endpoint(limit=50, offset=0)
    assert [item.artifact_id for item in listed.items[:2]] == [
        second.artifact_id,
        first.artifact_id,
    ]

    fetched = get_concept_artifact_endpoint(second.artifact_id)
    assert fetched.artifact_id == second.artifact_id
    assert fetched.ir.concept_id == "concept_second"
    assert fetched.analysis is not None
    assert fetched.analysis.forced.status in {"COMPLETE", "PARTIAL", "UNAVAILABLE"}


def test_list_concept_artifact_validator_runs_endpoint(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))

    created = create_concept_artifact_endpoint(
        ConceptArtifactCreateRequest(
            source_text=_fixture_source(),
            ir=_coherent_ir(),
            mode=KernelMode.LAX,
        )
    )

    runs = list_concept_artifact_validator_runs_endpoint(created.artifact_id)
    assert len(runs.items) == 1
    run = runs.items[0]
    assert run.concept_artifact_id == created.artifact_id
    assert run.artifact_id is None
    assert run.status == "SAT"


def test_payload_too_large_guard_on_concepts_endpoints() -> None:
    oversized = "x" * 200_001

    with pytest.raises(HTTPException) as propose_error:
        propose_concept(
            ConceptProposeRequest(
                source_text=oversized,
                provider="mock",
            )
        )
    assert propose_error.value.status_code == 400
    assert propose_error.value.detail["code"] == "PAYLOAD_TOO_LARGE"

    with pytest.raises(HTTPException) as artifact_error:
        create_concept_artifact_endpoint(
            ConceptArtifactCreateRequest(
                source_text=oversized,
                ir=_coherent_ir(),
                mode=KernelMode.LAX,
            )
        )
    assert artifact_error.value.status_code == 400
    assert artifact_error.value.detail["code"] == "PAYLOAD_TOO_LARGE"

    with pytest.raises(HTTPException) as check_error:
        check_concept_variant(
            ConceptCheckRequest(
                ir=_coherent_ir(),
                source_text=oversized,
                mode=KernelMode.LAX,
            )
        )
    assert check_error.value.status_code == 400
    assert check_error.value.detail["code"] == "PAYLOAD_TOO_LARGE"

    with pytest.raises(HTTPException) as analyze_error:
        analyze_concept_variant(
            ConceptAnalyzeRequest(
                ir=_coherent_ir(),
                source_text=oversized,
                mode=KernelMode.LAX,
            )
        )
    assert analyze_error.value.status_code == 400
    assert analyze_error.value.detail["code"] == "PAYLOAD_TOO_LARGE"


def test_concept_artifact_list_filters_and_pagination(
    monkeypatch,
    tmp_path: Path,
) -> None:
    db_path = tmp_path / "adeu.sqlite3"
    monkeypatch.setenv("ADEU_API_DB_PATH", str(db_path))

    base_ir = _coherent_ir()
    warn_ir = base_ir.model_copy(
        update={
            "concept_id": "concept_warn",
            "context": base_ir.context.model_copy(
                update={"doc_id": "doc:warn", "domain_tags": ["paper"]}
            ),
            "claims": [
                base_ir.claims[0].model_copy(update={"provenance": None}),
                *base_ir.claims[1:],
            ],
        }
    )
    warn = create_concept_artifact_endpoint(
        ConceptArtifactCreateRequest(
            source_text=_fixture_source(),
            ir=warn_ir,
            mode=KernelMode.LAX,
        )
    )
    passed = create_concept_artifact_endpoint(
        ConceptArtifactCreateRequest(
            source_text=_fixture_source(),
            ir=base_ir.model_copy(
                update={
                    "concept_id": "concept_pass",
                    "context": base_ir.context.model_copy(
                        update={"doc_id": "doc:pass", "domain_tags": ["paper"]}
                    ),
                }
            ),
            mode=KernelMode.STRICT,
        )
    )
    warn_row = get_concept_artifact_endpoint(warn.artifact_id)
    pass_row = get_concept_artifact_endpoint(passed.artifact_id)
    assert warn.check_report.status == "WARN"
    assert passed.check_report.status == "PASS"

    by_doc = list_concept_artifacts_endpoint(doc_id="doc:warn", limit=50, offset=0)
    assert [item.artifact_id for item in by_doc.items] == [warn.artifact_id]

    by_status = list_concept_artifacts_endpoint(
        status=passed.check_report.status, limit=50, offset=0
    )
    assert [item.artifact_id for item in by_status.items] == [passed.artifact_id]

    after_filtered = list_concept_artifacts_endpoint(
        created_after=pass_row.created_at,
        limit=50,
        offset=0,
    )
    assert [item.artifact_id for item in after_filtered.items] == [passed.artifact_id]

    before_filtered = list_concept_artifacts_endpoint(
        created_before=warn_row.created_at,
        limit=50,
        offset=0,
    )
    assert [item.artifact_id for item in before_filtered.items] == [warn.artifact_id]

    paged = list_concept_artifacts_endpoint(limit=1, offset=1)
    assert len(paged.items) == 1
    assert paged.items[0].artifact_id == warn.artifact_id


def test_validator_runs_migration_adds_concept_fk_for_existing_db(tmp_path: Path) -> None:
    db_path = tmp_path / "legacy.sqlite3"

    with sqlite3.connect(db_path) as con:
        con.execute(
            """
            CREATE TABLE artifacts (
              artifact_id TEXT PRIMARY KEY,
              created_at TEXT NOT NULL,
              clause_text TEXT NOT NULL,
              ir_json TEXT NOT NULL,
              check_report_json TEXT NOT NULL
            )
            """
        )
        con.execute(
            """
            CREATE TABLE concept_artifacts (
              artifact_id TEXT PRIMARY KEY,
              created_at TEXT NOT NULL,
              schema_version TEXT NOT NULL,
              artifact_version INTEGER NOT NULL,
              source_text TEXT NOT NULL,
              doc_id TEXT,
              status TEXT,
              num_errors INTEGER,
              num_warns INTEGER,
              ir_json TEXT NOT NULL,
              check_report_json TEXT NOT NULL,
              analysis_json TEXT
            )
            """
        )
        con.execute(
            """
            CREATE TABLE validator_runs (
              run_id TEXT PRIMARY KEY,
              artifact_id TEXT,
              created_at TEXT NOT NULL,
              backend TEXT NOT NULL,
              backend_version TEXT,
              timeout_ms INTEGER NOT NULL,
              options_json TEXT NOT NULL,
              request_hash TEXT NOT NULL,
              formula_hash TEXT NOT NULL,
              status TEXT NOT NULL,
              evidence_json TEXT NOT NULL,
              atom_map_json TEXT NOT NULL,
              FOREIGN KEY(artifact_id) REFERENCES artifacts(artifact_id)
            )
            """
        )
        con.execute(
            "INSERT INTO artifacts "
            "(artifact_id, created_at, clause_text, ir_json, check_report_json) "
            "VALUES (?, ?, ?, ?, ?)",
            ("art_legacy", "2026-02-07T00:00:00+00:00", "x", "{}", "{}"),
        )
        con.execute(
            "INSERT INTO concept_artifacts "
            "(artifact_id, created_at, schema_version, artifact_version, source_text, doc_id, "
            "status, num_errors, num_warns, ir_json, check_report_json, analysis_json) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (
                "concept_legacy",
                "2026-02-07T00:00:00+00:00",
                "adeu.concepts.v0",
                1,
                "x",
                None,
                "PASS",
                0,
                0,
                "{}",
                "{}",
                None,
            ),
        )
        con.execute(
            "INSERT INTO validator_runs "
            "(run_id, artifact_id, created_at, backend, backend_version, timeout_ms, options_json, "
            "request_hash, formula_hash, status, evidence_json, atom_map_json) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (
                "run_legacy",
                "art_legacy",
                "2026-02-07T00:00:00+00:00",
                "z3",
                "4.13.3.0",
                3000,
                "{}",
                "req",
                "frm",
                "SAT",
                "{}",
                "{}",
            ),
        )

    create_validator_run(
        artifact_id=None,
        concept_artifact_id="concept_legacy",
        backend="z3",
        backend_version="4.13.3.0",
        timeout_ms=3000,
        options_json={},
        request_hash="req2",
        formula_hash="frm2",
        status="SAT",
        evidence_json={},
        atom_map_json={},
        db_path=db_path,
    )

    with sqlite3.connect(db_path) as con:
        fk_rows = con.execute("PRAGMA foreign_key_list(validator_runs)").fetchall()
        has_concept_fk = any(
            str(row[2]) == "concept_artifacts" and str(row[3]) == "concept_artifact_id"
            for row in fk_rows
        )
        assert has_concept_fk
