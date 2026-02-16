from __future__ import annotations

import json
import os
import sqlite3
import uuid
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from adeu_ir.repo import repo_root


@dataclass(frozen=True)
class ArtifactRow:
    artifact_id: str
    created_at: str
    clause_text: str
    doc_id: str | None
    jurisdiction: str | None
    status: str | None
    num_errors: int | None
    num_warns: int | None
    ir_json: dict[str, Any]
    check_report_json: dict[str, Any]


@dataclass(frozen=True)
class ArtifactSummaryRow:
    artifact_id: str
    created_at: str
    doc_id: str | None
    jurisdiction: str | None
    status: str | None
    num_errors: int | None
    num_warns: int | None


@dataclass(frozen=True)
class ValidatorRunRow:
    run_id: str
    artifact_id: str | None
    concept_artifact_id: str | None
    created_at: str
    backend: str
    backend_version: str | None
    timeout_ms: int
    options_json: dict[str, Any]
    request_hash: str
    formula_hash: str
    status: str
    assurance: str | None
    evidence_json: dict[str, Any]
    atom_map_json: dict[str, Any]


@dataclass(frozen=True)
class ProofArtifactRow:
    proof_id: str
    artifact_id: str
    created_at: str
    backend: str
    theorem_id: str
    status: str
    proof_hash: str
    inputs_json: list[dict[str, Any]]
    details_json: dict[str, Any]


@dataclass(frozen=True)
class ExplainArtifactRow:
    explain_id: str
    created_at: str
    client_request_id: str
    request_payload_hash: str
    explain_kind: str
    explain_hash: str
    packet_json: dict[str, Any]
    parent_stream_id: str
    parent_seq: int


@dataclass(frozen=True)
class SemanticDepthReportRow:
    semantic_depth_report_id: str
    created_at: str
    client_request_id: str
    request_payload_hash: str
    semantic_depth_hash: str
    report_json: dict[str, Any]
    parent_stream_id: str
    parent_seq: int


@dataclass(frozen=True)
class ConceptArtifactRow:
    artifact_id: str
    created_at: str
    schema_version: str
    artifact_version: int
    source_text: str
    doc_id: str | None
    status: str | None
    num_errors: int | None
    num_warns: int | None
    ir_json: dict[str, Any]
    check_report_json: dict[str, Any]
    analysis_json: dict[str, Any] | None


@dataclass(frozen=True)
class ConceptArtifactSummaryRow:
    artifact_id: str
    created_at: str
    doc_id: str | None
    status: str | None
    num_errors: int | None
    num_warns: int | None


@dataclass(frozen=True)
class DocumentRow:
    doc_id: str
    domain: str
    source_text: str
    created_at: str
    metadata_json: dict[str, Any]


@dataclass(frozen=True)
class DocumentSummaryRow:
    doc_id: str
    domain: str
    created_at: str


def _default_db_path() -> Path:
    env = os.environ.get("ADEU_API_DB_PATH")
    if env:
        return Path(env).expanduser().resolve()

    try:
        root = repo_root(anchor=Path(__file__))
        var_dir = root / "apps" / "api" / "var"
    except RuntimeError:
        var_dir = Path.cwd() / ".adeu" / "api"

    var_dir.mkdir(parents=True, exist_ok=True)
    return var_dir / "adeu.sqlite3"


def _resolve_db_path(db_path: Path | None) -> Path:
    return _default_db_path() if db_path is None else db_path


@contextmanager
def transaction(*, db_path: Path | None = None) -> Iterator[sqlite3.Connection]:
    resolved_db_path = _resolve_db_path(db_path)
    con = sqlite3.connect(resolved_db_path)
    try:
        con.execute("PRAGMA foreign_keys=ON")
        _ensure_schema(con)
        con.commit()
        con.execute("BEGIN IMMEDIATE")
        try:
            yield con
        except Exception:
            con.rollback()
            raise
        else:
            con.commit()
    finally:
        con.close()


def _ensure_columns(con: sqlite3.Connection) -> None:
    existing = {
        str(row[1])
        for row in con.execute("PRAGMA table_info(artifacts)").fetchall()
        if row and row[1]
    }
    migrations: list[tuple[str, str]] = [
        ("doc_id", "TEXT"),
        ("jurisdiction", "TEXT"),
        ("status", "TEXT"),
        ("num_errors", "INTEGER"),
        ("num_warns", "INTEGER"),
    ]
    for col, col_type in migrations:
        if col not in existing:
            con.execute(f"ALTER TABLE artifacts ADD COLUMN {col} {col_type}")


def _ensure_indexes(con: sqlite3.Connection) -> None:
    con.execute("CREATE INDEX IF NOT EXISTS idx_artifacts_created_at ON artifacts(created_at)")
    con.execute("CREATE INDEX IF NOT EXISTS idx_artifacts_doc_id ON artifacts(doc_id)")
    con.execute("CREATE INDEX IF NOT EXISTS idx_artifacts_status ON artifacts(status)")


def _ensure_validator_schema(con: sqlite3.Connection) -> None:
    con.execute(
        """
        CREATE TABLE IF NOT EXISTS validator_runs (
          run_id TEXT PRIMARY KEY,
          artifact_id TEXT,
          concept_artifact_id TEXT,
          created_at TEXT NOT NULL,
          backend TEXT NOT NULL,
          backend_version TEXT,
          timeout_ms INTEGER NOT NULL,
          options_json TEXT NOT NULL,
          request_hash TEXT NOT NULL,
          formula_hash TEXT NOT NULL,
          status TEXT NOT NULL,
          assurance TEXT,
          evidence_json TEXT NOT NULL,
          atom_map_json TEXT NOT NULL,
          FOREIGN KEY(artifact_id) REFERENCES artifacts(artifact_id),
          FOREIGN KEY(concept_artifact_id) REFERENCES concept_artifacts(artifact_id)
        )
        """
    )
    existing = {
        str(row[1])
        for row in con.execute("PRAGMA table_info(validator_runs)").fetchall()
        if row and row[1]
    }
    if "concept_artifact_id" not in existing:
        con.execute("ALTER TABLE validator_runs ADD COLUMN concept_artifact_id TEXT")
    if "assurance" not in existing:
        con.execute("ALTER TABLE validator_runs ADD COLUMN assurance TEXT")
    if not _validator_runs_has_concept_fk(con):
        _rebuild_validator_runs_with_concept_fk(con)


def _validator_runs_has_concept_fk(con: sqlite3.Connection) -> bool:
    for row in con.execute("PRAGMA foreign_key_list(validator_runs)").fetchall():
        # PRAGMA columns: id, seq, table, from, to, on_update, on_delete, match
        if str(row[2]) == "concept_artifacts" and str(row[3]) == "concept_artifact_id":
            return True
    return False


def _rebuild_validator_runs_with_concept_fk(con: sqlite3.Connection) -> None:
    existing = {
        str(row[1])
        for row in con.execute("PRAGMA table_info(validator_runs)").fetchall()
        if row and row[1]
    }
    concept_expr = (
        "CASE WHEN concept_artifact_id IS NULL OR concept_artifact_id IN "
        "(SELECT artifact_id FROM concept_artifacts) THEN concept_artifact_id ELSE NULL END"
        if "concept_artifact_id" in existing
        else "NULL"
    )
    assurance_expr = "assurance" if "assurance" in existing else "NULL"
    con.execute(
        """
        CREATE TABLE validator_runs_new (
          run_id TEXT PRIMARY KEY,
          artifact_id TEXT,
          concept_artifact_id TEXT,
          created_at TEXT NOT NULL,
          backend TEXT NOT NULL,
          backend_version TEXT,
          timeout_ms INTEGER NOT NULL,
          options_json TEXT NOT NULL,
          request_hash TEXT NOT NULL,
          formula_hash TEXT NOT NULL,
          status TEXT NOT NULL,
          assurance TEXT,
          evidence_json TEXT NOT NULL,
          atom_map_json TEXT NOT NULL,
          FOREIGN KEY(artifact_id) REFERENCES artifacts(artifact_id),
          FOREIGN KEY(concept_artifact_id) REFERENCES concept_artifacts(artifact_id)
        )
        """
    )
    con.execute(
        f"""
        INSERT INTO validator_runs_new (
          run_id,
          artifact_id,
          concept_artifact_id,
          created_at,
          backend,
          backend_version,
          timeout_ms,
          options_json,
          request_hash,
          formula_hash,
          status,
          assurance,
          evidence_json,
          atom_map_json
        )
        SELECT
          run_id,
          CASE WHEN artifact_id IS NULL OR artifact_id IN (SELECT artifact_id FROM artifacts)
            THEN artifact_id ELSE NULL END,
          {concept_expr},
          created_at,
          backend,
          backend_version,
          timeout_ms,
          options_json,
          request_hash,
          formula_hash,
          status,
          {assurance_expr},
          evidence_json,
          atom_map_json
        FROM validator_runs
        """
    )
    con.execute("DROP TABLE validator_runs")
    con.execute("ALTER TABLE validator_runs_new RENAME TO validator_runs")


def _ensure_validator_indexes(con: sqlite3.Connection) -> None:
    con.execute(
        "CREATE INDEX IF NOT EXISTS idx_validator_runs_artifact_id ON validator_runs(artifact_id)"
    )
    con.execute(
        "CREATE INDEX IF NOT EXISTS idx_validator_runs_created_at ON validator_runs(created_at)"
    )
    con.execute("CREATE INDEX IF NOT EXISTS idx_validator_runs_status ON validator_runs(status)")
    con.execute(
        "CREATE INDEX IF NOT EXISTS idx_validator_runs_concept_artifact_id "
        "ON validator_runs(concept_artifact_id)"
    )


def _ensure_proof_schema(con: sqlite3.Connection) -> None:
    con.execute(
        """
        CREATE TABLE IF NOT EXISTS proof_artifacts (
          proof_id TEXT PRIMARY KEY,
          artifact_id TEXT NOT NULL,
          created_at TEXT NOT NULL,
          backend TEXT NOT NULL,
          theorem_id TEXT NOT NULL,
          status TEXT NOT NULL,
          proof_hash TEXT NOT NULL,
          inputs_json TEXT NOT NULL,
          details_json TEXT NOT NULL,
          FOREIGN KEY(artifact_id) REFERENCES artifacts(artifact_id)
        )
        """
    )


def _ensure_proof_indexes(con: sqlite3.Connection) -> None:
    con.execute(
        "CREATE INDEX IF NOT EXISTS idx_proof_artifacts_artifact_id ON proof_artifacts(artifact_id)"
    )
    con.execute(
        "CREATE INDEX IF NOT EXISTS idx_proof_artifacts_status ON proof_artifacts(status)"
    )
    con.execute(
        "CREATE INDEX IF NOT EXISTS idx_proof_artifacts_created_at ON proof_artifacts(created_at)"
    )


def _ensure_explain_artifact_schema(con: sqlite3.Connection) -> None:
    con.execute(
        """
        CREATE TABLE IF NOT EXISTS explain_artifacts (
          explain_id TEXT PRIMARY KEY,
          created_at TEXT NOT NULL,
          client_request_id TEXT NOT NULL UNIQUE,
          request_payload_hash TEXT NOT NULL,
          explain_kind TEXT NOT NULL,
          explain_hash TEXT NOT NULL,
          packet_json TEXT NOT NULL,
          parent_stream_id TEXT NOT NULL,
          parent_seq INTEGER NOT NULL
        )
        """
    )


def _ensure_explain_artifact_indexes(con: sqlite3.Connection) -> None:
    con.execute(
        "CREATE INDEX IF NOT EXISTS idx_explain_artifacts_created_at "
        "ON explain_artifacts(created_at)"
    )
    con.execute(
        "CREATE INDEX IF NOT EXISTS idx_explain_artifacts_explain_hash "
        "ON explain_artifacts(explain_hash)"
    )
    con.execute(
        "CREATE INDEX IF NOT EXISTS idx_explain_artifacts_parent_stream "
        "ON explain_artifacts(parent_stream_id, parent_seq)"
    )


def _ensure_semantic_depth_report_schema(con: sqlite3.Connection) -> None:
    con.execute(
        """
        CREATE TABLE IF NOT EXISTS semantic_depth_reports (
          semantic_depth_report_id TEXT PRIMARY KEY,
          created_at TEXT NOT NULL,
          client_request_id TEXT NOT NULL UNIQUE,
          request_payload_hash TEXT NOT NULL,
          semantic_depth_hash TEXT NOT NULL,
          report_json TEXT NOT NULL,
          parent_stream_id TEXT NOT NULL,
          parent_seq INTEGER NOT NULL
        )
        """
    )


def _ensure_semantic_depth_report_indexes(con: sqlite3.Connection) -> None:
    con.execute(
        "CREATE INDEX IF NOT EXISTS idx_semantic_depth_reports_created_at "
        "ON semantic_depth_reports(created_at)"
    )
    con.execute(
        "CREATE INDEX IF NOT EXISTS idx_semantic_depth_reports_hash "
        "ON semantic_depth_reports(semantic_depth_hash)"
    )
    con.execute(
        "CREATE INDEX IF NOT EXISTS idx_semantic_depth_reports_parent_stream "
        "ON semantic_depth_reports(parent_stream_id, parent_seq)"
    )


def _ensure_concept_artifact_schema(con: sqlite3.Connection) -> None:
    con.execute(
        """
        CREATE TABLE IF NOT EXISTS concept_artifacts (
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


def _ensure_concept_artifact_indexes(con: sqlite3.Connection) -> None:
    con.execute(
        "CREATE INDEX IF NOT EXISTS idx_concept_artifacts_created_at "
        "ON concept_artifacts(created_at)"
    )
    con.execute(
        "CREATE INDEX IF NOT EXISTS idx_concept_artifacts_doc_id ON concept_artifacts(doc_id)"
    )
    con.execute(
        "CREATE INDEX IF NOT EXISTS idx_concept_artifacts_status ON concept_artifacts(status)"
    )


def _ensure_documents_schema(con: sqlite3.Connection) -> None:
    con.execute(
        """
        CREATE TABLE IF NOT EXISTS documents (
          doc_id TEXT PRIMARY KEY,
          domain TEXT NOT NULL,
          source_text TEXT NOT NULL,
          created_at TEXT NOT NULL,
          metadata_json TEXT NOT NULL
        )
        """
    )


def _ensure_documents_indexes(con: sqlite3.Connection) -> None:
    con.execute("CREATE INDEX IF NOT EXISTS idx_documents_created_at ON documents(created_at)")
    con.execute("CREATE INDEX IF NOT EXISTS idx_documents_domain ON documents(domain)")


def _ensure_schema(con: sqlite3.Connection) -> None:
    con.execute(
        """
        CREATE TABLE IF NOT EXISTS artifacts (
          artifact_id TEXT PRIMARY KEY,
          created_at TEXT NOT NULL,
          clause_text TEXT NOT NULL,
          doc_id TEXT,
          jurisdiction TEXT,
          status TEXT,
          num_errors INTEGER,
          num_warns INTEGER,
          ir_json TEXT NOT NULL,
          check_report_json TEXT NOT NULL
        )
        """
    )
    _ensure_columns(con)
    _ensure_indexes(con)
    _ensure_documents_schema(con)
    _ensure_documents_indexes(con)
    _ensure_concept_artifact_schema(con)
    _ensure_concept_artifact_indexes(con)
    _ensure_validator_schema(con)
    _ensure_validator_indexes(con)
    _ensure_proof_schema(con)
    _ensure_proof_indexes(con)
    _ensure_explain_artifact_schema(con)
    _ensure_explain_artifact_indexes(con)
    _ensure_semantic_depth_report_schema(con)
    _ensure_semantic_depth_report_indexes(con)


def _normalize_datetime_filter(value: str) -> str:
    try:
        normalized = value.strip()
        if normalized.endswith("Z"):
            normalized = normalized[:-1] + "+00:00"
        parsed = datetime.fromisoformat(normalized)
    except ValueError as exc:
        raise ValueError(f"invalid datetime filter: {value!r}") from exc

    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    else:
        parsed = parsed.astimezone(timezone.utc)
    return parsed.isoformat()


def create_artifact(
    *,
    clause_text: str,
    doc_id: str | None,
    jurisdiction: str | None,
    status: str | None,
    num_errors: int | None,
    num_warns: int | None,
    ir_json: dict[str, Any],
    check_report_json: dict[str, Any],
    db_path: Path | None = None,
    connection: sqlite3.Connection | None = None,
) -> ArtifactRow:
    resolved_db_path = _resolve_db_path(db_path)
    artifact_id = uuid.uuid4().hex
    created_at = datetime.now(tz=timezone.utc).isoformat()

    def _insert(con: sqlite3.Connection) -> None:
        con.execute(
            """
            INSERT INTO artifacts (
              artifact_id,
              created_at,
              clause_text,
              doc_id,
              jurisdiction,
              status,
              num_errors,
              num_warns,
              ir_json,
              check_report_json
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                artifact_id,
                created_at,
                clause_text,
                doc_id,
                jurisdiction,
                status,
                num_errors,
                num_warns,
                json.dumps(ir_json, sort_keys=True),
                json.dumps(check_report_json, sort_keys=True),
            ),
        )
    if connection is not None:
        _insert(connection)
    else:
        with sqlite3.connect(resolved_db_path) as con:
            con.execute("PRAGMA foreign_keys=ON")
            _ensure_schema(con)
            _insert(con)

    return ArtifactRow(
        artifact_id=artifact_id,
        created_at=created_at,
        clause_text=clause_text,
        doc_id=doc_id,
        jurisdiction=jurisdiction,
        status=status,
        num_errors=num_errors,
        num_warns=num_warns,
        ir_json=ir_json,
        check_report_json=check_report_json,
    )


def get_artifact(*, artifact_id: str, db_path: Path | None = None) -> ArtifactRow | None:
    if db_path is None:
        db_path = _default_db_path()

    with sqlite3.connect(db_path) as con:
        _ensure_schema(con)
        con.row_factory = sqlite3.Row
        row = con.execute(
            "SELECT artifact_id, created_at, clause_text, doc_id, jurisdiction, status, "
            "num_errors, num_warns, ir_json, check_report_json "
            "FROM artifacts WHERE artifact_id = ?",
            (artifact_id,),
        ).fetchone()
        if row is None:
            return None

    return ArtifactRow(
        artifact_id=row["artifact_id"],
        created_at=row["created_at"],
        clause_text=row["clause_text"],
        doc_id=row["doc_id"],
        jurisdiction=row["jurisdiction"],
        status=row["status"],
        num_errors=row["num_errors"],
        num_warns=row["num_warns"],
        ir_json=json.loads(row["ir_json"]),
        check_report_json=json.loads(row["check_report_json"]),
    )


def list_artifacts(
    *,
    doc_id: str | None = None,
    status: str | None = None,
    created_after: str | None = None,
    created_before: str | None = None,
    limit: int = 50,
    offset: int = 0,
    db_path: Path | None = None,
) -> list[ArtifactSummaryRow]:
    if db_path is None:
        db_path = _default_db_path()

    where: list[str] = []
    params: list[object] = []

    if doc_id is not None:
        where.append("doc_id = ?")
        params.append(doc_id)

    if status is not None:
        where.append("status = ?")
        params.append(status)

    if created_after is not None:
        where.append("created_at >= ?")
        params.append(_normalize_datetime_filter(created_after))

    if created_before is not None:
        where.append("created_at <= ?")
        params.append(_normalize_datetime_filter(created_before))

    sql = (
        "SELECT artifact_id, created_at, doc_id, jurisdiction, status, num_errors, num_warns "
        "FROM artifacts"
    )
    if where:
        sql += " WHERE " + " AND ".join(where)
    sql += " ORDER BY created_at DESC LIMIT ? OFFSET ?"
    params.extend([limit, offset])

    with sqlite3.connect(db_path) as con:
        _ensure_schema(con)
        con.row_factory = sqlite3.Row
        rows = con.execute(sql, params).fetchall()

    summaries: list[ArtifactSummaryRow] = []
    for row in rows:
        summaries.append(
            ArtifactSummaryRow(
                artifact_id=row["artifact_id"],
                created_at=row["created_at"],
                doc_id=row["doc_id"],
                jurisdiction=row["jurisdiction"],
                status=row["status"],
                num_errors=row["num_errors"],
                num_warns=row["num_warns"],
            )
        )
    return summaries


def create_validator_run(
    *,
    artifact_id: str | None,
    concept_artifact_id: str | None = None,
    backend: str,
    backend_version: str | None,
    timeout_ms: int,
    options_json: dict[str, Any],
    request_hash: str,
    formula_hash: str,
    status: str,
    assurance: str | None = None,
    evidence_json: dict[str, Any],
    atom_map_json: dict[str, Any],
    db_path: Path | None = None,
    connection: sqlite3.Connection | None = None,
) -> ValidatorRunRow:
    resolved_db_path = _resolve_db_path(db_path)
    run_id = uuid.uuid4().hex
    created_at = datetime.now(tz=timezone.utc).isoformat()

    def _insert(con: sqlite3.Connection) -> None:
        con.execute(
            """
            INSERT INTO validator_runs (
              run_id,
              artifact_id,
              concept_artifact_id,
              created_at,
              backend,
              backend_version,
              timeout_ms,
              options_json,
              request_hash,
              formula_hash,
              status,
              assurance,
              evidence_json,
              atom_map_json
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                run_id,
                artifact_id,
                concept_artifact_id,
                created_at,
                backend,
                backend_version,
                timeout_ms,
                json.dumps(options_json, sort_keys=True),
                request_hash,
                formula_hash,
                status,
                assurance,
                json.dumps(evidence_json, sort_keys=True),
                json.dumps(atom_map_json, sort_keys=True),
            ),
        )
    if connection is not None:
        _insert(connection)
    else:
        with sqlite3.connect(resolved_db_path) as con:
            con.execute("PRAGMA foreign_keys=ON")
            _ensure_schema(con)
            _insert(con)

    return ValidatorRunRow(
        run_id=run_id,
        artifact_id=artifact_id,
        concept_artifact_id=concept_artifact_id,
        created_at=created_at,
        backend=backend,
        backend_version=backend_version,
        timeout_ms=timeout_ms,
        options_json=options_json,
        request_hash=request_hash,
        formula_hash=formula_hash,
        status=status,
        assurance=assurance,
        evidence_json=evidence_json,
        atom_map_json=atom_map_json,
    )


def create_proof_artifact(
    *,
    proof_id: str | None = None,
    artifact_id: str,
    backend: str,
    theorem_id: str,
    status: str,
    proof_hash: str,
    inputs_json: list[dict[str, Any]],
    details_json: dict[str, Any],
    db_path: Path | None = None,
    connection: sqlite3.Connection | None = None,
) -> ProofArtifactRow:
    resolved_db_path = _resolve_db_path(db_path)
    proof_id = proof_id or uuid.uuid4().hex
    created_at = datetime.now(tz=timezone.utc).isoformat()

    def _insert(con: sqlite3.Connection) -> None:
        con.execute(
            """
            INSERT INTO proof_artifacts (
              proof_id,
              artifact_id,
              created_at,
              backend,
              theorem_id,
              status,
              proof_hash,
              inputs_json,
              details_json
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                proof_id,
                artifact_id,
                created_at,
                backend,
                theorem_id,
                status,
                proof_hash,
                json.dumps(inputs_json, sort_keys=True),
                json.dumps(details_json, sort_keys=True),
            ),
        )
    if connection is not None:
        _insert(connection)
    else:
        with sqlite3.connect(resolved_db_path) as con:
            con.execute("PRAGMA foreign_keys=ON")
            _ensure_schema(con)
            _insert(con)

    return ProofArtifactRow(
        proof_id=proof_id,
        artifact_id=artifact_id,
        created_at=created_at,
        backend=backend,
        theorem_id=theorem_id,
        status=status,
        proof_hash=proof_hash,
        inputs_json=inputs_json,
        details_json=details_json,
    )


def create_explain_artifact(
    *,
    client_request_id: str,
    request_payload_hash: str,
    explain_kind: str,
    explain_hash: str,
    packet_json: dict[str, Any],
    parent_stream_id: str,
    parent_seq: int,
    explain_id: str | None = None,
    db_path: Path | None = None,
    connection: sqlite3.Connection | None = None,
) -> ExplainArtifactRow:
    resolved_db_path = _resolve_db_path(db_path)
    explain_id = explain_id or uuid.uuid4().hex
    created_at = datetime.now(tz=timezone.utc).isoformat()

    def _insert(con: sqlite3.Connection) -> None:
        con.execute(
            """
            INSERT INTO explain_artifacts (
              explain_id,
              created_at,
              client_request_id,
              request_payload_hash,
              explain_kind,
              explain_hash,
              packet_json,
              parent_stream_id,
              parent_seq
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                explain_id,
                created_at,
                client_request_id,
                request_payload_hash,
                explain_kind,
                explain_hash,
                json.dumps(packet_json, sort_keys=True),
                parent_stream_id,
                int(parent_seq),
            ),
        )

    if connection is not None:
        _insert(connection)
    else:
        with sqlite3.connect(resolved_db_path) as con:
            con.execute("PRAGMA foreign_keys=ON")
            _ensure_schema(con)
            _insert(con)

    return ExplainArtifactRow(
        explain_id=explain_id,
        created_at=created_at,
        client_request_id=client_request_id,
        request_payload_hash=request_payload_hash,
        explain_kind=explain_kind,
        explain_hash=explain_hash,
        packet_json=packet_json,
        parent_stream_id=parent_stream_id,
        parent_seq=int(parent_seq),
    )


def get_explain_artifact_by_client_request_id(
    *,
    client_request_id: str,
    db_path: Path | None = None,
    connection: sqlite3.Connection | None = None,
) -> ExplainArtifactRow | None:
    if connection is not None:
        connection.row_factory = sqlite3.Row
        row = connection.execute(
            """
            SELECT explain_id, created_at, client_request_id, request_payload_hash,
                   explain_kind, explain_hash, packet_json, parent_stream_id, parent_seq
            FROM explain_artifacts
            WHERE client_request_id = ?
            """,
            (client_request_id,),
        ).fetchone()
        return _explain_artifact_from_row(row) if row is not None else None

    if db_path is None:
        db_path = _default_db_path()

    with sqlite3.connect(db_path) as con:
        _ensure_schema(con)
        con.row_factory = sqlite3.Row
        row = con.execute(
            """
            SELECT explain_id, created_at, client_request_id, request_payload_hash,
                   explain_kind, explain_hash, packet_json, parent_stream_id, parent_seq
            FROM explain_artifacts
            WHERE client_request_id = ?
            """,
            (client_request_id,),
        ).fetchone()
        if row is None:
            return None
        return _explain_artifact_from_row(row)


def get_explain_artifact(
    *,
    explain_id: str,
    db_path: Path | None = None,
) -> ExplainArtifactRow | None:
    if db_path is None:
        db_path = _default_db_path()

    with sqlite3.connect(db_path) as con:
        _ensure_schema(con)
        con.row_factory = sqlite3.Row
        row = con.execute(
            """
            SELECT explain_id, created_at, client_request_id, request_payload_hash,
                   explain_kind, explain_hash, packet_json, parent_stream_id, parent_seq
            FROM explain_artifacts
            WHERE explain_id = ?
            """,
            (explain_id,),
        ).fetchone()
        if row is None:
            return None
        return _explain_artifact_from_row(row)


def create_semantic_depth_report(
    *,
    client_request_id: str,
    request_payload_hash: str,
    semantic_depth_hash: str,
    report_json: dict[str, Any],
    parent_stream_id: str,
    parent_seq: int,
    semantic_depth_report_id: str | None = None,
    db_path: Path | None = None,
    connection: sqlite3.Connection | None = None,
) -> SemanticDepthReportRow:
    resolved_db_path = _resolve_db_path(db_path)
    semantic_depth_report_id = semantic_depth_report_id or uuid.uuid4().hex
    created_at = datetime.now(tz=timezone.utc).isoformat()

    def _insert(con: sqlite3.Connection) -> None:
        con.execute(
            """
            INSERT INTO semantic_depth_reports (
              semantic_depth_report_id,
              created_at,
              client_request_id,
              request_payload_hash,
              semantic_depth_hash,
              report_json,
              parent_stream_id,
              parent_seq
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                semantic_depth_report_id,
                created_at,
                client_request_id,
                request_payload_hash,
                semantic_depth_hash,
                json.dumps(report_json, sort_keys=True),
                parent_stream_id,
                int(parent_seq),
            ),
        )

    if connection is not None:
        _insert(connection)
    else:
        with sqlite3.connect(resolved_db_path) as con:
            con.execute("PRAGMA foreign_keys=ON")
            _ensure_schema(con)
            _insert(con)

    return SemanticDepthReportRow(
        semantic_depth_report_id=semantic_depth_report_id,
        created_at=created_at,
        client_request_id=client_request_id,
        request_payload_hash=request_payload_hash,
        semantic_depth_hash=semantic_depth_hash,
        report_json=report_json,
        parent_stream_id=parent_stream_id,
        parent_seq=int(parent_seq),
    )


def get_semantic_depth_report_by_client_request_id(
    *,
    client_request_id: str,
    db_path: Path | None = None,
    connection: sqlite3.Connection | None = None,
) -> SemanticDepthReportRow | None:
    if connection is not None:
        connection.row_factory = sqlite3.Row
        row = connection.execute(
            """
            SELECT semantic_depth_report_id, created_at, client_request_id, request_payload_hash,
                   semantic_depth_hash, report_json, parent_stream_id, parent_seq
            FROM semantic_depth_reports
            WHERE client_request_id = ?
            """,
            (client_request_id,),
        ).fetchone()
        return _semantic_depth_report_from_row(row) if row is not None else None

    if db_path is None:
        db_path = _default_db_path()

    with sqlite3.connect(db_path) as con:
        _ensure_schema(con)
        con.row_factory = sqlite3.Row
        row = con.execute(
            """
            SELECT semantic_depth_report_id, created_at, client_request_id, request_payload_hash,
                   semantic_depth_hash, report_json, parent_stream_id, parent_seq
            FROM semantic_depth_reports
            WHERE client_request_id = ?
            """,
            (client_request_id,),
        ).fetchone()
        if row is None:
            return None
        return _semantic_depth_report_from_row(row)


def get_semantic_depth_report(
    *,
    semantic_depth_report_id: str,
    db_path: Path | None = None,
    connection: sqlite3.Connection | None = None,
) -> SemanticDepthReportRow | None:
    if connection is not None:
        connection.row_factory = sqlite3.Row
        row = connection.execute(
            """
            SELECT semantic_depth_report_id, created_at, client_request_id, request_payload_hash,
                   semantic_depth_hash, report_json, parent_stream_id, parent_seq
            FROM semantic_depth_reports
            WHERE semantic_depth_report_id = ?
            """,
            (semantic_depth_report_id,),
        ).fetchone()
        return _semantic_depth_report_from_row(row) if row is not None else None

    if db_path is None:
        db_path = _default_db_path()

    with sqlite3.connect(db_path) as con:
        _ensure_schema(con)
        con.row_factory = sqlite3.Row
        row = con.execute(
            """
            SELECT semantic_depth_report_id, created_at, client_request_id, request_payload_hash,
                   semantic_depth_hash, report_json, parent_stream_id, parent_seq
            FROM semantic_depth_reports
            WHERE semantic_depth_report_id = ?
            """,
            (semantic_depth_report_id,),
        ).fetchone()
        if row is None:
            return None
        return _semantic_depth_report_from_row(row)


def list_validator_runs(
    *,
    artifact_id: str,
    db_path: Path | None = None,
) -> list[ValidatorRunRow]:
    if db_path is None:
        db_path = _default_db_path()

    with sqlite3.connect(db_path) as con:
        _ensure_schema(con)
        con.row_factory = sqlite3.Row
        rows = con.execute(
            """
            SELECT run_id, artifact_id, created_at, backend, backend_version, timeout_ms,
                   concept_artifact_id, options_json, request_hash, formula_hash, status,
                   assurance, evidence_json, atom_map_json
            FROM validator_runs
            WHERE artifact_id = ?
            ORDER BY created_at ASC
            """,
            (artifact_id,),
        ).fetchall()

    return [_validator_run_from_row(row) for row in rows]


def list_validator_runs_for_artifacts(
    *,
    artifact_ids: list[str],
    db_path: Path | None = None,
) -> dict[str, list[ValidatorRunRow]]:
    normalized_ids = sorted({item for item in artifact_ids if item})
    if not normalized_ids:
        return {}
    if db_path is None:
        db_path = _default_db_path()

    placeholders = ",".join("?" for _ in normalized_ids)
    with sqlite3.connect(db_path) as con:
        _ensure_schema(con)
        con.row_factory = sqlite3.Row
        rows = con.execute(
            f"""
            SELECT run_id, artifact_id, created_at, backend, backend_version, timeout_ms,
                   concept_artifact_id, options_json, request_hash, formula_hash, status,
                   assurance, evidence_json, atom_map_json
            FROM validator_runs
            WHERE artifact_id IN ({placeholders})
            ORDER BY artifact_id ASC, created_at ASC, run_id ASC
            """,
            tuple(normalized_ids),
        ).fetchall()

    grouped: dict[str, list[ValidatorRunRow]] = {artifact_id: [] for artifact_id in normalized_ids}
    for row in rows:
        artifact_id = str(row["artifact_id"])
        grouped.setdefault(artifact_id, []).append(_validator_run_from_row(row))
    return grouped


def list_concept_validator_runs(
    *,
    concept_artifact_id: str,
    db_path: Path | None = None,
) -> list[ValidatorRunRow]:
    if db_path is None:
        db_path = _default_db_path()

    with sqlite3.connect(db_path) as con:
        _ensure_schema(con)
        con.row_factory = sqlite3.Row
        rows = con.execute(
            """
            SELECT run_id, artifact_id, concept_artifact_id, created_at, backend, backend_version,
                   timeout_ms, options_json, request_hash, formula_hash, status, assurance,
                   evidence_json, atom_map_json
            FROM validator_runs
            WHERE concept_artifact_id = ?
            ORDER BY created_at ASC
            """,
            (concept_artifact_id,),
        ).fetchall()

    return [
        ValidatorRunRow(
            run_id=row["run_id"],
            artifact_id=row["artifact_id"],
            concept_artifact_id=row["concept_artifact_id"],
            created_at=row["created_at"],
            backend=row["backend"],
            backend_version=row["backend_version"],
            timeout_ms=row["timeout_ms"],
            options_json=json.loads(row["options_json"]),
            request_hash=row["request_hash"],
            formula_hash=row["formula_hash"],
            status=row["status"],
            assurance=row["assurance"],
            evidence_json=json.loads(row["evidence_json"]),
            atom_map_json=json.loads(row["atom_map_json"]),
        )
        for row in rows
    ]


def list_proof_artifacts(
    *,
    artifact_id: str,
    db_path: Path | None = None,
) -> list[ProofArtifactRow]:
    if db_path is None:
        db_path = _default_db_path()

    with sqlite3.connect(db_path) as con:
        _ensure_schema(con)
        con.row_factory = sqlite3.Row
        rows = con.execute(
            """
            SELECT proof_id, artifact_id, created_at, backend, theorem_id, status, proof_hash,
                   inputs_json, details_json
            FROM proof_artifacts
            WHERE artifact_id = ?
            ORDER BY created_at ASC
            """,
            (artifact_id,),
        ).fetchall()

    return [_proof_artifact_from_row(row) for row in rows]


def list_proof_artifacts_for_artifacts(
    *,
    artifact_ids: list[str],
    db_path: Path | None = None,
) -> dict[str, list[ProofArtifactRow]]:
    normalized_ids = sorted({item for item in artifact_ids if item})
    if not normalized_ids:
        return {}
    if db_path is None:
        db_path = _default_db_path()

    placeholders = ",".join("?" for _ in normalized_ids)
    with sqlite3.connect(db_path) as con:
        _ensure_schema(con)
        con.row_factory = sqlite3.Row
        rows = con.execute(
            f"""
            SELECT proof_id, artifact_id, created_at, backend, theorem_id, status, proof_hash,
                   inputs_json, details_json
            FROM proof_artifacts
            WHERE artifact_id IN ({placeholders})
            ORDER BY artifact_id ASC, created_at ASC, proof_id ASC
            """,
            tuple(normalized_ids),
        ).fetchall()

    grouped: dict[str, list[ProofArtifactRow]] = {artifact_id: [] for artifact_id in normalized_ids}
    for row in rows:
        artifact_id = str(row["artifact_id"])
        grouped.setdefault(artifact_id, []).append(_proof_artifact_from_row(row))
    return grouped


def _validator_run_from_row(row: sqlite3.Row) -> ValidatorRunRow:
    return ValidatorRunRow(
        run_id=row["run_id"],
        artifact_id=row["artifact_id"],
        concept_artifact_id=row["concept_artifact_id"],
        created_at=row["created_at"],
        backend=row["backend"],
        backend_version=row["backend_version"],
        timeout_ms=row["timeout_ms"],
        options_json=json.loads(row["options_json"]),
        request_hash=row["request_hash"],
        formula_hash=row["formula_hash"],
        status=row["status"],
        assurance=row["assurance"],
        evidence_json=json.loads(row["evidence_json"]),
        atom_map_json=json.loads(row["atom_map_json"]),
    )


def _proof_artifact_from_row(row: sqlite3.Row) -> ProofArtifactRow:
    return ProofArtifactRow(
        proof_id=row["proof_id"],
        artifact_id=row["artifact_id"],
        created_at=row["created_at"],
        backend=row["backend"],
        theorem_id=row["theorem_id"],
        status=row["status"],
        proof_hash=row["proof_hash"],
        inputs_json=json.loads(row["inputs_json"]),
        details_json=json.loads(row["details_json"]),
    )


def _explain_artifact_from_row(row: sqlite3.Row) -> ExplainArtifactRow:
    return ExplainArtifactRow(
        explain_id=row["explain_id"],
        created_at=row["created_at"],
        client_request_id=row["client_request_id"],
        request_payload_hash=row["request_payload_hash"],
        explain_kind=row["explain_kind"],
        explain_hash=row["explain_hash"],
        packet_json=json.loads(row["packet_json"]),
        parent_stream_id=row["parent_stream_id"],
        parent_seq=int(row["parent_seq"]),
    )


def _semantic_depth_report_from_row(row: sqlite3.Row) -> SemanticDepthReportRow:
    return SemanticDepthReportRow(
        semantic_depth_report_id=row["semantic_depth_report_id"],
        created_at=row["created_at"],
        client_request_id=row["client_request_id"],
        request_payload_hash=row["request_payload_hash"],
        semantic_depth_hash=row["semantic_depth_hash"],
        report_json=json.loads(row["report_json"]),
        parent_stream_id=row["parent_stream_id"],
        parent_seq=int(row["parent_seq"]),
    )


def create_concept_artifact(
    *,
    schema_version: str,
    artifact_version: int,
    source_text: str,
    doc_id: str | None,
    status: str | None,
    num_errors: int | None,
    num_warns: int | None,
    ir_json: dict[str, Any],
    check_report_json: dict[str, Any],
    analysis_json: dict[str, Any] | None,
    db_path: Path | None = None,
    connection: sqlite3.Connection | None = None,
) -> ConceptArtifactRow:
    resolved_db_path = _resolve_db_path(db_path)
    artifact_id = uuid.uuid4().hex
    created_at = datetime.now(tz=timezone.utc).isoformat()

    def _insert(con: sqlite3.Connection) -> None:
        con.execute(
            """
            INSERT INTO concept_artifacts (
              artifact_id,
              created_at,
              schema_version,
              artifact_version,
              source_text,
              doc_id,
              status,
              num_errors,
              num_warns,
              ir_json,
              check_report_json,
              analysis_json
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            (
                artifact_id,
                created_at,
                schema_version,
                artifact_version,
                source_text,
                doc_id,
                status,
                num_errors,
                num_warns,
                json.dumps(ir_json, sort_keys=True),
                json.dumps(check_report_json, sort_keys=True),
                json.dumps(analysis_json, sort_keys=True) if analysis_json is not None else None,
            ),
        )
    if connection is not None:
        _insert(connection)
    else:
        with sqlite3.connect(resolved_db_path) as con:
            con.execute("PRAGMA foreign_keys=ON")
            _ensure_schema(con)
            _insert(con)

    return ConceptArtifactRow(
        artifact_id=artifact_id,
        created_at=created_at,
        schema_version=schema_version,
        artifact_version=artifact_version,
        source_text=source_text,
        doc_id=doc_id,
        status=status,
        num_errors=num_errors,
        num_warns=num_warns,
        ir_json=ir_json,
        check_report_json=check_report_json,
        analysis_json=analysis_json,
    )


def create_document(
    *,
    doc_id: str,
    domain: str,
    source_text: str,
    metadata_json: dict[str, Any] | None = None,
    db_path: Path | None = None,
    connection: sqlite3.Connection | None = None,
) -> DocumentRow:
    resolved_db_path = _resolve_db_path(db_path)
    created_at = datetime.now(tz=timezone.utc).isoformat()
    payload = metadata_json or {}

    def _insert(con: sqlite3.Connection) -> None:
        con.execute(
            """
            INSERT INTO documents (
              doc_id,
              domain,
              source_text,
              created_at,
              metadata_json
            )
            VALUES (?, ?, ?, ?, ?)
            """,
            (
                doc_id,
                domain,
                source_text,
                created_at,
                json.dumps(payload, sort_keys=True),
            ),
        )

    try:
        if connection is not None:
            _insert(connection)
        else:
            with sqlite3.connect(resolved_db_path) as con:
                con.execute("PRAGMA foreign_keys=ON")
                _ensure_schema(con)
                _insert(con)
    except sqlite3.IntegrityError as exc:
        raise ValueError(f"document with doc_id={doc_id!r} already exists") from exc

    return DocumentRow(
        doc_id=doc_id,
        domain=domain,
        source_text=source_text,
        created_at=created_at,
        metadata_json=payload,
    )


def get_document(
    *,
    doc_id: str,
    db_path: Path | None = None,
) -> DocumentRow | None:
    if db_path is None:
        db_path = _default_db_path()

    with sqlite3.connect(db_path) as con:
        _ensure_schema(con)
        con.row_factory = sqlite3.Row
        row = con.execute(
            """
            SELECT doc_id, domain, source_text, created_at, metadata_json
            FROM documents
            WHERE doc_id = ?
            """,
            (doc_id,),
        ).fetchone()
        if row is None:
            return None

    return DocumentRow(
        doc_id=row["doc_id"],
        domain=row["domain"],
        source_text=row["source_text"],
        created_at=row["created_at"],
        metadata_json=json.loads(row["metadata_json"]),
    )


def list_documents(
    *,
    domain: str | None = None,
    created_after: str | None = None,
    created_before: str | None = None,
    limit: int = 50,
    offset: int = 0,
    db_path: Path | None = None,
) -> list[DocumentSummaryRow]:
    if db_path is None:
        db_path = _default_db_path()

    where: list[str] = []
    params: list[object] = []

    if domain is not None:
        where.append("domain = ?")
        params.append(domain)

    if created_after is not None:
        where.append("created_at >= ?")
        params.append(_normalize_datetime_filter(created_after))

    if created_before is not None:
        where.append("created_at <= ?")
        params.append(_normalize_datetime_filter(created_before))

    sql = "SELECT doc_id, domain, created_at FROM documents"
    if where:
        sql += " WHERE " + " AND ".join(where)
    sql += " ORDER BY created_at DESC, doc_id ASC LIMIT ? OFFSET ?"
    params.extend([limit, offset])

    with sqlite3.connect(db_path) as con:
        _ensure_schema(con)
        con.row_factory = sqlite3.Row
        rows = con.execute(sql, params).fetchall()

    return [
        DocumentSummaryRow(
            doc_id=row["doc_id"],
            domain=row["domain"],
            created_at=row["created_at"],
        )
        for row in rows
    ]


def get_concept_artifact(
    *,
    artifact_id: str,
    db_path: Path | None = None,
) -> ConceptArtifactRow | None:
    if db_path is None:
        db_path = _default_db_path()

    with sqlite3.connect(db_path) as con:
        _ensure_schema(con)
        con.row_factory = sqlite3.Row
        row = con.execute(
            """
            SELECT artifact_id, created_at, schema_version, artifact_version, source_text, doc_id,
                   status, num_errors, num_warns, ir_json, check_report_json, analysis_json
            FROM concept_artifacts
            WHERE artifact_id = ?
            """,
            (artifact_id,),
        ).fetchone()
        if row is None:
            return None

    return ConceptArtifactRow(
        artifact_id=row["artifact_id"],
        created_at=row["created_at"],
        schema_version=row["schema_version"],
        artifact_version=row["artifact_version"],
        source_text=row["source_text"],
        doc_id=row["doc_id"],
        status=row["status"],
        num_errors=row["num_errors"],
        num_warns=row["num_warns"],
        ir_json=json.loads(row["ir_json"]),
        check_report_json=json.loads(row["check_report_json"]),
        analysis_json=(
            json.loads(row["analysis_json"]) if row["analysis_json"] is not None else None
        ),
    )


def list_concept_artifacts(
    *,
    doc_id: str | None = None,
    status: str | None = None,
    created_after: str | None = None,
    created_before: str | None = None,
    limit: int = 50,
    offset: int = 0,
    db_path: Path | None = None,
) -> list[ConceptArtifactSummaryRow]:
    if db_path is None:
        db_path = _default_db_path()

    where: list[str] = []
    params: list[object] = []

    if doc_id is not None:
        where.append("doc_id = ?")
        params.append(doc_id)

    if status is not None:
        where.append("status = ?")
        params.append(status)

    if created_after is not None:
        where.append("created_at >= ?")
        params.append(_normalize_datetime_filter(created_after))

    if created_before is not None:
        where.append("created_at <= ?")
        params.append(_normalize_datetime_filter(created_before))

    sql = (
        "SELECT artifact_id, created_at, doc_id, status, num_errors, num_warns "
        "FROM concept_artifacts"
    )
    if where:
        sql += " WHERE " + " AND ".join(where)
    sql += " ORDER BY created_at DESC, artifact_id ASC LIMIT ? OFFSET ?"
    params.extend([limit, offset])

    with sqlite3.connect(db_path) as con:
        _ensure_schema(con)
        con.row_factory = sqlite3.Row
        rows = con.execute(sql, params).fetchall()

    return [
        ConceptArtifactSummaryRow(
            artifact_id=row["artifact_id"],
            created_at=row["created_at"],
            doc_id=row["doc_id"],
            status=row["status"],
            num_errors=row["num_errors"],
            num_warns=row["num_warns"],
        )
        for row in rows
    ]
