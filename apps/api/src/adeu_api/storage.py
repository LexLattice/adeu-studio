from __future__ import annotations

import json
import os
import sqlite3
import uuid
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
) -> ArtifactRow:
    if db_path is None:
        db_path = _default_db_path()

    artifact_id = uuid.uuid4().hex
    created_at = datetime.now(tz=timezone.utc).isoformat()

    with sqlite3.connect(db_path) as con:
        _ensure_schema(con)
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
