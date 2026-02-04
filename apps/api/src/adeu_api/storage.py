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
    ir_json: dict[str, Any]
    check_report_json: dict[str, Any]

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


def _ensure_schema(con: sqlite3.Connection) -> None:
    con.execute(
        """
        CREATE TABLE IF NOT EXISTS artifacts (
          artifact_id TEXT PRIMARY KEY,
          created_at TEXT NOT NULL,
          clause_text TEXT NOT NULL,
          ir_json TEXT NOT NULL,
          check_report_json TEXT NOT NULL
        )
        """
    )


def create_artifact(
    *,
    clause_text: str,
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
            INSERT INTO artifacts (artifact_id, created_at, clause_text, ir_json, check_report_json)
            VALUES (?, ?, ?, ?, ?)
            """,
            (
                artifact_id,
                created_at,
                clause_text,
                json.dumps(ir_json, sort_keys=True),
                json.dumps(check_report_json, sort_keys=True),
            ),
        )

    return ArtifactRow(
        artifact_id=artifact_id,
        created_at=created_at,
        clause_text=clause_text,
        ir_json=ir_json,
        check_report_json=check_report_json,
    )


def get_artifact(*, artifact_id: str, db_path: Path | None = None) -> ArtifactRow | None:
    if db_path is None:
        db_path = _default_db_path()

    with sqlite3.connect(db_path) as con:
        _ensure_schema(con)
        row = con.execute(
            "SELECT artifact_id, created_at, clause_text, ir_json, check_report_json "
            "FROM artifacts WHERE artifact_id = ?",
            (artifact_id,),
        ).fetchone()
        if row is None:
            return None

    return ArtifactRow(
        artifact_id=row[0],
        created_at=row[1],
        clause_text=row[2],
        ir_json=json.loads(row[3]),
        check_report_json=json.loads(row[4]),
    )
