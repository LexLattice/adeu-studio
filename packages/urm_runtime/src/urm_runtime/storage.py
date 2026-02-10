from __future__ import annotations

import json
import sqlite3
import uuid
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from .config import URMRuntimeConfig

URM_SCHEMA_VERSION = 1


@dataclass(frozen=True)
class IdempotencyReservation:
    worker_id: str
    response_json: dict[str, Any] | None
    replay: bool


@contextmanager
def transaction(*, db_path: Path) -> Iterator[sqlite3.Connection]:
    con = sqlite3.connect(db_path)
    try:
        con.execute("PRAGMA foreign_keys=ON")
        ensure_urm_schema(con)
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


def ensure_urm_schema(con: sqlite3.Connection) -> None:
    con.execute(
        """
        CREATE TABLE IF NOT EXISTS urm_schema_ledger (
          schema_version INTEGER PRIMARY KEY,
          applied_at TEXT NOT NULL,
          notes TEXT
        )
        """
    )
    con.execute(
        """
        CREATE TABLE IF NOT EXISTS urm_codex_capability_probe (
          probe_id TEXT PRIMARY KEY,
          created_at TEXT NOT NULL,
          codex_version TEXT,
          exec_available INTEGER NOT NULL,
          app_server_available INTEGER NOT NULL,
          output_schema_available INTEGER NOT NULL,
          probe_json TEXT NOT NULL
        )
        """
    )
    con.execute(
        """
        CREATE TABLE IF NOT EXISTS urm_copilot_session (
          copilot_session_id TEXT PRIMARY KEY,
          role TEXT NOT NULL,
          status TEXT NOT NULL,
          started_at TEXT NOT NULL,
          ended_at TEXT,
          codex_version TEXT,
          capability_probe_id TEXT,
          pid INTEGER,
          bin_path TEXT,
          raw_jsonl_path TEXT,
          last_seq INTEGER NOT NULL DEFAULT 0,
          writes_allowed INTEGER NOT NULL DEFAULT 0,
          error_code TEXT,
          error_message TEXT,
          FOREIGN KEY(capability_probe_id) REFERENCES urm_codex_capability_probe(probe_id)
        )
        """
    )
    con.execute(
        """
        CREATE TABLE IF NOT EXISTS urm_worker_run (
          worker_id TEXT PRIMARY KEY,
          created_at TEXT NOT NULL,
          ended_at TEXT,
          role TEXT NOT NULL,
          provider TEXT NOT NULL,
          status TEXT NOT NULL,
          template_id TEXT,
          template_version TEXT,
          schema_version TEXT,
          domain_pack_id TEXT,
          domain_pack_version TEXT,
          raw_jsonl_path TEXT,
          exit_code INTEGER,
          error_code TEXT,
          error_message TEXT,
          result_json TEXT
        )
        """
    )
    con.execute(
        """
        CREATE TABLE IF NOT EXISTS urm_evidence_record (
          evidence_id TEXT PRIMARY KEY,
          created_at TEXT NOT NULL,
          source TEXT NOT NULL,
          role TEXT NOT NULL,
          copilot_session_id TEXT,
          worker_id TEXT,
          template_id TEXT,
          started_at TEXT NOT NULL,
          ended_at TEXT,
          raw_jsonl_path TEXT NOT NULL,
          status TEXT NOT NULL,
          error_json TEXT,
          metadata_json TEXT NOT NULL,
          purged_at TEXT,
          purge_reason TEXT,
          FOREIGN KEY(copilot_session_id) REFERENCES urm_copilot_session(copilot_session_id),
          FOREIGN KEY(worker_id) REFERENCES urm_worker_run(worker_id)
        )
        """
    )
    con.execute(
        """
        CREATE TABLE IF NOT EXISTS urm_approval (
          approval_id TEXT PRIMARY KEY,
          action_kind TEXT NOT NULL,
          action_hash TEXT NOT NULL,
          created_at TEXT NOT NULL,
          expires_at TEXT NOT NULL,
          granted_by_user INTEGER NOT NULL,
          revoked_at TEXT,
          consumed_at TEXT,
          consumed_by_evidence_id TEXT,
          copilot_session_id TEXT,
          FOREIGN KEY(copilot_session_id) REFERENCES urm_copilot_session(copilot_session_id),
          FOREIGN KEY(consumed_by_evidence_id) REFERENCES urm_evidence_record(evidence_id)
        )
        """
    )
    con.execute(
        """
        CREATE TABLE IF NOT EXISTS urm_idempotency_key (
          endpoint_name TEXT NOT NULL,
          client_request_id TEXT NOT NULL,
          payload_hash TEXT NOT NULL,
          worker_id TEXT NOT NULL,
          created_at TEXT NOT NULL,
          response_json TEXT,
          PRIMARY KEY(endpoint_name, client_request_id)
        )
        """
    )
    con.execute(
        """
        CREATE INDEX IF NOT EXISTS idx_urm_worker_run_created_at
        ON urm_worker_run(created_at)
        """
    )
    con.execute(
        """
        CREATE INDEX IF NOT EXISTS idx_urm_evidence_worker_id
        ON urm_evidence_record(worker_id)
        """
    )
    con.execute(
        """
        CREATE INDEX IF NOT EXISTS idx_urm_idempotency_worker_id
        ON urm_idempotency_key(worker_id)
        """
    )
    if (
        con.execute(
            "SELECT 1 FROM urm_schema_ledger WHERE schema_version = ?",
            (URM_SCHEMA_VERSION,),
        ).fetchone()
        is None
    ):
        con.execute(
            """
            INSERT INTO urm_schema_ledger (schema_version, applied_at, notes)
            VALUES (?, ?, ?)
            """,
            (
                URM_SCHEMA_VERSION,
                datetime.now(tz=timezone.utc).isoformat(),
                "urm runtime v0 initial schema",
            ),
        )


def reserve_worker_idempotency(
    *,
    con: sqlite3.Connection,
    endpoint_name: str,
    client_request_id: str,
    payload_hash: str,
    worker_id: str,
) -> IdempotencyReservation:
    now = datetime.now(tz=timezone.utc).isoformat()
    try:
        con.execute(
            """
            INSERT INTO urm_idempotency_key (
              endpoint_name,
              client_request_id,
              payload_hash,
              worker_id,
              created_at,
              response_json
            )
            VALUES (?, ?, ?, ?, ?, NULL)
            """,
            (endpoint_name, client_request_id, payload_hash, worker_id, now),
        )
        return IdempotencyReservation(worker_id=worker_id, response_json=None, replay=False)
    except sqlite3.IntegrityError:
        row = con.execute(
            """
            SELECT payload_hash, worker_id, response_json
            FROM urm_idempotency_key
            WHERE endpoint_name = ? AND client_request_id = ?
            """,
            (endpoint_name, client_request_id),
        ).fetchone()
        if row is None:
            raise RuntimeError("idempotency row missing after integrity error")
        stored_hash = str(row[0])
        stored_worker_id = str(row[1])
        stored_response = str(row[2]) if row[2] is not None else None
        if stored_hash != payload_hash:
            raise ValueError("idempotency payload hash mismatch")
        response_json = json.loads(stored_response) if stored_response is not None else None
        return IdempotencyReservation(
            worker_id=stored_worker_id,
            response_json=response_json,
            replay=response_json is not None,
        )


def persist_worker_run_start(
    *,
    con: sqlite3.Connection,
    worker_id: str,
    role: str,
    provider: str,
    template_id: str | None,
    template_version: str | None,
    schema_version: str | None,
    domain_pack_id: str | None,
    domain_pack_version: str | None,
    raw_jsonl_path: str,
) -> None:
    created_at = datetime.now(tz=timezone.utc).isoformat()
    con.execute(
        """
        INSERT OR IGNORE INTO urm_worker_run (
          worker_id,
          created_at,
          role,
          provider,
          status,
          template_id,
          template_version,
          schema_version,
          domain_pack_id,
          domain_pack_version,
          raw_jsonl_path
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            worker_id,
            created_at,
            role,
            provider,
            "running",
            template_id,
            template_version,
            schema_version,
            domain_pack_id,
            domain_pack_version,
            raw_jsonl_path,
        ),
    )


def persist_worker_run_end(
    *,
    con: sqlite3.Connection,
    worker_id: str,
    status: str,
    exit_code: int | None,
    error_code: str | None,
    error_message: str | None,
    result_json: dict[str, Any],
) -> None:
    ended_at = datetime.now(tz=timezone.utc).isoformat()
    con.execute(
        """
        UPDATE urm_worker_run
        SET status = ?,
            ended_at = ?,
            exit_code = ?,
            error_code = ?,
            error_message = ?,
            result_json = ?
        WHERE worker_id = ?
        """,
        (
            status,
            ended_at,
            exit_code,
            error_code,
            error_message,
            json.dumps(result_json, sort_keys=True),
            worker_id,
        ),
    )


def persist_evidence_record(
    *,
    con: sqlite3.Connection,
    source: str,
    role: str,
    worker_id: str | None,
    copilot_session_id: str | None,
    template_id: str | None,
    started_at: str,
    ended_at: str,
    raw_jsonl_path: str,
    status: str,
    error_json: dict[str, Any] | None,
    metadata_json: dict[str, Any],
) -> str:
    evidence_id = uuid.uuid4().hex
    created_at = datetime.now(tz=timezone.utc).isoformat()
    con.execute(
        """
        INSERT INTO urm_evidence_record (
          evidence_id,
          created_at,
          source,
          role,
          copilot_session_id,
          worker_id,
          template_id,
          started_at,
          ended_at,
          raw_jsonl_path,
          status,
          error_json,
          metadata_json
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            evidence_id,
            created_at,
            source,
            role,
            copilot_session_id,
            worker_id,
            template_id,
            started_at,
            ended_at,
            raw_jsonl_path,
            status,
            json.dumps(error_json, sort_keys=True) if error_json is not None else None,
            json.dumps(metadata_json, sort_keys=True),
        ),
    )
    return evidence_id


def persist_idempotency_response(
    *,
    con: sqlite3.Connection,
    endpoint_name: str,
    client_request_id: str,
    response_json: dict[str, Any],
) -> None:
    con.execute(
        """
        UPDATE urm_idempotency_key
        SET response_json = ?
        WHERE endpoint_name = ? AND client_request_id = ?
        """,
        (
            json.dumps(response_json, sort_keys=True),
            endpoint_name,
            client_request_id,
        ),
    )


def db_path_from_config(config: URMRuntimeConfig) -> Path:
    config.db_path.parent.mkdir(parents=True, exist_ok=True)
    return config.db_path
