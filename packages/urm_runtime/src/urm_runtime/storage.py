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
from .errors import (
    ApprovalExpiredError,
    ApprovalInvalidStateError,
    ApprovalMismatchError,
    ApprovalNotFoundError,
)

URM_SCHEMA_VERSION = 3


@dataclass(frozen=True)
class IdempotencyReservation:
    resource_id: str
    response_json: dict[str, Any] | None
    replay: bool


@dataclass(frozen=True)
class CopilotSessionRow:
    copilot_session_id: str
    role: str
    status: str
    started_at: str
    ended_at: str | None
    codex_version: str | None
    capability_probe_id: str | None
    pid: int | None
    bin_path: str | None
    raw_jsonl_path: str | None
    last_seq: int
    writes_allowed: bool
    profile_id: str
    profile_version: str
    profile_policy_hash: str | None
    error_code: str | None
    error_message: str | None


@dataclass(frozen=True)
class EvidenceRecordRow:
    evidence_id: str
    created_at: str
    source: str
    role: str
    copilot_session_id: str | None
    worker_id: str | None
    template_id: str | None
    started_at: str
    ended_at: str | None
    raw_jsonl_path: str
    status: str
    error_json: dict[str, Any] | None
    metadata_json: dict[str, Any]
    purged_at: str | None
    purge_reason: str | None


@dataclass(frozen=True)
class WorkerRunRow:
    worker_id: str
    created_at: str
    ended_at: str | None
    role: str
    provider: str
    status: str
    template_id: str | None
    template_version: str | None
    schema_version: str | None
    domain_pack_id: str | None
    domain_pack_version: str | None
    raw_jsonl_path: str | None
    exit_code: int | None
    error_code: str | None
    error_message: str | None
    result_json: dict[str, Any] | None


@dataclass(frozen=True)
class ConnectorSnapshotRow:
    snapshot_id: str
    created_at: str
    session_id: str
    provider: str
    capability_snapshot_id: str
    connector_snapshot_hash: str
    connectors: list[dict[str, Any]]
    artifact_path: str


@dataclass(frozen=True)
class ApprovalRow:
    approval_id: str
    action_kind: str
    action_hash: str
    created_at: str
    expires_at: str
    granted_by_user: bool
    revoked_at: str | None
    consumed_at: str | None
    consumed_by_evidence_id: str | None
    copilot_session_id: str | None


PURGED_PATH_PREFIX = "__purged__"


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
          profile_id TEXT NOT NULL DEFAULT 'default',
          profile_version TEXT NOT NULL DEFAULT 'profile.v1',
          profile_policy_hash TEXT,
          error_code TEXT,
          error_message TEXT,
          FOREIGN KEY(capability_probe_id) REFERENCES urm_codex_capability_probe(probe_id)
        )
        """
    )
    copilot_session_columns = {
        str(row[1])
        for row in con.execute("PRAGMA table_info(urm_copilot_session)").fetchall()
        if row and row[1]
    }
    if "profile_id" not in copilot_session_columns:
        con.execute(
            "ALTER TABLE urm_copilot_session ADD COLUMN profile_id TEXT NOT NULL DEFAULT 'default'"
        )
    if "profile_version" not in copilot_session_columns:
        con.execute(
            "ALTER TABLE urm_copilot_session ADD COLUMN profile_version "
            "TEXT NOT NULL DEFAULT 'profile.v1'"
        )
    if "profile_policy_hash" not in copilot_session_columns:
        con.execute("ALTER TABLE urm_copilot_session ADD COLUMN profile_policy_hash TEXT")
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
        CREATE TABLE IF NOT EXISTS urm_connector_snapshot (
          snapshot_id TEXT PRIMARY KEY,
          created_at TEXT NOT NULL,
          session_id TEXT NOT NULL,
          provider TEXT NOT NULL,
          capability_snapshot_id TEXT NOT NULL,
          connector_snapshot_hash TEXT NOT NULL,
          connectors_json TEXT NOT NULL,
          artifact_path TEXT NOT NULL,
          FOREIGN KEY(session_id) REFERENCES urm_copilot_session(copilot_session_id)
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
          resource_id TEXT NOT NULL,
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
        CREATE INDEX IF NOT EXISTS idx_urm_connector_snapshot_session
        ON urm_connector_snapshot(session_id, created_at)
        """
    )
    idempotency_columns = {
        str(row[1])
        for row in con.execute("PRAGMA table_info(urm_idempotency_key)").fetchall()
        if row and row[1]
    }
    if "resource_id" not in idempotency_columns and "worker_id" in idempotency_columns:
        con.execute("ALTER TABLE urm_idempotency_key ADD COLUMN resource_id TEXT")
        con.execute(
            "UPDATE urm_idempotency_key SET resource_id = worker_id WHERE resource_id IS NULL"
        )
    con.execute(
        """
        CREATE INDEX IF NOT EXISTS idx_urm_idempotency_resource_id
        ON urm_idempotency_key(resource_id)
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
                "urm runtime schema v3 connector snapshots",
            ),
        )


def reserve_request_idempotency(
    *,
    con: sqlite3.Connection,
    endpoint_name: str,
    client_request_id: str,
    payload_hash: str,
    resource_id: str,
) -> IdempotencyReservation:
    now = datetime.now(tz=timezone.utc).isoformat()
    try:
        con.execute(
            """
            INSERT INTO urm_idempotency_key (
              endpoint_name,
              client_request_id,
              payload_hash,
              resource_id,
              created_at,
              response_json
            )
            VALUES (?, ?, ?, ?, ?, NULL)
            """,
            (endpoint_name, client_request_id, payload_hash, resource_id, now),
        )
        return IdempotencyReservation(
            resource_id=resource_id,
            response_json=None,
            replay=False,
        )
    except sqlite3.IntegrityError:
        row = con.execute(
            """
            SELECT payload_hash, resource_id, response_json
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
            resource_id=stored_worker_id,
            response_json=response_json,
            replay=response_json is not None,
        )


def reserve_worker_idempotency(
    *,
    con: sqlite3.Connection,
    endpoint_name: str,
    client_request_id: str,
    payload_hash: str,
    worker_id: str,
) -> IdempotencyReservation:
    return reserve_request_idempotency(
        con=con,
        endpoint_name=endpoint_name,
        client_request_id=client_request_id,
        payload_hash=payload_hash,
        resource_id=worker_id,
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
    status: str = "running",
    result_json: dict[str, Any] | None = None,
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
          raw_jsonl_path,
          result_json
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
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
            raw_jsonl_path,
            json.dumps(result_json, sort_keys=True) if result_json is not None else None,
        ),
    )


def persist_connector_snapshot(
    *,
    con: sqlite3.Connection,
    snapshot_id: str,
    session_id: str,
    provider: str,
    capability_snapshot_id: str,
    connector_snapshot_hash: str,
    connectors: list[dict[str, Any]],
    artifact_path: str,
) -> str:
    created_at = datetime.now(tz=timezone.utc).isoformat()
    con.execute(
        """
        INSERT INTO urm_connector_snapshot (
          snapshot_id,
          created_at,
          session_id,
          provider,
          capability_snapshot_id,
          connector_snapshot_hash,
          connectors_json,
          artifact_path
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            snapshot_id,
            created_at,
            session_id,
            provider,
            capability_snapshot_id,
            connector_snapshot_hash,
            json.dumps(connectors, sort_keys=True, separators=(",", ":")),
            artifact_path,
        ),
    )
    return created_at


def update_worker_run_status(
    *,
    con: sqlite3.Connection,
    worker_id: str,
    status: str,
    error_code: str | None = None,
    error_message: str | None = None,
    result_json: dict[str, Any] | None = None,
) -> None:
    con.execute(
        """
        UPDATE urm_worker_run
        SET status = ?,
            error_code = ?,
            error_message = ?,
            result_json = ?
        WHERE worker_id = ?
        """,
        (
            status,
            error_code,
            error_message,
            json.dumps(result_json, sort_keys=True) if result_json is not None else None,
            worker_id,
        ),
    )


def persist_capability_probe(
    *,
    con: sqlite3.Connection,
    codex_version: str | None,
    exec_available: bool,
    app_server_available: bool,
    output_schema_available: bool,
    probe_json: dict[str, Any],
) -> str:
    probe_id = uuid.uuid4().hex
    created_at = datetime.now(tz=timezone.utc).isoformat()
    con.execute(
        """
        INSERT INTO urm_codex_capability_probe (
          probe_id,
          created_at,
          codex_version,
          exec_available,
          app_server_available,
          output_schema_available,
          probe_json
        )
        VALUES (?, ?, ?, ?, ?, ?, ?)
        """,
        (
            probe_id,
            created_at,
            codex_version,
            1 if exec_available else 0,
            1 if app_server_available else 0,
            1 if output_schema_available else 0,
            json.dumps(probe_json, sort_keys=True),
        ),
    )
    return probe_id


def persist_copilot_session_start(
    *,
    con: sqlite3.Connection,
    copilot_session_id: str,
    role: str,
    status: str,
    codex_version: str | None,
    capability_probe_id: str | None,
    pid: int | None,
    bin_path: str,
    raw_jsonl_path: str,
    profile_id: str,
    profile_version: str,
    profile_policy_hash: str | None,
) -> None:
    started_at = datetime.now(tz=timezone.utc).isoformat()
    con.execute(
        """
        INSERT INTO urm_copilot_session (
          copilot_session_id,
          role,
          status,
          started_at,
          codex_version,
          capability_probe_id,
          pid,
          bin_path,
          raw_jsonl_path,
          last_seq,
          writes_allowed,
          profile_id,
          profile_version,
          profile_policy_hash
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, 0, 0, ?, ?, ?)
        """,
        (
            copilot_session_id,
            role,
            status,
            started_at,
            codex_version,
            capability_probe_id,
            pid,
            bin_path,
            raw_jsonl_path,
            profile_id,
            profile_version,
            profile_policy_hash,
        ),
    )


def update_copilot_session_status(
    *,
    con: sqlite3.Connection,
    copilot_session_id: str,
    status: str,
    error_code: str | None = None,
    error_message: str | None = None,
    ended: bool = False,
) -> None:
    ended_at = datetime.now(tz=timezone.utc).isoformat() if ended else None
    if ended:
        con.execute(
            """
            UPDATE urm_copilot_session
            SET status = ?, error_code = ?, error_message = ?, ended_at = ?
            WHERE copilot_session_id = ?
            """,
            (status, error_code, error_message, ended_at, copilot_session_id),
        )
    else:
        con.execute(
            """
            UPDATE urm_copilot_session
            SET status = ?, error_code = ?, error_message = ?
            WHERE copilot_session_id = ?
            """,
            (status, error_code, error_message, copilot_session_id),
        )


def update_copilot_session_pid(
    *,
    con: sqlite3.Connection,
    copilot_session_id: str,
    pid: int | None,
) -> None:
    con.execute(
        """
        UPDATE urm_copilot_session
        SET pid = ?
        WHERE copilot_session_id = ?
        """,
        (pid, copilot_session_id),
    )


def update_copilot_session_last_seq(
    *,
    con: sqlite3.Connection,
    copilot_session_id: str,
    last_seq: int,
) -> None:
    con.execute(
        """
        UPDATE urm_copilot_session
        SET last_seq = ?
        WHERE copilot_session_id = ?
        """,
        (last_seq, copilot_session_id),
    )


def set_copilot_writes_allowed(
    *,
    con: sqlite3.Connection,
    copilot_session_id: str,
    writes_allowed: bool,
) -> None:
    con.execute(
        """
        UPDATE urm_copilot_session
        SET writes_allowed = ?
        WHERE copilot_session_id = ?
        """,
        (1 if writes_allowed else 0, copilot_session_id),
    )


def update_copilot_session_profile(
    *,
    con: sqlite3.Connection,
    copilot_session_id: str,
    profile_id: str,
    profile_version: str,
    profile_policy_hash: str | None,
) -> None:
    con.execute(
        """
        UPDATE urm_copilot_session
        SET profile_id = ?,
            profile_version = ?,
            profile_policy_hash = ?
        WHERE copilot_session_id = ?
        """,
        (
            profile_id,
            profile_version,
            profile_policy_hash,
            copilot_session_id,
        ),
    )


def get_copilot_session(
    *,
    con: sqlite3.Connection,
    copilot_session_id: str,
) -> CopilotSessionRow | None:
    row = con.execute(
        """
        SELECT
          copilot_session_id,
          role,
          status,
          started_at,
          ended_at,
          codex_version,
          capability_probe_id,
          pid,
          bin_path,
          raw_jsonl_path,
          last_seq,
          writes_allowed,
          profile_id,
          profile_version,
          profile_policy_hash,
          error_code,
          error_message
        FROM urm_copilot_session
        WHERE copilot_session_id = ?
        """,
        (copilot_session_id,),
    ).fetchone()
    if row is None:
        return None
    return CopilotSessionRow(
        copilot_session_id=str(row[0]),
        role=str(row[1]),
        status=str(row[2]),
        started_at=str(row[3]),
        ended_at=str(row[4]) if row[4] is not None else None,
        codex_version=str(row[5]) if row[5] is not None else None,
        capability_probe_id=str(row[6]) if row[6] is not None else None,
        pid=int(row[7]) if row[7] is not None else None,
        bin_path=str(row[8]) if row[8] is not None else None,
        raw_jsonl_path=str(row[9]) if row[9] is not None else None,
        last_seq=int(row[10]),
        writes_allowed=bool(row[11]),
        profile_id=str(row[12]),
        profile_version=str(row[13]),
        profile_policy_hash=str(row[14]) if row[14] is not None else None,
        error_code=str(row[15]) if row[15] is not None else None,
        error_message=str(row[16]) if row[16] is not None else None,
    )


def get_evidence_record(
    *,
    con: sqlite3.Connection,
    evidence_id: str,
) -> EvidenceRecordRow | None:
    row = con.execute(
        """
        SELECT
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
          metadata_json,
          purged_at,
          purge_reason
        FROM urm_evidence_record
        WHERE evidence_id = ?
        """,
        (evidence_id,),
    ).fetchone()
    if row is None:
        return None
    error_json_raw = str(row[11]) if row[11] is not None else None
    metadata_json_raw = str(row[12]) if row[12] is not None else "{}"
    return EvidenceRecordRow(
        evidence_id=str(row[0]),
        created_at=str(row[1]),
        source=str(row[2]),
        role=str(row[3]),
        copilot_session_id=str(row[4]) if row[4] is not None else None,
        worker_id=str(row[5]) if row[5] is not None else None,
        template_id=str(row[6]) if row[6] is not None else None,
        started_at=str(row[7]),
        ended_at=str(row[8]) if row[8] is not None else None,
        raw_jsonl_path=str(row[9]),
        status=str(row[10]),
        error_json=json.loads(error_json_raw) if error_json_raw is not None else None,
        metadata_json=json.loads(metadata_json_raw),
        purged_at=str(row[13]) if row[13] is not None else None,
        purge_reason=str(row[14]) if row[14] is not None else None,
    )


def list_unpurged_evidence_records(
    *,
    con: sqlite3.Connection,
) -> list[EvidenceRecordRow]:
    rows = con.execute(
        """
        SELECT
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
          metadata_json,
          purged_at,
          purge_reason
        FROM urm_evidence_record
        WHERE purged_at IS NULL
        ORDER BY created_at ASC, evidence_id ASC
        """
    ).fetchall()
    records: list[EvidenceRecordRow] = []
    for row in rows:
        error_json_raw = str(row[11]) if row[11] is not None else None
        metadata_json_raw = str(row[12]) if row[12] is not None else "{}"
        records.append(
            EvidenceRecordRow(
                evidence_id=str(row[0]),
                created_at=str(row[1]),
                source=str(row[2]),
                role=str(row[3]),
                copilot_session_id=str(row[4]) if row[4] is not None else None,
                worker_id=str(row[5]) if row[5] is not None else None,
                template_id=str(row[6]) if row[6] is not None else None,
                started_at=str(row[7]),
                ended_at=str(row[8]) if row[8] is not None else None,
                raw_jsonl_path=str(row[9]),
                status=str(row[10]),
                error_json=json.loads(error_json_raw) if error_json_raw is not None else None,
                metadata_json=json.loads(metadata_json_raw),
                purged_at=str(row[13]) if row[13] is not None else None,
                purge_reason=str(row[14]) if row[14] is not None else None,
            )
        )
    return records


def mark_evidence_record_purged(
    *,
    con: sqlite3.Connection,
    evidence_id: str,
    purge_reason: str,
) -> None:
    purged_at = datetime.now(tz=timezone.utc).isoformat()
    con.execute(
        """
        UPDATE urm_evidence_record
        SET purged_at = ?,
            purge_reason = ?,
            raw_jsonl_path = ?
        WHERE evidence_id = ?
        """,
        (
            purged_at,
            purge_reason,
            f"{PURGED_PATH_PREFIX}/{evidence_id}.jsonl",
            evidence_id,
        ),
    )


def get_worker_run(
    *,
    con: sqlite3.Connection,
    worker_id: str,
) -> WorkerRunRow | None:
    row = con.execute(
        """
        SELECT
          worker_id,
          created_at,
          ended_at,
          role,
          provider,
          status,
          template_id,
          template_version,
          schema_version,
          domain_pack_id,
          domain_pack_version,
          raw_jsonl_path,
          exit_code,
          error_code,
          error_message,
          result_json
        FROM urm_worker_run
        WHERE worker_id = ?
        """,
        (worker_id,),
    ).fetchone()
    if row is None:
        return None
    return WorkerRunRow(
        worker_id=str(row[0]),
        created_at=str(row[1]),
        ended_at=str(row[2]) if row[2] is not None else None,
        role=str(row[3]),
        provider=str(row[4]),
        status=str(row[5]),
        template_id=str(row[6]) if row[6] is not None else None,
        template_version=str(row[7]) if row[7] is not None else None,
        schema_version=str(row[8]) if row[8] is not None else None,
        domain_pack_id=str(row[9]) if row[9] is not None else None,
        domain_pack_version=str(row[10]) if row[10] is not None else None,
        raw_jsonl_path=str(row[11]) if row[11] is not None else None,
        exit_code=int(row[12]) if row[12] is not None else None,
        error_code=str(row[13]) if row[13] is not None else None,
        error_message=str(row[14]) if row[14] is not None else None,
        result_json=json.loads(str(row[15])) if row[15] is not None else None,
    )


def get_connector_snapshot(
    *,
    con: sqlite3.Connection,
    snapshot_id: str,
) -> ConnectorSnapshotRow | None:
    row = con.execute(
        """
        SELECT
          snapshot_id,
          created_at,
          session_id,
          provider,
          capability_snapshot_id,
          connector_snapshot_hash,
          connectors_json,
          artifact_path
        FROM urm_connector_snapshot
        WHERE snapshot_id = ?
        """,
        (snapshot_id,),
    ).fetchone()
    if row is None:
        return None
    connectors_raw = str(row[6]) if row[6] is not None else "[]"
    parsed_connectors = json.loads(connectors_raw)
    connectors: list[dict[str, Any]] = []
    if isinstance(parsed_connectors, list):
        for item in parsed_connectors:
            if isinstance(item, dict):
                connectors.append(item)
    return ConnectorSnapshotRow(
        snapshot_id=str(row[0]),
        created_at=str(row[1]),
        session_id=str(row[2]),
        provider=str(row[3]),
        capability_snapshot_id=str(row[4]),
        connector_snapshot_hash=str(row[5]),
        connectors=connectors,
        artifact_path=str(row[7]),
    )


def count_running_worker_runs(*, con: sqlite3.Connection) -> int:
    row = con.execute(
        """
        SELECT COUNT(*)
        FROM urm_worker_run
        WHERE status = 'running'
          AND role != 'copilot_child'
        """
    ).fetchone()
    return int(row[0]) if row is not None else 0


def list_active_copilot_child_runs(*, con: sqlite3.Connection) -> list[WorkerRunRow]:
    rows = con.execute(
        """
        SELECT
          worker_id,
          created_at,
          ended_at,
          role,
          provider,
          status,
          template_id,
          template_version,
          schema_version,
          domain_pack_id,
          domain_pack_version,
          raw_jsonl_path,
          exit_code,
          error_code,
          error_message,
          result_json
        FROM urm_worker_run
        WHERE role = 'copilot_child'
          AND status IN ('queued', 'running')
        ORDER BY created_at ASC, worker_id ASC
        """
    ).fetchall()
    active: list[WorkerRunRow] = []
    for row in rows:
        active.append(
            WorkerRunRow(
                worker_id=str(row[0]),
                created_at=str(row[1]),
                ended_at=str(row[2]) if row[2] is not None else None,
                role=str(row[3]),
                provider=str(row[4]),
                status=str(row[5]),
                template_id=str(row[6]) if row[6] is not None else None,
                template_version=str(row[7]) if row[7] is not None else None,
                schema_version=str(row[8]) if row[8] is not None else None,
                domain_pack_id=str(row[9]) if row[9] is not None else None,
                domain_pack_version=str(row[10]) if row[10] is not None else None,
                raw_jsonl_path=str(row[11]) if row[11] is not None else None,
                exit_code=int(row[12]) if row[12] is not None else None,
                error_code=str(row[13]) if row[13] is not None else None,
                error_message=str(row[14]) if row[14] is not None else None,
                result_json=json.loads(str(row[15])) if row[15] is not None else None,
            )
        )
    return active


def mark_running_sessions_terminated(
    *,
    con: sqlite3.Connection,
    error_code: str,
    error_message: str,
    terminal_status: str = "stopped",
) -> int:
    ended_at = datetime.now(tz=timezone.utc).isoformat()
    cursor = con.execute(
        """
        UPDATE urm_copilot_session
        SET status = ?,
            error_code = ?,
            error_message = ?,
            ended_at = ?
        WHERE status IN ('starting', 'running')
        """,
        (terminal_status, error_code, error_message, ended_at),
    )
    return int(cursor.rowcount)


def create_approval(
    *,
    con: sqlite3.Connection,
    action_kind: str,
    action_hash: str,
    expires_at: str,
    copilot_session_id: str,
    granted_by_user: bool = True,
) -> str:
    approval_id = uuid.uuid4().hex
    created_at = datetime.now(tz=timezone.utc).isoformat()
    con.execute(
        """
        INSERT INTO urm_approval (
          approval_id,
          action_kind,
          action_hash,
          created_at,
          expires_at,
          granted_by_user,
          revoked_at,
          consumed_at,
          consumed_by_evidence_id,
          copilot_session_id
        )
        VALUES (?, ?, ?, ?, ?, ?, NULL, NULL, NULL, ?)
        """,
        (
            approval_id,
            action_kind,
            action_hash,
            created_at,
            expires_at,
            1 if granted_by_user else 0,
            copilot_session_id,
        ),
    )
    return approval_id


def get_approval(
    *,
    con: sqlite3.Connection,
    approval_id: str,
) -> ApprovalRow | None:
    row = con.execute(
        """
        SELECT
          approval_id,
          action_kind,
          action_hash,
          created_at,
          expires_at,
          granted_by_user,
          revoked_at,
          consumed_at,
          consumed_by_evidence_id,
          copilot_session_id
        FROM urm_approval
        WHERE approval_id = ?
        """,
        (approval_id,),
    ).fetchone()
    if row is None:
        return None
    return ApprovalRow(
        approval_id=str(row[0]),
        action_kind=str(row[1]),
        action_hash=str(row[2]),
        created_at=str(row[3]),
        expires_at=str(row[4]),
        granted_by_user=bool(row[5]),
        revoked_at=str(row[6]) if row[6] is not None else None,
        consumed_at=str(row[7]) if row[7] is not None else None,
        consumed_by_evidence_id=str(row[8]) if row[8] is not None else None,
        copilot_session_id=str(row[9]) if row[9] is not None else None,
    )


def revoke_approval(
    *,
    con: sqlite3.Connection,
    approval_id: str,
) -> bool:
    revoked_at = datetime.now(tz=timezone.utc).isoformat()
    cursor = con.execute(
        """
        UPDATE urm_approval
        SET revoked_at = ?
        WHERE approval_id = ? AND revoked_at IS NULL
        """,
        (revoked_at, approval_id),
    )
    return int(cursor.rowcount) > 0


def consume_approval(
    *,
    con: sqlite3.Connection,
    approval_id: str,
    action_kind: str,
    action_hash: str,
    consumed_by_evidence_id: str | None = None,
) -> ApprovalRow:
    approval = get_approval(con=con, approval_id=approval_id)
    if approval is None:
        raise ApprovalNotFoundError("approval_not_found")
    if approval.action_kind != action_kind or approval.action_hash != action_hash:
        raise ApprovalMismatchError("approval_mismatch")
    if approval.revoked_at is not None or approval.consumed_at is not None:
        raise ApprovalInvalidStateError("approval_invalid")
    now = datetime.now(tz=timezone.utc)
    expires_at = datetime.fromisoformat(approval.expires_at)
    if expires_at <= now:
        raise ApprovalExpiredError("approval_expired")
    consumed_at = now.isoformat()
    cursor = con.execute(
        """
        UPDATE urm_approval
        SET consumed_at = ?,
            consumed_by_evidence_id = ?
        WHERE approval_id = ? AND consumed_at IS NULL AND revoked_at IS NULL
        """,
        (consumed_at, consumed_by_evidence_id, approval_id),
    )
    if int(cursor.rowcount) != 1:
        raise ApprovalInvalidStateError("approval_invalid")
    resolved = get_approval(con=con, approval_id=approval_id)
    if resolved is None:
        raise RuntimeError("approval missing after consumption")
    return resolved


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
