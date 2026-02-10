from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from pathlib import Path

from .config import URMRuntimeConfig
from .storage import (
    db_path_from_config,
    list_unpurged_evidence_records,
    mark_evidence_record_purged,
    transaction,
)


@dataclass(frozen=True)
class EvidenceRetentionStats:
    purged_count: int
    purged_bytes: int
    remaining_bytes: int


def _resolve_evidence_path(*, config: URMRuntimeConfig, relative_path: str) -> Path | None:
    path = Path(relative_path)
    if path.is_absolute():
        return None
    resolved = (config.var_root / path).resolve()
    root = config.evidence_root.resolve()
    if not resolved.is_relative_to(root):
        return None
    return resolved


def run_evidence_retention_gc(*, config: URMRuntimeConfig) -> EvidenceRetentionStats:
    db_path = db_path_from_config(config)
    now = datetime.now(tz=timezone.utc)
    expiry_cutoff = now - timedelta(days=config.retention_days)
    purged_count = 0
    purged_bytes = 0

    with transaction(db_path=db_path) as con:
        records = list_unpurged_evidence_records(con=con)
        entries: list[tuple[str, datetime, Path | None, int]] = []
        for record in records:
            created_at = datetime.fromisoformat(record.created_at)
            resolved = _resolve_evidence_path(
                config=config,
                relative_path=record.raw_jsonl_path,
            )
            size = 0
            if resolved is not None and resolved.exists():
                size = resolved.stat().st_size
            entries.append((record.evidence_id, created_at, resolved, size))

        for evidence_id, created_at, resolved, size in entries:
            if created_at >= expiry_cutoff:
                continue
            if resolved is not None and resolved.exists():
                resolved.unlink(missing_ok=True)
                purged_bytes += size
            mark_evidence_record_purged(
                con=con,
                evidence_id=evidence_id,
                purge_reason="retention_expired",
            )
            purged_count += 1

        remaining_entries = [entry for entry in entries if entry[1] >= expiry_cutoff]
        remaining_bytes = sum(entry[3] for entry in remaining_entries)

        if remaining_bytes > config.max_total_evidence_bytes:
            for evidence_id, _created_at, resolved, size in sorted(
                remaining_entries,
                key=lambda item: (item[1], item[0]),
            ):
                if remaining_bytes <= config.max_total_evidence_bytes:
                    break
                if resolved is not None and resolved.exists():
                    resolved.unlink(missing_ok=True)
                mark_evidence_record_purged(
                    con=con,
                    evidence_id=evidence_id,
                    purge_reason="size_budget_exceeded",
                )
                remaining_bytes = max(0, remaining_bytes - size)
                purged_bytes += size
                purged_count += 1

    return EvidenceRetentionStats(
        purged_count=purged_count,
        purged_bytes=purged_bytes,
        remaining_bytes=remaining_bytes,
    )
