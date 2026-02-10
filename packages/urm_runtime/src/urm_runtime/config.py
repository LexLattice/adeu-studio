from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path

DEFAULT_MAX_LINE_BYTES = 1_000_000
DEFAULT_MAX_EVIDENCE_FILE_BYTES = 200_000_000
DEFAULT_MAX_SESSION_DURATION_SECS = 6 * 60 * 60
DEFAULT_MAX_CONCURRENT_WORKERS = 2
DEFAULT_APPROVAL_TTL_SECS = 120
DEFAULT_RETENTION_DAYS = 14
DEFAULT_MAX_TOTAL_EVIDENCE_BYTES = 2_000_000_000


def _env_int(
    name: str,
    default: int,
    *,
    minimum: int | None = None,
    maximum: int | None = None,
) -> int:
    raw = os.environ.get(name, "").strip()
    if not raw:
        value = default
    else:
        try:
            value = int(raw)
        except ValueError as exc:
            raise RuntimeError(f"{name} must be an integer") from exc
    if minimum is not None and value < minimum:
        raise RuntimeError(f"{name} must be >= {minimum}")
    if maximum is not None and value > maximum:
        raise RuntimeError(f"{name} must be <= {maximum}")
    return value


def _discover_repo_root(anchor: Path) -> Path | None:
    for parent in anchor.parents:
        if (parent / ".git").exists() and (parent / "apps" / "api").is_dir():
            return parent
    return None


def _default_var_root() -> Path:
    repo_root = _discover_repo_root(Path(__file__).resolve())
    if repo_root is not None:
        return repo_root / "apps" / "api" / "var"
    return Path.cwd() / ".adeu" / "api"


def _default_db_path() -> Path:
    env = os.environ.get("ADEU_API_DB_PATH", "").strip()
    if env:
        return Path(env).expanduser().resolve()
    return _default_var_root() / "adeu.sqlite3"


def _default_evidence_root(var_root: Path) -> Path:
    env = os.environ.get("URM_EVIDENCE_ROOT", "").strip()
    if env:
        return Path(env).expanduser().resolve()
    return var_root / "evidence" / "codex"


@dataclass(frozen=True)
class URMRuntimeConfig:
    codex_bin: str
    db_path: Path
    var_root: Path
    evidence_root: Path
    max_line_bytes: int
    max_evidence_file_bytes: int
    max_session_duration_secs: int
    max_concurrent_workers: int
    approval_ttl_secs: int
    retention_days: int
    max_total_evidence_bytes: int

    @classmethod
    def from_env(cls) -> "URMRuntimeConfig":
        db_path = _default_db_path()
        var_root = db_path.parent
        evidence_root = _default_evidence_root(var_root)

        var_root.mkdir(parents=True, exist_ok=True)
        evidence_root.mkdir(parents=True, exist_ok=True)

        return cls(
            codex_bin=os.environ.get("ADEU_CODEX_BIN", "codex").strip() or "codex",
            db_path=db_path,
            var_root=var_root,
            evidence_root=evidence_root,
            max_line_bytes=_env_int(
                "URM_MAX_LINE_BYTES",
                DEFAULT_MAX_LINE_BYTES,
                minimum=1,
            ),
            max_evidence_file_bytes=_env_int(
                "URM_MAX_EVIDENCE_FILE_BYTES",
                DEFAULT_MAX_EVIDENCE_FILE_BYTES,
                minimum=1,
            ),
            max_session_duration_secs=_env_int(
                "URM_MAX_SESSION_DURATION_SECS",
                DEFAULT_MAX_SESSION_DURATION_SECS,
                minimum=1,
            ),
            max_concurrent_workers=_env_int(
                "URM_MAX_CONCURRENT_WORKERS",
                DEFAULT_MAX_CONCURRENT_WORKERS,
                minimum=1,
            ),
            approval_ttl_secs=_env_int(
                "URM_APPROVAL_TTL_SECS",
                DEFAULT_APPROVAL_TTL_SECS,
                minimum=1,
            ),
            retention_days=_env_int(
                "URM_RETENTION_DAYS",
                DEFAULT_RETENTION_DAYS,
                minimum=1,
            ),
            max_total_evidence_bytes=_env_int(
                "URM_MAX_TOTAL_EVIDENCE_BYTES",
                DEFAULT_MAX_TOTAL_EVIDENCE_BYTES,
                minimum=1,
            ),
        )
