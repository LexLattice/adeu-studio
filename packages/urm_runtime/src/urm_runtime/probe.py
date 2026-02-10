from __future__ import annotations

import json
import subprocess
import threading
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from queue import Empty, Queue
from typing import Any

from .config import URMRuntimeConfig
from .storage import persist_capability_probe, transaction

SMOKE_TIMEOUT_SECS = 5


@dataclass(frozen=True)
class CodexCapabilityProbeResult:
    probe_id: str
    codex_version: str | None
    exec_available: bool
    app_server_available: bool
    output_schema_available: bool
    app_server_unavailable: bool
    artifact_path: Path
    details: dict[str, Any]


def _run_help(config: URMRuntimeConfig, *args: str) -> tuple[bool, str, str]:
    try:
        completed = subprocess.run(
            [config.codex_bin, *args],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=SMOKE_TIMEOUT_SECS,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return False, "", str(exc)
    output = (completed.stdout or "") + "\n" + (completed.stderr or "")
    return completed.returncode == 0, output, ""


def _app_server_smoke(config: URMRuntimeConfig) -> tuple[bool, dict[str, Any]]:
    try:
        process = subprocess.Popen(
            [config.codex_bin, "app-server"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
    except OSError as exc:
        return False, {"error": str(exc), "phase": "spawn"}

    queue: Queue[str] = Queue(maxsize=1)

    def _read_ready_line() -> None:
        if process.stdout is None:
            return
        line = process.stdout.readline()
        if line:
            queue.put(line.rstrip("\n"))

    reader = threading.Thread(target=_read_ready_line, daemon=True)
    reader.start()

    ready_line: str | None = None
    try:
        ready_line = queue.get(timeout=SMOKE_TIMEOUT_SECS)
        ok = True
    except Empty:
        ok = False
    finally:
        process.terminate()
        try:
            process.wait(timeout=SMOKE_TIMEOUT_SECS)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait(timeout=SMOKE_TIMEOUT_SECS)

    return ok, {"ready_line": ready_line, "exit_code": process.returncode}


def run_and_persist_capability_probe(
    *,
    config: URMRuntimeConfig,
) -> CodexCapabilityProbeResult:
    timestamp = datetime.now(tz=timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    probe_dir = config.var_root / "urm" / "codex_probe"
    probe_dir.mkdir(parents=True, exist_ok=True)
    artifact_path = probe_dir / f"{timestamp}.json"

    version_ok, version_output, version_error = _run_help(config, "--version")
    codex_version = (
        version_output.strip().splitlines()[0]
        if version_ok and version_output.strip()
        else None
    )

    exec_ok, exec_help, exec_error = _run_help(config, "exec", "--help")
    app_help_ok, app_help, app_help_error = _run_help(config, "app-server", "--help")
    output_schema_available = "--output-schema" in exec_help
    app_smoke_ok = False
    app_smoke_meta: dict[str, Any] = {}
    if app_help_ok:
        app_smoke_ok, app_smoke_meta = _app_server_smoke(config)

    app_server_available = app_help_ok and app_smoke_ok
    details = {
        "codex_bin": config.codex_bin,
        "timestamp": timestamp,
        "version_ok": version_ok,
        "version_output": version_output.strip(),
        "version_error": version_error,
        "exec_help_ok": exec_ok,
        "exec_help_error": exec_error,
        "exec_help_contains_json": "--json" in exec_help,
        "exec_help_contains_output_schema": output_schema_available,
        "app_server_help_ok": app_help_ok,
        "app_server_help_error": app_help_error,
        "app_server_smoke_ok": app_smoke_ok,
        "app_server_smoke": app_smoke_meta,
    }
    artifact_path.write_text(json.dumps(details, sort_keys=True, indent=2), encoding="utf-8")

    with transaction(db_path=config.db_path) as con:
        probe_id = persist_capability_probe(
            con=con,
            codex_version=codex_version,
            exec_available=exec_ok,
            app_server_available=app_server_available,
            output_schema_available=output_schema_available,
            probe_json=details,
        )
    return CodexCapabilityProbeResult(
        probe_id=probe_id,
        codex_version=codex_version,
        exec_available=exec_ok,
        app_server_available=app_server_available,
        output_schema_available=output_schema_available,
        app_server_unavailable=not app_server_available,
        artifact_path=artifact_path,
        details=details,
    )
