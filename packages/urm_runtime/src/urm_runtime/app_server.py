from __future__ import annotations

import subprocess
import threading
from collections.abc import Callable
from queue import Empty, Queue
from typing import Any

from .config import URMRuntimeConfig
from .errors import URMError
from .hashing import canonical_json

APP_SERVER_READY_SECS = 5
APP_SERVER_GRACE_SECS = 5


class CodexAppServerHost:
    def __init__(
        self,
        *,
        config: URMRuntimeConfig,
        on_line: Callable[[str], None],
    ) -> None:
        self._config = config
        self._on_line = on_line
        self._process: subprocess.Popen[str] | None = None
        self._stdin_lock = threading.Lock()
        self._ready_queue: Queue[str] = Queue(maxsize=1)
        self._reader_thread: threading.Thread | None = None
        self._closed = False

    @property
    def pid(self) -> int | None:
        return self._process.pid if self._process is not None else None

    def _reader_loop(self) -> None:
        process = self._process
        if process is None or process.stdout is None:
            return
        for line in process.stdout:
            if self._ready_queue.empty():
                self._ready_queue.put(line.rstrip("\n"))
            self._on_line(line)

    def start(self, *, cwd: str | None = None) -> None:
        if self._process is not None:
            raise RuntimeError("app server already started")
        try:
            process = subprocess.Popen(
                [self._config.codex_bin, "app-server"],
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                stdin=subprocess.PIPE,
                text=True,
                encoding="utf-8",
                errors="replace",
                cwd=cwd,
            )
        except OSError as exc:
            raise URMError(
                code="URM_CODEX_START_FAILED",
                message=f"failed to start codex app-server: {exc}",
                context={"exception": str(exc)},
            ) from exc
        self._process = process
        self._reader_thread = threading.Thread(target=self._reader_loop, daemon=True)
        self._reader_thread.start()
        self._await_readiness()

    def _await_readiness(self) -> None:
        process = self._process
        if process is None:
            raise RuntimeError("missing process")
        if process.poll() is not None:
            self.stop()
            raise URMError(
                code="URM_CODEX_APP_SERVER_UNAVAILABLE",
                message="codex app-server exited before readiness",
                context={"exit_code": process.returncode},
            )
        try:
            self._ready_queue.get(timeout=APP_SERVER_READY_SECS)
        except Empty:
            # Newer codex app-server builds can be healthy-but-silent at startup.
            # Treat a still-running process as ready even without a startup line.
            if process.poll() is None:
                return
            self.stop()
            raise URMError(
                code="URM_CODEX_APP_SERVER_UNAVAILABLE",
                message="codex app-server readiness timeout",
                context={"timeout_secs": APP_SERVER_READY_SECS},
            ) from None

    def send(self, message: dict[str, Any]) -> str:
        process = self._process
        if process is None or process.stdin is None:
            raise URMError(
                code="URM_CODEX_SESSION_TERMINATED",
                message="copilot session is not active",
            )
        line = canonical_json(message)
        with self._stdin_lock:
            process.stdin.write(line + "\n")
            process.stdin.flush()
        return line

    def stop(self) -> int | None:
        if self._closed:
            return self._process.returncode if self._process is not None else None
        self._closed = True
        process = self._process
        if process is None:
            return None
        if process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=APP_SERVER_GRACE_SECS)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=APP_SERVER_GRACE_SECS)
        return process.returncode
