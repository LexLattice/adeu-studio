from __future__ import annotations

from pathlib import Path

from .hashing import canonical_json, sha256_text


class EvidenceFileLimitExceeded(RuntimeError):
    pass


class EvidenceFileWriter:
    def __init__(
        self,
        *,
        path: Path,
        max_line_bytes: int,
        max_file_bytes: int,
    ) -> None:
        self.path = path
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.max_line_bytes = max_line_bytes
        self.max_file_bytes = max_file_bytes
        self._bytes_written = self.path.stat().st_size if self.path.exists() else 0
        self._handle = self.path.open("ab")

    @property
    def bytes_written(self) -> int:
        return self._bytes_written

    def close(self) -> None:
        self._handle.close()

    def _write_bytes(self, data: bytes) -> None:
        next_size = self._bytes_written + len(data)
        if next_size > self.max_file_bytes:
            raise EvidenceFileLimitExceeded(
                f"evidence file cap exceeded ({next_size} > {self.max_file_bytes})"
            )
        self._handle.write(data)
        self._handle.flush()
        self._bytes_written = next_size

    def write_json_line(self, payload: dict[str, object]) -> None:
        encoded = (canonical_json(payload) + "\n").encode("utf-8")
        self._write_bytes(encoded)

    def write_raw_line(self, raw_line: str) -> None:
        encoded = raw_line.encode("utf-8", errors="replace")
        if len(encoded) <= self.max_line_bytes:
            if not raw_line.endswith("\n"):
                encoded += b"\n"
            self._write_bytes(encoded)
            return

        dropped = len(encoded) - self.max_line_bytes
        prefix = encoded[: self.max_line_bytes]
        if not prefix.endswith(b"\n"):
            prefix += b"\n"
        self._write_bytes(prefix)
        self.write_json_line(
            {
                "event_kind": "raw_line_truncated",
                "truncated": True,
                "original_bytes": len(encoded),
                "bytes_dropped": dropped,
                "sha256_full_line": sha256_text(raw_line),
            }
        )
