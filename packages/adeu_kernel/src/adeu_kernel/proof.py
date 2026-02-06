from __future__ import annotations

import hashlib
import os
import re
import subprocess
import tempfile
from dataclasses import dataclass
from typing import Literal, Protocol

from adeu_ir import ProofArtifact, ProofInput

DEFAULT_LEAN_TIMEOUT_MS = 5000
ProofBackendKind = Literal["mock", "lean"]


class ProofBackend(Protocol):
    def check(
        self,
        *,
        theorem_id: str,
        theorem_src: str,
        inputs: list[ProofInput],
    ) -> ProofArtifact:
        ...


def _sha256(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def sanitize_theorem_id(value: str) -> str:
    cleaned = re.sub(r"[^a-zA-Z0-9_]+", "_", value).strip("_")
    if not cleaned:
        cleaned = "adeu_theorem"
    if cleaned[0].isdigit():
        cleaned = f"t_{cleaned}"
    return cleaned


def build_trivial_theorem_source(*, theorem_id: str) -> str:
    theorem_name = sanitize_theorem_id(theorem_id)
    return f"theorem {theorem_name} : True := by\n  trivial\n"


def _default_timeout_ms() -> int:
    raw = os.environ.get("ADEU_LEAN_TIMEOUT_MS")
    if raw is None or not raw.strip():
        return DEFAULT_LEAN_TIMEOUT_MS
    try:
        timeout_ms = int(raw)
    except ValueError as exc:
        raise RuntimeError("ADEU_LEAN_TIMEOUT_MS must be a positive integer") from exc
    if timeout_ms <= 0:
        raise RuntimeError("ADEU_LEAN_TIMEOUT_MS must be a positive integer")
    return timeout_ms


@dataclass(frozen=True)
class MockProofBackend:
    def check(
        self,
        *,
        theorem_id: str,
        theorem_src: str,
        inputs: list[ProofInput],
    ) -> ProofArtifact:
        return ProofArtifact(
            proof_id=f"proof_{_sha256(theorem_id)[:16]}",
            backend="mock",
            theorem_id=theorem_id,
            status="proved",
            proof_hash=_sha256(theorem_src),
            inputs=inputs,
            details={"mode": "mock"},
        )


@dataclass(frozen=True)
class LeanCliProofBackend:
    lean_bin: str = "lean"
    timeout_ms: int = DEFAULT_LEAN_TIMEOUT_MS

    def check(
        self,
        *,
        theorem_id: str,
        theorem_src: str,
        inputs: list[ProofInput],
    ) -> ProofArtifact:
        proof_id = f"proof_{_sha256(theorem_id)[:16]}"
        try:
            with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", encoding="utf-8") as handle:
                handle.write(theorem_src)
                handle.flush()
                proc = subprocess.run(
                    [self.lean_bin, handle.name],
                    capture_output=True,
                    text=True,
                    timeout=max(1, self.timeout_ms // 1000),
                    check=False,
                )
        except FileNotFoundError:
            return ProofArtifact(
                proof_id=proof_id,
                backend="lean",
                theorem_id=theorem_id,
                status="failed",
                proof_hash=_sha256(theorem_src + "::missing_lean_binary"),
                inputs=inputs,
                details={"error": f"lean binary not found: {self.lean_bin}"},
            )
        except subprocess.TimeoutExpired:
            return ProofArtifact(
                proof_id=proof_id,
                backend="lean",
                theorem_id=theorem_id,
                status="failed",
                proof_hash=_sha256(theorem_src + "::timeout"),
                inputs=inputs,
                details={"error": "lean proof-check timeout"},
            )

        result_hash = _sha256(
            theorem_src
            + "\n--stdout--\n"
            + (proc.stdout or "")
            + "\n--stderr--\n"
            + (proc.stderr or "")
        )
        status: Literal["proved", "failed"] = "proved" if proc.returncode == 0 else "failed"
        details = {"returncode": proc.returncode}
        if proc.stdout.strip():
            details["stdout"] = proc.stdout.strip()
        if proc.stderr.strip():
            details["stderr"] = proc.stderr.strip()
        return ProofArtifact(
            proof_id=proof_id,
            backend="lean",
            theorem_id=theorem_id,
            status=status,
            proof_hash=result_hash,
            inputs=inputs,
            details=details,
        )


def build_proof_backend(kind: ProofBackendKind | None = None) -> ProofBackend:
    selected = kind or os.environ.get("ADEU_PROOF_BACKEND", "mock").strip().lower()
    if selected == "mock":
        return MockProofBackend()
    if selected == "lean":
        lean_bin = os.environ.get("ADEU_LEAN_BIN", "lean").strip() or "lean"
        return LeanCliProofBackend(lean_bin=lean_bin, timeout_ms=_default_timeout_ms())
    raise RuntimeError("ADEU_PROOF_BACKEND must be one of: mock, lean")
