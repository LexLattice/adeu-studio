from __future__ import annotations

import hashlib
import os
import re
from dataclasses import dataclass
from typing import Literal, Protocol

from adeu_ir import ProofArtifact, ProofInput
from adeu_lean import (
    DEFAULT_SEMANTICS_VERSION,
    LeanRequest,
    build_obligation_requests,
    run_lean_request,
)
from adeu_lean import (
    build_proof_mapping_id as build_lean_proof_mapping_id,
)

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


def build_adeu_core_proof_requests(
    *,
    theorem_prefix: str,
    inputs: list[ProofInput],
    semantics_version: str = DEFAULT_SEMANTICS_VERSION,
) -> list[LeanRequest]:
    return build_obligation_requests(
        theorem_prefix=theorem_prefix,
        inputs=inputs,
        semantics_version=semantics_version,
    )


def build_proof_mapping_id(
    *,
    theorem_id: str,
    obligation_kind: str,
    inputs_hash: str,
    proof_semantics_version: str,
    theorem_src_hash: str,
) -> str:
    return build_lean_proof_mapping_id(
        theorem_id=theorem_id,
        obligation_kind=obligation_kind,
        inputs_hash=inputs_hash,
        proof_semantics_version=proof_semantics_version,
        theorem_src_hash=theorem_src_hash,
    )


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


def _default_lean_bin() -> str:
    value = os.environ.get("ADEU_LEAN_BIN")
    if value is None or not value.strip():
        value = os.environ.get("LEAN_BIN")
    if value is None or not value.strip():
        return "lean"
    return value.strip()


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
        request = LeanRequest(
            theorem_id=theorem_id,
            theorem_src=theorem_src,
            semantics_version=DEFAULT_SEMANTICS_VERSION,
            inputs=inputs,
        )
        result = run_lean_request(
            request,
            timeout_ms=self.timeout_ms,
            lean_bin=self.lean_bin,
        )
        details = dict(result.details)
        details.setdefault("semantics_version", request.semantics_version)
        if result.lean_version:
            details.setdefault("lean_version", result.lean_version)
        return ProofArtifact(
            proof_id=proof_id,
            backend="lean",
            theorem_id=theorem_id,
            status=result.status,
            proof_hash=result.proof_hash,
            inputs=inputs,
            details=details,
        )


def build_proof_backend(kind: ProofBackendKind | None = None) -> ProofBackend:
    selected = kind or os.environ.get("ADEU_PROOF_BACKEND", "mock").strip().lower()
    if selected == "mock":
        return MockProofBackend()
    if selected == "lean":
        lean_bin = _default_lean_bin()
        return LeanCliProofBackend(lean_bin=lean_bin, timeout_ms=_default_timeout_ms())
    raise RuntimeError("ADEU_PROOF_BACKEND must be one of: mock, lean")
