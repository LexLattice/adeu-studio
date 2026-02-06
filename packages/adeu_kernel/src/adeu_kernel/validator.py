from __future__ import annotations

import hashlib
import json
import os
from dataclasses import dataclass
from typing import Any, Literal, Protocol

from adeu_ir import SolverEvidence, ValidatorRequest, ValidatorResult

DEFAULT_Z3_TIMEOUT_MS = 3000


ValidatorBackendKind = Literal["z3", "mock", "lean"]


class ValidatorBackend(Protocol):
    def run(self, request: ValidatorRequest) -> ValidatorResult:
        ...


def _hash_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _request_hash(request: ValidatorRequest) -> str:
    payload = request.model_dump(mode="json", exclude_none=True)
    encoded = json.dumps(payload, ensure_ascii=False, sort_keys=True)
    return _hash_text(encoded)


def _formula_hash(request: ValidatorRequest) -> str:
    return _hash_text(request.payload.formula_smt2)


def _default_timeout_ms() -> int:
    raw = os.environ.get("ADEU_Z3_TIMEOUT_MS")
    if raw is None or not raw.strip():
        return DEFAULT_Z3_TIMEOUT_MS
    try:
        timeout_ms = int(raw)
    except ValueError as exc:
        raise RuntimeError("ADEU_Z3_TIMEOUT_MS must be a positive integer") from exc
    if timeout_ms <= 0:
        raise RuntimeError("ADEU_Z3_TIMEOUT_MS must be a positive integer")
    return timeout_ms


def _normalize_symbol(value: str) -> str:
    return value.strip("|")


def _result(
    *,
    status: Literal["SAT", "UNSAT", "UNKNOWN", "TIMEOUT", "INVALID_REQUEST", "ERROR"],
    assurance: Literal["kernel_only", "solver_backed", "proof_checked"],
    backend: Literal["z3", "lean", "mock"],
    backend_version: str | None,
    timeout_ms: int,
    options: dict[str, Any],
    request_hash: str,
    formula_hash: str,
    evidence: SolverEvidence,
    trace,
) -> ValidatorResult:
    return ValidatorResult(
        status=status,
        assurance=assurance,
        backend=backend,
        backend_version=backend_version,
        timeout_ms=timeout_ms,
        options=options,
        request_hash=request_hash,
        formula_hash=formula_hash,
        evidence=evidence,
        trace=trace,
    )


@dataclass(frozen=True)
class MockValidator:
    timeout_ms: int = DEFAULT_Z3_TIMEOUT_MS

    def run(self, request: ValidatorRequest) -> ValidatorResult:
        return _result(
            status="INVALID_REQUEST",
            assurance="kernel_only",
            backend="mock",
            backend_version="0",
            timeout_ms=self.timeout_ms,
            options={},
            request_hash=_request_hash(request),
            formula_hash=_formula_hash(request),
            evidence=SolverEvidence(error="mock validator does not execute formulas"),
            trace=[],
        )


@dataclass(frozen=True)
class Z3Validator:
    timeout_ms: int = DEFAULT_Z3_TIMEOUT_MS
    options: dict[str, Any] | None = None

    def run(self, request: ValidatorRequest) -> ValidatorResult:
        request_hash = _request_hash(request)
        formula_hash = _formula_hash(request)
        options = dict(self.options or {})
        if request.logic != "QF_UF":
            return _result(
                status="INVALID_REQUEST",
                assurance="kernel_only",
                backend="z3",
                backend_version=None,
                timeout_ms=self.timeout_ms,
                options=options,
                request_hash=request_hash,
                formula_hash=formula_hash,
                evidence=SolverEvidence(error=f"Unsupported logic: {request.logic}"),
                trace=[],
            )

        try:
            import z3  # type: ignore[import-not-found]
        except Exception as exc:
            return _result(
                status="ERROR",
                assurance="kernel_only",
                backend="z3",
                backend_version=None,
                timeout_ms=self.timeout_ms,
                options=options,
                request_hash=request_hash,
                formula_hash=formula_hash,
                evidence=SolverEvidence(error=f"z3 import failed: {exc}"),
                trace=[],
            )

        atom_map_by_name = {a.assertion_name: a for a in request.payload.atom_map}

        try:
            solver = z3.Solver()
            solver.set(timeout=self.timeout_ms)
            solver.set(unsat_core=True)
            for key, value in options.items():
                solver.set(**{key: value})
            solver.from_string(request.payload.formula_smt2)
            result = solver.check()
            backend_version = str(z3.get_full_version())
        except z3.Z3Exception as exc:
            return _result(
                status="INVALID_REQUEST",
                assurance="kernel_only",
                backend="z3",
                backend_version=None,
                timeout_ms=self.timeout_ms,
                options=options,
                request_hash=request_hash,
                formula_hash=formula_hash,
                evidence=SolverEvidence(error=f"z3 parse/check failed: {exc}"),
                trace=[],
            )
        except Exception as exc:
            return _result(
                status="ERROR",
                assurance="kernel_only",
                backend="z3",
                backend_version=None,
                timeout_ms=self.timeout_ms,
                options=options,
                request_hash=request_hash,
                formula_hash=formula_hash,
                evidence=SolverEvidence(error=f"z3 unexpected error: {exc}"),
                trace=[],
            )

        if result == z3.sat:
            model = solver.model()
            model_map = {str(d.name()): str(model[d]) for d in model.decls()}
            sat_trace = [atom_map_by_name[name] for name in sorted(atom_map_by_name)]
            return _result(
                status="SAT",
                assurance="solver_backed",
                backend="z3",
                backend_version=backend_version,
                timeout_ms=self.timeout_ms,
                options=options,
                request_hash=request_hash,
                formula_hash=formula_hash,
                evidence=SolverEvidence(
                    model=model_map,
                    stats={"num_assertions": len(solver.assertions())},
                ),
                trace=sat_trace,
            )

        if result == z3.unsat:
            core = [_normalize_symbol(str(item)) for item in solver.unsat_core()]
            core_trace = [atom_map_by_name[name] for name in core if name in atom_map_by_name]
            return _result(
                status="UNSAT",
                assurance="solver_backed",
                backend="z3",
                backend_version=backend_version,
                timeout_ms=self.timeout_ms,
                options=options,
                request_hash=request_hash,
                formula_hash=formula_hash,
                evidence=SolverEvidence(
                    unsat_core=core,
                    stats={"num_assertions": len(solver.assertions())},
                ),
                trace=core_trace,
            )

        reason = str(solver.reason_unknown() or "")
        if "timeout" in reason.lower():
            return _result(
                status="TIMEOUT",
                assurance="solver_backed",
                backend="z3",
                backend_version=backend_version,
                timeout_ms=self.timeout_ms,
                options=options,
                request_hash=request_hash,
                formula_hash=formula_hash,
                evidence=SolverEvidence(
                    error=f"solver timeout/unknown: {reason}",
                    stats={"num_assertions": len(solver.assertions())},
                ),
                trace=[],
            )

        return _result(
            status="UNKNOWN",
            assurance="solver_backed",
            backend="z3",
            backend_version=backend_version,
            timeout_ms=self.timeout_ms,
            options=options,
            request_hash=request_hash,
            formula_hash=formula_hash,
            evidence=SolverEvidence(
                error=f"solver unknown: {reason}",
                stats={"num_assertions": len(solver.assertions())},
            ),
            trace=[],
        )


def build_validator_backend(kind: ValidatorBackendKind = "z3") -> ValidatorBackend:
    timeout_ms = _default_timeout_ms()
    if kind == "mock":
        return MockValidator(timeout_ms=timeout_ms)
    if kind == "z3":
        return Z3Validator(timeout_ms=timeout_ms)
    raise RuntimeError(f"Unsupported validator backend: {kind}")
