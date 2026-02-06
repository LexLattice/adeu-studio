from __future__ import annotations

import hashlib
from dataclasses import dataclass

from adeu_ir import SolverEvidence, ValidatorRequest, ValidatorResult
from adeu_kernel import KernelMode, check, check_with_validator_runs


@dataclass(frozen=True)
class _FixedBackend:
    result: ValidatorResult

    def run(self, request: ValidatorRequest) -> ValidatorResult:
        return self.result


class _ModelSelectingBackend:
    def run(self, request: ValidatorRequest) -> ValidatorResult:
        symbol_map = request.payload.metadata.get("assertion_symbols", {})
        symbols = sorted(str(sym) for sym in symbol_map.values())
        model: dict[str, str] = {}
        for sym in symbols:
            model[sym] = "False"
        if symbols:
            model[symbols[-1]] = "True"

        return ValidatorResult(
            status="SAT",
            assurance="solver_backed",
            backend="mock",
            backend_version="0",
            timeout_ms=3000,
            options={},
            request_hash="r",
            formula_hash="f",
            evidence=SolverEvidence(model=model),
            trace=[],
        )


def _conflict_ir() -> dict:
    return {
        "schema_version": "adeu.ir.v0",
        "ir_id": "ir_validator_conflict",
        "context": {
            "doc_id": "doc:test:validator",
            "jurisdiction": "US-CA",
            "time_eval": "2026-02-06T00:00:00Z",
        },
        "D_norm": {
            "statements": [
                {
                    "id": "dn_ob_1",
                    "kind": "obligation",
                    "subject": {"ref_type": "text", "text": "Supplier"},
                    "action": {"verb": "deliver"},
                    "scope": {
                        "jurisdiction": "US-CA",
                        "time_about": {
                            "kind": "between",
                            "start": "2026-01-01T00:00:00Z",
                            "end": "2026-12-31T00:00:00Z",
                        },
                    },
                    "provenance": {"doc_ref": "doc:test:validator#sec1"},
                },
                {
                    "id": "dn_proh_1",
                    "kind": "prohibition",
                    "subject": {"ref_type": "text", "text": "Supplier"},
                    "action": {"verb": "deliver"},
                    "scope": {
                        "jurisdiction": "US-CA",
                        "time_about": {
                            "kind": "between",
                            "start": "2026-01-01T00:00:00Z",
                            "end": "2026-12-31T00:00:00Z",
                        },
                    },
                    "provenance": {"doc_ref": "doc:test:validator#sec2"},
                },
            ]
        },
    }


def _multi_conflict_ir() -> dict:
    return {
        "schema_version": "adeu.ir.v0",
        "ir_id": "ir_validator_multi_conflict",
        "context": {
            "doc_id": "doc:test:validator",
            "jurisdiction": "US-CA",
            "time_eval": "2026-02-06T00:00:00Z",
        },
        "D_norm": {
            "statements": [
                {
                    "id": "dn_ob_main",
                    "kind": "obligation",
                    "subject": {"ref_type": "text", "text": "Supplier"},
                    "action": {"verb": "deliver"},
                    "scope": {
                        "jurisdiction": "US-CA",
                        "time_about": {
                            "kind": "between",
                            "start": "2026-01-01T00:00:00Z",
                            "end": "2026-12-31T00:00:00Z",
                        },
                    },
                    "provenance": {"doc_ref": "doc:test:validator#sec1"},
                },
                {
                    "id": "dn_proh_a",
                    "kind": "prohibition",
                    "subject": {"ref_type": "text", "text": "Supplier"},
                    "action": {"verb": "deliver"},
                    "scope": {
                        "jurisdiction": "US-CA",
                        "time_about": {
                            "kind": "between",
                            "start": "2026-01-01T00:00:00Z",
                            "end": "2026-12-31T00:00:00Z",
                        },
                    },
                    "provenance": {"doc_ref": "doc:test:validator#sec2"},
                },
                {
                    "id": "dn_proh_b",
                    "kind": "prohibition",
                    "subject": {"ref_type": "text", "text": "Supplier"},
                    "action": {"verb": "deliver"},
                    "scope": {
                        "jurisdiction": "US-CA",
                        "time_about": {
                            "kind": "between",
                            "start": "2026-01-01T00:00:00Z",
                            "end": "2026-12-31T00:00:00Z",
                        },
                    },
                    "provenance": {"doc_ref": "doc:test:validator#sec3"},
                },
            ]
        },
    }


def test_check_with_validator_runs_emits_unsat_fallback_run_for_non_conflict() -> None:
    report, runs = check_with_validator_runs(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_validator_non_conflict",
            "context": {
                "doc_id": "doc:test:validator",
                "jurisdiction": "US-CA",
                "time_eval": "2026-02-06T00:00:00Z",
            },
        },
        mode=KernelMode.LAX,
    )
    assert report.status == "PASS"
    assert len(runs) == 1
    assert runs[0].result.status == "UNSAT"
    assert runs[0].request.payload.atom_map


def test_validator_unknown_maps_to_refuse_in_strict() -> None:
    backend = _FixedBackend(
        ValidatorResult(
            status="UNKNOWN",
            assurance="solver_backed",
            backend="mock",
            backend_version="0",
            timeout_ms=3000,
            options={},
            request_hash="r",
            formula_hash="f",
            evidence=SolverEvidence(error="forced unknown"),
            trace=[],
        )
    )

    report = check(_conflict_ir(), mode=KernelMode.STRICT, validator_backend=backend)
    reasons = [r for r in report.reason_codes if r.code == "VALIDATOR_UNKNOWN"]
    assert report.status == "REFUSE"
    assert reasons
    assert reasons[0].severity == "ERROR"


def test_validator_invalid_request_stays_error_in_lax() -> None:
    backend = _FixedBackend(
        ValidatorResult(
            status="INVALID_REQUEST",
            assurance="kernel_only",
            backend="mock",
            backend_version="0",
            timeout_ms=3000,
            options={},
            request_hash="r",
            formula_hash="f",
            evidence=SolverEvidence(error="forced invalid"),
            trace=[],
        )
    )

    report = check(_conflict_ir(), mode=KernelMode.LAX, validator_backend=backend)
    reasons = [r for r in report.reason_codes if r.code == "VALIDATOR_INVALID_REQUEST"]
    assert reasons
    assert reasons[0].severity == "ERROR"


def test_assertion_name_uses_object_and_json_path_hash() -> None:
    _, runs = check_with_validator_runs(_conflict_ir(), mode=KernelMode.LAX)
    assert runs

    run = runs[0]
    assert run.result.status in {"SAT", "UNSAT"}
    atom = run.request.payload.atom_map[0]
    expected_hash = hashlib.sha256(atom.json_path.encode("utf-8")).hexdigest()[:12]
    expected_name = f"a:{atom.object_id}:{expected_hash}"
    assert atom.assertion_name == expected_name


def test_sat_conflicts_use_model_true_symbols_not_trace() -> None:
    report = check(
        _multi_conflict_ir(),
        mode=KernelMode.LAX,
        validator_backend=_ModelSelectingBackend(),
    )
    conflicts = [r for r in report.reason_codes if r.code == "CONFLICT_OBLIGATION_VS_PROHIBITION"]
    assert len(conflicts) == 1
    assert "dn_proh_b" in conflicts[0].message
