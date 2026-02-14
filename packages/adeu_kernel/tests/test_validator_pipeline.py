from __future__ import annotations

import hashlib
from dataclasses import dataclass

import adeu_kernel.checker as checker_module
from adeu_ir import SolverEvidence, ValidatorRequest, ValidatorResult
from adeu_kernel import KernelMode, check, check_with_validator_runs


@dataclass(frozen=True)
class _FixedBackend:
    result: ValidatorResult

    def run(self, request: ValidatorRequest) -> ValidatorResult:
        return self.result


class _ModelSelectingBackend:
    def run(self, request: ValidatorRequest) -> ValidatorResult:
        return ValidatorResult(
            status="UNSAT",
            assurance="solver_backed",
            backend="mock",
            backend_version="0",
            timeout_ms=3000,
            options={},
            request_hash="r",
            formula_hash="f",
            evidence=SolverEvidence(
                unsat_core=[a.assertion_name for a in request.payload.atom_map]
            ),
            trace=[],
        )


class _UnsortedUnsatBackend:
    def run(self, request: ValidatorRequest) -> ValidatorResult:
        names = [atom.assertion_name for atom in request.payload.atom_map]
        unsorted_core = list(reversed(names))
        return ValidatorResult(
            status="UNSAT",
            assurance="solver_backed",
            backend="mock",
            backend_version="0",
            timeout_ms=3000,
            options={},
            request_hash="r",
            formula_hash="f0123456789abcdef",
            evidence=SolverEvidence(
                unsat_core=unsorted_core,
            ),
            trace=[],
        )


@dataclass
class _FailIfCalledBackend:
    called: bool = False

    def run(self, request: ValidatorRequest) -> ValidatorResult:
        _ = request
        self.called = True
        raise AssertionError("backend should not execute on assertion-name collision")


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
    assert runs[0].result.status == "SAT"
    assert runs[0].request.payload.atom_map == []


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


def test_unsat_conflicts_report_all_kernel_candidates() -> None:
    report = check(
        _multi_conflict_ir(),
        mode=KernelMode.LAX,
        validator_backend=_ModelSelectingBackend(),
    )
    conflicts = [r for r in report.reason_codes if r.code == "CONFLICT_OBLIGATION_VS_PROHIBITION"]
    assert len(conflicts) == 2
    messages = "\n".join(r.message for r in conflicts)
    assert "dn_proh_a" in messages
    assert "dn_proh_b" in messages


def test_unsat_core_and_trace_are_canonicalized_from_atom_map() -> None:
    report, runs = check_with_validator_runs(
        _multi_conflict_ir(),
        mode=KernelMode.LAX,
        validator_backend=_UnsortedUnsatBackend(),
    )
    assert report.status == "REFUSE"
    assert len(runs) == 1

    run = runs[0]
    core = run.result.evidence.unsat_core
    assert core == sorted(core)
    assert [item.assertion_name for item in run.result.trace] == core


def test_assertion_name_collision_fails_closed_before_backend_execution(monkeypatch) -> None:
    backend = _FailIfCalledBackend()
    monkeypatch.setattr(checker_module, "_json_path_hash", lambda _: "deadbeefcafe")

    report, runs = check_with_validator_runs(
        _multi_conflict_ir(),
        mode=KernelMode.LAX,
        validator_backend=backend,
    )

    assert backend.called is False
    assert report.status == "REFUSE"
    reasons = [r for r in report.reason_codes if r.code == "VALIDATOR_INVALID_REQUEST"]
    assert reasons
    assert reasons[0].message.endswith('["a:dn_ob_main:deadbeefcafe"]')
    assert runs == []
