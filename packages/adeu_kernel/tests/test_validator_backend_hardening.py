from __future__ import annotations

import sys
import types

from adeu_ir import ValidatorAtomRef, ValidatorPayload, ValidatorRequest
from adeu_kernel.validator import Z3Validator


def _request(*, atom_map: list[ValidatorAtomRef] | None = None) -> ValidatorRequest:
    return ValidatorRequest(
        kind="smt_check",
        logic="QF_UF",
        payload=ValidatorPayload(
            formula_smt2="(set-logic QF_UF)\n(assert true)\n(check-sat)\n",
            atom_map=atom_map or [],
            metadata={},
        ),
        origin=[],
    )


class _FakeSolverUnknown:
    def __init__(self, *, reason: str) -> None:
        self._reason = reason

    def set(self, **kwargs) -> None:  # noqa: ANN003
        _ = kwargs

    def from_string(self, formula: str) -> None:
        _ = formula

    def check(self) -> str:
        return "unknown"

    def reason_unknown(self) -> str:
        return self._reason

    def assertions(self) -> list[str]:
        return ["a1"]


def test_z3_validator_maps_resourceout_unknown_to_timeout(monkeypatch) -> None:
    fake_z3 = types.SimpleNamespace(
        Solver=lambda: _FakeSolverUnknown(reason="RESOURCEOUT"),
        sat="sat",
        unsat="unsat",
        get_full_version=lambda: "fake-z3",
        Z3Exception=Exception,
    )
    monkeypatch.setitem(sys.modules, "z3", fake_z3)

    result = Z3Validator(timeout_ms=10).run(_request())
    assert result.status == "TIMEOUT"
    assert "resourceout" in (result.evidence.error or "").lower()


def test_z3_validator_duplicate_assertion_names_fail_closed() -> None:
    duplicate_name = "a:dn1:aaaaaaaaaaaa"
    request = _request(
        atom_map=[
            ValidatorAtomRef(
                assertion_name=duplicate_name,
                object_id="dn1",
                json_path="/D_norm/statements/0",
            ),
            ValidatorAtomRef(
                assertion_name=duplicate_name,
                object_id="dn2",
                json_path="/D_norm/statements/1",
            ),
        ]
    )
    result = Z3Validator(timeout_ms=10).run(request)
    assert result.status == "INVALID_REQUEST"
    assert "duplicate assertion_name" in (result.evidence.error or "")
