from __future__ import annotations

import json
from pathlib import Path

from adeu_concepts import ConceptIR, check_with_validator_runs
from adeu_ir import ReasonSeverity
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode, build_validator_backend


def _fixture_payload(name: str) -> dict:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / "bank_sense_coherence" / "proposals" / name
    return json.loads(path.read_text(encoding="utf-8"))


def test_concept_checker_reports_sat_and_unsat_in_strict_mode() -> None:
    coherent = ConceptIR.model_validate(_fixture_payload("var1.json"))
    incoherent = ConceptIR.model_validate(_fixture_payload("var2.json"))

    coherent_report, coherent_runs = check_with_validator_runs(coherent, mode=KernelMode.STRICT)
    incoherent_report, incoherent_runs = check_with_validator_runs(
        incoherent, mode=KernelMode.STRICT
    )

    assert coherent_report.status == "PASS"
    assert coherent_runs and coherent_runs[0].result.status == "SAT"

    assert incoherent_report.status == "REFUSE"
    assert any(
        reason.code == "CONCEPT_INCOHERENT_UNSAT" for reason in incoherent_report.reason_codes
    )
    assert incoherent_runs and incoherent_runs[0].result.status == "UNSAT"


def test_concept_checker_unsat_warns_in_lax_mode() -> None:
    incoherent = ConceptIR.model_validate(_fixture_payload("var2.json"))
    report, _ = check_with_validator_runs(incoherent, mode=KernelMode.LAX)

    assert report.status == "WARN"
    assert any(reason.code == "CONCEPT_INCOHERENT_UNSAT" for reason in report.reason_codes)


def test_concept_checker_lax_invalid_request_is_warn_with_error_reason() -> None:
    coherent = ConceptIR.model_validate(_fixture_payload("var1.json"))
    mock_backend = build_validator_backend("mock")

    report, runs = check_with_validator_runs(
        coherent,
        mode=KernelMode.LAX,
        validator_backend=mock_backend,
    )

    assert runs and runs[0].result.status == "INVALID_REQUEST"
    assert report.status == "WARN"

    reasons = [
        reason for reason in report.reason_codes if reason.code == "CONCEPT_SOLVER_INVALID_REQUEST"
    ]
    assert reasons
    assert reasons[0].severity == ReasonSeverity.ERROR
