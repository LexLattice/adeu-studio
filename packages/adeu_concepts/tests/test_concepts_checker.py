from __future__ import annotations

import json
from pathlib import Path

from adeu_concepts import ConceptIR, build_concept_coherence_request, check_with_validator_runs
from adeu_ir import ReasonSeverity
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode, build_validator_backend


def _fixture_payload(*, fixture: str, name: str) -> dict:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / fixture / "proposals" / name
    return json.loads(path.read_text(encoding="utf-8"))


def _fixture_source(*, fixture: str) -> str:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / fixture / "source.txt"
    return path.read_text(encoding="utf-8").strip()


def test_concept_checker_reports_sat_and_unsat_in_strict_mode() -> None:
    coherent = ConceptIR.model_validate(
        _fixture_payload(fixture="bank_sense_coherence", name="var1.json")
    )
    incoherent = ConceptIR.model_validate(
        _fixture_payload(fixture="bank_sense_coherence", name="var2.json")
    )
    source_text = _fixture_source(fixture="bank_sense_coherence")

    coherent_report, coherent_runs = check_with_validator_runs(
        coherent,
        mode=KernelMode.STRICT,
        source_text=source_text,
    )
    incoherent_report, incoherent_runs = check_with_validator_runs(
        incoherent,
        mode=KernelMode.STRICT,
        source_text=source_text,
    )

    assert coherent_report.status == "PASS"
    assert coherent_runs and coherent_runs[0].result.status == "SAT"

    assert incoherent_report.status == "REFUSE"
    assert any(
        reason.code == "CONCEPT_INCOHERENT_UNSAT" for reason in incoherent_report.reason_codes
    )
    assert incoherent_runs and incoherent_runs[0].result.status == "UNSAT"


def test_concept_checker_unsat_warns_in_lax_mode() -> None:
    incoherent = ConceptIR.model_validate(
        _fixture_payload(fixture="bank_sense_coherence", name="var2.json")
    )
    report, _ = check_with_validator_runs(
        incoherent,
        mode=KernelMode.LAX,
        source_text=_fixture_source(fixture="bank_sense_coherence"),
    )

    assert report.status == "WARN"
    assert any(reason.code == "CONCEPT_INCOHERENT_UNSAT" for reason in report.reason_codes)


def test_concept_checker_lax_invalid_request_is_warn_with_error_reason() -> None:
    coherent = ConceptIR.model_validate(
        _fixture_payload(fixture="bank_sense_coherence", name="var1.json")
    )
    mock_backend = build_validator_backend("mock")

    report, runs = check_with_validator_runs(
        coherent,
        mode=KernelMode.LAX,
        source_text=_fixture_source(fixture="bank_sense_coherence"),
        validator_backend=mock_backend,
    )

    assert runs and runs[0].result.status == "INVALID_REQUEST"
    assert report.status == "WARN"

    reasons = [
        reason for reason in report.reason_codes if reason.code == "CONCEPT_SOLVER_INVALID_REQUEST"
    ]
    assert reasons
    assert reasons[0].severity == ReasonSeverity.ERROR


def test_concept_checker_lax_provenance_oob_warns_but_keeps_error_severity() -> None:
    span_oob = ConceptIR.model_validate(
        _fixture_payload(fixture="claim_resolution_and_span_guard", name="var2.json")
    )
    source_text = _fixture_source(fixture="claim_resolution_and_span_guard")

    report, runs = check_with_validator_runs(
        span_oob,
        mode=KernelMode.LAX,
        source_text=source_text,
    )

    assert runs == []
    assert report.status == "WARN"
    reasons = [
        reason for reason in report.reason_codes if reason.code == "CONCEPT_PROVENANCE_MISSING"
    ]
    assert reasons
    assert reasons[0].severity == ReasonSeverity.ERROR


def test_concept_checker_without_source_text_skips_upper_bound_guard() -> None:
    span_oob = ConceptIR.model_validate(
        _fixture_payload(fixture="claim_resolution_and_span_guard", name="var2.json")
    )
    report, runs = check_with_validator_runs(
        span_oob,
        mode=KernelMode.STRICT,
    )

    assert report.status == "PASS"
    assert runs and runs[0].result.status == "SAT"


def test_concept_checker_lax_unresolved_endpoint_still_refuses() -> None:
    unresolved = ConceptIR.model_validate(
        _fixture_payload(fixture="claim_resolution_and_span_guard", name="var1.json")
    )
    report, runs = check_with_validator_runs(
        unresolved,
        mode=KernelMode.LAX,
        source_text=_fixture_source(fixture="claim_resolution_and_span_guard"),
    )

    assert runs == []
    assert report.status == "REFUSE"
    assert any(reason.code == "CONCEPT_ENDPOINT_UNRESOLVED" for reason in report.reason_codes)


def test_concept_solver_atom_map_covers_claim_ambiguity_and_links() -> None:
    coherent = ConceptIR.model_validate(
        _fixture_payload(fixture="bank_sense_coherence", name="var1.json")
    )
    request = build_concept_coherence_request(coherent)
    paths = {atom.json_path for atom in request.payload.atom_map}

    assert "/claims/0/active" in paths
    assert "/claims/0/sense_id" in paths
    assert any(path.startswith("/ambiguity/0/") for path in paths)
    assert "/links/0" in paths
    assert "/links/1" in paths


def test_concept_solver_skips_claim_implication_for_unresolved_sense() -> None:
    unresolved = ConceptIR.model_validate(
        _fixture_payload(fixture="claim_resolution_and_span_guard", name="var1.json")
    )
    request = build_concept_coherence_request(unresolved)
    paths = {atom.json_path for atom in request.payload.atom_map}

    assert "/claims/0/active" in paths
    assert "/claims/0/sense_id" not in paths
