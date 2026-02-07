from __future__ import annotations

import json
from pathlib import Path

from adeu_api.main import (
    ConceptCheckRequest,
    ConceptDiffRequest,
    check_concept_variant,
    diff_concepts_endpoint,
)
from adeu_concepts import ConceptIR
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode


def _fixture_payload(name: str) -> dict:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / "bank_sense_coherence" / "proposals" / name
    return json.loads(path.read_text(encoding="utf-8"))


def _coherent_ir() -> ConceptIR:
    return ConceptIR.model_validate(_fixture_payload("var1.json"))


def _incoherent_ir() -> ConceptIR:
    return ConceptIR.model_validate(_fixture_payload("var2.json"))


def _guard_fixture_payload(name: str) -> dict:
    root = repo_root(anchor=Path(__file__))
    path = (
        root
        / "examples"
        / "concepts"
        / "fixtures"
        / "claim_resolution_and_span_guard"
        / "proposals"
        / name
    )
    return json.loads(path.read_text(encoding="utf-8"))


def _guard_source_text() -> str:
    root = repo_root(anchor=Path(__file__))
    path = (
        root
        / "examples"
        / "concepts"
        / "fixtures"
        / "claim_resolution_and_span_guard"
        / "source.txt"
    )
    return path.read_text(encoding="utf-8").strip()


def test_check_concept_endpoint_strict_unsat_refuses() -> None:
    report = check_concept_variant(ConceptCheckRequest(ir=_incoherent_ir(), mode=KernelMode.STRICT))
    assert report.status == "REFUSE"
    assert any(reason.code == "CONCEPT_INCOHERENT_UNSAT" for reason in report.reason_codes)


def test_check_concept_endpoint_lax_unsat_warns() -> None:
    report = check_concept_variant(ConceptCheckRequest(ir=_incoherent_ir(), mode=KernelMode.LAX))
    assert report.status == "WARN"
    assert any(reason.code == "CONCEPT_INCOHERENT_UNSAT" for reason in report.reason_codes)


def test_check_concept_endpoint_strict_span_oob_refuses_with_source_text() -> None:
    report = check_concept_variant(
        ConceptCheckRequest(
            ir=ConceptIR.model_validate(_guard_fixture_payload("var2.json")),
            source_text=_guard_source_text(),
            mode=KernelMode.STRICT,
        )
    )
    assert report.status == "REFUSE"
    assert any(reason.code == "CONCEPT_PROVENANCE_MISSING" for reason in report.reason_codes)


def test_check_concept_endpoint_lax_span_oob_warns_with_error_severity() -> None:
    report = check_concept_variant(
        ConceptCheckRequest(
            ir=ConceptIR.model_validate(_guard_fixture_payload("var2.json")),
            source_text=_guard_source_text(),
            mode=KernelMode.LAX,
        )
    )
    assert report.status == "WARN"
    reasons = [
        reason for reason in report.reason_codes if reason.code == "CONCEPT_PROVENANCE_MISSING"
    ]
    assert reasons
    assert reasons[0].severity == "ERROR"


def test_check_concept_endpoint_lax_unresolved_endpoint_still_refuses() -> None:
    report = check_concept_variant(
        ConceptCheckRequest(
            ir=ConceptIR.model_validate(_guard_fixture_payload("var1.json")),
            source_text=_guard_source_text(),
            mode=KernelMode.LAX,
        )
    )
    assert report.status == "REFUSE"
    assert any(reason.code == "CONCEPT_ENDPOINT_UNRESOLVED" for reason in report.reason_codes)


def test_concepts_diff_endpoint_highlights_sense_flip_atom() -> None:
    left = _coherent_ir().model_copy(
        update={
            "concept_id": "concept_left",
            "claims": [
                _coherent_ir()
                .claims[0]
                .model_copy(update={"id": "claim_1", "sense_id": "s_bank_fin"})
            ],
        }
    )
    right = _coherent_ir().model_copy(
        update={
            "concept_id": "concept_right",
            "claims": [
                _coherent_ir()
                .claims[0]
                .model_copy(update={"id": "claim_1", "sense_id": "s_bank_river"})
            ],
        }
    )

    resp = diff_concepts_endpoint(
        ConceptDiffRequest(
            left_ir=left,
            right_ir=right,
            left_validator_runs=[
                {
                    "request_hash": "req-sense",
                    "formula_hash": "f-sense",
                    "status": "UNSAT",
                    "evidence_json": {"unsat_core": ["atom_claim"], "model": {}},
                    "atom_map_json": {
                        "atom_claim": {"object_id": "claim_1", "json_path": "/claims/0/sense_id"}
                    },
                }
            ],
            right_validator_runs=[
                {
                    "request_hash": "req-sense",
                    "formula_hash": "f-sense",
                    "status": "SAT",
                    "evidence_json": {"unsat_core": [], "model": {"atom_claim": "True"}},
                    "atom_map_json": {
                        "atom_claim": {"object_id": "claim_1", "json_path": "/claims/0/sense_id"}
                    },
                }
            ],
        )
    )

    assert resp.solver.status_flip == "UNSAT→SAT"
    assert resp.causal_slice.touched_atoms == ["atom_claim"]
    assert resp.causal_slice.touched_object_ids == ["claim_1"]
    assert resp.causal_slice.touched_json_paths == ["/claims/0/sense_id"]
