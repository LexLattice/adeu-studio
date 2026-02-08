from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_api import main as api_main
from adeu_api.main import (
    ConceptApplyAmbiguityOptionRequest,
    apply_concept_ambiguity_option_endpoint,
)
from adeu_concepts import ConceptIR
from adeu_ir.models import JsonPatchOp
from adeu_ir.repo import repo_root
from adeu_kernel import KernelMode
from fastapi import HTTPException


def _fixture_payload(name: str) -> dict:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / "bank_sense_coherence" / "proposals" / name
    return json.loads(path.read_text(encoding="utf-8"))


def _fixture_source_text() -> str:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / "bank_sense_coherence" / "source.txt"
    return path.read_text(encoding="utf-8").strip()


def _patchable_concept() -> ConceptIR:
    concept = ConceptIR.model_validate(_fixture_payload("var1.json"))
    payload = concept.model_dump(mode="json")
    payload["ambiguity"][0]["option_details_by_id"] = {
        "s_bank_fin": {
            "option_id": "s_bank_fin",
            "label": "Use financial sense",
            "patch": [
                JsonPatchOp(op="remove", path="/links/1").model_dump(
                    mode="json", by_alias=True, exclude_none=True
                ),
                JsonPatchOp(op="remove", path="/senses/1").model_dump(
                    mode="json", by_alias=True, exclude_none=True
                ),
                JsonPatchOp(op="remove", path="/ambiguity/0").model_dump(
                    mode="json", by_alias=True, exclude_none=True
                ),
            ],
        },
        "s_bank_river": {
            "option_id": "s_bank_river",
            "label": "Use river sense",
            "patch": [
                JsonPatchOp(op="remove", path="/links/1").model_dump(
                    mode="json", by_alias=True, exclude_none=True
                ),
                JsonPatchOp(op="remove", path="/links/0").model_dump(
                    mode="json", by_alias=True, exclude_none=True
                ),
                JsonPatchOp(op="remove", path="/senses/0").model_dump(
                    mode="json", by_alias=True, exclude_none=True
                ),
                JsonPatchOp(op="remove", path="/ambiguity/0").model_dump(
                    mode="json", by_alias=True, exclude_none=True
                ),
            ],
        },
    }
    payload["ambiguity"][0]["option_labels_by_id"] = {
        "s_bank_fin": "Financial bank",
        "s_bank_river": "River bank",
    }
    return ConceptIR.model_validate(payload)


def test_concepts_apply_ambiguity_option_returns_patched_ir_and_validator_runs() -> None:
    concept = _patchable_concept()

    resp = apply_concept_ambiguity_option_endpoint(
        ConceptApplyAmbiguityOptionRequest(
            ir=concept,
            ambiguity_id="amb_bank",
            option_id="s_bank_fin",
            source_text=_fixture_source_text(),
            mode=KernelMode.LAX,
            include_validator_runs=True,
        )
    )

    assert resp.check_report.status == "PASS"
    assert resp.patched_ir.ambiguity == []
    assert [sense.id for sense in resp.patched_ir.senses] == ["s_bank_fin", "s_credit"]
    assert resp.validator_runs is not None
    assert resp.validator_runs[0].status == "SAT"
    assert resp.solver_trust == "solver_backed"
    assert resp.mapping_trust is None
    assert resp.proof_trust is None


def test_concepts_apply_ambiguity_option_dry_run_skips_run_persistence(monkeypatch) -> None:
    concept = _patchable_concept()

    monkeypatch.setenv("ADEU_PERSIST_VALIDATOR_RUNS", "1")

    def _unexpected_persist(
        *,
        runs,
        artifact_id,
        concept_artifact_id=None,
        connection=None,
    ) -> None:
        del runs, artifact_id, concept_artifact_id, connection
        raise AssertionError("dry_run should not persist validator runs")

    monkeypatch.setattr(api_main, "_persist_validator_runs", _unexpected_persist)

    resp = apply_concept_ambiguity_option_endpoint(
        ConceptApplyAmbiguityOptionRequest(
            ir=concept,
            ambiguity_id="amb_bank",
            option_id="s_bank_fin",
            source_text=_fixture_source_text(),
            mode=KernelMode.LAX,
            dry_run=True,
        )
    )

    assert resp.check_report.status == "PASS"
    assert resp.validator_runs is None


def test_concepts_apply_ambiguity_option_patch_errors_are_sorted() -> None:
    concept = ConceptIR.model_validate(_fixture_payload("var1.json"))
    payload = concept.model_dump(mode="json")
    payload["ambiguity"][0]["option_details_by_id"] = {
        "s_bank_fin": {
            "option_id": "s_bank_fin",
            "label": "broken",
            "patch": [
                JsonPatchOp(op="replace", path="/forbidden/0", value="x").model_dump(
                    mode="json", by_alias=True, exclude_none=True
                ),
                JsonPatchOp(op="move", path="/claims/0", from_path="/claims/1").model_dump(
                    mode="json", by_alias=True, exclude_none=True
                ),
            ],
        }
    }
    concept = ConceptIR.model_validate(payload)

    with pytest.raises(HTTPException) as excinfo:
        apply_concept_ambiguity_option_endpoint(
            ConceptApplyAmbiguityOptionRequest(
                ir=concept,
                ambiguity_id="amb_bank",
                option_id="s_bank_fin",
                mode=KernelMode.LAX,
            )
        )

    detail = excinfo.value.detail
    assert detail["code"] == "AMBIGUITY_OPTION_INVALID"
    assert [item["code"] for item in detail["errors"]] == [
        "PATCH_PATH_NOT_ALLOWED",
        "PATCH_OP_UNSUPPORTED",
    ]
    assert detail["errors"] == sorted(
        detail["errors"],
        key=lambda item: (item["op_index"], item["path"], item["code"]),
    )
