from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_concepts import (
    ConceptIR,
    ConceptPatchValidationError,
    apply_concept_ambiguity_option,
    apply_concept_json_patch,
)
from adeu_ir.models import JsonPatchOp
from adeu_ir.repo import repo_root


def _fixture_payload(name: str) -> dict:
    root = repo_root(anchor=Path(__file__))
    path = root / "examples" / "concepts" / "fixtures" / "bank_sense_coherence" / "proposals" / name
    return json.loads(path.read_text(encoding="utf-8"))


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


def test_apply_concept_ambiguity_option_applies_patch_without_id_canonicalization() -> None:
    concept = _patchable_concept()

    patched = apply_concept_ambiguity_option(
        concept,
        ambiguity_id="amb_bank",
        option_id="s_bank_fin",
    )

    assert patched.concept_id == concept.concept_id
    assert [sense.id for sense in patched.senses] == ["s_bank_fin", "s_credit"]
    assert [link.id for link in patched.links] == ["ln_commit"]
    assert patched.ambiguity == []


def test_apply_concept_json_patch_rejects_dangling_references() -> None:
    concept = ConceptIR.model_validate(_fixture_payload("var1.json"))
    patch_ops = [JsonPatchOp(op="remove", path="/senses/1")]

    with pytest.raises(ConceptPatchValidationError) as excinfo:
        apply_concept_json_patch(concept, patch_ops)

    errors = list(excinfo.value.errors)
    assert errors == sorted(errors, key=lambda err: (err.op_index, err.path, err.code))
    assert any(err.path == "/ambiguity/0/options/1" for err in errors)


def test_apply_concept_json_patch_sorts_errors_deterministically() -> None:
    concept = ConceptIR.model_validate(_fixture_payload("var1.json"))
    patch_ops = [
        JsonPatchOp(op="replace", path="/forbidden/0", value="x"),
        JsonPatchOp(op="move", path="/claims/0", from_path="/claims/1"),
    ]

    with pytest.raises(ConceptPatchValidationError) as excinfo:
        apply_concept_json_patch(concept, patch_ops)

    errors = list(excinfo.value.errors)
    assert errors == sorted(errors, key=lambda err: (err.op_index, err.path, err.code))
    assert [err.code for err in errors] == ["PATCH_PATH_NOT_ALLOWED", "PATCH_OP_UNSUPPORTED"]
