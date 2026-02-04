from __future__ import annotations

import pytest
from adeu_ir import AdeuIR
from adeu_ir.models import JsonPatchOp
from adeu_kernel import KernelMode, PatchValidationError, apply_json_patch, check


def _base_ir() -> AdeuIR:
    return AdeuIR.model_validate(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_patch_test",
            "context": {
                "doc_id": "doc1",
                "jurisdiction": "US-CA",
                "time_eval": "2026-02-04T00:00:00Z",
            },
            "D_norm": {
                "statements": [
                    {
                        "id": "dn1",
                        "kind": "permission",
                        "subject": {"ref_type": "text", "text": "Supplier"},
                        "action": {
                            "verb": "terminate",
                            "object": {"ref_type": "text", "text": "Agreement"},
                        },
                        "scope": {
                            "jurisdiction": "US-CA",
                            "time_about": {"kind": "unspecified"},
                        },
                        "provenance": {"doc_ref": "doc1#clause1"},
                    }
                ]
            },
        }
    )


def test_apply_json_patch_replace_ok() -> None:
    ir = _base_ir()
    patch = [
        JsonPatchOp.model_validate(
            {"op": "replace", "path": "/D_norm/statements/0/kind", "value": "obligation"}
        )
    ]
    out = apply_json_patch(ir, patch)
    assert ir.D_norm.statements[0].kind == "permission"
    assert out.D_norm.statements[0].kind == "obligation"


def test_apply_json_patch_disallowed_path() -> None:
    ir = _base_ir()
    patch = [JsonPatchOp.model_validate({"op": "replace", "path": "/schema_version", "value": "x"})]
    with pytest.raises(PatchValidationError) as exc:
        apply_json_patch(ir, patch)
    assert exc.value.reason.code == "AMBIGUITY_OPTION_INVALID"


def test_apply_json_patch_fail_closed() -> None:
    ir = _base_ir()
    patch = [
        JsonPatchOp.model_validate(
            {"op": "replace", "path": "/D_norm/statements/0/kind", "value": "obligation"}
        ),
        JsonPatchOp.model_validate({"op": "replace", "path": "/schema_version", "value": "x"}),
    ]
    with pytest.raises(PatchValidationError):
        apply_json_patch(ir, patch)
    assert ir.D_norm.statements[0].kind == "permission"


def test_apply_json_patch_disallows_move_copy() -> None:
    ir = _base_ir()
    patch = [JsonPatchOp.model_validate({"op": "move", "from": "/D_norm", "path": "/E"})]
    with pytest.raises(PatchValidationError):
        apply_json_patch(ir, patch)


def test_check_maps_bad_ambiguity_option() -> None:
    report = check(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_bad_amb",
            "context": {
                "doc_id": "doc1",
                "jurisdiction": "US-CA",
                "time_eval": "2026-02-04T00:00:00Z",
            },
            "ambiguity": [
                {
                    "id": "amb1",
                    "span": {"start": 0, "end": 3},
                    "issue": "modal_verb_may",
                    "options": [
                        {
                            "option_id": "opt1",
                            "label": "bad",
                            "effect": "both variant and patch",
                            "variant_ir_id": "ir_other",
                            "patch": [
                                {
                                    "op": "replace",
                                    "path": "/D_norm/statements/0/kind",
                                    "value": "permission",
                                }
                            ],
                        }
                    ],
                }
            ],
        },
        mode=KernelMode.STRICT,
    )
    assert report.status == "REFUSE"
    assert report.reason_codes and report.reason_codes[0].code == "AMBIGUITY_OPTION_INVALID"
