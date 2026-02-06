from __future__ import annotations

from adeu_api.main import ApplyAmbiguityOptionRequest, apply_ambiguity_option_endpoint
from adeu_ir import AdeuIR
from adeu_kernel import KernelMode


def _patchable_ir() -> AdeuIR:
    return AdeuIR.model_validate(
        {
            "schema_version": "adeu.ir.v0",
            "ir_id": "ir_patch_defs",
            "context": {
                "doc_id": "doc:test:patch",
                "jurisdiction": "US-CA",
                "time_eval": "2026-02-06T00:00:00Z",
            },
            "D_norm": {
                "statements": [
                    {
                        "id": "dn_raw_1",
                        "kind": "obligation",
                        "subject": {"ref_type": "text", "text": "Supplier"},
                        "action": {
                            "verb": "suspend",
                            "object": {"ref_type": "def", "def_id": "def_material_breach"},
                        },
                        "scope": {"jurisdiction": "US-CA", "time_about": {"kind": "unspecified"}},
                        "provenance": {
                            "doc_ref": "doc:test:patch#sec1",
                            "span": {"start": 0, "end": 20},
                        },
                    }
                ]
            },
            "ambiguity": [
                {
                    "id": "amb_material_1",
                    "span": {"start": 5, "end": 12},
                    "issue": "material_breach_term",
                    "options": [
                        {
                            "option_id": "opt_add_def",
                            "label": "Define term",
                            "effect": "Add definition",
                            "patch": [
                                {
                                    "op": "add",
                                    "path": "/O/definitions/0",
                                    "value": {
                                        "id": "def_material_breach",
                                        "term": "material breach",
                                        "meaning": "Significant violation",
                                    },
                                }
                            ],
                        }
                    ],
                }
            ],
        }
    )


def test_apply_ambiguity_option_endpoint_canonicalizes_patch_added_ids() -> None:
    ir = _patchable_ir()
    resp = apply_ambiguity_option_endpoint(
        ApplyAmbiguityOptionRequest(
            ir=ir,
            ambiguity_id="amb_material_1",
            option_id="opt_add_def",
            mode=KernelMode.LAX,
        )
    )

    patched = resp.patched_ir
    assert patched.O.definitions, "Expected patch to add a definition"
    new_def_id = patched.O.definitions[0].id
    assert new_def_id.startswith("def_")
    assert new_def_id != "def_material_breach"

    action_obj = patched.D_norm.statements[0].action.object
    assert action_obj is not None
    assert action_obj.ref_type == "def"
    assert action_obj.def_id == new_def_id
