from __future__ import annotations

import copy

import pytest
from adeu_ir.models import JsonPatchOp
from adeu_patch_core import PatchCoreValidationError, apply_patch_ops, encode_patch_size_bytes


def _base_doc() -> dict:
    return {
        "items": [
            {"id": "a", "value": 1},
            {"id": "b", "value": 2},
        ],
        "meta": {"name": "demo"},
    }


def test_encode_patch_size_bytes_is_deterministic() -> None:
    patch_ops = [
        JsonPatchOp(op="replace", path="/meta/name", value="demo2"),
        JsonPatchOp(op="test", path="/items/0/id", value="a"),
    ]
    assert encode_patch_size_bytes(patch_ops) == encode_patch_size_bytes(patch_ops)


def test_apply_patch_ops_supports_move_and_copy() -> None:
    doc = _base_doc()
    patch_ops = [
        JsonPatchOp(op="copy", from_path="/items/0", path="/items/2"),
        JsonPatchOp(op="move", from_path="/items/1", path="/items/0"),
    ]

    apply_patch_ops(doc, patch_ops)

    assert [item["id"] for item in doc["items"]] == ["b", "a", "a"]


def test_apply_patch_ops_collects_sorted_errors() -> None:
    doc = _base_doc()
    patch_ops = [
        JsonPatchOp(op="replace", path="/forbidden/x", value="bad"),
        JsonPatchOp(op="move", from_path="/items/0", path="/items/1"),
        JsonPatchOp(op="test", path="/items/0/id", value="mismatch"),
    ]

    with pytest.raises(PatchCoreValidationError) as excinfo:
        apply_patch_ops(
            doc,
            patch_ops,
            allowed_prefixes=("/items",),
            disallowed_ops=frozenset({"move"}),
            collect_errors=True,
        )

    errors = list(excinfo.value.errors)
    assert errors == sorted(errors, key=lambda err: (err.op_index, err.path, err.code))
    assert [err.code for err in errors] == [
        "PATCH_PATH_NOT_ALLOWED",
        "PATCH_OP_UNSUPPORTED",
        "PATCH_TEST_FAILED",
    ]


def test_apply_patch_ops_fail_fast_by_default() -> None:
    doc = _base_doc()
    original = copy.deepcopy(doc)
    patch_ops = [
        JsonPatchOp(op="replace", path="/forbidden/x", value="bad"),
        JsonPatchOp(op="replace", path="/meta/name", value="changed"),
    ]

    with pytest.raises(PatchCoreValidationError) as excinfo:
        apply_patch_ops(doc, patch_ops, allowed_prefixes=("/items",))

    assert len(excinfo.value.errors) == 1
    assert excinfo.value.errors[0].code == "PATCH_PATH_NOT_ALLOWED"
    assert doc == original


def test_apply_patch_ops_value_policy_modes() -> None:
    doc_explicit = _base_doc()
    explicit_null_patch = [JsonPatchOp(op="add", path="/meta/extra", value=None)]
    apply_patch_ops(doc_explicit, explicit_null_patch, value_policy="explicit_member")
    assert "extra" in doc_explicit["meta"] and doc_explicit["meta"]["extra"] is None

    doc_non_null = _base_doc()
    with pytest.raises(PatchCoreValidationError) as excinfo:
        apply_patch_ops(doc_non_null, explicit_null_patch, value_policy="non_null")
    assert excinfo.value.errors[0].code == "PATCH_VALUE_REQUIRED"
