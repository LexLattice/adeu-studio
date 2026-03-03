from __future__ import annotations

import copy

import pytest
from adeu_commitments_ir import ADEU_COMMITMENTS_IR_SCHEMA, AdeuCommitmentsIR
from pydantic import ValidationError


def _minimal_commitments_payload() -> dict[str, object]:
    return {
        "schema": ADEU_COMMITMENTS_IR_SCHEMA,
        "compiler": {
            "name": "adeu-semantic-compiler",
            "version": "0.1.0",
            "pass_versions": ["build_ir@1"],
            "config_hash": "cfg-1",
        },
        "source_set": {
            "repo_root_rel": "docs",
            "files": [
                {
                    "path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS38.md",
                    "semantic_source_hash": "sem-hash-1",
                    "file_hash": "file-hash-1",
                }
            ],
            "source_set_hash": "source-set-hash-1",
        },
        "modules": [
            {
                "module_id": "arc:vnext_plus38",
                "module_kind": "arc_lock",
                "title": "Locked Continuation vNext+38",
                "status": "draft",
                "source": {"path": "docs/LOCKED_CONTINUATION_vNEXT_PLUS38.md"},
                "depends_on": [],
                "effects_declared": ["contract_validation"],
                "locks": [],
                "surfaces": [],
                "assertions": [],
                "evidence_requirements": [],
                "module_hash": "module-hash-1",
                "arc_id": "vnext_plus38",
            }
        ],
        "diagnostics": [],
    }


def test_commitments_ir_schema_label_is_stable() -> None:
    payload = _minimal_commitments_payload()
    model = AdeuCommitmentsIR.model_validate(payload)
    dumped = model.model_dump(mode="json", by_alias=True, exclude_none=True)
    assert dumped["schema"] == ADEU_COMMITMENTS_IR_SCHEMA


def test_commitments_ir_rejects_unknown_root_fields() -> None:
    payload = _minimal_commitments_payload()
    payload["unknown_root_field"] = True
    with pytest.raises(ValidationError):
        AdeuCommitmentsIR.model_validate(payload)


def test_commitments_ir_rejects_unknown_nested_fields() -> None:
    payload = _minimal_commitments_payload()
    payload["modules"][0]["unknown_nested_field"] = "x"
    with pytest.raises(ValidationError):
        AdeuCommitmentsIR.model_validate(payload)


def test_discriminated_union_rejects_mismatched_payload_for_known_module_kind() -> None:
    payload = _minimal_commitments_payload()
    bad_module = copy.deepcopy(payload["modules"][0])
    del bad_module["arc_id"]
    bad_module["stop_gate_id"] = "stop_gate:vnext_plus38"
    payload["modules"] = [bad_module]
    with pytest.raises(ValidationError):
        AdeuCommitmentsIR.model_validate(payload)
