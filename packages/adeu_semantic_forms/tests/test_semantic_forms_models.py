from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest
from adeu_semantic_forms import (
    ADEU_SEMANTIC_NORMAL_FORM_SCHEMA,
    ADEU_SEMANTIC_PARSE_RESULT_SCHEMA,
    ADEU_SEMANTIC_STATEMENT_CORE_SCHEMA,
    SemanticLexiconEntry,
    SemanticNormalForm,
    SemanticParseResult,
    SemanticStatementCore,
    WorkerAnchor,
    sha256_canonical_json,
)
from pydantic import ValidationError


def _fixture_path(name: str) -> Path:
    return Path(__file__).parent / "fixtures" / "v49a" / name


def _read_json(name: str) -> dict[str, object]:
    return json.loads(_fixture_path(name).read_text(encoding="utf-8"))


def test_reference_statement_core_replays_deterministically() -> None:
    payload = _read_json("reference_semantic_statement_core.json")

    model = SemanticStatementCore.model_validate(payload)

    assert model.schema == ADEU_SEMANTIC_STATEMENT_CORE_SCHEMA
    assert model.model_dump(mode="json", by_alias=True, exclude_none=True) == payload


def test_reference_normal_form_replays_deterministically() -> None:
    payload = _read_json("reference_semantic_normal_form.json")

    model = SemanticNormalForm.model_validate(payload)

    assert model.schema == ADEU_SEMANTIC_NORMAL_FORM_SCHEMA
    assert model.model_dump(mode="json", by_alias=True, exclude_none=True) == payload


@pytest.mark.parametrize(
    ("fixture_name", "expected_status"),
    [
        ("reference_semantic_parse_result_resolved_singleton.json", "resolved_singleton"),
        ("reference_semantic_parse_result_typed_alternatives.json", "typed_alternatives"),
        ("reference_semantic_parse_result_rejected_unsupported.json", "rejected_unsupported"),
    ],
)
def test_reference_parse_results_replay_deterministically(
    fixture_name: str, expected_status: str
) -> None:
    payload = _read_json(fixture_name)

    model = SemanticParseResult.model_validate(payload)

    assert model.schema == ADEU_SEMANTIC_PARSE_RESULT_SCHEMA
    assert model.parse_status == expected_status
    assert model.model_dump(mode="json", by_alias=True, exclude_none=True) == payload


def test_projection_only_fields_do_not_change_semantic_hash() -> None:
    reference_payload = _read_json("reference_semantic_normal_form.json")
    projection_mutation = _read_json("mutation_semantic_normal_form_projection_only.json")

    reference = SemanticNormalForm.model_validate(reference_payload)
    mutated = SemanticNormalForm.model_validate(projection_mutation)

    assert mutated.semantic_hash == reference.semantic_hash
    assert mutated.model_dump(mode="json", by_alias=True, exclude_none=True) == projection_mutation


def test_identity_field_change_does_change_semantic_hash() -> None:
    reference_payload = _read_json("reference_semantic_normal_form.json")
    identity_mutation = _read_json("mutation_semantic_normal_form_identity_change.json")

    reference = SemanticNormalForm.model_validate(reference_payload)
    mutated = SemanticNormalForm.model_validate(identity_mutation)

    assert mutated.semantic_hash != reference.semantic_hash
    assert mutated.model_dump(mode="json", by_alias=True, exclude_none=True) == identity_mutation


def test_invalid_parse_status_fixture_fails_closed() -> None:
    payload = _read_json("reject_invalid_parse_result_status.json")

    with pytest.raises(ValidationError):
        SemanticParseResult.model_validate(payload)


def test_clarification_required_contract_accepts_missing_required_anchor_case() -> None:
    reference = _read_json("reference_semantic_parse_result_rejected_unsupported.json")
    input_text = "Prepare a read-only binding seed under the owner rule."
    input_text_hash = sha256_canonical_json({"input_text": input_text})
    payload = {
        "schema": ADEU_SEMANTIC_PARSE_RESULT_SCHEMA,
        "parse_result_id": f"parse:{input_text_hash[:16]}",
        "profile_id": reference["profile_id"],
        "input_kind": "natural_language",
        "input_text": input_text,
        "input_text_hash": input_text_hash,
        "parse_status": "clarification_required",
        "candidates": [],
        "ambiguities": [
            {
                "ambiguity_id": "missing_scope_anchor",
                "ambiguity_kind": "missing_required_anchor",
                "alternatives": [],
                "notes": "No released scope anchor was resolved from the bounded starter calculus.",
            }
        ],
        "rejected_reason_codes": [],
        "notices": ["clarification required before a canonical semantic object can be licensed"],
    }

    model = SemanticParseResult.model_validate(payload)

    assert model.parse_status == "clarification_required"
    assert model.candidates == []


def test_statement_core_rejects_relation_lane_mismatch() -> None:
    payload = copy.deepcopy(_read_json("reference_semantic_statement_core.json"))
    payload["lane_tag"] = "worker"

    with pytest.raises(ValidationError):
        SemanticStatementCore.model_validate(payload)


def test_rejected_unsupported_rejects_ambiguity_mixture() -> None:
    payload = copy.deepcopy(_read_json("reference_semantic_parse_result_rejected_unsupported.json"))
    payload["ambiguities"] = [
        {
            "ambiguity_id": "mixed_status",
            "ambiguity_kind": "missing_required_anchor",
            "alternatives": [],
            "notes": "Unsupported posture may not also claim ambiguity in V49-A.",
        }
    ]

    with pytest.raises(ValidationError):
        SemanticParseResult.model_validate(payload)


def test_parse_result_rejects_mismatched_hash_and_id() -> None:
    payload = _read_json("reference_semantic_parse_result_resolved_singleton.json")
    payload["input_text_hash"] = "tampered"

    with pytest.raises(ValidationError):
        SemanticParseResult.model_validate(payload)

    payload = _read_json("reference_semantic_parse_result_resolved_singleton.json")
    payload["parse_result_id"] = "parse:tampered"

    with pytest.raises(ValidationError):
        SemanticParseResult.model_validate(payload)


def test_worker_anchor_requires_at_least_one_alias() -> None:
    with pytest.raises(ValidationError):
        WorkerAnchor.model_validate(
            {
                "anchor_id": "worker:repo_internal_single_codex_worker:default",
                "resolved_worker_subject_ref": "worker:repo_internal_single_codex_worker:default",
                "aliases": [],
            }
        )


def test_lexicon_entry_requires_at_least_one_alias() -> None:
    with pytest.raises(ValidationError):
        SemanticLexiconEntry.model_validate(
            {
                "canonical_value": "read_only",
                "aliases": [],
            }
        )
