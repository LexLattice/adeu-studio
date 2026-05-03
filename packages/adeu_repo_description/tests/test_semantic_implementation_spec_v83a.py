from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_INTENT_NON_IMPLEMENTATION_GUARDRAIL_SCHEMA,
    REPO_INTENT_SOURCE_INDEX_SCHEMA,
    REPO_SEMANTIC_INTENT_CONTRACT_SCHEMA,
    RepoIntentNonImplementationGuardrail,
    RepoIntentSourceIndex,
    RepoSemanticIntentContract,
    derive_v83a_repo_intent_non_implementation_guardrail,
    derive_v83a_semantic_implementation_spec_bundle,
    validate_v83a_semantic_implementation_spec_bundle,
)
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root(slice_name: str) -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / slice_name


def _load_fixture(slice_name: str, name: str) -> dict[str, Any]:
    return json.loads((_fixture_root(slice_name) / name).read_text(encoding="utf-8"))


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_repo_description" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _v83a_source_index(
    name: str = "repo_intent_source_index_v233_reference.json",
) -> RepoIntentSourceIndex:
    return RepoIntentSourceIndex.model_validate(_load_fixture("vnext_plus233", name))


def _v83a_contract(
    name: str = "repo_semantic_intent_contract_v233_reference.json",
) -> RepoSemanticIntentContract:
    return RepoSemanticIntentContract.model_validate(_load_fixture("vnext_plus233", name))


def _v83a_guardrail(
    name: str = "repo_intent_non_implementation_guardrail_v233_reference.json",
) -> RepoIntentNonImplementationGuardrail:
    return RepoIntentNonImplementationGuardrail.model_validate(
        _load_fixture("vnext_plus233", name)
    )


def _validate_reference_bundle_with(
    *,
    source_index: RepoIntentSourceIndex | None = None,
    contract: RepoSemanticIntentContract | None = None,
    guardrail: RepoIntentNonImplementationGuardrail | None = None,
) -> None:
    resolved_contract = contract if contract is not None else _v83a_contract()
    validate_v83a_semantic_implementation_spec_bundle(
        intent_source_index=source_index if source_index is not None else _v83a_source_index(),
        semantic_intent_contract=resolved_contract,
        intent_non_implementation_guardrail=(
            guardrail
            if guardrail is not None
            else (
                derive_v83a_repo_intent_non_implementation_guardrail(
                    semantic_intent_contract=resolved_contract
                )
                if contract is not None
                else _v83a_guardrail()
            )
        ),
    )


def test_v233_reference_bundle_validates() -> None:
    source_index = _v83a_source_index()
    contract = _v83a_contract()
    guardrail = _v83a_guardrail()

    assert source_index.schema == REPO_INTENT_SOURCE_INDEX_SCHEMA
    assert contract.schema == REPO_SEMANTIC_INTENT_CONTRACT_SCHEMA
    assert guardrail.schema == REPO_INTENT_NON_IMPLEMENTATION_GUARDRAIL_SCHEMA
    assert {
        row.semantic_spec_eligibility_posture for row in contract.intent_contract_rows
    } == {
        "blocked_by_external_source_import_gap",
        "eligible_for_semantic_spec_review",
        "future_family_only",
    }
    eligible_rows = [
        row
        for row in contract.intent_contract_rows
        if row.semantic_spec_eligibility_posture == "eligible_for_semantic_spec_review"
    ]
    assert len(eligible_rows) == 1
    assert eligible_rows[0].success_horizon_kind == "implementation_packet_success"
    assert eligible_rows[0].non_goal_refs
    assert eligible_rows[0].authority_boundary_refs
    assert all(
        row.model_agent_authority_posture
        in {
            "no_model_authority",
            "authority_requires_later_lock",
        }
        for row in source_index.source_rows
    )
    assert all(
        row.non_implementation_posture == "non_implementation_guardrail_active"
        for row in guardrail.guardrail_rows
    )

    _validate_reference_bundle_with(
        source_index=source_index,
        contract=contract,
        guardrail=guardrail,
    )


def test_v233_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_intent_source_index.v1.json").validate(
        _load_fixture("vnext_plus233", "repo_intent_source_index_v233_reference.json")
    )
    _schema_validator("repo_semantic_intent_contract.v1.json").validate(
        _load_fixture("vnext_plus233", "repo_semantic_intent_contract_v233_reference.json")
    )
    _schema_validator("repo_intent_non_implementation_guardrail.v1.json").validate(
        _load_fixture(
            "vnext_plus233",
            "repo_intent_non_implementation_guardrail_v233_reference.json",
        )
    )


def test_v233_derivation_helper_matches_reference_fixtures() -> None:
    source_index, contract, guardrail = derive_v83a_semantic_implementation_spec_bundle(
        repo_root=_repo_root()
    )

    assert source_index.model_dump(mode="json") == _load_fixture(
        "vnext_plus233",
        "repo_intent_source_index_v233_reference.json",
    )
    assert contract.model_dump(mode="json") == _load_fixture(
        "vnext_plus233",
        "repo_semantic_intent_contract_v233_reference.json",
    )
    assert guardrail.model_dump(mode="json") == _load_fixture(
        "vnext_plus233",
        "repo_intent_non_implementation_guardrail_v233_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_semantic_implementation_spec_v233_reject_missing_source_without_absence_posture.json",
            RepoIntentSourceIndex,
            "present or import-gapped",
        ),
        (
            "repo_semantic_implementation_spec_v233_reject_contract_without_source_refs.json",
            RepoSemanticIntentContract,
            "at least 1 item",
        ),
        (
            "repo_semantic_implementation_spec_v233_reject_ready_to_implement_now.json",
            RepoSemanticIntentContract,
            "implementation authority",
        ),
        (
            "repo_semantic_implementation_spec_v233_reject_success_horizon_tests_only.json",
            RepoSemanticIntentContract,
            "success horizon cannot be only passing tests",
        ),
        (
            "repo_semantic_implementation_spec_v233_reject_eligible_without_non_goal_refs.json",
            RepoSemanticIntentContract,
            "eligible semantic intent contracts require non-goal refs",
        ),
        (
            "repo_semantic_implementation_spec_v233_reject_future_surface_refs.json",
            RepoSemanticIntentContract,
            "Extra inputs are not permitted",
        ),
        (
            "repo_semantic_implementation_spec_v233_reject_empty_forbidden_implementation_actions.json",
            RepoIntentNonImplementationGuardrail,
            "at least 1 item",
        ),
        (
            "repo_semantic_implementation_spec_v233_reject_empty_forbidden_runtime_actions.json",
            RepoIntentNonImplementationGuardrail,
            "at least 1 item",
        ),
        (
            "repo_semantic_implementation_spec_v233_reject_empty_forbidden_downstream_authority.json",
            RepoIntentNonImplementationGuardrail,
            "at least 1 item",
        ),
    ],
)
def test_v233_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoIntentSourceIndex
        | RepoSemanticIntentContract
        | RepoIntentNonImplementationGuardrail
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus233", fixture_name))


def test_v233_bundle_rejects_support_only_eligibility_sources() -> None:
    contract = _v83a_contract(
        "repo_semantic_implementation_spec_v233_reject_support_only_eligibility.json"
    )

    with pytest.raises(
        ValueError,
        match="eligible semantic intent contracts require released V82-C sources",
    ):
        _validate_reference_bundle_with(contract=contract)


def test_v233_bundle_rejects_unbounded_generated_spec_eligibility() -> None:
    source_index = _v83a_source_index(
        "repo_semantic_implementation_spec_v233_reject_generated_unbounded_source_index.json"
    )
    contract = _v83a_contract(
        "repo_semantic_implementation_spec_v233_reject_generated_unbounded_eligibility.json"
    )

    with pytest.raises(ValueError, match="unbounded generated specs cannot support eligibility"):
        _validate_reference_bundle_with(source_index=source_index, contract=contract)
