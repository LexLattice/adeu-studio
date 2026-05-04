from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CANONICAL_META_LOOKUP_INDEX_SCHEMA,
    REPO_OBLIGATION_FAMILY_REGISTRY_SCHEMA,
    REPO_SEMANTIC_OPERATOR_CLASS_REGISTRY_SCHEMA,
    REPO_SEMANTIC_POINTER_LOOKUP_FIXTURE_SCHEMA,
    RepoCanonicalMetaLookupIndex,
    RepoObligationFamilyRegistry,
    RepoSemanticDeclarationNonAuthorityGuardrail,
    RepoSemanticDeclarationSourceIndex,
    RepoSemanticOperatorClassRegistry,
    RepoSemanticPointerLookupFixture,
    RepoTurnSemanticDeclarationRequest,
    derive_v85b_repo_canonical_meta_lookup_index,
    derive_v85b_repo_obligation_family_registry,
    derive_v85b_repo_semantic_operator_class_registry,
    derive_v85b_repo_semantic_pointer_lookup_fixture,
    derive_v85b_semantic_lookup_registry_bundle,
    validate_v85b_semantic_lookup_registry_bundle,
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


def _v85a_source_index() -> RepoSemanticDeclarationSourceIndex:
    return RepoSemanticDeclarationSourceIndex.model_validate(
        _load_fixture(
            "vnext_plus239",
            "repo_semantic_declaration_source_index_v239_reference.json",
        )
    )


def _v85a_request() -> RepoTurnSemanticDeclarationRequest:
    return RepoTurnSemanticDeclarationRequest.model_validate(
        _load_fixture(
            "vnext_plus239",
            "repo_turn_semantic_declaration_request_v239_reference.json",
        )
    )


def _v85a_guardrail() -> RepoSemanticDeclarationNonAuthorityGuardrail:
    return RepoSemanticDeclarationNonAuthorityGuardrail.model_validate(
        _load_fixture(
            "vnext_plus239",
            "repo_semantic_declaration_non_authority_guardrail_v239_reference.json",
        )
    )


def _v85b_lookup(
    name: str = "repo_canonical_meta_lookup_index_v240_reference.json",
) -> RepoCanonicalMetaLookupIndex:
    return RepoCanonicalMetaLookupIndex.model_validate(_load_fixture("vnext_plus240", name))


def _v85b_registry(
    name: str = "repo_semantic_operator_class_registry_v240_reference.json",
) -> RepoSemanticOperatorClassRegistry:
    return RepoSemanticOperatorClassRegistry.model_validate(_load_fixture("vnext_plus240", name))


def _v85b_obligations(
    name: str = "repo_obligation_family_registry_v240_reference.json",
) -> RepoObligationFamilyRegistry:
    return RepoObligationFamilyRegistry.model_validate(_load_fixture("vnext_plus240", name))


def _v85b_fixture(
    name: str = "repo_semantic_pointer_lookup_fixture_v240_reference.json",
) -> RepoSemanticPointerLookupFixture:
    return RepoSemanticPointerLookupFixture.model_validate(_load_fixture("vnext_plus240", name))


def _validate_reference_bundle_with(
    *,
    lookup: RepoCanonicalMetaLookupIndex | None = None,
    registry: RepoSemanticOperatorClassRegistry | None = None,
    obligations: RepoObligationFamilyRegistry | None = None,
    fixture: RepoSemanticPointerLookupFixture | None = None,
) -> None:
    source_index = _v85a_source_index()
    request = _v85a_request()
    guardrail = _v85a_guardrail()
    actual_registry = registry or _v85b_registry()
    actual_obligations = obligations or _v85b_obligations()
    actual_lookup = lookup or _v85b_lookup()
    actual_fixture = fixture or _v85b_fixture()
    validate_v85b_semantic_lookup_registry_bundle(
        semantic_declaration_source_index=source_index,
        turn_semantic_declaration_request=request,
        semantic_declaration_non_authority_guardrail=guardrail,
        canonical_meta_lookup_index=actual_lookup,
        semantic_operator_class_registry=actual_registry,
        obligation_family_registry=actual_obligations,
        semantic_pointer_lookup_fixture=actual_fixture,
    )


def test_v85b_reference_fixtures_match_derivation() -> None:
    *_, lookup, registry, obligations, fixture = derive_v85b_semantic_lookup_registry_bundle()
    assert lookup.model_dump(mode="json") == _load_fixture(
        "vnext_plus240",
        "repo_canonical_meta_lookup_index_v240_reference.json",
    )
    assert registry.model_dump(mode="json") == _load_fixture(
        "vnext_plus240",
        "repo_semantic_operator_class_registry_v240_reference.json",
    )
    assert obligations.model_dump(mode="json") == _load_fixture(
        "vnext_plus240",
        "repo_obligation_family_registry_v240_reference.json",
    )
    assert fixture.model_dump(mode="json") == _load_fixture(
        "vnext_plus240",
        "repo_semantic_pointer_lookup_fixture_v240_reference.json",
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name"),
    [
        (
            REPO_CANONICAL_META_LOOKUP_INDEX_SCHEMA,
            "repo_canonical_meta_lookup_index.v1.json",
            "repo_canonical_meta_lookup_index_v240_reference.json",
        ),
        (
            REPO_SEMANTIC_OPERATOR_CLASS_REGISTRY_SCHEMA,
            "repo_semantic_operator_class_registry.v1.json",
            "repo_semantic_operator_class_registry_v240_reference.json",
        ),
        (
            REPO_OBLIGATION_FAMILY_REGISTRY_SCHEMA,
            "repo_obligation_family_registry.v1.json",
            "repo_obligation_family_registry_v240_reference.json",
        ),
        (
            REPO_SEMANTIC_POINTER_LOOKUP_FIXTURE_SCHEMA,
            "repo_semantic_pointer_lookup_fixture.v1.json",
            "repo_semantic_pointer_lookup_fixture_v240_reference.json",
        ),
    ],
)
def test_v85b_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
) -> None:
    payload = _load_fixture("vnext_plus240", fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)


def test_v85b_reference_bundle_links_released_v85a_substrate() -> None:
    _validate_reference_bundle_with(
        lookup=_v85b_lookup(),
        registry=_v85b_registry(),
        obligations=_v85b_obligations(),
        fixture=_v85b_fixture(),
    )


def test_v85b_reference_preserves_lookup_review_boundary() -> None:
    lookup = _v85b_lookup()
    explicit = next(
        row for row in lookup.lookup_rows if row.lookup_ref == "lookup:v85b:create-ui-menu"
    )
    assert explicit.lookup_posture == "exact_match_for_review_only"
    assert explicit.competency_claim_horizon == "exact_lookup_only"
    assert explicit.obligation_expansion_posture == "named_for_later_expansion_only"
    assert set(explicit.obligation_family_refs) == {
        "obligation-family:v85b:birth_continuation_death_algebra@v1",
        "obligation-family:v85b:failure_path_fail_closed@v1",
        "obligation-family:v85b:rollback_cleanup_teardown@v1",
        "obligation-family:v85b:stateful_lifecycle@v1",
    }
    opaque = next(
        row for row in lookup.lookup_rows if row.lookup_ref == "lookup:v85b:opaque-m42-sequence"
    )
    assert opaque.lookup_input_kind == "opaque_pointer"
    assert opaque.competency_claim_horizon == "pointer_obedience_only"
    assert opaque.obligation_family_refs == []


def test_v85b_registry_keeps_gate_non_authorizing() -> None:
    gate = next(row for row in _v85b_registry().registry_rows if row.canonical_id == "GATE")
    assert gate.registry_domain == "operator"
    assert gate.operator_semantics_posture == "guard_or_route_for_later_authority_review"
    assert gate.class_semantics_posture == "not_runtime_class_behavior"


@pytest.mark.parametrize(
    ("model", "fixture_name", "message"),
    [
        (
            RepoCanonicalMetaLookupIndex,
            "repo_semantic_declaration_lookup_v240_reject_unknown_pointer_expands_obligation.json",
            "unknown or registry-gap lookup cannot name obligations",
        ),
        (
            RepoCanonicalMetaLookupIndex,
            "repo_semantic_declaration_lookup_v240_reject_unknown_version_latest.json",
            "unknown pointer versions cannot normalize to latest",
        ),
        (
            RepoSemanticOperatorClassRegistry,
            "repo_semantic_declaration_lookup_v240_reject_gate_authority.json",
            "GATE must remain guard or route",
        ),
        (
            RepoObligationFamilyRegistry,
            "repo_semantic_declaration_lookup_v240_reject_obligation_expansion.json",
            "obligation family rows cannot expand obligations",
        ),
        (
            RepoSemanticPointerLookupFixture,
            "repo_semantic_declaration_lookup_v240_reject_opaque_truth.json",
            "opaque fixtures can claim pointer obedience only",
        ),
    ],
)
def test_v85b_surfaces_reject_lookup_authority_leaks(
    model: type,
    fixture_name: str,
    message: str,
) -> None:
    with pytest.raises(ValidationError, match=message):
        model.model_validate(_load_fixture("vnext_plus240", fixture_name))


def test_v85b_bundle_rejects_alias_lookup_without_registry_alias() -> None:
    lookup = RepoCanonicalMetaLookupIndex.model_validate(
        _load_fixture(
            "vnext_plus240",
            "repo_semantic_declaration_lookup_v240_reject_alias_without_row.json",
        )
    )
    registry = _v85b_registry()
    registry_rows = [
        row.model_copy(update={"alias_rows": []}) if row.canonical_id == "ui.menu@v1" else row
        for row in registry.registry_rows
    ]
    fixture = _v85b_fixture().model_copy(
        update={"canonical_meta_lookup_index_id": lookup.canonical_meta_lookup_index_id}
    )
    with pytest.raises(ValueError, match="alias pointer lookup requires a registry alias row"):
        _validate_reference_bundle_with(
            lookup=lookup,
            registry=registry.model_copy(update={"registry_rows": registry_rows}),
            fixture=fixture,
        )


def test_v85b_bundle_rejects_fixture_result_refs_that_do_not_resolve() -> None:
    fixture = RepoSemanticPointerLookupFixture.model_validate(
        _load_fixture(
            "vnext_plus240",
            "repo_semantic_declaration_lookup_v240_reject_missing_lookup_result.json",
        )
    )
    with pytest.raises(ValueError, match="fixture actual result refs must resolve"):
        _validate_reference_bundle_with(fixture=fixture)


def test_v85b_bundle_rejects_fixture_linked_to_stale_surface_ids() -> None:
    fixture = _v85b_fixture().model_copy(
        update={"canonical_meta_lookup_index_id": "repo_canonical_meta_lookup_index:stale"}
    )
    with pytest.raises(ValueError, match="lookup fixture must reference supplied V85-B surfaces"):
        _validate_reference_bundle_with(fixture=fixture)


def test_v85b_lookup_source_refs_reject_absolute_paths() -> None:
    payload = deepcopy(
        _load_fixture("vnext_plus240", "repo_canonical_meta_lookup_index_v240_reference.json")
    )
    payload["lookup_rows"][0]["source_refs"] = ["/tmp/not-repo-relative"]
    with pytest.raises(ValidationError, match="source_refs must be repo-relative"):
        RepoCanonicalMetaLookupIndex.model_validate(payload)


def test_v85b_derivation_helpers_accept_released_v85a_inputs() -> None:
    source_index = _v85a_source_index()
    request = _v85a_request()
    guardrail = _v85a_guardrail()
    assert (
        derive_v85b_repo_canonical_meta_lookup_index(
            semantic_declaration_source_index=source_index,
            turn_semantic_declaration_request=request,
            semantic_declaration_non_authority_guardrail=guardrail,
        ).schema
        == REPO_CANONICAL_META_LOOKUP_INDEX_SCHEMA
    )
    assert (
        derive_v85b_repo_semantic_operator_class_registry(
            semantic_declaration_source_index=source_index,
            turn_semantic_declaration_request=request,
            semantic_declaration_non_authority_guardrail=guardrail,
        ).schema
        == REPO_SEMANTIC_OPERATOR_CLASS_REGISTRY_SCHEMA
    )
    assert (
        derive_v85b_repo_obligation_family_registry(
            semantic_declaration_source_index=source_index,
            turn_semantic_declaration_request=request,
            semantic_declaration_non_authority_guardrail=guardrail,
        ).schema
        == REPO_OBLIGATION_FAMILY_REGISTRY_SCHEMA
    )
    assert (
        derive_v85b_repo_semantic_pointer_lookup_fixture(
            semantic_declaration_source_index=source_index,
            turn_semantic_declaration_request=request,
            semantic_declaration_non_authority_guardrail=guardrail,
        ).schema
        == REPO_SEMANTIC_POINTER_LOOKUP_FIXTURE_SCHEMA
    )
