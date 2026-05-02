from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CONNECTOR_ACCESS_REVIEW_BOUNDARY_SCHEMA,
    REPO_CORPUS_DATA_HANDLING_AUTHORITY_REVIEW_SCHEMA,
    REPO_CORPUS_INGESTION_EXCEPTION_REGISTER_SCHEMA,
    REPO_CORPUS_INGESTION_PREFLIGHT_CONTRACT_SCHEMA,
    RepoConnectorAccessReviewBoundary,
    RepoCorpusDataHandlingAuthorityReview,
    RepoCorpusIngestionExceptionRegister,
    RepoCorpusIngestionNonTransferGuardrail,
    RepoCorpusIngestionPreflightContract,
    RepoCorpusIngestionReviewRequest,
    RepoCorpusIngestionSourceIndex,
    derive_v82b_corpus_ingestion_boundary_bundle,
    validate_v82b_corpus_ingestion_boundary_bundle,
)
from adeu_repo_description.corpus_ingestion_review import _surface_id
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


def _v82a_source_index() -> RepoCorpusIngestionSourceIndex:
    return RepoCorpusIngestionSourceIndex.model_validate(
        _load_fixture("vnext_plus230", "repo_corpus_ingestion_source_index_v230_reference.json")
    )


def _v82a_request() -> RepoCorpusIngestionReviewRequest:
    return RepoCorpusIngestionReviewRequest.model_validate(
        _load_fixture(
            "vnext_plus230",
            "repo_corpus_ingestion_review_request_v230_reference.json",
        )
    )


def _v82a_guardrail() -> RepoCorpusIngestionNonTransferGuardrail:
    return RepoCorpusIngestionNonTransferGuardrail.model_validate(
        _load_fixture(
            "vnext_plus230",
            "repo_corpus_ingestion_non_transfer_guardrail_v230_reference.json",
        )
    )


def _v82b_preflight(
    name: str = "repo_corpus_ingestion_preflight_contract_v231_reference.json",
) -> RepoCorpusIngestionPreflightContract:
    return RepoCorpusIngestionPreflightContract.model_validate(_load_fixture("vnext_plus231", name))


def _v82b_connector_boundary(
    name: str = "repo_connector_access_review_boundary_v231_reference.json",
) -> RepoConnectorAccessReviewBoundary:
    return RepoConnectorAccessReviewBoundary.model_validate(_load_fixture("vnext_plus231", name))


def _v82b_authority_review(
    name: str = "repo_corpus_data_handling_authority_review_v231_reference.json",
) -> RepoCorpusDataHandlingAuthorityReview:
    return RepoCorpusDataHandlingAuthorityReview.model_validate(
        _load_fixture("vnext_plus231", name)
    )


def _v82b_exception_register(
    name: str = "repo_corpus_ingestion_exception_register_v231_reference.json",
) -> RepoCorpusIngestionExceptionRegister:
    return RepoCorpusIngestionExceptionRegister.model_validate(_load_fixture("vnext_plus231", name))


def _validate_reference_bundle_with(
    *,
    preflight: RepoCorpusIngestionPreflightContract | None = None,
    connector_boundary: RepoConnectorAccessReviewBoundary | None = None,
    authority_review: RepoCorpusDataHandlingAuthorityReview | None = None,
    exception_register: RepoCorpusIngestionExceptionRegister | None = None,
) -> None:
    validate_v82b_corpus_ingestion_boundary_bundle(
        corpus_ingestion_source_index=_v82a_source_index(),
        corpus_ingestion_review_request=_v82a_request(),
        corpus_ingestion_non_transfer_guardrail=_v82a_guardrail(),
        corpus_ingestion_preflight_contract=preflight
        if preflight is not None
        else _v82b_preflight(),
        connector_access_review_boundary=(
            connector_boundary if connector_boundary is not None else _v82b_connector_boundary()
        ),
        corpus_data_handling_authority_review=(
            authority_review if authority_review is not None else _v82b_authority_review()
        ),
        corpus_ingestion_exception_register=(
            exception_register if exception_register is not None else _v82b_exception_register()
        ),
    )


def _rehash(payload: dict[str, Any], surface_name: str, id_field: str) -> dict[str, Any]:
    payload = deepcopy(payload)
    payload[id_field] = _surface_id(surface_name, payload["schema"], payload, id_field)
    return payload


def test_v231_reference_bundle_validates() -> None:
    preflight = _v82b_preflight()
    connector_boundary = _v82b_connector_boundary()
    authority_review = _v82b_authority_review()
    exception_register = _v82b_exception_register()

    assert preflight.schema == REPO_CORPUS_INGESTION_PREFLIGHT_CONTRACT_SCHEMA
    assert connector_boundary.schema == REPO_CONNECTOR_ACCESS_REVIEW_BOUNDARY_SCHEMA
    assert authority_review.schema == REPO_CORPUS_DATA_HANDLING_AUTHORITY_REVIEW_SCHEMA
    assert exception_register.schema == REPO_CORPUS_INGESTION_EXCEPTION_REGISTER_SCHEMA
    assert {row.corpus_ingestion_posture for row in preflight.preflight_rows} == {
        "no_corpus_ingestion_performed_by_v82"
    }
    assert {
        row.connector_activation_posture for row in connector_boundary.connector_boundary_rows
    } == {"no_connector_activation_performed_by_v82"}
    assert {row.endpoint_access_posture for row in connector_boundary.connector_boundary_rows} == {
        "no_endpoint_access_performed_by_v82"
    }
    assert {
        "missing_retention_authority",
        "missing_deletion_or_withdrawal_authority",
        "missing_endpoint_access_boundary",
    }.issubset({row.exception_kind for row in exception_register.exception_rows})
    authority_by_ref = {
        row.authority_review_ref: row for row in authority_review.authority_review_rows
    }
    assert (
        authority_by_ref["authority-review:v82b:self-evidencing:connector-missing"].authority_kind
        == "connector_authority"
    )
    assert (
        authority_by_ref[
            "authority-review:v82b:self-evidencing:deletion-withdrawal-missing"
        ].authority_kind
        == "deletion_or_withdrawal_authority"
    )
    assert (
        authority_by_ref[
            "authority-review:v82b:self-evidencing:endpoint-missing"
        ].required_before_surface
        == "future_endpoint_access_authority_review"
    )
    assert (
        authority_by_ref[
            "authority-review:v82b:self-evidencing:transfer-missing"
        ].required_before_surface
        == "future_data_transfer_authority_review"
    )

    _validate_reference_bundle_with(
        preflight=preflight,
        connector_boundary=connector_boundary,
        authority_review=authority_review,
        exception_register=exception_register,
    )


def test_v231_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_corpus_ingestion_preflight_contract.v1.json").validate(
        _load_fixture(
            "vnext_plus231",
            "repo_corpus_ingestion_preflight_contract_v231_reference.json",
        )
    )
    _schema_validator("repo_connector_access_review_boundary.v1.json").validate(
        _load_fixture(
            "vnext_plus231",
            "repo_connector_access_review_boundary_v231_reference.json",
        )
    )
    _schema_validator("repo_corpus_data_handling_authority_review.v1.json").validate(
        _load_fixture(
            "vnext_plus231",
            "repo_corpus_data_handling_authority_review_v231_reference.json",
        )
    )
    _schema_validator("repo_corpus_ingestion_exception_register.v1.json").validate(
        _load_fixture(
            "vnext_plus231",
            "repo_corpus_ingestion_exception_register_v231_reference.json",
        )
    )


def test_v231_derivation_helper_matches_reference_fixtures() -> None:
    _, _, _, preflight, connector_boundary, authority_review, exception_register = (
        derive_v82b_corpus_ingestion_boundary_bundle(repo_root=_repo_root())
    )

    assert preflight.model_dump(mode="json") == _load_fixture(
        "vnext_plus231",
        "repo_corpus_ingestion_preflight_contract_v231_reference.json",
    )
    assert connector_boundary.model_dump(mode="json") == _load_fixture(
        "vnext_plus231",
        "repo_connector_access_review_boundary_v231_reference.json",
    )
    assert authority_review.model_dump(mode="json") == _load_fixture(
        "vnext_plus231",
        "repo_corpus_data_handling_authority_review_v231_reference.json",
    )
    assert exception_register.model_dump(mode="json") == _load_fixture(
        "vnext_plus231",
        "repo_corpus_ingestion_exception_register_v231_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_corpus_ingestion_v231_reject_preflight_claims_ingestion.json",
            RepoCorpusIngestionPreflightContract,
            "must not ingest corpora",
        ),
        (
            "repo_corpus_ingestion_v231_reject_preflight_observed_monitoring.json",
            RepoCorpusIngestionPreflightContract,
            "may not claim V82-B permission or observation",
        ),
        (
            "repo_corpus_ingestion_v231_reject_connector_activation_claim.json",
            RepoConnectorAccessReviewBoundary,
            "must not activate connectors",
        ),
        (
            "repo_corpus_ingestion_v231_reject_endpoint_access_claim.json",
            RepoConnectorAccessReviewBoundary,
            "must not access endpoints",
        ),
        (
            "repo_corpus_ingestion_v231_reject_authority_grants_clearance.json",
            RepoCorpusDataHandlingAuthorityReview,
            "may not carry corpus-ingestion action authority",
        ),
        (
            "repo_corpus_ingestion_v231_reject_exception_resolved_by_v82b.json",
            RepoCorpusIngestionExceptionRegister,
            "must not be marked resolved",
        ),
        (
            "repo_corpus_ingestion_v231_reject_exception_without_evidence_refs.json",
            RepoCorpusIngestionExceptionRegister,
            "blocking corpus-ingestion exceptions require evidence refs",
        ),
    ],
)
def test_v231_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoCorpusIngestionPreflightContract
        | RepoConnectorAccessReviewBoundary
        | RepoCorpusDataHandlingAuthorityReview
        | RepoCorpusIngestionExceptionRegister
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus231", fixture_name))


def test_v231_bundle_rejects_unknown_connector_boundary_ref() -> None:
    payload = _load_fixture(
        "vnext_plus231",
        "repo_corpus_ingestion_preflight_contract_v231_reference.json",
    )
    payload = deepcopy(payload)
    payload["preflight_rows"][0]["connector_boundary_refs"] = ["connector-boundary:v82b:missing"]
    payload = _rehash(
        payload,
        "repo_corpus_ingestion_preflight_contract",
        "corpus_ingestion_preflight_contract_id",
    )
    exception_payload = _load_fixture(
        "vnext_plus231",
        "repo_corpus_ingestion_exception_register_v231_reference.json",
    )
    exception_payload = deepcopy(exception_payload)
    exception_payload["corpus_ingestion_preflight_contract_id"] = payload[
        "corpus_ingestion_preflight_contract_id"
    ]
    exception_payload = _rehash(
        exception_payload,
        "repo_corpus_ingestion_exception_register",
        "corpus_ingestion_exception_register_id",
    )
    with pytest.raises(ValueError, match="preflight connector refs must resolve"):
        _validate_reference_bundle_with(
            preflight=RepoCorpusIngestionPreflightContract.model_validate(payload),
            exception_register=RepoCorpusIngestionExceptionRegister.model_validate(
                exception_payload
            ),
        )


def test_v231_bundle_rejects_product_pressure_preflight_readiness() -> None:
    payload = _load_fixture(
        "vnext_plus231",
        "repo_corpus_ingestion_preflight_contract_v231_reference.json",
    )
    payload = deepcopy(payload)
    for row in payload["preflight_rows"]:
        if "product" in row["candidate_ref"]:
            row["preflight_posture"] = "preflight_recorded_for_review_only"
            row["plan_completeness_posture"] = "incomplete_for_review"
            break
    payload = _rehash(
        payload,
        "repo_corpus_ingestion_preflight_contract",
        "corpus_ingestion_preflight_contract_id",
    )
    exception_payload = _load_fixture(
        "vnext_plus231",
        "repo_corpus_ingestion_exception_register_v231_reference.json",
    )
    exception_payload = deepcopy(exception_payload)
    exception_payload["corpus_ingestion_preflight_contract_id"] = payload[
        "corpus_ingestion_preflight_contract_id"
    ]
    exception_payload = _rehash(
        exception_payload,
        "repo_corpus_ingestion_exception_register",
        "corpus_ingestion_exception_register_id",
    )
    with pytest.raises(ValueError, match="product pressure preflight"):
        _validate_reference_bundle_with(
            preflight=RepoCorpusIngestionPreflightContract.model_validate(payload),
            exception_register=RepoCorpusIngestionExceptionRegister.model_validate(
                exception_payload
            ),
        )
