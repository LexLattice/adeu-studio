from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CORPUS_INGESTION_NON_TRANSFER_GUARDRAIL_SCHEMA,
    REPO_CORPUS_INGESTION_REVIEW_REQUEST_SCHEMA,
    REPO_CORPUS_INGESTION_SOURCE_INDEX_SCHEMA,
    RepoCorpusIngestionNonTransferGuardrail,
    RepoCorpusIngestionReviewRequest,
    RepoCorpusIngestionReviewRequestRow,
    RepoCorpusIngestionSourceIndex,
    derive_v82a_corpus_ingestion_review_bundle,
    validate_v82a_corpus_ingestion_review_bundle,
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


def _v82a_source_index(
    name: str = "repo_corpus_ingestion_source_index_v230_reference.json",
) -> RepoCorpusIngestionSourceIndex:
    return RepoCorpusIngestionSourceIndex.model_validate(_load_fixture("vnext_plus230", name))


def _v82a_request(
    name: str = "repo_corpus_ingestion_review_request_v230_reference.json",
) -> RepoCorpusIngestionReviewRequest:
    return RepoCorpusIngestionReviewRequest.model_validate(_load_fixture("vnext_plus230", name))


def _v82a_guardrail(
    name: str = "repo_corpus_ingestion_non_transfer_guardrail_v230_reference.json",
) -> RepoCorpusIngestionNonTransferGuardrail:
    return RepoCorpusIngestionNonTransferGuardrail.model_validate(
        _load_fixture("vnext_plus230", name)
    )


def _validate_reference_bundle_with(
    *,
    source_index: RepoCorpusIngestionSourceIndex | None = None,
    request: RepoCorpusIngestionReviewRequest | None = None,
    guardrail: RepoCorpusIngestionNonTransferGuardrail | None = None,
) -> None:
    validate_v82a_corpus_ingestion_review_bundle(
        corpus_ingestion_source_index=(
            source_index if source_index is not None else _v82a_source_index()
        ),
        corpus_ingestion_review_request=request if request is not None else _v82a_request(),
        corpus_ingestion_non_transfer_guardrail=(
            guardrail if guardrail is not None else _v82a_guardrail()
        ),
    )


def test_v230_reference_bundle_validates() -> None:
    source_index = _v82a_source_index()
    request = _v82a_request()
    guardrail = _v82a_guardrail()

    assert source_index.schema == REPO_CORPUS_INGESTION_SOURCE_INDEX_SCHEMA
    assert request.schema == REPO_CORPUS_INGESTION_REVIEW_REQUEST_SCHEMA
    assert guardrail.schema == REPO_CORPUS_INGESTION_NON_TRANSFER_GUARDRAIL_SCHEMA
    assert {row.ingestion_review_posture for row in request.request_rows} == {
        "blocked_by_missing_corpus_source",
        "blocked_by_product_authority_gap",
    }
    assert {row.corpus_source_currentness for row in request.request_rows} == {
        "explicit_absence_marker"
    }
    assert {row.corpus_ingestion_posture for row in request.request_rows} == {
        "no_corpus_ingestion_performed_by_v82"
    }
    assert {row.data_transfer_posture for row in request.request_rows} == {
        "no_data_transfer_performed_by_v82"
    }
    assert {row.customer_data_handling_posture for row in request.request_rows} == {
        "no_customer_data_handling_performed_by_v82"
    }
    assert {row.connector_activation_posture for row in request.request_rows} == {
        "no_connector_activation_performed_by_v82"
    }
    assert {row.endpoint_access_posture for row in request.request_rows} == {
        "no_endpoint_access_performed_by_v82"
    }
    assert {row.adjudication_execution_posture for row in request.request_rows} == {
        "no_cross_corpus_adjudication_performed_by_v82"
    }
    assert all(
        not hasattr(row, "corpus_ingestion_preflight_contract_refs") for row in request.request_rows
    )

    _validate_reference_bundle_with(
        source_index=source_index,
        request=request,
        guardrail=guardrail,
    )


def test_v230_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_corpus_ingestion_source_index.v1.json").validate(
        _load_fixture("vnext_plus230", "repo_corpus_ingestion_source_index_v230_reference.json")
    )
    _schema_validator("repo_corpus_ingestion_review_request.v1.json").validate(
        _load_fixture(
            "vnext_plus230",
            "repo_corpus_ingestion_review_request_v230_reference.json",
        )
    )
    _schema_validator("repo_corpus_ingestion_non_transfer_guardrail.v1.json").validate(
        _load_fixture(
            "vnext_plus230",
            "repo_corpus_ingestion_non_transfer_guardrail_v230_reference.json",
        )
    )


def test_v230_derivation_helper_matches_reference_fixtures() -> None:
    source_index, request, guardrail = derive_v82a_corpus_ingestion_review_bundle(
        repo_root=_repo_root()
    )

    assert source_index.model_dump(mode="json") == _load_fixture(
        "vnext_plus230",
        "repo_corpus_ingestion_source_index_v230_reference.json",
    )
    assert request.model_dump(mode="json") == _load_fixture(
        "vnext_plus230",
        "repo_corpus_ingestion_review_request_v230_reference.json",
    )
    assert guardrail.model_dump(mode="json") == _load_fixture(
        "vnext_plus230",
        "repo_corpus_ingestion_non_transfer_guardrail_v230_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_corpus_ingestion_v230_reject_missing_source_without_absence_posture.json",
            RepoCorpusIngestionSourceIndex,
            "non-absence corpus-ingestion source rows must be present",
        ),
        (
            "repo_corpus_ingestion_v230_reject_request_without_source_refs.json",
            RepoCorpusIngestionReviewRequest,
            "at least 1 item",
        ),
        (
            "repo_corpus_ingestion_v230_reject_connector_activation_claim.json",
            RepoCorpusIngestionReviewRequest,
            "V82-A request rows must not activate connectors",
        ),
        (
            "repo_corpus_ingestion_v230_reject_endpoint_access_claim.json",
            RepoCorpusIngestionReviewRequest,
            "V82-A request rows must not access endpoints",
        ),
        (
            "repo_corpus_ingestion_v230_reject_future_surface_refs.json",
            RepoCorpusIngestionReviewRequest,
            "Extra inputs are not permitted",
        ),
        (
            "repo_corpus_ingestion_v230_reject_product_pressure_eligible.json",
            RepoCorpusIngestionReviewRequest,
            "product pressure must remain blocked in V82-A",
        ),
        (
            "repo_corpus_ingestion_v230_reject_empty_forbidden_ingestion_actions.json",
            RepoCorpusIngestionNonTransferGuardrail,
            "at least 1 item",
        ),
        (
            "repo_corpus_ingestion_v230_reject_empty_forbidden_transfer_actions.json",
            RepoCorpusIngestionNonTransferGuardrail,
            "at least 1 item",
        ),
        (
            "repo_corpus_ingestion_v230_reject_empty_forbidden_connector_actions.json",
            RepoCorpusIngestionNonTransferGuardrail,
            "at least 1 item",
        ),
        (
            "repo_corpus_ingestion_v230_reject_empty_forbidden_endpoint_actions.json",
            RepoCorpusIngestionNonTransferGuardrail,
            "at least 1 item",
        ),
        (
            "repo_corpus_ingestion_v230_reject_empty_forbidden_downstream_authority.json",
            RepoCorpusIngestionNonTransferGuardrail,
            "at least 1 item",
        ),
    ],
)
def test_v230_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoCorpusIngestionSourceIndex
        | RepoCorpusIngestionReviewRequest
        | RepoCorpusIngestionNonTransferGuardrail
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus230", fixture_name))


def test_v230_bundle_rejects_support_only_eligibility_sources() -> None:
    request = _v82a_request("repo_corpus_ingestion_v230_reject_support_only_eligibility.json")
    guardrail = _v82a_guardrail(
        "repo_corpus_ingestion_v230_reject_support_only_eligibility_guardrail.json"
    )

    with pytest.raises(
        ValueError,
        match="eligible corpus-ingestion requests require released V81-C sources",
    ):
        _validate_reference_bundle_with(request=request, guardrail=guardrail)


def test_v230_bundle_rejects_descriptor_only_eligibility_sources() -> None:
    request = _v82a_request("repo_corpus_ingestion_v230_reject_descriptor_only_eligibility.json")
    guardrail = _v82a_guardrail(
        "repo_corpus_ingestion_v230_reject_descriptor_only_eligibility_guardrail.json"
    )

    with pytest.raises(
        ValueError,
        match="eligible corpus-ingestion requests require concrete corpus source",
    ):
        _validate_reference_bundle_with(request=request, guardrail=guardrail)


def test_v230_bundle_rejects_required_later_authority_future_ref() -> None:
    guardrail = _v82a_guardrail(
        "repo_corpus_ingestion_v230_reject_required_later_authority_future_ref.json"
    )

    with pytest.raises(
        ValueError,
        match="same-row authority requirements",
    ):
        _validate_reference_bundle_with(guardrail=guardrail)


def test_v230_bundle_rejects_required_later_authority_source_refs() -> None:
    payload = _load_fixture(
        "vnext_plus230",
        "repo_corpus_ingestion_non_transfer_guardrail_v230_reference.json",
    )
    payload["guardrail_rows"][0]["required_later_authority_refs"] = [
        "product-authority:corpus-ingestion:current:absent"
    ]
    payload["corpus_ingestion_non_transfer_guardrail_id"] = _surface_id(
        "repo_corpus_ingestion_non_transfer_guardrail",
        payload["schema"],
        payload,
        "corpus_ingestion_non_transfer_guardrail_id",
    )
    guardrail = RepoCorpusIngestionNonTransferGuardrail.model_validate(payload)

    with pytest.raises(
        ValueError,
        match="same-row authority requirements",
    ):
        _validate_reference_bundle_with(guardrail=guardrail)


@pytest.mark.parametrize(
    "limitation_note",
    [
        "Corpus ingestion is performed by V82.",
        "Data transfer is now available in V82.",
        "Customer data handling is now available in V82.",
        "Connector activation proceeds in V82.",
        "Endpoint access proceeds in V82.",
        "Cross-corpus adjudication execution proceeds in V82.",
        "Product authorization is now available in V82.",
        "Release follows from this row.",
        "V83 selection follows from this row.",
    ],
)
def test_v230_request_rows_reject_action_claim_noun_forms(limitation_note: str) -> None:
    row_payload = _load_fixture(
        "vnext_plus230",
        "repo_corpus_ingestion_review_request_v230_reference.json",
    )["request_rows"][0]
    row_payload["limitation_note"] = limitation_note

    with pytest.raises(ValidationError, match="corpus-ingestion action authority"):
        RepoCorpusIngestionReviewRequestRow.model_validate(row_payload)


def test_v230_request_rows_allow_negated_action_noun_forms() -> None:
    row_payload = _load_fixture(
        "vnext_plus230",
        "repo_corpus_ingestion_review_request_v230_reference.json",
    )["request_rows"][0]
    row_payload["limitation_note"] = (
        "This row preserves no corpus ingestion, no data transfer, no customer data "
        "handling, no connector activation, no endpoint access, no cross-corpus "
        "adjudication execution, no product authorization, no release, and no V83 "
        "selection."
    )

    RepoCorpusIngestionReviewRequestRow.model_validate(row_payload)


def test_v230_bundle_rejects_cross_snapshot_guardrail_mix() -> None:
    guardrail = _v82a_guardrail().model_copy(
        update={"snapshot_id": "vNext+000-unrelated-corpus-ingestion-snapshot"}
    )

    with pytest.raises(
        ValueError,
        match="corpus-ingestion guardrail provenance must match request",
    ):
        _validate_reference_bundle_with(guardrail=guardrail)
