from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CROSS_CORPUS_GOVERNANCE_REQUEST_SCHEMA,
    REPO_CROSS_CORPUS_NON_INGESTION_GUARDRAIL_SCHEMA,
    REPO_CROSS_CORPUS_SOURCE_INDEX_SCHEMA,
    RepoCrossCorpusGovernanceRequest,
    RepoCrossCorpusNonIngestionGuardrail,
    RepoCrossCorpusSourceIndex,
    derive_v81a_cross_corpus_governance_bundle,
    validate_v81a_cross_corpus_governance_bundle,
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


def _v81a_source_index(
    name: str = "repo_cross_corpus_source_index_v227_reference.json",
) -> RepoCrossCorpusSourceIndex:
    return RepoCrossCorpusSourceIndex.model_validate(_load_fixture("vnext_plus227", name))


def _v81a_request(
    name: str = "repo_cross_corpus_governance_request_v227_reference.json",
) -> RepoCrossCorpusGovernanceRequest:
    return RepoCrossCorpusGovernanceRequest.model_validate(_load_fixture("vnext_plus227", name))


def _v81a_guardrail(
    name: str = "repo_cross_corpus_non_ingestion_guardrail_v227_reference.json",
) -> RepoCrossCorpusNonIngestionGuardrail:
    return RepoCrossCorpusNonIngestionGuardrail.model_validate(
        _load_fixture("vnext_plus227", name)
    )


def _validate_reference_bundle_with(
    *,
    source_index: RepoCrossCorpusSourceIndex | None = None,
    request: RepoCrossCorpusGovernanceRequest | None = None,
    guardrail: RepoCrossCorpusNonIngestionGuardrail | None = None,
) -> None:
    validate_v81a_cross_corpus_governance_bundle(
        cross_corpus_source_index=(
            source_index if source_index is not None else _v81a_source_index()
        ),
        cross_corpus_governance_request=request if request is not None else _v81a_request(),
        cross_corpus_non_ingestion_guardrail=(
            guardrail if guardrail is not None else _v81a_guardrail()
        ),
    )


def test_v227_reference_bundle_validates() -> None:
    source_index = _v81a_source_index()
    request = _v81a_request()
    guardrail = _v81a_guardrail()

    assert source_index.schema == REPO_CROSS_CORPUS_SOURCE_INDEX_SCHEMA
    assert request.schema == REPO_CROSS_CORPUS_GOVERNANCE_REQUEST_SCHEMA
    assert guardrail.schema == REPO_CROSS_CORPUS_NON_INGESTION_GUARDRAIL_SCHEMA
    assert {row.corpus_review_posture for row in request.request_rows} == {
        "blocked_by_missing_corpus_source",
        "blocked_by_product_authority_gap",
    }
    assert {row.corpus_source_currentness for row in request.request_rows} == {
        "explicit_absence_marker"
    }
    assert {row.corpus_ingestion_posture for row in request.request_rows} == {
        "no_corpus_ingestion_performed_by_v81"
    }
    assert {row.connector_activation_posture for row in request.request_rows} == {
        "no_connector_activation_performed_by_v81"
    }
    assert {row.external_endpoint_access_posture for row in request.request_rows} == {
        "no_endpoint_access_performed_by_v81"
    }
    assert {row.adjudication_execution_posture for row in request.request_rows} == {
        "no_cross_corpus_adjudication_performed_by_v81"
    }
    assert all(not hasattr(row, "corpus_boundary_contract_refs") for row in request.request_rows)

    _validate_reference_bundle_with(
        source_index=source_index,
        request=request,
        guardrail=guardrail,
    )


def test_v227_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_cross_corpus_source_index.v1.json").validate(
        _load_fixture("vnext_plus227", "repo_cross_corpus_source_index_v227_reference.json")
    )
    _schema_validator("repo_cross_corpus_governance_request.v1.json").validate(
        _load_fixture(
            "vnext_plus227",
            "repo_cross_corpus_governance_request_v227_reference.json",
        )
    )
    _schema_validator("repo_cross_corpus_non_ingestion_guardrail.v1.json").validate(
        _load_fixture(
            "vnext_plus227",
            "repo_cross_corpus_non_ingestion_guardrail_v227_reference.json",
        )
    )


def test_v227_derivation_helper_matches_reference_fixtures() -> None:
    source_index, request, guardrail = derive_v81a_cross_corpus_governance_bundle(
        repo_root=_repo_root()
    )

    assert source_index.model_dump(mode="json") == _load_fixture(
        "vnext_plus227",
        "repo_cross_corpus_source_index_v227_reference.json",
    )
    assert request.model_dump(mode="json") == _load_fixture(
        "vnext_plus227",
        "repo_cross_corpus_governance_request_v227_reference.json",
    )
    assert guardrail.model_dump(mode="json") == _load_fixture(
        "vnext_plus227",
        "repo_cross_corpus_non_ingestion_guardrail_v227_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_cross_corpus_governance_v227_reject_missing_source_without_absence_posture.json",
            RepoCrossCorpusSourceIndex,
            "non-absence cross-corpus source rows must be present",
        ),
        (
            "repo_cross_corpus_governance_v227_reject_request_without_source_refs.json",
            RepoCrossCorpusGovernanceRequest,
            "at least 1 item",
        ),
        (
            "repo_cross_corpus_governance_v227_reject_customer_without_privacy_license_authority.json",
            RepoCrossCorpusGovernanceRequest,
            "customer corpus rows require privacy, license, and authority",
        ),
        (
            "repo_cross_corpus_governance_v227_reject_benchmark_truth_claim.json",
            RepoCrossCorpusGovernanceRequest,
            "may not carry cross-corpus action authority",
        ),
        (
            "repo_cross_corpus_governance_v227_reject_connector_activation_claim.json",
            RepoCrossCorpusGovernanceRequest,
            "V81-A request rows must not activate connectors",
        ),
        (
            "repo_cross_corpus_governance_v227_reject_future_surface_refs.json",
            RepoCrossCorpusGovernanceRequest,
            "Extra inputs are not permitted",
        ),
        (
            "repo_cross_corpus_governance_v227_reject_product_pressure_eligible.json",
            RepoCrossCorpusGovernanceRequest,
            "product pressure must remain blocked in V81-A",
        ),
        (
            "repo_cross_corpus_governance_v227_reject_empty_forbidden_data_actions.json",
            RepoCrossCorpusNonIngestionGuardrail,
            "at least 1 item",
        ),
        (
            "repo_cross_corpus_governance_v227_reject_empty_forbidden_connector_actions.json",
            RepoCrossCorpusNonIngestionGuardrail,
            "at least 1 item",
        ),
        (
            "repo_cross_corpus_governance_v227_reject_empty_forbidden_downstream_authority.json",
            RepoCrossCorpusNonIngestionGuardrail,
            "at least 1 item",
        ),
    ],
)
def test_v227_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoCrossCorpusSourceIndex
        | RepoCrossCorpusGovernanceRequest
        | RepoCrossCorpusNonIngestionGuardrail
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus227", fixture_name))


def test_v227_bundle_rejects_support_only_eligibility_sources() -> None:
    request = _v81a_request(
        "repo_cross_corpus_governance_v227_reject_support_only_eligibility.json"
    )
    guardrail = _v81a_guardrail(
        "repo_cross_corpus_governance_v227_reject_support_only_eligibility_guardrail.json"
    )

    with pytest.raises(
        ValueError,
        match="eligible cross-corpus requests require released V80-C sources",
    ):
        _validate_reference_bundle_with(request=request, guardrail=guardrail)


def test_v227_bundle_rejects_cross_snapshot_guardrail_mix() -> None:
    guardrail = _v81a_guardrail().model_copy(
        update={"snapshot_id": "vNext+000-unrelated-cross-corpus-snapshot"}
    )

    with pytest.raises(
        ValueError,
        match="cross-corpus guardrail provenance must match request",
    ):
        _validate_reference_bundle_with(guardrail=guardrail)


def test_v227_bundle_rejects_explicit_absence_as_eligibility() -> None:
    request = _v81a_request(
        "repo_cross_corpus_governance_v227_reject_absence_only_eligibility.json"
    )
    guardrail = _v81a_guardrail(
        "repo_cross_corpus_governance_v227_reject_absence_only_eligibility_guardrail.json"
    )

    with pytest.raises(
        ValueError,
        match="eligible cross-corpus requests require concrete corpus source",
    ):
        _validate_reference_bundle_with(request=request, guardrail=guardrail)
