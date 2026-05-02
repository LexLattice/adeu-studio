from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CORPUS_INGESTION_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_CORPUS_INGESTION_REVIEW_SUMMARY_SCHEMA,
    REPO_POST_CORPUS_INGESTION_REVIEW_HANDOFF_SCHEMA,
    RepoConnectorAccessReviewBoundary,
    RepoCorpusDataHandlingAuthorityReview,
    RepoCorpusIngestionExceptionRegister,
    RepoCorpusIngestionNonTransferGuardrail,
    RepoCorpusIngestionPreflightContract,
    RepoCorpusIngestionReviewFamilyCloseoutAlignment,
    RepoCorpusIngestionReviewRequest,
    RepoCorpusIngestionReviewSummary,
    RepoCorpusIngestionSourceIndex,
    RepoPostCorpusIngestionReviewHandoff,
    derive_v82c_corpus_ingestion_review_closeout_bundle,
    derive_v82c_repo_post_corpus_ingestion_review_handoff,
    validate_v82c_corpus_ingestion_review_closeout_bundle,
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


def _rehash(payload: dict[str, Any], surface_name: str, id_field: str) -> dict[str, Any]:
    payload = deepcopy(payload)
    payload[id_field] = _surface_id(surface_name, payload["schema"], payload, id_field)
    return payload


def _v82a_source_index() -> RepoCorpusIngestionSourceIndex:
    return RepoCorpusIngestionSourceIndex.model_validate(
        _load_fixture("vnext_plus230", "repo_corpus_ingestion_source_index_v230_reference.json")
    )


def _v82a_request() -> RepoCorpusIngestionReviewRequest:
    return RepoCorpusIngestionReviewRequest.model_validate(
        _load_fixture("vnext_plus230", "repo_corpus_ingestion_review_request_v230_reference.json")
    )


def _v82a_guardrail() -> RepoCorpusIngestionNonTransferGuardrail:
    return RepoCorpusIngestionNonTransferGuardrail.model_validate(
        _load_fixture(
            "vnext_plus230",
            "repo_corpus_ingestion_non_transfer_guardrail_v230_reference.json",
        )
    )


def _v82b_preflight() -> RepoCorpusIngestionPreflightContract:
    return RepoCorpusIngestionPreflightContract.model_validate(
        _load_fixture(
            "vnext_plus231",
            "repo_corpus_ingestion_preflight_contract_v231_reference.json",
        )
    )


def _v82b_connector_boundary() -> RepoConnectorAccessReviewBoundary:
    return RepoConnectorAccessReviewBoundary.model_validate(
        _load_fixture(
            "vnext_plus231",
            "repo_connector_access_review_boundary_v231_reference.json",
        )
    )


def _v82b_authority_review() -> RepoCorpusDataHandlingAuthorityReview:
    return RepoCorpusDataHandlingAuthorityReview.model_validate(
        _load_fixture(
            "vnext_plus231",
            "repo_corpus_data_handling_authority_review_v231_reference.json",
        )
    )


def _v82b_exception_register() -> RepoCorpusIngestionExceptionRegister:
    return RepoCorpusIngestionExceptionRegister.model_validate(
        _load_fixture(
            "vnext_plus231",
            "repo_corpus_ingestion_exception_register_v231_reference.json",
        )
    )


def _v82c_summary(
    name: str = "repo_corpus_ingestion_review_summary_v232_reference.json",
) -> RepoCorpusIngestionReviewSummary:
    return RepoCorpusIngestionReviewSummary.model_validate(_load_fixture("vnext_plus232", name))


def _v82c_handoff(
    name: str = "repo_post_corpus_ingestion_review_handoff_v232_reference.json",
) -> RepoPostCorpusIngestionReviewHandoff:
    return RepoPostCorpusIngestionReviewHandoff.model_validate(_load_fixture("vnext_plus232", name))


def _v82c_closeout(
    name: str = "repo_corpus_ingestion_review_family_closeout_alignment_v232_reference.json",
) -> RepoCorpusIngestionReviewFamilyCloseoutAlignment:
    return RepoCorpusIngestionReviewFamilyCloseoutAlignment.model_validate(
        _load_fixture("vnext_plus232", name)
    )


def _validate_reference_bundle_with(
    *,
    summary: RepoCorpusIngestionReviewSummary | None = None,
    handoff: RepoPostCorpusIngestionReviewHandoff | None = None,
    closeout: RepoCorpusIngestionReviewFamilyCloseoutAlignment | None = None,
) -> None:
    validate_v82c_corpus_ingestion_review_closeout_bundle(
        corpus_ingestion_source_index=_v82a_source_index(),
        corpus_ingestion_review_request=_v82a_request(),
        corpus_ingestion_non_transfer_guardrail=_v82a_guardrail(),
        corpus_ingestion_preflight_contract=_v82b_preflight(),
        connector_access_review_boundary=_v82b_connector_boundary(),
        corpus_data_handling_authority_review=_v82b_authority_review(),
        corpus_ingestion_exception_register=_v82b_exception_register(),
        corpus_ingestion_review_summary=summary if summary is not None else _v82c_summary(),
        post_corpus_ingestion_review_handoff=handoff if handoff is not None else _v82c_handoff(),
        corpus_ingestion_review_family_closeout_alignment=(
            closeout if closeout is not None else _v82c_closeout()
        ),
    )


def test_v232_reference_bundle_validates() -> None:
    summary = _v82c_summary()
    handoff = _v82c_handoff()
    closeout = _v82c_closeout()

    assert summary.schema == REPO_CORPUS_INGESTION_REVIEW_SUMMARY_SCHEMA
    assert handoff.schema == REPO_POST_CORPUS_INGESTION_REVIEW_HANDOFF_SCHEMA
    assert closeout.schema == REPO_CORPUS_INGESTION_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    assert {row.corpus_ingestion_posture for row in summary.summary_rows} == {
        "no_corpus_ingestion_performed_by_v82"
    }
    assert {row.data_transfer_posture for row in handoff.handoff_rows} == {
        "no_data_transfer_performed_by_v82"
    }
    assert "v83_selection" in closeout.unselected_future_surfaces

    _validate_reference_bundle_with(summary=summary, handoff=handoff, closeout=closeout)


def test_v232_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_corpus_ingestion_review_summary.v1.json").validate(
        _load_fixture("vnext_plus232", "repo_corpus_ingestion_review_summary_v232_reference.json")
    )
    _schema_validator("repo_post_corpus_ingestion_review_handoff.v1.json").validate(
        _load_fixture(
            "vnext_plus232",
            "repo_post_corpus_ingestion_review_handoff_v232_reference.json",
        )
    )
    _schema_validator("repo_corpus_ingestion_review_family_closeout_alignment.v1.json").validate(
        _load_fixture(
            "vnext_plus232",
            "repo_corpus_ingestion_review_family_closeout_alignment_v232_reference.json",
        )
    )


def test_v232_derivation_helper_matches_reference_fixtures() -> None:
    *_, summary, handoff, closeout = derive_v82c_corpus_ingestion_review_closeout_bundle(
        repo_root=_repo_root()
    )

    assert summary.model_dump(mode="json") == _load_fixture(
        "vnext_plus232",
        "repo_corpus_ingestion_review_summary_v232_reference.json",
    )
    assert handoff.model_dump(mode="json") == _load_fixture(
        "vnext_plus232",
        "repo_post_corpus_ingestion_review_handoff_v232_reference.json",
    )
    assert closeout.model_dump(mode="json") == _load_fixture(
        "vnext_plus232",
        "repo_corpus_ingestion_review_family_closeout_alignment_v232_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_corpus_ingestion_v232_reject_summary_ready_missing_preflight.json",
            RepoCorpusIngestionReviewSummary,
            "ready corpus-ingestion summaries require released refs",
        ),
        (
            "repo_corpus_ingestion_v232_reject_summary_warning_with_blocker.json",
            RepoCorpusIngestionReviewSummary,
            "warning-ready summaries cannot carry blockers",
        ),
        (
            "repo_corpus_ingestion_v232_reject_handoff_ready_with_blockers.json",
            RepoPostCorpusIngestionReviewHandoff,
            "ready corpus-ingestion handoffs cannot carry exceptions",
        ),
        (
            "repo_corpus_ingestion_v232_reject_handoff_missing_privacy_authority.json",
            RepoPostCorpusIngestionReviewHandoff,
            "privacy handoffs require authority refs",
        ),
        (
            "repo_corpus_ingestion_v232_reject_closeout_selects_v83.json",
            RepoCorpusIngestionReviewFamilyCloseoutAlignment,
            "must not select V83",
        ),
        (
            "repo_corpus_ingestion_v232_reject_closeout_claims_ingestion.json",
            RepoCorpusIngestionReviewFamilyCloseoutAlignment,
            "must mention no corpus ingestion",
        ),
    ],
)
def test_v232_reject_fixtures_fail_validation(
    fixture_name: str,
    model_type: type[
        RepoCorpusIngestionReviewSummary
        | RepoPostCorpusIngestionReviewHandoff
        | RepoCorpusIngestionReviewFamilyCloseoutAlignment
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus232", fixture_name))


def test_v232_bundle_rejects_unknown_summary_request_ref() -> None:
    summary = RepoCorpusIngestionReviewSummary.model_validate(
        _load_fixture(
            "vnext_plus232",
            "repo_corpus_ingestion_v232_reject_summary_unknown_request_ref.json",
        )
    )
    handoff_payload = _load_fixture(
        "vnext_plus232",
        "repo_post_corpus_ingestion_review_handoff_v232_reference.json",
    )
    handoff_payload["corpus_ingestion_review_summary_id"] = (
        summary.corpus_ingestion_review_summary_id
    )
    handoff_payload = _rehash(
        handoff_payload,
        "repo_post_corpus_ingestion_review_handoff",
        "post_corpus_ingestion_review_handoff_id",
    )
    closeout_payload = _load_fixture(
        "vnext_plus232",
        "repo_corpus_ingestion_review_family_closeout_alignment_v232_reference.json",
    )
    closeout_payload["corpus_ingestion_review_summary_id"] = (
        summary.corpus_ingestion_review_summary_id
    )
    closeout_payload["post_corpus_ingestion_review_handoff_id"] = handoff_payload[
        "post_corpus_ingestion_review_handoff_id"
    ]
    closeout_payload = _rehash(
        closeout_payload,
        "repo_corpus_ingestion_review_family_closeout_alignment",
        "corpus_ingestion_review_family_closeout_alignment_id",
    )

    with pytest.raises(ValueError, match="summary request refs must be known"):
        _validate_reference_bundle_with(
            summary=summary,
            handoff=RepoPostCorpusIngestionReviewHandoff.model_validate(handoff_payload),
            closeout=RepoCorpusIngestionReviewFamilyCloseoutAlignment.model_validate(
                closeout_payload
            ),
        )


def test_v232_bundle_rejects_handoff_guardrail_candidate_mismatch() -> None:
    handoff_payload = _load_fixture(
        "vnext_plus232",
        "repo_post_corpus_ingestion_review_handoff_v232_reference.json",
    )
    handoff_payload["handoff_rows"][0]["guardrail_refs"] = [
        "guardrail:v82a:product-wedge:non-transfer"
    ]
    handoff_payload = _rehash(
        handoff_payload,
        "repo_post_corpus_ingestion_review_handoff",
        "post_corpus_ingestion_review_handoff_id",
    )
    closeout_payload = _load_fixture(
        "vnext_plus232",
        "repo_corpus_ingestion_review_family_closeout_alignment_v232_reference.json",
    )
    closeout_payload["post_corpus_ingestion_review_handoff_id"] = handoff_payload[
        "post_corpus_ingestion_review_handoff_id"
    ]
    closeout_payload = _rehash(
        closeout_payload,
        "repo_corpus_ingestion_review_family_closeout_alignment",
        "corpus_ingestion_review_family_closeout_alignment_id",
    )

    with pytest.raises(ValueError, match="handoff guardrail refs must match candidate"):
        _validate_reference_bundle_with(
            handoff=RepoPostCorpusIngestionReviewHandoff.model_validate(handoff_payload),
            closeout=RepoCorpusIngestionReviewFamilyCloseoutAlignment.model_validate(
                closeout_payload
            ),
        )


def test_v232_handoff_derivation_rejects_unknown_summary_authority_ref() -> None:
    summary_payload = _load_fixture(
        "vnext_plus232",
        "repo_corpus_ingestion_review_summary_v232_reference.json",
    )
    summary_payload["summary_rows"][0]["authority_review_refs"].append(
        "authority-review:v82b:missing"
    )
    summary_payload["summary_rows"][0]["authority_review_refs"].sort()
    summary_payload = _rehash(
        summary_payload,
        "repo_corpus_ingestion_review_summary",
        "corpus_ingestion_review_summary_id",
    )
    summary = RepoCorpusIngestionReviewSummary.model_validate(summary_payload)

    with pytest.raises(
        ValueError,
        match="V82-C handoff derivation requires known summary authority refs",
    ):
        derive_v82c_repo_post_corpus_ingestion_review_handoff(
            repo_root=_repo_root(),
            corpus_ingestion_source_index=_v82a_source_index(),
            corpus_ingestion_review_request=_v82a_request(),
            corpus_ingestion_non_transfer_guardrail=_v82a_guardrail(),
            corpus_ingestion_preflight_contract=_v82b_preflight(),
            connector_access_review_boundary=_v82b_connector_boundary(),
            corpus_data_handling_authority_review=_v82b_authority_review(),
            corpus_ingestion_exception_register=_v82b_exception_register(),
            corpus_ingestion_review_summary=summary,
        )
