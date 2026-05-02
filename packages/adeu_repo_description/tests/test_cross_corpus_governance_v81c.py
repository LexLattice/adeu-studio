from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CROSS_CORPUS_GOVERNANCE_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_CROSS_CORPUS_GOVERNANCE_SUMMARY_SCHEMA,
    REPO_POST_CROSS_CORPUS_REVIEW_HANDOFF_SCHEMA,
    RepoCorpusBoundaryContract,
    RepoCrossCorpusAuthorityGapRegister,
    RepoCrossCorpusExceptionRegister,
    RepoCrossCorpusGovernanceFamilyCloseoutAlignment,
    RepoCrossCorpusGovernanceRequest,
    RepoCrossCorpusGovernanceSummary,
    RepoCrossCorpusNonIngestionGuardrail,
    RepoCrossCorpusSourceIndex,
    RepoImportedSubstrateProvenanceRegister,
    RepoPostCrossCorpusReviewHandoff,
    derive_v81c_cross_corpus_governance_closeout_bundle,
    validate_v81c_cross_corpus_governance_closeout_bundle,
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


def _v81a_source_index() -> RepoCrossCorpusSourceIndex:
    return RepoCrossCorpusSourceIndex.model_validate(
        _load_fixture("vnext_plus227", "repo_cross_corpus_source_index_v227_reference.json")
    )


def _v81a_request() -> RepoCrossCorpusGovernanceRequest:
    return RepoCrossCorpusGovernanceRequest.model_validate(
        _load_fixture(
            "vnext_plus227",
            "repo_cross_corpus_governance_request_v227_reference.json",
        )
    )


def _v81a_guardrail() -> RepoCrossCorpusNonIngestionGuardrail:
    return RepoCrossCorpusNonIngestionGuardrail.model_validate(
        _load_fixture(
            "vnext_plus227",
            "repo_cross_corpus_non_ingestion_guardrail_v227_reference.json",
        )
    )


def _boundary() -> RepoCorpusBoundaryContract:
    return RepoCorpusBoundaryContract.model_validate(
        _load_fixture("vnext_plus228", "repo_corpus_boundary_contract_v228_reference.json")
    )


def _provenance() -> RepoImportedSubstrateProvenanceRegister:
    return RepoImportedSubstrateProvenanceRegister.model_validate(
        _load_fixture(
            "vnext_plus228",
            "repo_imported_substrate_provenance_register_v228_reference.json",
        )
    )


def _authority_gap() -> RepoCrossCorpusAuthorityGapRegister:
    return RepoCrossCorpusAuthorityGapRegister.model_validate(
        _load_fixture(
            "vnext_plus228",
            "repo_cross_corpus_authority_gap_register_v228_reference.json",
        )
    )


def _exception_register() -> RepoCrossCorpusExceptionRegister:
    return RepoCrossCorpusExceptionRegister.model_validate(
        _load_fixture("vnext_plus228", "repo_cross_corpus_exception_register_v228_reference.json")
    )


def _summary(
    name: str = "repo_cross_corpus_governance_summary_v229_reference.json",
) -> RepoCrossCorpusGovernanceSummary:
    return RepoCrossCorpusGovernanceSummary.model_validate(_load_fixture("vnext_plus229", name))


def _handoff(
    name: str = "repo_post_cross_corpus_review_handoff_v229_reference.json",
) -> RepoPostCrossCorpusReviewHandoff:
    return RepoPostCrossCorpusReviewHandoff.model_validate(_load_fixture("vnext_plus229", name))


def _closeout(
    name: str = "repo_cross_corpus_governance_family_closeout_alignment_v229_reference.json",
) -> RepoCrossCorpusGovernanceFamilyCloseoutAlignment:
    return RepoCrossCorpusGovernanceFamilyCloseoutAlignment.model_validate(
        _load_fixture("vnext_plus229", name)
    )


def _validate_reference_bundle_with(
    *,
    summary: RepoCrossCorpusGovernanceSummary | None = None,
    handoff: RepoPostCrossCorpusReviewHandoff | None = None,
    closeout: RepoCrossCorpusGovernanceFamilyCloseoutAlignment | None = None,
) -> None:
    resolved_summary = summary or _summary()
    resolved_handoff = handoff or _handoff()
    resolved_closeout = closeout or _closeout()
    if summary is not None and handoff is None:
        resolved_handoff = resolved_handoff.model_copy(
            update={
                "cross_corpus_governance_summary_id": (
                    resolved_summary.cross_corpus_governance_summary_id
                )
            }
        )
    if (summary is not None or handoff is not None) and closeout is None:
        resolved_closeout = resolved_closeout.model_copy(
            update={
                "cross_corpus_governance_summary_id": (
                    resolved_summary.cross_corpus_governance_summary_id
                ),
                "post_cross_corpus_review_handoff_id": (
                    resolved_handoff.post_cross_corpus_review_handoff_id
                ),
            }
        )
    validate_v81c_cross_corpus_governance_closeout_bundle(
        cross_corpus_source_index=_v81a_source_index(),
        cross_corpus_governance_request=_v81a_request(),
        cross_corpus_non_ingestion_guardrail=_v81a_guardrail(),
        corpus_boundary_contract=_boundary(),
        imported_substrate_provenance_register=_provenance(),
        cross_corpus_authority_gap_register=_authority_gap(),
        cross_corpus_exception_register=_exception_register(),
        cross_corpus_governance_summary=resolved_summary,
        post_cross_corpus_review_handoff=resolved_handoff,
        cross_corpus_governance_family_closeout_alignment=resolved_closeout,
    )


def test_v229_reference_bundle_validates() -> None:
    summary = _summary()
    handoff = _handoff()
    closeout = _closeout()

    assert summary.schema == REPO_CROSS_CORPUS_GOVERNANCE_SUMMARY_SCHEMA
    assert handoff.schema == REPO_POST_CROSS_CORPUS_REVIEW_HANDOFF_SCHEMA
    assert closeout.schema == REPO_CROSS_CORPUS_GOVERNANCE_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    assert {row.corpus_ingestion_posture for row in summary.summary_rows} == {
        "no_corpus_ingestion_performed_by_v81"
    }
    assert {row.connector_activation_posture for row in handoff.handoff_rows} == {
        "no_connector_activation_performed_by_v81"
    }
    assert "v82_selection" in closeout.unselected_future_surfaces

    _validate_reference_bundle_with(summary=summary, handoff=handoff, closeout=closeout)


def test_v229_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_cross_corpus_governance_summary.v1.json").validate(
        _load_fixture("vnext_plus229", "repo_cross_corpus_governance_summary_v229_reference.json")
    )
    _schema_validator("repo_post_cross_corpus_review_handoff.v1.json").validate(
        _load_fixture("vnext_plus229", "repo_post_cross_corpus_review_handoff_v229_reference.json")
    )
    _schema_validator(
        "repo_cross_corpus_governance_family_closeout_alignment.v1.json"
    ).validate(
        _load_fixture(
            "vnext_plus229",
            "repo_cross_corpus_governance_family_closeout_alignment_v229_reference.json",
        )
    )


def test_v229_derivation_helper_matches_reference_fixtures() -> None:
    (*_, summary, handoff, closeout) = derive_v81c_cross_corpus_governance_closeout_bundle(
        repo_root=_repo_root()
    )

    assert summary.model_dump(mode="json") == _load_fixture(
        "vnext_plus229",
        "repo_cross_corpus_governance_summary_v229_reference.json",
    )
    assert handoff.model_dump(mode="json") == _load_fixture(
        "vnext_plus229",
        "repo_post_cross_corpus_review_handoff_v229_reference.json",
    )
    assert closeout.model_dump(mode="json") == _load_fixture(
        "vnext_plus229",
        "repo_cross_corpus_governance_family_closeout_alignment_v229_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_cross_corpus_governance_v229_reject_summary_ingests_corpus.json",
            RepoCrossCorpusGovernanceSummary,
            "V81-C summaries must not ingest corpora",
        ),
        (
            "repo_cross_corpus_governance_v229_reject_ready_summary_missing_boundary.json",
            RepoCrossCorpusGovernanceSummary,
            "ready cross-corpus summaries require released refs",
        ),
        (
            "repo_cross_corpus_governance_v229_reject_handoff_executes_adjudication.json",
            RepoPostCrossCorpusReviewHandoff,
            "V81-C handoffs must not execute cross-corpus adjudication",
        ),
        (
            "repo_cross_corpus_governance_v229_reject_handoff_ready_with_blocker.json",
            RepoPostCrossCorpusReviewHandoff,
            "ready handoffs cannot carry exceptions",
        ),
        (
            "repo_cross_corpus_governance_v229_reject_corpus_ingestion_handoff_missing_authority.json",
            RepoPostCrossCorpusReviewHandoff,
            "privacy handoffs require authority refs",
        ),
        (
            "repo_cross_corpus_governance_v229_reject_product_handoff_missing_authority.json",
            RepoPostCrossCorpusReviewHandoff,
            "product handoffs require authority refs",
        ),
        (
            "repo_cross_corpus_governance_v229_reject_closeout_selects_v82.json",
            RepoCrossCorpusGovernanceFamilyCloseoutAlignment,
            "cross-corpus closeout must not select V82",
        ),
        (
            "repo_cross_corpus_governance_v229_reject_closeout_claims_graph_memory.json",
            RepoCrossCorpusGovernanceFamilyCloseoutAlignment,
            "may not carry cross-corpus action authority",
        ),
    ],
)
def test_v229_reject_fixtures_fail_model_validation(
    fixture_name: str,
    model_type: type[
        RepoCrossCorpusGovernanceSummary
        | RepoPostCrossCorpusReviewHandoff
        | RepoCrossCorpusGovernanceFamilyCloseoutAlignment
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus229", fixture_name))


def test_v229_bundle_rejects_unknown_summary_request_ref() -> None:
    summary = _summary()
    summary_row = summary.summary_rows[0].model_copy(
        update={"request_refs": ["cross-corpus-governance:v81a:unknown"]}
    )
    summary = summary.model_copy(
        update={"summary_rows": [summary_row, *summary.summary_rows[1:]]}
    )

    with pytest.raises(ValueError, match="summary request refs must be known"):
        _validate_reference_bundle_with(summary=summary)


def test_v229_bundle_rejects_summary_missing_request_candidate() -> None:
    summary = _summary().model_copy(update={"summary_rows": _summary().summary_rows[:1]})

    with pytest.raises(ValueError, match="summary must cover all request candidates"):
        _validate_reference_bundle_with(summary=summary)


def test_v229_bundle_rejects_warning_ready_with_blocking_exception() -> None:
    summary = _summary(
        "repo_cross_corpus_governance_v229_reject_warning_ready_carries_blocking_exception.json"
    )

    with pytest.raises(
        ValueError,
        match="ready cross-corpus summaries cannot hide blocking exceptions",
    ):
        _validate_reference_bundle_with(summary=summary)


def test_v229_bundle_rejects_handoff_missing_request_candidate() -> None:
    handoff = _handoff().model_copy(update={"handoff_rows": _handoff().handoff_rows[:1]})

    with pytest.raises(ValueError, match="handoff must cover all request candidates"):
        _validate_reference_bundle_with(handoff=handoff)


def test_v229_bundle_rejects_unknown_handoff_boundary_ref() -> None:
    handoff = _handoff()
    handoff_row = handoff.handoff_rows[0].model_copy(
        update={"boundary_contract_refs": ["corpus-boundary:v81b:unknown"]}
    )
    handoff = handoff.model_copy(
        update={"handoff_rows": [handoff_row, *handoff.handoff_rows[1:]]}
    )

    with pytest.raises(ValueError, match="handoff boundary refs must be known"):
        _validate_reference_bundle_with(handoff=handoff)


def test_v229_bundle_rejects_closeout_unknown_summary_ref() -> None:
    closeout = _closeout().model_copy(
        update={"cross_corpus_governance_summary_id": "repo_cross_corpus_summary:wrong"}
    )

    with pytest.raises(ValueError, match="V81-C closeout must reference released summary"):
        _validate_reference_bundle_with(closeout=closeout)
