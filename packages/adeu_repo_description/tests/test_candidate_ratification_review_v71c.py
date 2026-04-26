from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CANDIDATE_RATIFICATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_POST_RATIFICATION_HANDOFF_SCHEMA,
    REPO_RATIFICATION_AMENDMENT_SCOPE_BOUNDARY_SCHEMA,
    RepoCandidateRatificationFamilyCloseoutAlignment,
    RepoCandidateRatificationRecord,
    RepoPostRatificationHandoff,
    RepoRatificationAmendmentScopeBoundary,
    RepoRatificationDissentRegister,
    RepoReviewSettlementRecord,
    derive_v71c_repo_candidate_ratification_closeout_bundle,
    validate_v71c_candidate_ratification_closeout_bundle,
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


def _v71b_ratification() -> RepoCandidateRatificationRecord:
    return RepoCandidateRatificationRecord.model_validate(
        _load_fixture("vnext_plus198", "repo_candidate_ratification_record_v198_reference.json")
    )


def _v71b_settlement() -> RepoReviewSettlementRecord:
    return RepoReviewSettlementRecord.model_validate(
        _load_fixture("vnext_plus198", "repo_review_settlement_record_v198_reference.json")
    )


def _v71b_dissent() -> RepoRatificationDissentRegister:
    return RepoRatificationDissentRegister.model_validate(
        _load_fixture("vnext_plus198", "repo_ratification_dissent_register_v198_reference.json")
    )


def _v71c_amendment_scope() -> RepoRatificationAmendmentScopeBoundary:
    return RepoRatificationAmendmentScopeBoundary.model_validate(
        _load_fixture(
            "vnext_plus199",
            "repo_ratification_amendment_scope_boundary_v199_reference.json",
        )
    )


def _v71c_handoff() -> RepoPostRatificationHandoff:
    return RepoPostRatificationHandoff.model_validate(
        _load_fixture("vnext_plus199", "repo_post_ratification_handoff_v199_reference.json")
    )


def _v71c_closeout() -> RepoCandidateRatificationFamilyCloseoutAlignment:
    return RepoCandidateRatificationFamilyCloseoutAlignment.model_validate(
        _load_fixture(
            "vnext_plus199",
            "repo_candidate_ratification_family_closeout_alignment_v199_reference.json",
        )
    )


def test_v199_reference_bundle_validates() -> None:
    amendment_scope = _v71c_amendment_scope()
    handoff = _v71c_handoff()
    closeout = _v71c_closeout()

    assert amendment_scope.schema == REPO_RATIFICATION_AMENDMENT_SCOPE_BOUNDARY_SCHEMA
    assert handoff.schema == REPO_POST_RATIFICATION_HANDOFF_SCHEMA
    assert closeout.schema == REPO_CANDIDATE_RATIFICATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    assert {row.handoff_posture for row in handoff.handoff_rows} == {
        "blocked_by_dissent",
        "deferred_to_future_family",
        "ready_for_v72_review",
    }
    assert not any(
        row.candidate_ref == "candidate:internal:typed_adjudication_product_wedge"
        and row.handoff_target == "v72_contained_integration_review"
        for row in handoff.handoff_rows
    )

    validate_v71c_candidate_ratification_closeout_bundle(
        ratification_record=_v71b_ratification(),
        settlement_record=_v71b_settlement(),
        dissent_register=_v71b_dissent(),
        amendment_scope_boundary=amendment_scope,
        post_ratification_handoff=handoff,
        family_closeout_alignment=closeout,
    )


def test_v199_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_ratification_amendment_scope_boundary.v1.json").validate(
        _load_fixture(
            "vnext_plus199",
            "repo_ratification_amendment_scope_boundary_v199_reference.json",
        )
    )
    _schema_validator("repo_post_ratification_handoff.v1.json").validate(
        _load_fixture("vnext_plus199", "repo_post_ratification_handoff_v199_reference.json")
    )
    _schema_validator("repo_candidate_ratification_family_closeout_alignment.v1.json").validate(
        _load_fixture(
            "vnext_plus199",
            "repo_candidate_ratification_family_closeout_alignment_v199_reference.json",
        )
    )


def test_v199_derivation_helper_matches_reference_fixtures() -> None:
    *_upstream, amendment_scope, handoff, closeout = (
        derive_v71c_repo_candidate_ratification_closeout_bundle(repo_root=_repo_root())
    )

    assert amendment_scope.model_dump(mode="json") == _load_fixture(
        "vnext_plus199",
        "repo_ratification_amendment_scope_boundary_v199_reference.json",
    )
    assert handoff.model_dump(mode="json") == _load_fixture(
        "vnext_plus199",
        "repo_post_ratification_handoff_v199_reference.json",
    )
    assert closeout.model_dump(mode="json") == _load_fixture(
        "vnext_plus199",
        "repo_candidate_ratification_family_closeout_alignment_v199_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_candidate_ratification_v199_reject_scope_without_ratification_ref.json",
            RepoRatificationAmendmentScopeBoundary,
            "at least 1 item",
        ),
        (
            "repo_candidate_ratification_v199_reject_handoff_without_ratification_ref.json",
            RepoPostRatificationHandoff,
            "at least 1 item",
        ),
        (
            "repo_candidate_ratification_v199_reject_scope_allows_release.json",
            RepoRatificationAmendmentScopeBoundary,
            "forbid downstream roles",
        ),
        (
            "repo_candidate_ratification_v199_reject_v72_integration_performed.json",
            RepoPostRatificationHandoff,
            "perform integration",
        ),
        (
            "repo_candidate_ratification_v199_reject_family_closeout_claims_release.json",
            RepoCandidateRatificationFamilyCloseoutAlignment,
            "downstream authority",
        ),
        (
            "repo_candidate_ratification_v199_reject_product_wedge_to_v72.json",
            RepoPostRatificationHandoff,
            "product wedge cannot be routed to V72",
        ),
    ],
)
def test_v199_rejects_invalid_surface_fixtures(
    fixture_name: str,
    model_type: type[
        RepoRatificationAmendmentScopeBoundary
        | RepoPostRatificationHandoff
        | RepoCandidateRatificationFamilyCloseoutAlignment
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus199", fixture_name))


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_candidate_ratification_v199_reject_rejected_candidate_to_v72.json",
            "deferred candidates cannot be routed to V72",
        ),
        (
            "repo_candidate_ratification_v199_reject_dissent_omitted.json",
            "carry forward dissent refs",
        ),
    ],
)
def test_v199_bundle_rejects_cross_surface_errors(fixture_name: str, match: str) -> None:
    handoff = RepoPostRatificationHandoff.model_validate(
        _load_fixture("vnext_plus199", fixture_name)
    )

    with pytest.raises(ValueError, match=match):
        validate_v71c_candidate_ratification_closeout_bundle(
            ratification_record=_v71b_ratification(),
            settlement_record=_v71b_settlement(),
            dissent_register=_v71b_dissent(),
            amendment_scope_boundary=_v71c_amendment_scope(),
            post_ratification_handoff=handoff,
            family_closeout_alignment=_v71c_closeout(),
        )
