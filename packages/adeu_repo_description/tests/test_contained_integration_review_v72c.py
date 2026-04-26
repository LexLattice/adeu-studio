from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_COMMIT_RELEASE_AUTHORITY_POSTURE_SCHEMA,
    REPO_CONTAINED_INTEGRATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_POST_INTEGRATION_OUTCOME_REVIEW_HANDOFF_SCHEMA,
    RepoCommitReleaseAuthorityPosture,
    RepoContainedIntegrationFamilyCloseoutAlignment,
    RepoContainedIntegrationTrialRecord,
    RepoIntegrationEffectSurfaceRegister,
    RepoIntegrationRollbackReadiness,
    RepoPostIntegrationOutcomeReviewHandoff,
    derive_v72c_repo_contained_integration_closeout_bundle,
    validate_v72c_contained_integration_closeout_bundle,
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


def _v72b_trial() -> RepoContainedIntegrationTrialRecord:
    return RepoContainedIntegrationTrialRecord.model_validate(
        _load_fixture(
            "vnext_plus201",
            "repo_contained_integration_trial_record_v201_reference.json",
        )
    )


def _v72b_effect() -> RepoIntegrationEffectSurfaceRegister:
    return RepoIntegrationEffectSurfaceRegister.model_validate(
        _load_fixture(
            "vnext_plus201",
            "repo_integration_effect_surface_register_v201_reference.json",
        )
    )


def _v72b_rollback() -> RepoIntegrationRollbackReadiness:
    return RepoIntegrationRollbackReadiness.model_validate(
        _load_fixture(
            "vnext_plus201",
            "repo_integration_rollback_readiness_v201_reference.json",
        )
    )


def _v72c_authority() -> RepoCommitReleaseAuthorityPosture:
    return RepoCommitReleaseAuthorityPosture.model_validate(
        _load_fixture(
            "vnext_plus202",
            "repo_commit_release_authority_posture_v202_reference.json",
        )
    )


def _v72c_handoff() -> RepoPostIntegrationOutcomeReviewHandoff:
    return RepoPostIntegrationOutcomeReviewHandoff.model_validate(
        _load_fixture(
            "vnext_plus202",
            "repo_post_integration_outcome_review_handoff_v202_reference.json",
        )
    )


def _v72c_closeout() -> RepoContainedIntegrationFamilyCloseoutAlignment:
    return RepoContainedIntegrationFamilyCloseoutAlignment.model_validate(
        _load_fixture(
            "vnext_plus202",
            "repo_contained_integration_family_closeout_alignment_v202_reference.json",
        )
    )


def _validate_reference_bundle_with(
    *,
    authority: RepoCommitReleaseAuthorityPosture | None = None,
    handoff: RepoPostIntegrationOutcomeReviewHandoff | None = None,
    closeout: RepoContainedIntegrationFamilyCloseoutAlignment | None = None,
    rollback: RepoIntegrationRollbackReadiness | None = None,
) -> None:
    validate_v72c_contained_integration_closeout_bundle(
        contained_integration_trial_record=_v72b_trial(),
        integration_effect_surface_register=_v72b_effect(),
        integration_rollback_readiness=rollback or _v72b_rollback(),
        commit_release_authority_posture=authority or _v72c_authority(),
        post_integration_outcome_review_handoff=handoff or _v72c_handoff(),
        contained_integration_family_closeout_alignment=closeout or _v72c_closeout(),
    )


def test_v202_reference_bundle_validates() -> None:
    authority = _v72c_authority()
    handoff = _v72c_handoff()
    closeout = _v72c_closeout()

    assert authority.schema == REPO_COMMIT_RELEASE_AUTHORITY_POSTURE_SCHEMA
    assert handoff.schema == REPO_POST_INTEGRATION_OUTCOME_REVIEW_HANDOFF_SCHEMA
    assert closeout.schema == REPO_CONTAINED_INTEGRATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    assert (
        authority.authority_posture_rows[0].released_truth_posture == "released_truth_not_claimed"
    )
    assert handoff.handoff_rows[0].handoff_target == "v73_outcome_review"

    _validate_reference_bundle_with(authority=authority, handoff=handoff, closeout=closeout)


def test_v202_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_commit_release_authority_posture.v1.json").validate(
        _load_fixture(
            "vnext_plus202",
            "repo_commit_release_authority_posture_v202_reference.json",
        )
    )
    _schema_validator("repo_post_integration_outcome_review_handoff.v1.json").validate(
        _load_fixture(
            "vnext_plus202",
            "repo_post_integration_outcome_review_handoff_v202_reference.json",
        )
    )
    _schema_validator("repo_contained_integration_family_closeout_alignment.v1.json").validate(
        _load_fixture(
            "vnext_plus202",
            "repo_contained_integration_family_closeout_alignment_v202_reference.json",
        )
    )


def test_v202_derivation_helper_matches_reference_fixtures() -> None:
    *_, authority, handoff, closeout = derive_v72c_repo_contained_integration_closeout_bundle(
        repo_root=_repo_root()
    )

    assert authority.model_dump(mode="json") == _load_fixture(
        "vnext_plus202",
        "repo_commit_release_authority_posture_v202_reference.json",
    )
    assert handoff.model_dump(mode="json") == _load_fixture(
        "vnext_plus202",
        "repo_post_integration_outcome_review_handoff_v202_reference.json",
    )
    assert closeout.model_dump(mode="json") == _load_fixture(
        "vnext_plus202",
        "repo_contained_integration_family_closeout_alignment_v202_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_contained_integration_v202_reject_authority_without_trial_ref.json",
            RepoCommitReleaseAuthorityPosture,
            "at least 1 item",
        ),
        (
            "repo_contained_integration_v202_reject_released_truth_claimed.json",
            RepoCommitReleaseAuthorityPosture,
            "released_truth_not_claimed",
        ),
        (
            "repo_contained_integration_v202_reject_unresolved_human_authority_ref.json",
            RepoCommitReleaseAuthorityPosture,
            "concrete ref",
        ),
        (
            "repo_contained_integration_v202_reject_auto_merge_or_release.json",
            RepoCommitReleaseAuthorityPosture,
            "forbid automatic actions",
        ),
        (
            "repo_contained_integration_v202_reject_v73_handoff_with_blocked_rollback.json",
            RepoPostIntegrationOutcomeReviewHandoff,
            "effect refs",
        ),
        (
            "repo_contained_integration_v202_reject_effect_gap_omitted.json",
            RepoPostIntegrationOutcomeReviewHandoff,
            "unresolved effect gaps",
        ),
        (
            "repo_contained_integration_v202_reject_product_wedge_as_integrated.json",
            RepoPostIntegrationOutcomeReviewHandoff,
            "product wedge",
        ),
        (
            "repo_contained_integration_v202_reject_family_closeout_claims_release.json",
            RepoContainedIntegrationFamilyCloseoutAlignment,
            "must state",
        ),
    ],
)
def test_v202_rejects_invalid_surface_fixtures(
    fixture_name: str,
    model_type: type[
        RepoCommitReleaseAuthorityPosture
        | RepoPostIntegrationOutcomeReviewHandoff
        | RepoContainedIntegrationFamilyCloseoutAlignment
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus202", fixture_name))


def test_v202_bundle_rejects_unknown_trial_ref() -> None:
    authority = _v72c_authority()
    rows = list(authority.authority_posture_rows)
    rows[0] = rows[0].model_copy(update={"trial_refs": ["trial:v72b:missing"]})
    authority = authority.model_copy(update={"authority_posture_rows": rows})

    with pytest.raises(ValueError, match="known trial rows"):
        _validate_reference_bundle_with(authority=authority)


def test_v202_bundle_rejects_candidate_mismatch() -> None:
    handoff = _v72c_handoff()
    rows = list(handoff.handoff_rows)
    rows[0] = rows[0].model_copy(update={"candidate_ref": "candidate:internal:mismatch"})
    handoff = handoff.model_copy(update={"handoff_rows": rows})

    with pytest.raises(ValueError, match="candidate_ref must match"):
        _validate_reference_bundle_with(handoff=handoff)


def test_v202_bundle_rejects_ready_handoff_with_blocked_rollback() -> None:
    rollback = _v72b_rollback()
    rows = list(rollback.rollback_rows)
    rows[0] = rows[0].model_copy(update={"rollback_posture": "rollback_blocked"})
    rollback = rollback.model_copy(update={"rollback_rows": rows})

    with pytest.raises(ValueError, match="blocked rollback"):
        _validate_reference_bundle_with(rollback=rollback)
