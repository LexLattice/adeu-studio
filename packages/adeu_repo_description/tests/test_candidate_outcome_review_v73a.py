from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CANDIDATE_OUTCOME_REVIEW_ENTRY_SCHEMA,
    REPO_OUTCOME_EVIDENCE_SOURCE_INDEX_SCHEMA,
    REPO_OUTCOME_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA,
    RepoCandidateOutcomeReviewEntry,
    RepoCommitReleaseAuthorityPosture,
    RepoContainedIntegrationFamilyCloseoutAlignment,
    RepoContainedIntegrationTrialRecord,
    RepoIntegrationEffectSurfaceRegister,
    RepoIntegrationRollbackReadiness,
    RepoOutcomeEvidenceSourceIndex,
    RepoOutcomeReviewBoundaryGuardrail,
    RepoPostIntegrationOutcomeReviewHandoff,
    derive_v73a_repo_candidate_outcome_review_bundle,
    validate_v73a_candidate_outcome_review_bundle,
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


def _v73a_source_index() -> RepoOutcomeEvidenceSourceIndex:
    return RepoOutcomeEvidenceSourceIndex.model_validate(
        _load_fixture(
            "vnext_plus203",
            "repo_outcome_evidence_source_index_v203_reference.json",
        )
    )


def _v73a_entry() -> RepoCandidateOutcomeReviewEntry:
    return RepoCandidateOutcomeReviewEntry.model_validate(
        _load_fixture(
            "vnext_plus203",
            "repo_candidate_outcome_review_entry_v203_reference.json",
        )
    )


def _v73a_guardrail() -> RepoOutcomeReviewBoundaryGuardrail:
    return RepoOutcomeReviewBoundaryGuardrail.model_validate(
        _load_fixture(
            "vnext_plus203",
            "repo_outcome_review_boundary_guardrail_v203_reference.json",
        )
    )


def _validate_reference_bundle_with(
    *,
    source_index: RepoOutcomeEvidenceSourceIndex | None = None,
    entry: RepoCandidateOutcomeReviewEntry | None = None,
    guardrail: RepoOutcomeReviewBoundaryGuardrail | None = None,
    handoff: RepoPostIntegrationOutcomeReviewHandoff | None = None,
) -> None:
    selected_entry = entry or _v73a_entry()
    selected_guardrail = guardrail or _v73a_guardrail()
    if guardrail is None and entry is not None:
        selected_guardrail = selected_guardrail.model_copy(
            update={"outcome_review_entry_id": selected_entry.outcome_review_entry_id}
        )
    validate_v73a_candidate_outcome_review_bundle(
        contained_integration_trial_record=_v72b_trial(),
        integration_effect_surface_register=_v72b_effect(),
        integration_rollback_readiness=_v72b_rollback(),
        commit_release_authority_posture=_v72c_authority(),
        post_integration_outcome_review_handoff=handoff or _v72c_handoff(),
        contained_integration_family_closeout_alignment=_v72c_closeout(),
        outcome_evidence_source_index=source_index or _v73a_source_index(),
        candidate_outcome_review_entry=selected_entry,
        outcome_review_boundary_guardrail=selected_guardrail,
    )


def test_v203_reference_bundle_validates() -> None:
    source_index = _v73a_source_index()
    entry = _v73a_entry()
    guardrail = _v73a_guardrail()

    assert source_index.schema == REPO_OUTCOME_EVIDENCE_SOURCE_INDEX_SCHEMA
    assert entry.schema == REPO_CANDIDATE_OUTCOME_REVIEW_ENTRY_SCHEMA
    assert guardrail.schema == REPO_OUTCOME_REVIEW_BOUNDARY_GUARDRAIL_SCHEMA
    assert {row.entry_posture for row in entry.entry_rows} == {"eligible_for_outcome_review"}
    assert {row.horizon_kind for row in source_index.outcome_horizon_rows} == {
        "baseline",
        "evaluation",
        "intervention",
    }
    assert all(
        "promotion_authority" in row.forbidden_downstream_roles
        and "dispatch_authority" in row.forbidden_downstream_roles
        for row in guardrail.guardrail_rows
    )

    _validate_reference_bundle_with(
        source_index=source_index,
        entry=entry,
        guardrail=guardrail,
    )


def test_v203_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_outcome_evidence_source_index.v1.json").validate(
        _load_fixture(
            "vnext_plus203",
            "repo_outcome_evidence_source_index_v203_reference.json",
        )
    )
    _schema_validator("repo_candidate_outcome_review_entry.v1.json").validate(
        _load_fixture(
            "vnext_plus203",
            "repo_candidate_outcome_review_entry_v203_reference.json",
        )
    )
    _schema_validator("repo_outcome_review_boundary_guardrail.v1.json").validate(
        _load_fixture(
            "vnext_plus203",
            "repo_outcome_review_boundary_guardrail_v203_reference.json",
        )
    )


def test_v203_derivation_helper_matches_reference_fixtures() -> None:
    *_, source_index, entry, guardrail = derive_v73a_repo_candidate_outcome_review_bundle(
        repo_root=_repo_root()
    )

    assert source_index.model_dump(mode="json") == _load_fixture(
        "vnext_plus203",
        "repo_outcome_evidence_source_index_v203_reference.json",
    )
    assert entry.model_dump(mode="json") == _load_fixture(
        "vnext_plus203",
        "repo_candidate_outcome_review_entry_v203_reference.json",
    )
    assert guardrail.model_dump(mode="json") == _load_fixture(
        "vnext_plus203",
        "repo_outcome_review_boundary_guardrail_v203_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_candidate_outcome_v203_reject_product_wedge_to_outcome_review.json",
            RepoCandidateOutcomeReviewEntry,
            "blocked or product candidates",
        ),
        (
            "repo_candidate_outcome_v203_reject_conceptual_diff_dissent_as_ready.json",
            RepoCandidateOutcomeReviewEntry,
            "blocked or product candidates",
        ),
        (
            "repo_candidate_outcome_v203_reject_missing_baseline_source_free.json",
            RepoOutcomeEvidenceSourceIndex,
            "missing outcome horizons require absence evidence source refs",
        ),
        (
            "repo_candidate_outcome_v203_reject_eligible_entry_without_horizons.json",
            RepoCandidateOutcomeReviewEntry,
            "baseline_horizon_ref",
        ),
        (
            "repo_candidate_outcome_v203_reject_trial_as_outcome_success.json",
            RepoOutcomeEvidenceSourceIndex,
            "context evidence cannot be primary outcome evidence",
        ),
        (
            "repo_candidate_outcome_v203_reject_effect_as_benefit_without_horizon.json",
            RepoOutcomeEvidenceSourceIndex,
            "may not carry outcome judgment",
        ),
        (
            "repo_candidate_outcome_v203_reject_guardrail_allows_promotion.json",
            RepoOutcomeReviewBoundaryGuardrail,
            "guardrails must forbid downstream roles",
        ),
        (
            "repo_candidate_outcome_v203_reject_entry_claims_release.json",
            RepoCandidateOutcomeReviewEntry,
            "may not carry outcome judgment",
        ),
    ],
)
def test_v203_rejects_invalid_surface_fixtures(
    fixture_name: str,
    model_type: type[
        RepoOutcomeEvidenceSourceIndex
        | RepoCandidateOutcomeReviewEntry
        | RepoOutcomeReviewBoundaryGuardrail
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus203", fixture_name))


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_candidate_outcome_v203_reject_unknown_v72c_handoff.json",
            "known V72-C handoff",
        ),
        (
            "repo_candidate_outcome_v203_reject_non_ready_handoff.json",
            "non-ready V72-C handoffs",
        ),
    ],
)
def test_v203_bundle_rejects_invalid_handoff_links(fixture_name: str, match: str) -> None:
    entry = RepoCandidateOutcomeReviewEntry.model_validate(
        _load_fixture("vnext_plus203", fixture_name)
    )
    handoff = _v72c_handoff()
    if "non_ready" in fixture_name:
        row = handoff.handoff_rows[0].model_copy(
            update={
                "handoff_ref": "handoff:v72c:not-ready:v73-review",
                "handoff_posture": "blocked_by_effect_gap",
                "carried_forward_gap_refs": ["gap:v72c:not-ready"],
            }
        )
        handoff = handoff.model_copy(update={"handoff_rows": [row]})

    with pytest.raises(ValueError, match=match):
        _validate_reference_bundle_with(entry=entry, handoff=handoff)


def test_v203_bundle_rejects_metadata_mismatch_across_surfaces() -> None:
    entry = _v73a_entry().model_copy(update={"review_id": "review:mismatch"})

    with pytest.raises(ValueError, match="review_id, snapshot_id, and source_set_id"):
        _validate_reference_bundle_with(entry=entry)


def test_v203_bundle_rejects_orphan_guardrail_rows() -> None:
    guardrail = _v73a_guardrail()
    orphan = guardrail.guardrail_rows[0].model_copy(
        update={"guardrail_ref": "guardrail:v73a:orphan:no-authority"}
    )
    guardrail = guardrail.model_copy(update={"guardrail_rows": [*guardrail.guardrail_rows, orphan]})

    with pytest.raises(ValueError, match="guardrail rows must be referenced"):
        _validate_reference_bundle_with(guardrail=guardrail)
