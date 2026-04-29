from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_OPERATOR_COGNITION_OUTCOME_SIGNAL_SCHEMA,
    REPO_OUTCOME_PROMOTION_DEMOTION_RECOMMENDATION_SCHEMA,
    REPO_OUTCOME_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_SELF_IMPROVEMENT_OUTCOME_LEDGER_SCHEMA,
    RepoCandidateOutcomeObservationRecord,
    RepoOperatorCognitionOutcomeSignal,
    RepoOutcomePromotionDemotionRecommendation,
    RepoOutcomeRegressionRegister,
    RepoOutcomeReviewFamilyCloseoutAlignment,
    RepoSelfImprovementOutcomeLedger,
    RepoToolFitnessDriftRegister,
    derive_v73c_repo_candidate_outcome_review_closeout_bundle,
    validate_v73c_candidate_outcome_review_closeout_bundle,
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


def _v73b_observation() -> RepoCandidateOutcomeObservationRecord:
    return RepoCandidateOutcomeObservationRecord.model_validate(
        _load_fixture(
            "vnext_plus204",
            "repo_candidate_outcome_observation_record_v204_reference.json",
        )
    )


def _v73b_regression() -> RepoOutcomeRegressionRegister:
    return RepoOutcomeRegressionRegister.model_validate(
        _load_fixture(
            "vnext_plus204",
            "repo_outcome_regression_register_v204_reference.json",
        )
    )


def _v73b_tool_fitness() -> RepoToolFitnessDriftRegister:
    return RepoToolFitnessDriftRegister.model_validate(
        _load_fixture(
            "vnext_plus204",
            "repo_tool_fitness_drift_register_v204_reference.json",
        )
    )


def _v73c_ledger() -> RepoSelfImprovementOutcomeLedger:
    return RepoSelfImprovementOutcomeLedger.model_validate(
        _load_fixture(
            "vnext_plus205",
            "repo_self_improvement_outcome_ledger_v205_reference.json",
        )
    )


def _v73c_operator_signal() -> RepoOperatorCognitionOutcomeSignal:
    return RepoOperatorCognitionOutcomeSignal.model_validate(
        _load_fixture(
            "vnext_plus205",
            "repo_operator_cognition_outcome_signal_v205_reference.json",
        )
    )


def _v73c_recommendation() -> RepoOutcomePromotionDemotionRecommendation:
    return RepoOutcomePromotionDemotionRecommendation.model_validate(
        _load_fixture(
            "vnext_plus205",
            "repo_outcome_promotion_demotion_recommendation_v205_reference.json",
        )
    )


def _v73c_alignment() -> RepoOutcomeReviewFamilyCloseoutAlignment:
    return RepoOutcomeReviewFamilyCloseoutAlignment.model_validate(
        _load_fixture(
            "vnext_plus205",
            "repo_outcome_review_family_closeout_alignment_v205_reference.json",
        )
    )


def _validate_reference_bundle_with(
    *,
    observation: RepoCandidateOutcomeObservationRecord | None = None,
    regression: RepoOutcomeRegressionRegister | None = None,
    tool_fitness: RepoToolFitnessDriftRegister | None = None,
    ledger: RepoSelfImprovementOutcomeLedger | None = None,
    operator_signal: RepoOperatorCognitionOutcomeSignal | None = None,
    recommendation: RepoOutcomePromotionDemotionRecommendation | None = None,
    alignment: RepoOutcomeReviewFamilyCloseoutAlignment | None = None,
) -> None:
    validate_v73c_candidate_outcome_review_closeout_bundle(
        candidate_outcome_observation_record=observation or _v73b_observation(),
        outcome_regression_register=regression or _v73b_regression(),
        tool_fitness_drift_register=tool_fitness or _v73b_tool_fitness(),
        self_improvement_outcome_ledger=ledger or _v73c_ledger(),
        operator_cognition_outcome_signal=operator_signal or _v73c_operator_signal(),
        outcome_promotion_demotion_recommendation=recommendation or _v73c_recommendation(),
        outcome_review_family_closeout_alignment=alignment or _v73c_alignment(),
    )


def test_v205_reference_bundle_validates() -> None:
    ledger = _v73c_ledger()
    operator_signal = _v73c_operator_signal()
    recommendation = _v73c_recommendation()
    alignment = _v73c_alignment()

    assert ledger.schema == REPO_SELF_IMPROVEMENT_OUTCOME_LEDGER_SCHEMA
    assert operator_signal.schema == REPO_OPERATOR_COGNITION_OUTCOME_SIGNAL_SCHEMA
    assert recommendation.schema == REPO_OUTCOME_PROMOTION_DEMOTION_RECOMMENDATION_SCHEMA
    assert alignment.schema == REPO_OUTCOME_REVIEW_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    assert {row.outcome_ledger_posture for row in ledger.ledger_rows} == {
        "positive_signal_recorded"
    }
    assert {row.signal_kind for row in operator_signal.operator_signal_rows} == {
        "workflow_exposed_missing_type"
    }
    assert {row.required_next_surface for row in recommendation.recommendation_rows} == {
        "v74_operator_projection_review"
    }
    assert {row.closeout_alignment_posture for row in alignment.alignment_rows} == {
        "family_closed_review_machinery_only"
    }

    _validate_reference_bundle_with(
        ledger=ledger,
        operator_signal=operator_signal,
        recommendation=recommendation,
        alignment=alignment,
    )


def test_v205_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_self_improvement_outcome_ledger.v1.json").validate(
        _load_fixture(
            "vnext_plus205",
            "repo_self_improvement_outcome_ledger_v205_reference.json",
        )
    )
    _schema_validator("repo_operator_cognition_outcome_signal.v1.json").validate(
        _load_fixture(
            "vnext_plus205",
            "repo_operator_cognition_outcome_signal_v205_reference.json",
        )
    )
    _schema_validator("repo_outcome_promotion_demotion_recommendation.v1.json").validate(
        _load_fixture(
            "vnext_plus205",
            "repo_outcome_promotion_demotion_recommendation_v205_reference.json",
        )
    )
    _schema_validator("repo_outcome_review_family_closeout_alignment.v1.json").validate(
        _load_fixture(
            "vnext_plus205",
            "repo_outcome_review_family_closeout_alignment_v205_reference.json",
        )
    )


def test_v205_derivation_helper_matches_reference_fixtures() -> None:
    *_, ledger, operator_signal, recommendation, alignment = (
        derive_v73c_repo_candidate_outcome_review_closeout_bundle(repo_root=_repo_root())
    )

    assert ledger.model_dump(mode="json") == _load_fixture(
        "vnext_plus205",
        "repo_self_improvement_outcome_ledger_v205_reference.json",
    )
    assert operator_signal.model_dump(mode="json") == _load_fixture(
        "vnext_plus205",
        "repo_operator_cognition_outcome_signal_v205_reference.json",
    )
    assert recommendation.model_dump(mode="json") == _load_fixture(
        "vnext_plus205",
        "repo_outcome_promotion_demotion_recommendation_v205_reference.json",
    )
    assert alignment.model_dump(mode="json") == _load_fixture(
        "vnext_plus205",
        "repo_outcome_review_family_closeout_alignment_v205_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_candidate_outcome_v205_reject_ledger_without_observation_ref.json",
            RepoSelfImprovementOutcomeLedger,
            "at least 1 item",
        ),
        (
            "repo_candidate_outcome_v205_reject_operator_signal_as_authority.json",
            RepoOperatorCognitionOutcomeSignal,
            "transcript as truth",
        ),
        (
            "repo_candidate_outcome_v205_reject_recommendation_without_ledger_ref.json",
            RepoOutcomePromotionDemotionRecommendation,
            "at least 1 item",
        ),
        (
            "repo_candidate_outcome_v205_reject_recommendation_without_authority_posture.json",
            RepoOutcomePromotionDemotionRecommendation,
            "promotion recommendations require later authority posture",
        ),
        (
            "repo_candidate_outcome_v205_reject_promotion_as_adoption.json",
            RepoOutcomePromotionDemotionRecommendation,
            "may not carry downstream authority or self-approval",
        ),
        (
            "repo_candidate_outcome_v205_reject_demotion_as_automatic_revert.json",
            RepoOutcomePromotionDemotionRecommendation,
            "may not carry downstream authority or self-approval",
        ),
        (
            "repo_candidate_outcome_v205_reject_product_work_without_v74.json",
            RepoOutcomePromotionDemotionRecommendation,
            "product recommendations require V74 review",
        ),
        (
            "repo_candidate_outcome_v205_reject_dispatch_selected.json",
            RepoOutcomePromotionDemotionRecommendation,
            "may not carry downstream authority or self-approval",
        ),
        (
            "repo_candidate_outcome_v205_reject_family_closeout_claims_release.json",
            RepoOutcomeReviewFamilyCloseoutAlignment,
            "may not carry downstream authority or self-approval",
        ),
    ],
)
def test_v205_rejects_invalid_surface_fixtures(
    fixture_name: str,
    model_type: type[
        RepoSelfImprovementOutcomeLedger
        | RepoOperatorCognitionOutcomeSignal
        | RepoOutcomePromotionDemotionRecommendation
        | RepoOutcomeReviewFamilyCloseoutAlignment
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus205", fixture_name))


def test_v205_rejects_positive_signal_with_hidden_blocking_regression() -> None:
    regression = _v73b_regression()
    regression = regression.model_copy(
        update={
            "regression_rows": [
                row.model_copy(update={"blocking_for_recommendation": True})
                for row in regression.regression_rows
            ]
        }
    )
    ledger = RepoSelfImprovementOutcomeLedger.model_validate(
        _load_fixture(
            "vnext_plus205",
            "repo_candidate_outcome_v205_reject_positive_signal_with_hidden_regression.json",
        )
    )

    with pytest.raises(
        ValueError,
        match="positive ledger signals must carry forward blocking regression refs",
    ):
        _validate_reference_bundle_with(regression=regression, ledger=ledger)


def test_v205_rejects_recommendation_unknown_v73b_evidence_ref() -> None:
    recommendation = _v73c_recommendation()
    recommendation = recommendation.model_copy(
        update={
            "recommendation_rows": [
                row.model_copy(update={"observation_refs": ["observation:v73b:missing"]})
                for row in recommendation.recommendation_rows
            ]
        }
    )

    with pytest.raises(
        ValueError,
        match="recommendation rows must reference known V73-B observation rows",
    ):
        _validate_reference_bundle_with(recommendation=recommendation)


def test_v205_rejects_recommendation_cross_candidate_evidence_ref() -> None:
    regression = _v73b_regression()
    extra_regression_ref = "regression:v73b:other-candidate"
    regression = regression.model_copy(
        update={
            "regression_rows": regression.regression_rows
            + [
                regression.regression_rows[0].model_copy(
                    update={
                        "regression_ref": extra_regression_ref,
                        "candidate_ref": "candidate:internal:other",
                        "blocking_for_recommendation": False,
                    }
                )
            ]
        }
    )
    recommendation = _v73c_recommendation()
    recommendation = recommendation.model_copy(
        update={
            "recommendation_rows": [
                row.model_copy(update={"regression_refs": [extra_regression_ref]})
                for row in recommendation.recommendation_rows
            ]
        }
    )

    with pytest.raises(
        ValueError,
        match="recommendation candidate_ref must match regression candidate_ref",
    ):
        _validate_reference_bundle_with(regression=regression, recommendation=recommendation)


def test_v205_rejects_family_closeout_reviewed_candidate_mismatch() -> None:
    alignment = _v73c_alignment()
    alignment = alignment.model_copy(
        update={
            "alignment_rows": [
                row.model_copy(update={"reviewed_candidate_refs": ["candidate:internal:other"]})
                for row in alignment.alignment_rows
            ]
        }
    )

    with pytest.raises(
        ValueError,
        match="reviewed_candidate_refs must match referenced V73-C row candidates",
    ):
        _validate_reference_bundle_with(alignment=alignment)


def test_v205_rejects_demotion_without_later_review_surface() -> None:
    payload = _load_fixture(
        "vnext_plus205",
        "repo_outcome_promotion_demotion_recommendation_v205_reference.json",
    )
    payload["recommendation_rows"][0]["recommendation_posture"] = (
        "recommend_demote_or_revert_for_later_review"
    )
    payload["recommendation_rows"][0]["required_next_surface"] = "deferred_no_selection"

    with pytest.raises(
        ValidationError,
        match="promotion and demotion recommendations require a later review surface",
    ):
        RepoOutcomePromotionDemotionRecommendation.model_validate(payload)
