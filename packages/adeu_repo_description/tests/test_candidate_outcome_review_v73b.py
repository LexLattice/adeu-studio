from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CANDIDATE_OUTCOME_OBSERVATION_RECORD_SCHEMA,
    REPO_OUTCOME_REGRESSION_REGISTER_SCHEMA,
    REPO_TOOL_FITNESS_DRIFT_REGISTER_SCHEMA,
    RepoCandidateOutcomeObservationRecord,
    RepoCandidateOutcomeReviewEntry,
    RepoOutcomeEvidenceSourceIndex,
    RepoOutcomeRegressionRegister,
    RepoOutcomeReviewBoundaryGuardrail,
    RepoToolFitnessDriftRegister,
    derive_v73b_repo_candidate_outcome_review_bundle,
    validate_v73b_candidate_outcome_review_bundle,
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


def _validate_reference_bundle_with(
    *,
    observation: RepoCandidateOutcomeObservationRecord | None = None,
    regression: RepoOutcomeRegressionRegister | None = None,
    tool_fitness: RepoToolFitnessDriftRegister | None = None,
) -> None:
    selected_observation = observation or _v73b_observation()
    selected_regression = regression or _v73b_regression()
    selected_tool_fitness = tool_fitness or _v73b_tool_fitness()
    if observation is not None and regression is None:
        selected_regression = selected_regression.model_copy(
            update={
                "outcome_observation_record_id": selected_observation.outcome_observation_record_id
            }
        )
    if observation is not None and tool_fitness is None:
        selected_tool_fitness = selected_tool_fitness.model_copy(
            update={
                "outcome_observation_record_id": selected_observation.outcome_observation_record_id
            }
        )
    validate_v73b_candidate_outcome_review_bundle(
        outcome_evidence_source_index=_v73a_source_index(),
        candidate_outcome_review_entry=_v73a_entry(),
        outcome_review_boundary_guardrail=_v73a_guardrail(),
        candidate_outcome_observation_record=selected_observation,
        outcome_regression_register=selected_regression,
        tool_fitness_drift_register=selected_tool_fitness,
    )


def test_v204_reference_bundle_validates() -> None:
    observation = _v73b_observation()
    regression = _v73b_regression()
    tool_fitness = _v73b_tool_fitness()

    assert observation.schema == REPO_CANDIDATE_OUTCOME_OBSERVATION_RECORD_SCHEMA
    assert regression.schema == REPO_OUTCOME_REGRESSION_REGISTER_SCHEMA
    assert tool_fitness.schema == REPO_TOOL_FITNESS_DRIFT_REGISTER_SCHEMA
    assert {row.outcome_observation_posture for row in observation.observation_rows} == {
        "benefit_observed"
    }
    assert {row.regression_posture for row in regression.regression_rows} == {
        "no_regression_observed"
    }
    assert {row.tool_fitness_posture for row in tool_fitness.tool_fitness_rows} == {
        "tool_fit_confirmed"
    }

    _validate_reference_bundle_with(
        observation=observation,
        regression=regression,
        tool_fitness=tool_fitness,
    )


def test_v204_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_candidate_outcome_observation_record.v1.json").validate(
        _load_fixture(
            "vnext_plus204",
            "repo_candidate_outcome_observation_record_v204_reference.json",
        )
    )
    _schema_validator("repo_outcome_regression_register.v1.json").validate(
        _load_fixture(
            "vnext_plus204",
            "repo_outcome_regression_register_v204_reference.json",
        )
    )
    _schema_validator("repo_tool_fitness_drift_register.v1.json").validate(
        _load_fixture(
            "vnext_plus204",
            "repo_tool_fitness_drift_register_v204_reference.json",
        )
    )


def test_v204_derivation_helper_matches_reference_fixtures() -> None:
    *_, observation, regression, tool_fitness = derive_v73b_repo_candidate_outcome_review_bundle(
        repo_root=_repo_root()
    )

    assert observation.model_dump(mode="json") == _load_fixture(
        "vnext_plus204",
        "repo_candidate_outcome_observation_record_v204_reference.json",
    )
    assert regression.model_dump(mode="json") == _load_fixture(
        "vnext_plus204",
        "repo_outcome_regression_register_v204_reference.json",
    )
    assert tool_fitness.model_dump(mode="json") == _load_fixture(
        "vnext_plus204",
        "repo_tool_fitness_drift_register_v204_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_candidate_outcome_v204_reject_benefit_without_evaluation_refs.json",
            RepoCandidateOutcomeObservationRecord,
            "benefit observations require",
        ),
        (
            "repo_candidate_outcome_v204_reject_no_regression_without_checked_horizon.json",
            RepoOutcomeRegressionRegister,
            "no_regression_observed requires checked evaluation refs",
        ),
        (
            "repo_candidate_outcome_v204_reject_tool_fit_without_result_refs.json",
            RepoToolFitnessDriftRegister,
            "tool_fit_confirmed requires target-bound evidence",
        ),
        (
            "repo_candidate_outcome_v204_reject_tool_fit_without_target_horizon.json",
            RepoToolFitnessDriftRegister,
            "tool_fit_confirmed requires target-bound evidence",
        ),
        (
            "repo_candidate_outcome_v204_reject_global_tool_fitness_claim.json",
            RepoToolFitnessDriftRegister,
            "may not carry downstream authority or global policy",
        ),
        (
            "repo_candidate_outcome_v204_reject_observation_as_promotion.json",
            RepoCandidateOutcomeObservationRecord,
            "may not carry downstream authority or global policy",
        ),
        (
            "repo_candidate_outcome_v204_reject_regression_as_implementation_priority.json",
            RepoOutcomeRegressionRegister,
            "may not carry downstream authority or global policy",
        ),
    ],
)
def test_v204_rejects_invalid_surface_fixtures(
    fixture_name: str,
    model_type: type[
        RepoCandidateOutcomeObservationRecord
        | RepoOutcomeRegressionRegister
        | RepoToolFitnessDriftRegister
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus204", fixture_name))


def test_v204_rejects_unknown_entry_ref() -> None:
    observation = RepoCandidateOutcomeObservationRecord.model_validate(
        _load_fixture(
            "vnext_plus204",
            "repo_candidate_outcome_v204_reject_unknown_entry_ref.json",
        )
    )

    with pytest.raises(ValueError, match="observation rows must reference known V73-A entries"):
        _validate_reference_bundle_with(observation=observation)


def test_v204_rejects_candidate_mismatch() -> None:
    observation = RepoCandidateOutcomeObservationRecord.model_validate(
        _load_fixture(
            "vnext_plus204",
            "repo_candidate_outcome_v204_reject_candidate_mismatch.json",
        )
    )

    with pytest.raises(ValueError, match="observation candidate_ref must match V73-A entry"):
        _validate_reference_bundle_with(observation=observation)


def test_v204_rejects_benefit_without_outcome_source_refs() -> None:
    payload = _load_fixture(
        "vnext_plus204",
        "repo_candidate_outcome_observation_record_v204_reference.json",
    )
    payload["observation_rows"][0]["outcome_source_refs"] = []

    with pytest.raises(ValidationError, match="benefit observations require"):
        RepoCandidateOutcomeObservationRecord.model_validate(payload)


def test_v204_rejects_benefit_with_uncarried_regression() -> None:
    regression = RepoOutcomeRegressionRegister.model_validate(
        _load_fixture(
            "vnext_plus204",
            "repo_candidate_outcome_v204_reject_benefit_with_uncarried_regression.json",
        )
    )

    with pytest.raises(
        ValueError,
        match="benefit observations must carry forward blocking regression refs",
    ):
        _validate_reference_bundle_with(regression=regression)


def test_v204_rejects_regression_without_observation_reverse_ref() -> None:
    observation = _v73b_observation()
    observation = observation.model_copy(
        update={
            "observation_rows": [
                observation.observation_rows[0].model_copy(update={"regression_refs": []})
            ]
        }
    )

    with pytest.raises(ValueError, match="observation rows must point back to regression rows"):
        _validate_reference_bundle_with(observation=observation)
