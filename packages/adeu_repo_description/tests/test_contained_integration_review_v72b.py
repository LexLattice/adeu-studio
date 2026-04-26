from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CONTAINED_INTEGRATION_TRIAL_RECORD_SCHEMA,
    REPO_INTEGRATION_EFFECT_SURFACE_REGISTER_SCHEMA,
    REPO_INTEGRATION_ROLLBACK_READINESS_SCHEMA,
    RepoContainedIntegrationCandidatePlan,
    RepoContainedIntegrationTrialRecord,
    RepoIntegrationEffectSurfaceRegister,
    RepoIntegrationNonReleaseGuardrail,
    RepoIntegrationRollbackReadiness,
    RepoIntegrationTargetBoundary,
    derive_v72b_repo_contained_integration_trial_bundle,
    validate_v72b_contained_integration_trial_bundle,
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


def _v72a_plan() -> RepoContainedIntegrationCandidatePlan:
    return RepoContainedIntegrationCandidatePlan.model_validate(
        _load_fixture(
            "vnext_plus200",
            "repo_contained_integration_candidate_plan_v200_reference.json",
        )
    )


def _v72a_target_boundary() -> RepoIntegrationTargetBoundary:
    return RepoIntegrationTargetBoundary.model_validate(
        _load_fixture("vnext_plus200", "repo_integration_target_boundary_v200_reference.json")
    )


def _v72a_guardrail() -> RepoIntegrationNonReleaseGuardrail:
    return RepoIntegrationNonReleaseGuardrail.model_validate(
        _load_fixture(
            "vnext_plus200",
            "repo_integration_non_release_guardrail_v200_reference.json",
        )
    )


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


def _validate_reference_bundle_with(
    *,
    trial: RepoContainedIntegrationTrialRecord | None = None,
    effect: RepoIntegrationEffectSurfaceRegister | None = None,
    rollback: RepoIntegrationRollbackReadiness | None = None,
) -> None:
    validate_v72b_contained_integration_trial_bundle(
        contained_integration_candidate_plan=_v72a_plan(),
        integration_target_boundary=_v72a_target_boundary(),
        integration_non_release_guardrail=_v72a_guardrail(),
        contained_integration_trial_record=trial or _v72b_trial(),
        integration_effect_surface_register=effect or _v72b_effect(),
        integration_rollback_readiness=rollback or _v72b_rollback(),
    )


def test_v201_reference_bundle_validates() -> None:
    trial = _v72b_trial()
    effect = _v72b_effect()
    rollback = _v72b_rollback()

    assert trial.schema == REPO_CONTAINED_INTEGRATION_TRIAL_RECORD_SCHEMA
    assert effect.schema == REPO_INTEGRATION_EFFECT_SURFACE_REGISTER_SCHEMA
    assert rollback.schema == REPO_INTEGRATION_ROLLBACK_READINESS_SCHEMA
    assert any(row.trial_posture == "trial_ready_for_outcome_review" for row in trial.trial_rows)
    assert all("release" in trial.non_authority_summary.lower() for _ in [trial])

    _validate_reference_bundle_with(trial=trial, effect=effect, rollback=rollback)


def test_v201_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_contained_integration_trial_record.v1.json").validate(
        _load_fixture(
            "vnext_plus201",
            "repo_contained_integration_trial_record_v201_reference.json",
        )
    )
    _schema_validator("repo_integration_effect_surface_register.v1.json").validate(
        _load_fixture(
            "vnext_plus201",
            "repo_integration_effect_surface_register_v201_reference.json",
        )
    )
    _schema_validator("repo_integration_rollback_readiness.v1.json").validate(
        _load_fixture(
            "vnext_plus201",
            "repo_integration_rollback_readiness_v201_reference.json",
        )
    )


def test_v201_derivation_helper_matches_reference_fixtures() -> None:
    *_, trial, effect, rollback = derive_v72b_repo_contained_integration_trial_bundle(
        repo_root=_repo_root()
    )

    assert trial.model_dump(mode="json") == _load_fixture(
        "vnext_plus201",
        "repo_contained_integration_trial_record_v201_reference.json",
    )
    assert effect.model_dump(mode="json") == _load_fixture(
        "vnext_plus201",
        "repo_integration_effect_surface_register_v201_reference.json",
    )
    assert rollback.model_dump(mode="json") == _load_fixture(
        "vnext_plus201",
        "repo_integration_rollback_readiness_v201_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_contained_integration_v201_reject_trial_without_target_boundary.json",
            RepoContainedIntegrationTrialRecord,
            "recorded trial rows require",
        ),
        (
            "repo_contained_integration_v201_reject_local_trial_without_active_lock_ref.json",
            RepoContainedIntegrationTrialRecord,
            "recorded trial rows require",
        ),
        (
            "repo_contained_integration_v201_reject_diff_accepted_as_commit.json",
            RepoContainedIntegrationTrialRecord,
            "downstream authority",
        ),
        (
            "repo_contained_integration_v201_reject_rollback_verified_without_evidence.json",
            RepoIntegrationRollbackReadiness,
            "rollback evidence refs",
        ),
        (
            "repo_contained_integration_v201_reject_trial_claims_release.json",
            RepoContainedIntegrationTrialRecord,
            "downstream authority",
        ),
    ],
)
def test_v201_rejects_invalid_surface_fixtures(
    fixture_name: str,
    model_type: type[
        RepoContainedIntegrationTrialRecord
        | RepoIntegrationEffectSurfaceRegister
        | RepoIntegrationRollbackReadiness
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus201", fixture_name))


def test_v201_bundle_rejects_unknown_plan_ref() -> None:
    trial = _v72b_trial()
    rows = list(trial.trial_rows)
    rows[2] = rows[2].model_copy(update={"plan_refs": ["plan:v72a:missing"]})
    trial = trial.model_copy(update={"trial_rows": rows})

    with pytest.raises(ValueError, match="known V72-A plan rows"):
        _validate_reference_bundle_with(trial=trial)


def test_v201_bundle_rejects_candidate_mismatch() -> None:
    trial = _v72b_trial()
    rows = list(trial.trial_rows)
    rows[2] = rows[2].model_copy(update={"candidate_ref": "candidate:internal:mismatch"})
    trial = trial.model_copy(update={"trial_rows": rows})

    with pytest.raises(ValueError, match="candidate_ref must match"):
        _validate_reference_bundle_with(trial=trial)


def test_v201_bundle_rejects_review_id_mismatch() -> None:
    effect = _v72b_effect().model_copy(update={"review_id": "review:v72b:mismatched"})

    with pytest.raises(ValueError, match="V72-B review_id must match"):
        _validate_reference_bundle_with(effect=effect)


def test_v201_bundle_rejects_ready_with_blocked_rollback() -> None:
    rollback = _v72b_rollback()
    rows = list(rollback.rollback_rows)
    rows[0] = rows[0].model_copy(update={"rollback_posture": "rollback_blocked"})
    rollback = rollback.model_copy(update={"rollback_rows": rows})

    with pytest.raises(ValueError, match="blocked rollback"):
        _validate_reference_bundle_with(rollback=rollback)


def test_v201_bundle_rejects_ready_with_uncarried_effect_gap() -> None:
    effect = _v72b_effect()
    rows = list(effect.effect_rows)
    rows[0] = rows[0].model_copy(
        update={
            "effect_posture": "effect_requires_later_review",
            "effect_gap_refs": ["gap:v72b:self-evidencing:uncarried"],
            "carried_forward_gap_refs": [],
            "limitation_note": "Effect gap requires later review.",
        }
    )
    effect = effect.model_copy(update={"effect_rows": rows})

    with pytest.raises(ValueError, match="carry effect gaps forward"):
        _validate_reference_bundle_with(effect=effect)


def test_v201_bundle_rejects_unknown_effect_ref() -> None:
    rollback = _v72b_rollback()
    rows = list(rollback.rollback_rows)
    rows[0] = rows[0].model_copy(update={"effect_refs": ["effect:v72b:missing"]})
    rollback = rollback.model_copy(update={"rollback_rows": rows})

    with pytest.raises(ValueError, match="known effect rows"):
        _validate_reference_bundle_with(rollback=rollback)
