from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CONTAINED_INTEGRATION_CANDIDATE_PLAN_SCHEMA,
    REPO_INTEGRATION_NON_RELEASE_GUARDRAIL_SCHEMA,
    REPO_INTEGRATION_TARGET_BOUNDARY_SCHEMA,
    RepoCandidateRatificationFamilyCloseoutAlignment,
    RepoContainedIntegrationCandidatePlan,
    RepoIntegrationNonReleaseGuardrail,
    RepoIntegrationTargetBoundary,
    RepoPostRatificationHandoff,
    RepoRatificationAmendmentScopeBoundary,
    derive_v72a_repo_contained_integration_review_bundle,
    validate_v72a_contained_integration_review_bundle,
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


def test_v200_reference_bundle_validates() -> None:
    plan = _v72a_plan()
    target_boundary = _v72a_target_boundary()
    guardrail = _v72a_guardrail()

    assert plan.schema == REPO_CONTAINED_INTEGRATION_CANDIDATE_PLAN_SCHEMA
    assert target_boundary.schema == REPO_INTEGRATION_TARGET_BOUNDARY_SCHEMA
    assert guardrail.schema == REPO_INTEGRATION_NON_RELEASE_GUARDRAIL_SCHEMA
    assert {row.containment_plan_posture for row in plan.plan_rows} == {
        "blocked_by_dissent",
        "eligible_for_containment_planning",
        "future_family_only",
    }
    assert not any(
        row.candidate_ref == "candidate:internal:typed_adjudication_product_wedge"
        and row.containment_plan_posture == "eligible_for_containment_planning"
        for row in plan.plan_rows
    )
    assert all(
        "released_truth" in row.forbidden_downstream_roles
        and "dispatch_authority" in row.forbidden_downstream_roles
        for row in guardrail.guardrail_rows
    )

    validate_v72a_contained_integration_review_bundle(
        amendment_scope_boundary=_v71c_amendment_scope(),
        post_ratification_handoff=_v71c_handoff(),
        family_closeout_alignment=_v71c_closeout(),
        contained_integration_candidate_plan=plan,
        integration_target_boundary=target_boundary,
        integration_non_release_guardrail=guardrail,
    )


def test_v200_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_contained_integration_candidate_plan.v1.json").validate(
        _load_fixture(
            "vnext_plus200",
            "repo_contained_integration_candidate_plan_v200_reference.json",
        )
    )
    _schema_validator("repo_integration_target_boundary.v1.json").validate(
        _load_fixture("vnext_plus200", "repo_integration_target_boundary_v200_reference.json")
    )
    _schema_validator("repo_integration_non_release_guardrail.v1.json").validate(
        _load_fixture(
            "vnext_plus200",
            "repo_integration_non_release_guardrail_v200_reference.json",
        )
    )


def test_v200_derivation_helper_matches_reference_fixtures() -> None:
    *_, plan, target_boundary, guardrail = derive_v72a_repo_contained_integration_review_bundle(
        repo_root=_repo_root()
    )

    assert plan.model_dump(mode="json") == _load_fixture(
        "vnext_plus200",
        "repo_contained_integration_candidate_plan_v200_reference.json",
    )
    assert target_boundary.model_dump(mode="json") == _load_fixture(
        "vnext_plus200",
        "repo_integration_target_boundary_v200_reference.json",
    )
    assert guardrail.model_dump(mode="json") == _load_fixture(
        "vnext_plus200",
        "repo_integration_non_release_guardrail_v200_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_contained_integration_v200_reject_product_wedge_to_integration.json",
            RepoContainedIntegrationCandidatePlan,
            "product wedge",
        ),
        (
            "repo_contained_integration_v200_reject_glob_target_boundary.json",
            RepoIntegrationTargetBoundary,
            "not a glob",
        ),
        (
            "repo_contained_integration_v200_reject_package_surface_without_child_refs.json",
            RepoIntegrationTargetBoundary,
            "non-empty target_refs",
        ),
        (
            "repo_contained_integration_v200_reject_eligible_without_rollback_requirement.json",
            RepoContainedIntegrationCandidatePlan,
            "rollback_requirement must be non-empty",
        ),
        (
            "repo_contained_integration_v200_reject_guardrail_allows_release.json",
            RepoIntegrationNonReleaseGuardrail,
            "forbid downstream roles",
        ),
        (
            "repo_contained_integration_v200_reject_trial_executed_in_v72a.json",
            RepoContainedIntegrationCandidatePlan,
            "Extra inputs are not permitted",
        ),
    ],
)
def test_v200_rejects_invalid_surface_fixtures(
    fixture_name: str,
    model_type: type[
        RepoContainedIntegrationCandidatePlan
        | RepoIntegrationTargetBoundary
        | RepoIntegrationNonReleaseGuardrail
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus200", fixture_name))


@pytest.mark.parametrize(
    ("fixture_name", "surface", "match"),
    [
        (
            "repo_contained_integration_v200_reject_unknown_v71c_handoff.json",
            "plan",
            "known V71-C handoff",
        ),
        (
            "repo_contained_integration_v200_reject_non_ready_handoff.json",
            "plan",
            "non-ready V71-C handoffs",
        ),
        (
            "repo_contained_integration_v200_reject_deferred_dissent_as_ready.json",
            "plan",
            "non-ready V71-C handoffs",
        ),
        (
            "repo_contained_integration_v200_reject_future_family_with_target_boundary.json",
            "target",
            "future-family-only plans",
        ),
    ],
)
def test_v200_bundle_rejects_cross_surface_errors(
    fixture_name: str,
    surface: str,
    match: str,
) -> None:
    plan = _v72a_plan()
    target_boundary = _v72a_target_boundary()
    if surface == "plan":
        plan = RepoContainedIntegrationCandidatePlan.model_validate(
            _load_fixture("vnext_plus200", fixture_name)
        )
        target_boundary = target_boundary.model_copy(
            update={"containment_plan_id": plan.containment_plan_id}
        )
        guardrail = _v72a_guardrail().model_copy(
            update={"containment_plan_id": plan.containment_plan_id}
        )
    elif surface == "target":
        target_boundary = RepoIntegrationTargetBoundary.model_validate(
            _load_fixture("vnext_plus200", fixture_name)
        )
        guardrail = _v72a_guardrail()
    else:
        guardrail = _v72a_guardrail()

    with pytest.raises(ValueError, match=match):
        validate_v72a_contained_integration_review_bundle(
            amendment_scope_boundary=_v71c_amendment_scope(),
            post_ratification_handoff=_v71c_handoff(),
            family_closeout_alignment=_v71c_closeout(),
            contained_integration_candidate_plan=plan,
            integration_target_boundary=target_boundary,
            integration_non_release_guardrail=guardrail,
        )


def _validate_reference_bundle_with(
    *,
    plan: RepoContainedIntegrationCandidatePlan | None = None,
    target_boundary: RepoIntegrationTargetBoundary | None = None,
    guardrail: RepoIntegrationNonReleaseGuardrail | None = None,
) -> None:
    validate_v72a_contained_integration_review_bundle(
        amendment_scope_boundary=_v71c_amendment_scope(),
        post_ratification_handoff=_v71c_handoff(),
        family_closeout_alignment=_v71c_closeout(),
        contained_integration_candidate_plan=plan or _v72a_plan(),
        integration_target_boundary=target_boundary or _v72a_target_boundary(),
        integration_non_release_guardrail=guardrail or _v72a_guardrail(),
    )


def test_v200_bundle_rejects_metadata_mismatch_across_surfaces() -> None:
    target_boundary = _v72a_target_boundary().model_copy(update={"review_id": "review:mismatch"})

    with pytest.raises(ValueError, match="review_id, snapshot_id, and source_set_id"):
        _validate_reference_bundle_with(target_boundary=target_boundary)


def test_v200_bundle_rejects_plan_without_guardrail_refs() -> None:
    plan = _v72a_plan()
    rows = list(plan.plan_rows)
    rows[0] = rows[0].model_copy(update={"guardrail_refs": []})
    plan = plan.model_copy(update={"plan_rows": rows})

    with pytest.raises(ValueError, match="guardrail refs"):
        _validate_reference_bundle_with(plan=plan)


def test_v200_bundle_rejects_unsorted_plan_refs() -> None:
    plan = _v72a_plan()
    rows = list(plan.plan_rows)
    rows[2] = rows[2].model_copy(
        update={
            "target_boundary_refs": [
                "target:v72a:self-evidencing:schema-surface",
                "target:v72a:odeu-diff:no-target",
            ],
            "guardrail_refs": [
                "guardrail:v72a:self-evidencing:no-release",
                "guardrail:v72a:odeu-diff:no-integration",
            ],
        }
    )
    plan = plan.model_copy(update={"plan_rows": rows})

    with pytest.raises(ValueError, match="target_boundary_refs must be lexicographically sorted"):
        _validate_reference_bundle_with(plan=plan)


def test_v200_bundle_rejects_orphan_target_and_guardrail_rows() -> None:
    target_boundary = _v72a_target_boundary()
    orphan_target = target_boundary.target_boundary_rows[0].model_copy(
        update={"target_boundary_ref": "target:v72a:orphan:no-target"}
    )
    target_boundary = target_boundary.model_copy(
        update={"target_boundary_rows": [*target_boundary.target_boundary_rows, orphan_target]}
    )

    with pytest.raises(ValueError, match="target boundary rows must be referenced"):
        _validate_reference_bundle_with(target_boundary=target_boundary)

    guardrail = _v72a_guardrail()
    orphan_guardrail = guardrail.guardrail_rows[0].model_copy(
        update={"guardrail_ref": "guardrail:v72a:orphan:no-release"}
    )
    guardrail = guardrail.model_copy(
        update={"guardrail_rows": [*guardrail.guardrail_rows, orphan_guardrail]}
    )

    with pytest.raises(ValueError, match="guardrail rows must be referenced"):
        _validate_reference_bundle_with(guardrail=guardrail)
