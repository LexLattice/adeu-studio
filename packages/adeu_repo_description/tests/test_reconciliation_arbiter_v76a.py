from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_ARBITER_RELATION_REGISTER_SCHEMA,
    REPO_RECONCILIATION_CLAIM_MAP_SCHEMA,
    REPO_RECONCILIATION_DISSENT_REGISTER_SCHEMA,
    RepoArbiterRelationRegister,
    RepoDispatchReconciliationContract,
    RepoDispatchReviewFamilyCloseoutAlignment,
    RepoPostDispatchReviewHandoff,
    RepoReconciliationClaimMap,
    RepoReconciliationDissentRegister,
    RepoWorkerOutputReconciliationPlan,
    derive_v76a_reconciliation_arbiter_bundle,
    validate_v76a_reconciliation_arbiter_bundle,
)
from adeu_repo_description.candidate_review_classification import _surface_id
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


def _reconciliation_plan() -> RepoWorkerOutputReconciliationPlan:
    return RepoWorkerOutputReconciliationPlan.model_validate(
        _load_fixture(
            "vnext_plus211",
            "repo_worker_output_reconciliation_plan_v211_reference.json",
        )
    )


def _contract() -> RepoDispatchReconciliationContract:
    return RepoDispatchReconciliationContract.model_validate(
        _load_fixture(
            "vnext_plus211",
            "repo_dispatch_reconciliation_contract_v211_reference.json",
        )
    )


def _handoff() -> RepoPostDispatchReviewHandoff:
    return RepoPostDispatchReviewHandoff.model_validate(
        _load_fixture("vnext_plus211", "repo_post_dispatch_review_handoff_v211_reference.json")
    )


def _family_closeout() -> RepoDispatchReviewFamilyCloseoutAlignment:
    return RepoDispatchReviewFamilyCloseoutAlignment.model_validate(
        _load_fixture(
            "vnext_plus211",
            "repo_dispatch_review_family_closeout_alignment_v211_reference.json",
        )
    )


def _claim_map() -> RepoReconciliationClaimMap:
    return RepoReconciliationClaimMap.model_validate(
        _load_fixture("vnext_plus212", "repo_reconciliation_claim_map_v212_reference.json")
    )


def _relation_register() -> RepoArbiterRelationRegister:
    return RepoArbiterRelationRegister.model_validate(
        _load_fixture("vnext_plus212", "repo_arbiter_relation_register_v212_reference.json")
    )


def _dissent_register() -> RepoReconciliationDissentRegister:
    return RepoReconciliationDissentRegister.model_validate(
        _load_fixture(
            "vnext_plus212",
            "repo_reconciliation_dissent_register_v212_reference.json",
        )
    )


def _relation_register_for_claim_map(
    claim_map: RepoReconciliationClaimMap,
) -> RepoArbiterRelationRegister:
    payload = _load_fixture("vnext_plus212", "repo_arbiter_relation_register_v212_reference.json")
    payload["reconciliation_claim_map_id"] = claim_map.reconciliation_claim_map_id
    payload["arbiter_relation_register_id"] = _surface_id(
        "repo_arbiter_relation_register",
        REPO_ARBITER_RELATION_REGISTER_SCHEMA,
        payload,
        "arbiter_relation_register_id",
    )
    return RepoArbiterRelationRegister.model_validate(payload)


def _dissent_register_for_surfaces(
    claim_map: RepoReconciliationClaimMap,
    relation_register: RepoArbiterRelationRegister,
) -> RepoReconciliationDissentRegister:
    payload = _load_fixture(
        "vnext_plus212",
        "repo_reconciliation_dissent_register_v212_reference.json",
    )
    payload["reconciliation_claim_map_id"] = claim_map.reconciliation_claim_map_id
    payload["arbiter_relation_register_id"] = relation_register.arbiter_relation_register_id
    payload["reconciliation_dissent_register_id"] = _surface_id(
        "repo_reconciliation_dissent_register",
        REPO_RECONCILIATION_DISSENT_REGISTER_SCHEMA,
        payload,
        "reconciliation_dissent_register_id",
    )
    return RepoReconciliationDissentRegister.model_validate(payload)


def test_v212_reference_bundle_validates() -> None:
    claim_map = _claim_map()
    relation_register = _relation_register()
    dissent_register = _dissent_register()

    assert claim_map.schema == REPO_RECONCILIATION_CLAIM_MAP_SCHEMA
    assert relation_register.schema == REPO_ARBITER_RELATION_REGISTER_SCHEMA
    assert dissent_register.schema == REPO_RECONCILIATION_DISSENT_REGISTER_SCHEMA
    assert {
        row.output_presence_posture for row in claim_map.claim_map_rows
    } == {"projected_not_observed"}
    assert all(not row.observed_worker_output_refs for row in claim_map.claim_map_rows)
    assert {
        row.dissent_presence_posture for row in dissent_register.dissent_rows
    } == {"dissent_present", "searched_none_found"}

    validate_v76a_reconciliation_arbiter_bundle(
        worker_output_reconciliation_plan=_reconciliation_plan(),
        dispatch_reconciliation_contract=_contract(),
        post_dispatch_review_handoff=_handoff(),
        dispatch_review_family_closeout_alignment=_family_closeout(),
        reconciliation_claim_map=claim_map,
        arbiter_relation_register=relation_register,
        reconciliation_dissent_register=dissent_register,
    )


def test_v212_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_reconciliation_claim_map.v1.json").validate(
        _load_fixture("vnext_plus212", "repo_reconciliation_claim_map_v212_reference.json")
    )
    _schema_validator("repo_arbiter_relation_register.v1.json").validate(
        _load_fixture("vnext_plus212", "repo_arbiter_relation_register_v212_reference.json")
    )
    _schema_validator("repo_reconciliation_dissent_register.v1.json").validate(
        _load_fixture(
            "vnext_plus212",
            "repo_reconciliation_dissent_register_v212_reference.json",
        )
    )


def test_v212_derivation_helper_matches_reference_fixtures() -> None:
    claim_map, relation_register, dissent_register = derive_v76a_reconciliation_arbiter_bundle(
        repo_root=_repo_root()
    )

    assert claim_map.model_dump(mode="json") == _load_fixture(
        "vnext_plus212",
        "repo_reconciliation_claim_map_v212_reference.json",
    )
    assert relation_register.model_dump(mode="json") == _load_fixture(
        "vnext_plus212",
        "repo_arbiter_relation_register_v212_reference.json",
    )
    assert dissent_register.model_dump(mode="json") == _load_fixture(
        "vnext_plus212",
        "repo_reconciliation_dissent_register_v212_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_reconciliation_arbiter_v212_reject_claim_map_without_source_refs.json",
            RepoReconciliationClaimMap,
            "at least 1 item",
        ),
        (
            "repo_reconciliation_arbiter_v212_reject_missing_source_without_absence_role.json",
            RepoReconciliationClaimMap,
            "non-absence reconciliation source rows must be present",
        ),
        (
            "repo_reconciliation_arbiter_v212_reject_projected_slot_with_observed_output.json",
            RepoReconciliationClaimMap,
            "projected claim maps must not carry observed worker outputs",
        ),
        (
            "repo_reconciliation_arbiter_v212_reject_projected_slot_as_observed_content_claim.json",
            RepoReconciliationClaimMap,
            "projected output slots cannot become observed content claims",
        ),
        (
            "repo_reconciliation_arbiter_v212_reject_blocker_to_arbiter_readiness.json",
            RepoReconciliationClaimMap,
            "authority blockers must remain blocked or future-family-only",
        ),
        (
            "repo_reconciliation_arbiter_v212_reject_relation_without_claim_map_refs.json",
            RepoArbiterRelationRegister,
            "at least 1 item",
        ),
        (
            "repo_reconciliation_arbiter_v212_reject_relation_settles_truth.json",
            RepoArbiterRelationRegister,
            "may not carry truth or correctness authority",
        ),
        (
            "repo_reconciliation_arbiter_v212_reject_majority_agreement_as_correctness.json",
            RepoArbiterRelationRegister,
            "may not carry truth or correctness authority",
        ),
        (
            "repo_reconciliation_arbiter_v212_reject_model_comparison_benchmark_truth.json",
            RepoArbiterRelationRegister,
            "may not carry truth or correctness authority",
        ),
        (
            "repo_reconciliation_arbiter_v212_reject_no_dissent_recorded_without_search_horizon.json",
            RepoReconciliationDissentRegister,
            "searched-none dissent rows require searched horizon",
        ),
    ],
)
def test_v212_reject_fixtures_fail_model_validation(
    fixture_name: str,
    model_type: type[
        RepoReconciliationClaimMap
        | RepoArbiterRelationRegister
        | RepoReconciliationDissentRegister
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus212", fixture_name))


def test_v212_bundle_rejects_unknown_reconciliation_plan_ref() -> None:
    claim_map = RepoReconciliationClaimMap.model_validate(
        _load_fixture(
            "vnext_plus212",
            "repo_reconciliation_arbiter_v212_reject_unknown_reconciliation_plan.json",
        )
    )

    with pytest.raises(ValueError, match="released V75-C reconciliation plans"):
        relation_register = _relation_register_for_claim_map(claim_map)
        validate_v76a_reconciliation_arbiter_bundle(
            worker_output_reconciliation_plan=_reconciliation_plan(),
            dispatch_reconciliation_contract=_contract(),
            post_dispatch_review_handoff=_handoff(),
            dispatch_review_family_closeout_alignment=_family_closeout(),
            reconciliation_claim_map=claim_map,
            arbiter_relation_register=relation_register,
            reconciliation_dissent_register=_dissent_register_for_surfaces(
                claim_map,
                relation_register,
            ),
        )


def test_v212_bundle_rejects_unknown_dissent_relation_ref() -> None:
    dissent_register = RepoReconciliationDissentRegister.model_validate(
        _load_fixture(
            "vnext_plus212",
            "repo_reconciliation_arbiter_v212_reject_dissent_unknown_relation_refs.json",
        )
    )

    with pytest.raises(ValueError, match="known arbiter relation rows"):
        validate_v76a_reconciliation_arbiter_bundle(
            worker_output_reconciliation_plan=_reconciliation_plan(),
            dispatch_reconciliation_contract=_contract(),
            post_dispatch_review_handoff=_handoff(),
            dispatch_review_family_closeout_alignment=_family_closeout(),
            reconciliation_claim_map=_claim_map(),
            arbiter_relation_register=_relation_register(),
            reconciliation_dissent_register=dissent_register,
        )
