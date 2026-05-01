from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import adeu_repo_description.reconciliation_arbiter as reconciliation_arbiter_module
import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_ADVERSARIAL_RELATION_REVIEW_SCHEMA,
    REPO_ARBITER_AUTHORITY_PROFILE_SCHEMA,
    REPO_RECONCILIATION_GAP_SCAN_SCHEMA,
    REPO_RECONCILIATION_SETTLEMENT_REQUEST_SCHEMA,
    RepoAdversarialRelationReview,
    RepoArbiterAuthorityProfile,
    RepoArbiterRelationRegister,
    RepoReconciliationClaimMap,
    RepoReconciliationDissentRegister,
    RepoReconciliationGapScan,
    RepoReconciliationSettlementRequest,
    derive_v76b_reconciliation_arbiter_bundle,
    validate_v76b_reconciliation_arbiter_bundle,
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


def _authority_profile() -> RepoArbiterAuthorityProfile:
    return RepoArbiterAuthorityProfile.model_validate(
        _load_fixture("vnext_plus213", "repo_arbiter_authority_profile_v213_reference.json")
    )


def _settlement_request() -> RepoReconciliationSettlementRequest:
    return RepoReconciliationSettlementRequest.model_validate(
        _load_fixture(
            "vnext_plus213",
            "repo_reconciliation_settlement_request_v213_reference.json",
        )
    )


def _adversarial_review() -> RepoAdversarialRelationReview:
    return RepoAdversarialRelationReview.model_validate(
        _load_fixture("vnext_plus213", "repo_adversarial_relation_review_v213_reference.json")
    )


def _gap_scan() -> RepoReconciliationGapScan:
    return RepoReconciliationGapScan.model_validate(
        _load_fixture("vnext_plus213", "repo_reconciliation_gap_scan_v213_reference.json")
    )


def test_v213_reference_bundle_validates() -> None:
    authority_profile = _authority_profile()
    settlement_request = _settlement_request()
    adversarial_review = _adversarial_review()
    gap_scan = _gap_scan()

    assert authority_profile.schema == REPO_ARBITER_AUTHORITY_PROFILE_SCHEMA
    assert settlement_request.schema == REPO_RECONCILIATION_SETTLEMENT_REQUEST_SCHEMA
    assert adversarial_review.schema == REPO_ADVERSARIAL_RELATION_REVIEW_SCHEMA
    assert gap_scan.schema == REPO_RECONCILIATION_GAP_SCAN_SCHEMA
    assert {
        row.settlement_request_posture
        for row in settlement_request.settlement_request_rows
    } == {"blocked_by_authority_gap", "request_ready_for_later_review"}

    validate_v76b_reconciliation_arbiter_bundle(
        reconciliation_claim_map=_claim_map(),
        arbiter_relation_register=_relation_register(),
        reconciliation_dissent_register=_dissent_register(),
        arbiter_authority_profile=authority_profile,
        reconciliation_settlement_request=settlement_request,
        adversarial_relation_review=adversarial_review,
        reconciliation_gap_scan=gap_scan,
    )


def test_v213_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_arbiter_authority_profile.v1.json").validate(
        _load_fixture("vnext_plus213", "repo_arbiter_authority_profile_v213_reference.json")
    )
    _schema_validator("repo_reconciliation_settlement_request.v1.json").validate(
        _load_fixture(
            "vnext_plus213",
            "repo_reconciliation_settlement_request_v213_reference.json",
        )
    )
    _schema_validator("repo_adversarial_relation_review.v1.json").validate(
        _load_fixture("vnext_plus213", "repo_adversarial_relation_review_v213_reference.json")
    )
    _schema_validator("repo_reconciliation_gap_scan.v1.json").validate(
        _load_fixture("vnext_plus213", "repo_reconciliation_gap_scan_v213_reference.json")
    )


def test_v213_derivation_helper_matches_reference_fixtures() -> None:
    authority_profile, settlement_request, adversarial_review, gap_scan = (
        derive_v76b_reconciliation_arbiter_bundle(repo_root=_repo_root())
    )

    assert authority_profile.model_dump(mode="json") == _load_fixture(
        "vnext_plus213",
        "repo_arbiter_authority_profile_v213_reference.json",
    )
    assert settlement_request.model_dump(mode="json") == _load_fixture(
        "vnext_plus213",
        "repo_reconciliation_settlement_request_v213_reference.json",
    )
    assert adversarial_review.model_dump(mode="json") == _load_fixture(
        "vnext_plus213",
        "repo_adversarial_relation_review_v213_reference.json",
    )
    assert gap_scan.model_dump(mode="json") == _load_fixture(
        "vnext_plus213",
        "repo_reconciliation_gap_scan_v213_reference.json",
    )


def test_v213_partial_derivation_chains_from_supplied_claim_map(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def _fail_default_bundle(**_: Any) -> None:
        raise AssertionError("full default V76-A bundle should not be derived")

    monkeypatch.setattr(
        reconciliation_arbiter_module,
        "derive_v76a_reconciliation_arbiter_bundle",
        _fail_default_bundle,
    )

    claim_map = _claim_map()
    authority_profile = reconciliation_arbiter_module.derive_v76b_repo_arbiter_authority_profile(
        repo_root=_repo_root(),
        reconciliation_claim_map=claim_map,
    )

    assert authority_profile.reconciliation_claim_map_id == claim_map.reconciliation_claim_map_id


def test_v213_partial_derivation_rejects_relation_without_claim_map() -> None:
    with pytest.raises(ValueError, match="partial V76-A dependencies must include the claim map"):
        reconciliation_arbiter_module.derive_v76b_repo_adversarial_relation_review(
            repo_root=_repo_root(),
            arbiter_relation_register=_relation_register(),
        )


def test_v213_authority_profile_rejects_non_lock_no_gap_posture() -> None:
    payload = _load_fixture(
        "vnext_plus213",
        "repo_arbiter_authority_profile_v213_reference.json",
    )
    payload["authority_profile_rows"][0]["authority_gap_posture"] = "authority_gap_missing"

    with pytest.raises(ValidationError, match="non-lock grant sources"):
        RepoArbiterAuthorityProfile.model_validate(payload)


def test_v213_settlement_overclaim_scans_later_unnegated_occurrences() -> None:
    payload = _load_fixture(
        "vnext_plus213",
        "repo_reconciliation_settlement_request_v213_reference.json",
    )
    payload["settlement_request_rows"][0]["limitation_note"] = (
        "This is not settlement complete as a review note, but settlement complete."
    )

    with pytest.raises(ValidationError, match="settlement or truth authority"):
        RepoReconciliationSettlementRequest.model_validate(payload)


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_reconciliation_arbiter_v213_reject_authority_profile_truth_authority.json",
            RepoArbiterAuthorityProfile,
            "settlement or truth authority",
        ),
        (
            "repo_reconciliation_arbiter_v213_reject_settlement_performs_settlement.json",
            RepoReconciliationSettlementRequest,
            "truth or correctness authority",
        ),
        (
            "repo_reconciliation_arbiter_v213_reject_no_counterevidence_without_horizon.json",
            RepoAdversarialRelationReview,
            "counterclaim_horizon must be non-empty",
        ),
        (
            "repo_reconciliation_arbiter_v213_reject_majority_agreement_as_correctness.json",
            RepoArbiterAuthorityProfile,
            "truth or correctness authority",
        ),
        (
            "repo_reconciliation_arbiter_v213_reject_gap_as_implementation_priority.json",
            RepoReconciliationGapScan,
            "settlement or truth authority",
        ),
    ],
)
def test_v213_reject_fixtures_fail_model_validation(
    fixture_name: str,
    model_type: type[
        RepoArbiterAuthorityProfile
        | RepoReconciliationSettlementRequest
        | RepoAdversarialRelationReview
        | RepoReconciliationGapScan
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus213", fixture_name))


def test_v213_bundle_rejects_unknown_claim_map_ref() -> None:
    settlement_request = RepoReconciliationSettlementRequest.model_validate(
        _load_fixture(
            "vnext_plus213",
            "repo_reconciliation_arbiter_v213_reject_settlement_unknown_claim_map.json",
        )
    )

    with pytest.raises(ValueError, match="known claim maps"):
        validate_v76b_reconciliation_arbiter_bundle(
            reconciliation_claim_map=_claim_map(),
            arbiter_relation_register=_relation_register(),
            reconciliation_dissent_register=_dissent_register(),
            arbiter_authority_profile=_authority_profile(),
            reconciliation_settlement_request=settlement_request,
            adversarial_relation_review=_adversarial_review(),
            reconciliation_gap_scan=_gap_scan(),
        )


def test_v213_bundle_rejects_settlement_horizon_outside_authority_profile() -> None:
    settlement_request = RepoReconciliationSettlementRequest.model_validate(
        _load_fixture(
            "vnext_plus213",
            "repo_reconciliation_arbiter_v213_reject_settlement_horizon_not_allowed.json",
        )
    )

    with pytest.raises(ValueError, match="settlement horizon"):
        validate_v76b_reconciliation_arbiter_bundle(
            reconciliation_claim_map=_claim_map(),
            arbiter_relation_register=_relation_register(),
            reconciliation_dissent_register=_dissent_register(),
            arbiter_authority_profile=_authority_profile(),
            reconciliation_settlement_request=settlement_request,
            adversarial_relation_review=_adversarial_review(),
            reconciliation_gap_scan=_gap_scan(),
        )


def test_v213_bundle_rejects_ready_request_with_blocking_dissent() -> None:
    settlement_request = RepoReconciliationSettlementRequest.model_validate(
        _load_fixture(
            "vnext_plus213",
            "repo_reconciliation_arbiter_v213_reject_settlement_ignores_blocking_dissent.json",
        )
    )

    with pytest.raises(ValueError, match="blocking dissent"):
        validate_v76b_reconciliation_arbiter_bundle(
            reconciliation_claim_map=_claim_map(),
            arbiter_relation_register=_relation_register(),
            reconciliation_dissent_register=_dissent_register(),
            arbiter_authority_profile=_authority_profile(),
            reconciliation_settlement_request=settlement_request,
            adversarial_relation_review=_adversarial_review(),
            reconciliation_gap_scan=_gap_scan(),
        )


def test_v213_bundle_rejects_downstream_gap_as_ready() -> None:
    settlement_request = RepoReconciliationSettlementRequest.model_validate(
        _load_fixture(
            "vnext_plus213",
            "repo_reconciliation_arbiter_v213_reject_downstream_gap_as_ready.json",
        )
    )

    with pytest.raises(ValueError, match="downstream authority gaps"):
        validate_v76b_reconciliation_arbiter_bundle(
            reconciliation_claim_map=_claim_map(),
            arbiter_relation_register=_relation_register(),
            reconciliation_dissent_register=_dissent_register(),
            arbiter_authority_profile=_authority_profile(),
            reconciliation_settlement_request=settlement_request,
            adversarial_relation_review=_adversarial_review(),
            reconciliation_gap_scan=_gap_scan(),
        )
