from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_POST_RECONCILIATION_HANDOFF_SCHEMA,
    REPO_RECONCILIATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    REPO_RECONCILIATION_REVIEW_SUMMARY_SCHEMA,
    RepoAdversarialRelationReview,
    RepoArbiterAuthorityProfile,
    RepoArbiterRelationRegister,
    RepoPostReconciliationHandoff,
    RepoReconciliationClaimMap,
    RepoReconciliationDissentRegister,
    RepoReconciliationFamilyCloseoutAlignment,
    RepoReconciliationGapScan,
    RepoReconciliationReviewSummary,
    RepoReconciliationSettlementRequest,
    derive_v76c_reconciliation_closeout_bundle,
    validate_v76c_reconciliation_closeout_bundle,
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


def _summary() -> RepoReconciliationReviewSummary:
    return RepoReconciliationReviewSummary.model_validate(
        _load_fixture(
            "vnext_plus214",
            "repo_reconciliation_review_summary_v214_reference.json",
        )
    )


def _handoff() -> RepoPostReconciliationHandoff:
    return RepoPostReconciliationHandoff.model_validate(
        _load_fixture(
            "vnext_plus214",
            "repo_post_reconciliation_handoff_v214_reference.json",
        )
    )


def _closeout_alignment() -> RepoReconciliationFamilyCloseoutAlignment:
    return RepoReconciliationFamilyCloseoutAlignment.model_validate(
        _load_fixture(
            "vnext_plus214",
            "repo_reconciliation_family_closeout_alignment_v214_reference.json",
        )
    )


def test_v214_reference_bundle_validates() -> None:
    summary = _summary()
    handoff = _handoff()
    closeout_alignment = _closeout_alignment()

    assert summary.schema == REPO_RECONCILIATION_REVIEW_SUMMARY_SCHEMA
    assert handoff.schema == REPO_POST_RECONCILIATION_HANDOFF_SCHEMA
    assert closeout_alignment.schema == REPO_RECONCILIATION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA
    assert {row.summary_posture for row in summary.summary_rows} == {
        "blocked_by_authority_gap",
        "ready_for_later_review",
    }

    validate_v76c_reconciliation_closeout_bundle(
        reconciliation_claim_map=_claim_map(),
        arbiter_relation_register=_relation_register(),
        reconciliation_dissent_register=_dissent_register(),
        arbiter_authority_profile=_authority_profile(),
        reconciliation_settlement_request=_settlement_request(),
        adversarial_relation_review=_adversarial_review(),
        reconciliation_gap_scan=_gap_scan(),
        reconciliation_review_summary=summary,
        post_reconciliation_handoff=handoff,
        reconciliation_family_closeout_alignment=closeout_alignment,
    )


def test_v214_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_reconciliation_review_summary.v1.json").validate(
        _load_fixture(
            "vnext_plus214",
            "repo_reconciliation_review_summary_v214_reference.json",
        )
    )
    _schema_validator("repo_post_reconciliation_handoff.v1.json").validate(
        _load_fixture(
            "vnext_plus214",
            "repo_post_reconciliation_handoff_v214_reference.json",
        )
    )
    _schema_validator("repo_reconciliation_family_closeout_alignment.v1.json").validate(
        _load_fixture(
            "vnext_plus214",
            "repo_reconciliation_family_closeout_alignment_v214_reference.json",
        )
    )


def test_v214_derivation_helper_matches_reference_fixtures() -> None:
    summary, handoff, closeout_alignment = derive_v76c_reconciliation_closeout_bundle(
        repo_root=_repo_root()
    )

    assert summary.model_dump(mode="json") == _load_fixture(
        "vnext_plus214",
        "repo_reconciliation_review_summary_v214_reference.json",
    )
    assert handoff.model_dump(mode="json") == _load_fixture(
        "vnext_plus214",
        "repo_post_reconciliation_handoff_v214_reference.json",
    )
    assert closeout_alignment.model_dump(mode="json") == _load_fixture(
        "vnext_plus214",
        "repo_reconciliation_family_closeout_alignment_v214_reference.json",
    )


def test_v214_bundle_rejects_unknown_summary_claim_ref() -> None:
    summary = _summary()
    rows = list(summary.summary_rows)
    rows[0] = rows[0].model_copy(
        update={"claim_map_refs": ["claim-map:v76a:unknown"]},
    )
    summary = summary.model_copy(update={"summary_rows": rows})

    with pytest.raises(ValueError, match="summary rows must reference known claim maps"):
        validate_v76c_reconciliation_closeout_bundle(
            reconciliation_claim_map=_claim_map(),
            arbiter_relation_register=_relation_register(),
            reconciliation_dissent_register=_dissent_register(),
            arbiter_authority_profile=_authority_profile(),
            reconciliation_settlement_request=_settlement_request(),
            adversarial_relation_review=_adversarial_review(),
            reconciliation_gap_scan=_gap_scan(),
            reconciliation_review_summary=summary,
            post_reconciliation_handoff=_handoff(),
            reconciliation_family_closeout_alignment=_closeout_alignment(),
        )


def test_v214_bundle_rejects_unknown_carried_blocker_ref() -> None:
    summary = _summary()
    rows = list(summary.summary_rows)
    rows[0] = rows[0].model_copy(
        update={"carried_blocker_refs": ["gap:v76b:unknown-blocker"]},
    )
    summary = summary.model_copy(update={"summary_rows": rows})

    with pytest.raises(ValueError, match="summary rows must reference known blockers"):
        validate_v76c_reconciliation_closeout_bundle(
            reconciliation_claim_map=_claim_map(),
            arbiter_relation_register=_relation_register(),
            reconciliation_dissent_register=_dissent_register(),
            arbiter_authority_profile=_authority_profile(),
            reconciliation_settlement_request=_settlement_request(),
            adversarial_relation_review=_adversarial_review(),
            reconciliation_gap_scan=_gap_scan(),
            reconciliation_review_summary=summary,
            post_reconciliation_handoff=_handoff(),
            reconciliation_family_closeout_alignment=_closeout_alignment(),
        )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_reconciliation_arbiter_v214_reject_summary_ready_with_blockers.json",
            RepoReconciliationReviewSummary,
            "ready summaries carrying blockers",
        ),
        (
            "repo_reconciliation_arbiter_v214_reject_handoff_product_without_authority.json",
            RepoPostReconciliationHandoff,
            "product handoffs require product authority refs",
        ),
        (
            "repo_reconciliation_arbiter_v214_reject_closeout_selects_v77.json",
            RepoReconciliationFamilyCloseoutAlignment,
            "downstream V76-C authority",
        ),
    ],
)
def test_v214_reject_fixtures_fail_model_validation(
    fixture_name: str,
    model_type: type[
        RepoReconciliationReviewSummary
        | RepoPostReconciliationHandoff
        | RepoReconciliationFamilyCloseoutAlignment
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus214", fixture_name))
