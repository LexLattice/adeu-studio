from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_POST_INCLUSION_HANDOFF_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_REVISION_READINESS_SUMMARY_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_REVISION_REGISTRATION_SCHEMA,
    ProgrambenchLocalMatrixAmendmentPlan,
    ProgrambenchLocalMatrixCandidateIntake,
    ProgrambenchLocalMatrixCaseDeltaManifest,
    ProgrambenchLocalMatrixComparabilityDeltaReview,
    ProgrambenchLocalMatrixContaminationDeltaReview,
    ProgrambenchLocalMatrixInclusionControlContract,
    ProgrambenchLocalMatrixInclusionDecisionRecord,
    ProgrambenchLocalMatrixInclusionEligibilityReview,
    ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment,
    ProgrambenchLocalMatrixInclusionNonAuthorityGuardrail,
    ProgrambenchLocalMatrixInclusionRequest,
    ProgrambenchLocalMatrixPostInclusionHandoff,
    ProgrambenchLocalMatrixRevisionReadinessSummary,
    ProgrambenchLocalMatrixRevisionRegistration,
    validate_pb_matrix_inclusion_0c_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root(arc: str) -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / arc


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root()
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _load_matrix_inclusion_a_rows() -> tuple[
    ProgrambenchLocalMatrixInclusionRequest,
    ProgrambenchLocalMatrixCandidateIntake,
    ProgrambenchLocalMatrixInclusionEligibilityReview,
    ProgrambenchLocalMatrixInclusionControlContract,
    ProgrambenchLocalMatrixInclusionNonAuthorityGuardrail,
]:
    root = _fixture_root("vnext_plus266")
    return (
        ProgrambenchLocalMatrixInclusionRequest.model_validate(
            _load_fixture(
                root,
                "programbench_local_matrix_inclusion_request_v266_reference.json",
            )
        ),
        ProgrambenchLocalMatrixCandidateIntake.model_validate(
            _load_fixture(
                root,
                "programbench_local_matrix_candidate_intake_v266_reference.json",
            )
        ),
        ProgrambenchLocalMatrixInclusionEligibilityReview.model_validate(
            _load_fixture(
                root,
                "programbench_local_matrix_inclusion_eligibility_review_v266_reference.json",
            )
        ),
        ProgrambenchLocalMatrixInclusionControlContract.model_validate(
            _load_fixture(
                root,
                "programbench_local_matrix_inclusion_control_contract_v266_reference.json",
            )
        ),
        ProgrambenchLocalMatrixInclusionNonAuthorityGuardrail.model_validate(
            _load_fixture(
                root,
                "programbench_local_matrix_inclusion_non_authority_guardrail_v266_reference.json",
            )
        ),
    )


def _load_matrix_inclusion_b_rows() -> tuple[
    ProgrambenchLocalMatrixAmendmentPlan,
    ProgrambenchLocalMatrixCaseDeltaManifest,
    ProgrambenchLocalMatrixComparabilityDeltaReview,
    ProgrambenchLocalMatrixContaminationDeltaReview,
    ProgrambenchLocalMatrixInclusionDecisionRecord,
]:
    root = _fixture_root("vnext_plus267")
    return (
        ProgrambenchLocalMatrixAmendmentPlan.model_validate(
            _load_fixture(root, "programbench_local_matrix_amendment_plan_v267_reference.json")
        ),
        ProgrambenchLocalMatrixCaseDeltaManifest.model_validate(
            _load_fixture(
                root,
                "programbench_local_matrix_case_delta_manifest_v267_reference.json",
            )
        ),
        ProgrambenchLocalMatrixComparabilityDeltaReview.model_validate(
            _load_fixture(
                root,
                "programbench_local_matrix_comparability_delta_review_v267_reference.json",
            )
        ),
        ProgrambenchLocalMatrixContaminationDeltaReview.model_validate(
            _load_fixture(
                root,
                "programbench_local_matrix_contamination_delta_review_v267_reference.json",
            )
        ),
        ProgrambenchLocalMatrixInclusionDecisionRecord.model_validate(
            _load_fixture(
                root,
                "programbench_local_matrix_inclusion_decision_record_v267_reference.json",
            )
        ),
    )


def _load_matrix_inclusion_c_rows() -> tuple[
    ProgrambenchLocalMatrixRevisionRegistration,
    ProgrambenchLocalMatrixRevisionReadinessSummary,
    ProgrambenchLocalMatrixPostInclusionHandoff,
    ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment,
]:
    root = _fixture_root("vnext_plus268")
    return (
        ProgrambenchLocalMatrixRevisionRegistration.model_validate(
            _load_fixture(
                root,
                "programbench_local_matrix_revision_registration_v268_reference.json",
            )
        ),
        ProgrambenchLocalMatrixRevisionReadinessSummary.model_validate(
            _load_fixture(
                root,
                "programbench_local_matrix_revision_readiness_summary_v268_reference.json",
            )
        ),
        ProgrambenchLocalMatrixPostInclusionHandoff.model_validate(
            _load_fixture(
                root,
                "programbench_local_matrix_post_inclusion_handoff_v268_reference.json",
            )
        ),
        ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment.model_validate(
            _load_fixture(
                root,
                "programbench_local_matrix_inclusion_family_closeout_alignment_v268_reference.json",
            )
        ),
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_LOCAL_MATRIX_REVISION_REGISTRATION_SCHEMA,
            "programbench_local_matrix_revision_registration.v1.json",
            "programbench_local_matrix_revision_registration_v268_reference.json",
            ProgrambenchLocalMatrixRevisionRegistration,
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_REVISION_READINESS_SUMMARY_SCHEMA,
            "programbench_local_matrix_revision_readiness_summary.v1.json",
            "programbench_local_matrix_revision_readiness_summary_v268_reference.json",
            ProgrambenchLocalMatrixRevisionReadinessSummary,
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_POST_INCLUSION_HANDOFF_SCHEMA,
            "programbench_local_matrix_post_inclusion_handoff.v1.json",
            "programbench_local_matrix_post_inclusion_handoff_v268_reference.json",
            ProgrambenchLocalMatrixPostInclusionHandoff,
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            "programbench_local_matrix_inclusion_family_closeout_alignment.v1.json",
            "programbench_local_matrix_inclusion_family_closeout_alignment_v268_reference.json",
            ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment,
        ),
    ],
)
def test_pb_matrix_inclusion_0c_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_fixture(_fixture_root("vnext_plus268"), fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_matrix_inclusion_0c_reference_bundle_closes_family() -> None:
    request, intake, eligibility, control, guardrail = _load_matrix_inclusion_a_rows()
    amendment, delta, comparability, contamination, decision = (
        _load_matrix_inclusion_b_rows()
    )
    registration, readiness, handoff, closeout = _load_matrix_inclusion_c_rows()

    validate_pb_matrix_inclusion_0c_bundle(
        inclusion_request=request,
        candidate_intake=intake,
        eligibility_review=eligibility,
        control_contract=control,
        non_authority_guardrail=guardrail,
        amendment_plan=amendment,
        case_delta_manifest=delta,
        comparability_delta_review=comparability,
        contamination_delta_review=contamination,
        inclusion_decision_record=decision,
        revision_registration=registration,
        revision_readiness_summary=readiness,
        post_inclusion_handoff=handoff,
        family_closeout=closeout,
    )


def test_pb_matrix_inclusion_0c_rejects_registration_membership_not_decided() -> None:
    request, intake, eligibility, control, guardrail = _load_matrix_inclusion_a_rows()
    amendment, delta, comparability, contamination, decision = (
        _load_matrix_inclusion_b_rows()
    )
    registration, readiness, handoff, closeout = _load_matrix_inclusion_c_rows()
    bad_registration = registration.model_copy(
        update={
            "included_case_lineage_refs": [],
            "deferred_case_lineage_refs": decision.included_case_lineage_refs,
        }
    )

    with pytest.raises(ValueError, match="revision included membership"):
        validate_pb_matrix_inclusion_0c_bundle(
            inclusion_request=request,
            candidate_intake=intake,
            eligibility_review=eligibility,
            control_contract=control,
            non_authority_guardrail=guardrail,
            amendment_plan=amendment,
            case_delta_manifest=delta,
            comparability_delta_review=comparability,
            contamination_delta_review=contamination,
            inclusion_decision_record=decision,
            revision_registration=bad_registration,
            revision_readiness_summary=readiness,
            post_inclusion_handoff=handoff,
            family_closeout=closeout,
        )


@pytest.mark.parametrize(
    ("field_name", "expected_message"),
    [
        ("matrix_amendment_plan_hash", "amendment plan hash"),
        ("contamination_delta_review_hash", "contamination delta review hash"),
        ("inclusion_decision_hash", "inclusion decision hash"),
    ],
)
def test_pb_matrix_inclusion_0c_rejects_registration_b_artifact_hash_drift(
    field_name: str,
    expected_message: str,
) -> None:
    request, intake, eligibility, control, guardrail = _load_matrix_inclusion_a_rows()
    amendment, delta, comparability, contamination, decision = (
        _load_matrix_inclusion_b_rows()
    )
    registration, readiness, handoff, closeout = _load_matrix_inclusion_c_rows()
    bad_registration = registration.model_copy(
        update={field_name: "sha256:" + "f" * 64}
    )

    with pytest.raises(ValueError, match=expected_message):
        validate_pb_matrix_inclusion_0c_bundle(
            inclusion_request=request,
            candidate_intake=intake,
            eligibility_review=eligibility,
            control_contract=control,
            non_authority_guardrail=guardrail,
            amendment_plan=amendment,
            case_delta_manifest=delta,
            comparability_delta_review=comparability,
            contamination_delta_review=contamination,
            inclusion_decision_record=decision,
            revision_registration=bad_registration,
            revision_readiness_summary=readiness,
            post_inclusion_handoff=handoff,
            family_closeout=closeout,
        )


def test_pb_matrix_inclusion_0c_rejects_readiness_forbidden_top_level_ref() -> None:
    payload = _load_fixture(
        _fixture_root("vnext_plus268"),
        "programbench_local_matrix_revision_readiness_summary_v268_reference.json",
    )
    payload["matrix_revision_readiness_summary_ref"] = (
        "matrix-revision-readiness:hidden-test:leak"
    )

    with pytest.raises(ValidationError, match="revision_readiness_top_level_refs"):
        ProgrambenchLocalMatrixRevisionReadinessSummary.model_validate(payload)


def test_pb_matrix_inclusion_0c_closeout_slice_refs_are_order_insensitive() -> None:
    payload = _load_fixture(
        _fixture_root("vnext_plus268"),
        "programbench_local_matrix_inclusion_family_closeout_alignment_v268_reference.json",
    )
    payload["closed_slice_refs"] = [
        "PB-MATRIX-INCLUSION-0-C",
        "PB-MATRIX-INCLUSION-0-A",
        "PB-MATRIX-INCLUSION-0-B",
    ]

    ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment.model_validate(payload)


def test_pb_matrix_inclusion_0c_rejects_readiness_result_language() -> None:
    payload = _load_fixture(
        _fixture_root("vnext_plus268"),
        "programbench_local_matrix_revision_readiness_summary_v268_reference.json",
    )
    payload["limitation_note"] = "This is a success rate for the local matrix."

    with pytest.raises(ValidationError, match="benchmark-like scoring"):
        ProgrambenchLocalMatrixRevisionReadinessSummary.model_validate(payload)


def test_pb_matrix_inclusion_0c_rejects_handoff_authority_language() -> None:
    payload = _load_fixture(
        _fixture_root("vnext_plus268"),
        "programbench_local_matrix_post_inclusion_handoff_v268_reference.json",
    )
    payload["limitation_note"] = "This handoff selects the leaderboard path."

    with pytest.raises(ValidationError, match="benchmark-like scoring"):
        ProgrambenchLocalMatrixPostInclusionHandoff.model_validate(payload)


def test_pb_matrix_inclusion_0c_rejects_closeout_missing_slice() -> None:
    payload = _load_fixture(
        _fixture_root("vnext_plus268"),
        "programbench_local_matrix_inclusion_family_closeout_alignment_v268_reference.json",
    )
    payload["closed_slice_refs"] = [
        "PB-MATRIX-INCLUSION-0-A",
        "PB-MATRIX-INCLUSION-0-B",
    ]

    with pytest.raises(ValidationError, match="close A, B, and C"):
        ProgrambenchLocalMatrixInclusionFamilyCloseoutAlignment.model_validate(payload)


def test_pb_matrix_inclusion_0c_schema_exports_are_current() -> None:
    export_schema_main()
    root = _repo_root()
    for schema_name in (
        "programbench_local_matrix_revision_registration.v1.json",
        "programbench_local_matrix_revision_readiness_summary.v1.json",
        "programbench_local_matrix_post_inclusion_handoff.v1.json",
        "programbench_local_matrix_inclusion_family_closeout_alignment.v1.json",
    ):
        authoritative = (
            root / "packages" / "adeu_benchmarking" / "schema" / schema_name
        ).read_text(encoding="utf-8")
        mirror = (
            root
            / "spec"
            / schema_name.replace(".v1.json", ".schema.json")
        ).read_text(encoding="utf-8")
        assert json.loads(authoritative) == json.loads(mirror)
