from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_LOCAL_MATRIX_AMENDMENT_PLAN_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_CASE_DELTA_MANIFEST_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_COMPARABILITY_DELTA_REVIEW_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_CONTAMINATION_DELTA_REVIEW_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_DECISION_RECORD_SCHEMA,
    ProgrambenchLocalMatrixAmendmentPlan,
    ProgrambenchLocalMatrixCandidateIntake,
    ProgrambenchLocalMatrixCaseDeltaManifest,
    ProgrambenchLocalMatrixComparabilityDeltaReview,
    ProgrambenchLocalMatrixContaminationDeltaReview,
    ProgrambenchLocalMatrixInclusionControlContract,
    ProgrambenchLocalMatrixInclusionDecisionRecord,
    ProgrambenchLocalMatrixInclusionEligibilityReview,
    ProgrambenchLocalMatrixInclusionNonAuthorityGuardrail,
    ProgrambenchLocalMatrixInclusionRequest,
    validate_pb_matrix_inclusion_0b_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root_matrix_inclusion_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus266"


def _fixture_root_matrix_inclusion_b() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus267"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_matrix_inclusion_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_matrix_inclusion_a(), name)


def _load_matrix_inclusion_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_matrix_inclusion_b(), name)


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


def _schema_pairs() -> list[tuple[str, Path, Path]]:
    root = _repo_root()
    return [
        (
            PROGRAMBENCH_LOCAL_MATRIX_AMENDMENT_PLAN_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_matrix_amendment_plan.v1.json",
            root / "spec" / "programbench_local_matrix_amendment_plan.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_CASE_DELTA_MANIFEST_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_matrix_case_delta_manifest.v1.json",
            root / "spec" / "programbench_local_matrix_case_delta_manifest.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_COMPARABILITY_DELTA_REVIEW_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_matrix_comparability_delta_review.v1.json",
            root
            / "spec"
            / "programbench_local_matrix_comparability_delta_review.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_CONTAMINATION_DELTA_REVIEW_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_matrix_contamination_delta_review.v1.json",
            root
            / "spec"
            / "programbench_local_matrix_contamination_delta_review.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_DECISION_RECORD_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_matrix_inclusion_decision_record.v1.json",
            root
            / "spec"
            / "programbench_local_matrix_inclusion_decision_record.schema.json",
        ),
    ]


def _load_matrix_inclusion_a_rows() -> tuple[
    ProgrambenchLocalMatrixInclusionRequest,
    ProgrambenchLocalMatrixCandidateIntake,
    ProgrambenchLocalMatrixInclusionEligibilityReview,
    ProgrambenchLocalMatrixInclusionControlContract,
    ProgrambenchLocalMatrixInclusionNonAuthorityGuardrail,
]:
    return (
        ProgrambenchLocalMatrixInclusionRequest.model_validate(
            _load_matrix_inclusion_a_fixture(
                "programbench_local_matrix_inclusion_request_v266_reference.json"
            )
        ),
        ProgrambenchLocalMatrixCandidateIntake.model_validate(
            _load_matrix_inclusion_a_fixture(
                "programbench_local_matrix_candidate_intake_v266_reference.json"
            )
        ),
        ProgrambenchLocalMatrixInclusionEligibilityReview.model_validate(
            _load_matrix_inclusion_a_fixture(
                "programbench_local_matrix_inclusion_eligibility_review_v266_reference.json"
            )
        ),
        ProgrambenchLocalMatrixInclusionControlContract.model_validate(
            _load_matrix_inclusion_a_fixture(
                "programbench_local_matrix_inclusion_control_contract_v266_reference.json"
            )
        ),
        ProgrambenchLocalMatrixInclusionNonAuthorityGuardrail.model_validate(
            _load_matrix_inclusion_a_fixture(
                "programbench_local_matrix_inclusion_non_authority_guardrail_v266_reference.json"
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
    return (
        ProgrambenchLocalMatrixAmendmentPlan.model_validate(
            _load_matrix_inclusion_b_fixture(
                "programbench_local_matrix_amendment_plan_v267_reference.json"
            )
        ),
        ProgrambenchLocalMatrixCaseDeltaManifest.model_validate(
            _load_matrix_inclusion_b_fixture(
                "programbench_local_matrix_case_delta_manifest_v267_reference.json"
            )
        ),
        ProgrambenchLocalMatrixComparabilityDeltaReview.model_validate(
            _load_matrix_inclusion_b_fixture(
                "programbench_local_matrix_comparability_delta_review_v267_reference.json"
            )
        ),
        ProgrambenchLocalMatrixContaminationDeltaReview.model_validate(
            _load_matrix_inclusion_b_fixture(
                "programbench_local_matrix_contamination_delta_review_v267_reference.json"
            )
        ),
        ProgrambenchLocalMatrixInclusionDecisionRecord.model_validate(
            _load_matrix_inclusion_b_fixture(
                "programbench_local_matrix_inclusion_decision_record_v267_reference.json"
            )
        ),
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_LOCAL_MATRIX_AMENDMENT_PLAN_SCHEMA,
            "programbench_local_matrix_amendment_plan.v1.json",
            "programbench_local_matrix_amendment_plan_v267_reference.json",
            ProgrambenchLocalMatrixAmendmentPlan,
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_CASE_DELTA_MANIFEST_SCHEMA,
            "programbench_local_matrix_case_delta_manifest.v1.json",
            "programbench_local_matrix_case_delta_manifest_v267_reference.json",
            ProgrambenchLocalMatrixCaseDeltaManifest,
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_COMPARABILITY_DELTA_REVIEW_SCHEMA,
            "programbench_local_matrix_comparability_delta_review.v1.json",
            "programbench_local_matrix_comparability_delta_review_v267_reference.json",
            ProgrambenchLocalMatrixComparabilityDeltaReview,
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_CONTAMINATION_DELTA_REVIEW_SCHEMA,
            "programbench_local_matrix_contamination_delta_review.v1.json",
            "programbench_local_matrix_contamination_delta_review_v267_reference.json",
            ProgrambenchLocalMatrixContaminationDeltaReview,
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_DECISION_RECORD_SCHEMA,
            "programbench_local_matrix_inclusion_decision_record.v1.json",
            "programbench_local_matrix_inclusion_decision_record_v267_reference.json",
            ProgrambenchLocalMatrixInclusionDecisionRecord,
        ),
    ],
)
def test_pb_matrix_inclusion_0b_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_matrix_inclusion_b_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_matrix_inclusion_0b_reference_bundle_records_local_membership_only() -> None:
    request, intake, eligibility, control, guardrail = _load_matrix_inclusion_a_rows()
    amendment, delta, comparability, contamination, decision = (
        _load_matrix_inclusion_b_rows()
    )

    validate_pb_matrix_inclusion_0b_bundle(
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
    )


def test_pb_matrix_inclusion_0b_rejects_missing_a_eligible_candidate() -> None:
    request, intake, eligibility, control, guardrail = _load_matrix_inclusion_a_rows()
    amendment_payload = _load_matrix_inclusion_b_fixture(
        "programbench_local_matrix_amendment_plan_v267_reference.json"
    )
    amendment_payload["planned_added_case_lineage_refs"] = [
        "case-lineage:pb-case-expansion-0c:other"
    ]
    amendment = ProgrambenchLocalMatrixAmendmentPlan.model_validate(amendment_payload)
    delta, comparability, contamination, decision = _load_matrix_inclusion_b_rows()[1:]

    with pytest.raises(ValueError, match="A-eligible candidate"):
        validate_pb_matrix_inclusion_0b_bundle(
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
        )


def test_pb_matrix_inclusion_0b_rejects_duplicate_delta_rows() -> None:
    payload = _load_matrix_inclusion_b_fixture(
        "programbench_local_matrix_case_delta_manifest_v267_reference.json"
    )
    payload["case_delta_rows"].append(
        {
            **payload["case_delta_rows"][0],
            "case_delta_ref": "matrix-case-delta:pb-matrix-inclusion-0b:duplicate",
        }
    )

    with pytest.raises(ValidationError, match="case_delta_lineage_refs"):
        ProgrambenchLocalMatrixCaseDeltaManifest.model_validate(payload)


def test_pb_matrix_inclusion_0b_rejects_soft_performance_decision_basis() -> None:
    payload = _load_matrix_inclusion_b_fixture(
        "programbench_local_matrix_inclusion_decision_record_v267_reference.json"
    )
    payload["decision_basis_rows"][0]["limitation_note"] = "Likely pass for the model."

    with pytest.raises(ValidationError, match="scoring or ranking language"):
        ProgrambenchLocalMatrixInclusionDecisionRecord.model_validate(payload)


def test_pb_matrix_inclusion_0b_ties_decision_basis_to_recorded_outcome() -> None:
    payload = _load_matrix_inclusion_b_fixture(
        "programbench_local_matrix_inclusion_decision_record_v267_reference.json"
    )
    payload["decision_basis_rows"][0]["decision_basis_kind"] = "contamination_blocked"

    with pytest.raises(ValidationError, match="included lineage refs"):
        ProgrambenchLocalMatrixInclusionDecisionRecord.model_validate(payload)


def test_pb_matrix_inclusion_0b_allows_rejected_only_accounting_decision() -> None:
    payload = _load_matrix_inclusion_b_fixture(
        "programbench_local_matrix_inclusion_decision_record_v267_reference.json"
    )
    payload["included_case_lineage_refs"] = []
    payload["rejected_case_lineage_refs"] = [
        "case-lineage:pb-case-expansion-0c:diagnostic"
    ]
    payload["decision_basis_rows"][0]["decision_basis_kind"] = "dedupe_blocked"

    ProgrambenchLocalMatrixInclusionDecisionRecord.model_validate(payload)


def test_pb_matrix_inclusion_0b_rejects_unchanged_hash_mismatch() -> None:
    payload = _load_matrix_inclusion_b_fixture(
        "programbench_local_matrix_comparability_delta_review_v267_reference.json"
    )
    payload["candidate_worker_profile_hash"] = (
        "sha256:2727272727272727272727272727272727272727272727272727272727272727"
    )

    with pytest.raises(ValidationError, match="cannot be unchanged"):
        ProgrambenchLocalMatrixComparabilityDeltaReview.model_validate(payload)


def test_pb_matrix_inclusion_0b_rejects_changed_hash_match() -> None:
    payload = _load_matrix_inclusion_b_fixture(
        "programbench_local_matrix_comparability_delta_review_v267_reference.json"
    )
    payload["worker_profile_delta_posture"] = (
        "changed_non_comparable_local_accounting_only"
    )
    payload["non_comparable_local_accounting_posture"] = (
        "changed_controls_non_comparable_local_accounting_only"
    )

    with pytest.raises(ValidationError, match="cannot be changed"):
        ProgrambenchLocalMatrixComparabilityDeltaReview.model_validate(payload)


def test_pb_matrix_inclusion_0b_rejects_contamination_summary_laundering() -> None:
    payload = _load_matrix_inclusion_b_fixture(
        "programbench_local_matrix_contamination_delta_review_v267_reference.json"
    )
    payload["limitation_note"] = "Redacted hidden test name was summarized here."

    with pytest.raises(ValidationError, match="hidden, forbidden"):
        ProgrambenchLocalMatrixContaminationDeltaReview.model_validate(payload)


def test_pb_matrix_inclusion_0b_rejects_inclusion_with_contaminated_transfer() -> None:
    request, intake, eligibility, control, guardrail = _load_matrix_inclusion_a_rows()
    amendment, delta, comparability, _, decision = _load_matrix_inclusion_b_rows()
    contamination_payload = _load_matrix_inclusion_b_fixture(
        "programbench_local_matrix_contamination_delta_review_v267_reference.json"
    )
    contamination_payload["contamination_transfer_status"] = "blocked"
    contamination_payload["cleanroom_boundary_status"] = "blocked"
    contamination_payload["contamination_delta_rows"][0][
        "contamination_source_kind"
    ] = "source_derived_exposure"
    contamination_payload["contamination_delta_rows"][0][
        "contamination_delta_status"
    ] = "blocked"
    contamination_payload["contamination_delta_rows"][0][
        "limitation_note"
    ] = "Blocked by category-only contamination review."
    contamination = ProgrambenchLocalMatrixContaminationDeltaReview.model_validate(
        contamination_payload
    )

    with pytest.raises(ValueError, match="contaminated transfers"):
        validate_pb_matrix_inclusion_0b_bundle(
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
        )


def test_pb_matrix_inclusion_0b_bundle_rejects_decision_basis_delta_mismatch() -> None:
    request, intake, eligibility, control, guardrail = _load_matrix_inclusion_a_rows()
    amendment, delta, comparability, contamination, decision = (
        _load_matrix_inclusion_b_rows()
    )
    amendment_payload = amendment.model_dump(by_alias=True)
    amendment_payload["planned_added_case_lineage_refs"] = []
    amendment_payload["planned_deferred_case_lineage_refs"] = [
        "case-lineage:pb-case-expansion-0c:diagnostic"
    ]
    amendment = ProgrambenchLocalMatrixAmendmentPlan.model_validate(amendment_payload)
    delta_payload = delta.model_dump(by_alias=True)
    delta_payload["case_delta_rows"][0]["case_delta_kind"] = (
        "deferred_from_revision_candidate"
    )
    delta_payload["case_delta_rows"][0]["new_matrix_membership_candidate_status"] = (
        "planned_deferred"
    )
    delta_payload["case_delta_rows"][0]["delta_reason"] = "matrix_capacity_deferred"
    delta = ProgrambenchLocalMatrixCaseDeltaManifest.model_validate(delta_payload)
    decision_payload = decision.model_dump(by_alias=True)
    decision_payload["included_case_lineage_refs"] = []
    decision_payload["deferred_case_lineage_refs"] = [
        "case-lineage:pb-case-expansion-0c:diagnostic"
    ]
    decision_payload["inclusion_decision_status"] = "open_with_deferred_candidates"
    decision_payload["decision_basis_rows"][0][
        "decision_basis_kind"
    ] = "horizon_mismatch_deferred"
    decision = ProgrambenchLocalMatrixInclusionDecisionRecord.model_validate(
        decision_payload
    )

    with pytest.raises(ValueError, match="decision basis kinds"):
        validate_pb_matrix_inclusion_0b_bundle(
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
        )


def test_pb_matrix_inclusion_0b_schema_exports_are_current() -> None:
    export_schema_main()
    for schema_name, authoritative_path, mirror_path in _schema_pairs():
        assert authoritative_path.exists(), schema_name
        assert mirror_path.exists(), schema_name
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))
        assert authoritative == mirror
        assert authoritative["properties"]["schema"]["const"] == schema_name
