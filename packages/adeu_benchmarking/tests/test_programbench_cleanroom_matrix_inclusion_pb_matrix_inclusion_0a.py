from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_LOCAL_MATRIX_CANDIDATE_INTAKE_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_CONTROL_CONTRACT_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_ELIGIBILITY_REVIEW_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_REQUEST_SCHEMA,
    ProgrambenchLocalCaseExpansionFamilyCloseoutAlignment,
    ProgrambenchLocalCaseExpansionReadinessSummary,
    ProgrambenchLocalCaseLineageRegistration,
    ProgrambenchLocalCaseMatrixCandidateHandoff,
    ProgrambenchLocalCaseMatrixFamilyCloseoutAlignment,
    ProgrambenchLocalMatrixCandidateIntake,
    ProgrambenchLocalMatrixInclusionControlContract,
    ProgrambenchLocalMatrixInclusionEligibilityReview,
    ProgrambenchLocalMatrixInclusionNonAuthorityGuardrail,
    ProgrambenchLocalMatrixInclusionRequest,
    validate_pb_matrix_inclusion_0a_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root_matrix_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus262"


def _fixture_root_case_expansion_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus265"


def _fixture_root_matrix_inclusion_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus266"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_matrix_inclusion_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_matrix_inclusion_a(), name)


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
            PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_REQUEST_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_matrix_inclusion_request.v1.json",
            root / "spec" / "programbench_local_matrix_inclusion_request.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_CANDIDATE_INTAKE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_matrix_candidate_intake.v1.json",
            root / "spec" / "programbench_local_matrix_candidate_intake.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_ELIGIBILITY_REVIEW_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_matrix_inclusion_eligibility_review.v1.json",
            root
            / "spec"
            / "programbench_local_matrix_inclusion_eligibility_review.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_CONTROL_CONTRACT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_matrix_inclusion_control_contract.v1.json",
            root
            / "spec"
            / "programbench_local_matrix_inclusion_control_contract.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_matrix_inclusion_non_authority_guardrail.v1.json",
            root
            / "spec"
            / "programbench_local_matrix_inclusion_non_authority_guardrail.schema.json",
        ),
    ]


def _load_matrix_closeout() -> ProgrambenchLocalCaseMatrixFamilyCloseoutAlignment:
    return ProgrambenchLocalCaseMatrixFamilyCloseoutAlignment.model_validate(
        _load_fixture(
            _fixture_root_matrix_c(),
            "programbench_local_case_matrix_family_closeout_alignment_v262_reference.json",
        )
    )


def _load_case_expansion_closeout_rows() -> tuple[
    ProgrambenchLocalCaseExpansionFamilyCloseoutAlignment,
    ProgrambenchLocalCaseLineageRegistration,
    ProgrambenchLocalCaseExpansionReadinessSummary,
    ProgrambenchLocalCaseMatrixCandidateHandoff,
]:
    return (
        ProgrambenchLocalCaseExpansionFamilyCloseoutAlignment.model_validate(
            _load_fixture(
                _fixture_root_case_expansion_c(),
                "programbench_local_case_expansion_family_closeout_alignment_v265_reference.json",
            )
        ),
        ProgrambenchLocalCaseLineageRegistration.model_validate(
            _load_fixture(
                _fixture_root_case_expansion_c(),
                "programbench_local_case_lineage_registration_v265_reference.json",
            )
        ),
        ProgrambenchLocalCaseExpansionReadinessSummary.model_validate(
            _load_fixture(
                _fixture_root_case_expansion_c(),
                "programbench_local_case_expansion_readiness_summary_v265_reference.json",
            )
        ),
        ProgrambenchLocalCaseMatrixCandidateHandoff.model_validate(
            _load_fixture(
                _fixture_root_case_expansion_c(),
                "programbench_local_case_matrix_candidate_handoff_v265_reference.json",
            )
        ),
    )


def _load_matrix_inclusion_rows() -> tuple[
    ProgrambenchLocalMatrixInclusionRequest,
    ProgrambenchLocalMatrixCandidateIntake,
    ProgrambenchLocalMatrixInclusionEligibilityReview,
    ProgrambenchLocalMatrixInclusionControlContract,
    ProgrambenchLocalMatrixInclusionNonAuthorityGuardrail,
]:
    return (
        ProgrambenchLocalMatrixInclusionRequest.model_validate(
            _load_matrix_inclusion_fixture(
                "programbench_local_matrix_inclusion_request_v266_reference.json"
            )
        ),
        ProgrambenchLocalMatrixCandidateIntake.model_validate(
            _load_matrix_inclusion_fixture(
                "programbench_local_matrix_candidate_intake_v266_reference.json"
            )
        ),
        ProgrambenchLocalMatrixInclusionEligibilityReview.model_validate(
            _load_matrix_inclusion_fixture(
                "programbench_local_matrix_inclusion_eligibility_review_v266_reference.json"
            )
        ),
        ProgrambenchLocalMatrixInclusionControlContract.model_validate(
            _load_matrix_inclusion_fixture(
                "programbench_local_matrix_inclusion_control_contract_v266_reference.json"
            )
        ),
        ProgrambenchLocalMatrixInclusionNonAuthorityGuardrail.model_validate(
            _load_matrix_inclusion_fixture(
                "programbench_local_matrix_inclusion_non_authority_guardrail_v266_reference.json"
            )
        ),
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_REQUEST_SCHEMA,
            "programbench_local_matrix_inclusion_request.v1.json",
            "programbench_local_matrix_inclusion_request_v266_reference.json",
            ProgrambenchLocalMatrixInclusionRequest,
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_CANDIDATE_INTAKE_SCHEMA,
            "programbench_local_matrix_candidate_intake.v1.json",
            "programbench_local_matrix_candidate_intake_v266_reference.json",
            ProgrambenchLocalMatrixCandidateIntake,
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_ELIGIBILITY_REVIEW_SCHEMA,
            "programbench_local_matrix_inclusion_eligibility_review.v1.json",
            "programbench_local_matrix_inclusion_eligibility_review_v266_reference.json",
            ProgrambenchLocalMatrixInclusionEligibilityReview,
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_CONTROL_CONTRACT_SCHEMA,
            "programbench_local_matrix_inclusion_control_contract.v1.json",
            "programbench_local_matrix_inclusion_control_contract_v266_reference.json",
            ProgrambenchLocalMatrixInclusionControlContract,
        ),
        (
            PROGRAMBENCH_LOCAL_MATRIX_INCLUSION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            "programbench_local_matrix_inclusion_non_authority_guardrail.v1.json",
            "programbench_local_matrix_inclusion_non_authority_guardrail_v266_reference.json",
            ProgrambenchLocalMatrixInclusionNonAuthorityGuardrail,
        ),
    ],
)
def test_pb_matrix_inclusion_0a_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_matrix_inclusion_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_matrix_inclusion_0a_reference_bundle_preserves_admission_boundary() -> None:
    request, intake, eligibility, control, guardrail = _load_matrix_inclusion_rows()
    (
        case_expansion_closeout,
        lineage_registration,
        readiness_summary,
        matrix_candidate_handoff,
    ) = _load_case_expansion_closeout_rows()

    validate_pb_matrix_inclusion_0a_bundle(
        matrix_family_closeout=_load_matrix_closeout(),
        case_expansion_family_closeout=case_expansion_closeout,
        lineage_registration=lineage_registration,
        readiness_summary=readiness_summary,
        matrix_candidate_handoff=matrix_candidate_handoff,
        inclusion_request=request,
        candidate_intake=intake,
        eligibility_review=eligibility,
        control_contract=control,
        non_authority_guardrail=guardrail,
    )


def test_pb_matrix_inclusion_0a_rejects_duplicate_existing_member_without_update() -> None:
    payload = _load_matrix_inclusion_fixture(
        "programbench_local_matrix_candidate_intake_v266_reference.json"
    )
    candidate = payload["candidate_case_rows"][0]
    candidate["prior_matrix_membership_status"] = "present_in_base_matrix"
    candidate["duplicate_case_refs"] = ["case-lineage:pb-case-expansion-0c:diagnostic"]
    candidate["duplicate_of_case_lineage_refs"] = [
        "case-lineage:pb-case-expansion-0c:diagnostic"
    ]
    candidate["dedupe_status"] = "duplicate_blocked_existing_member"
    candidate["duplicate_allowed_posture"] = "duplicate_blocked_without_replacement_or_update"

    with pytest.raises(ValidationError, match="existing base matrix members"):
        ProgrambenchLocalMatrixCandidateIntake.model_validate(payload)


def test_pb_matrix_inclusion_0a_rejects_representative_or_scoring_language() -> None:
    payload = _load_matrix_inclusion_fixture(
        "programbench_local_matrix_inclusion_request_v266_reference.json"
    )
    payload["selection_rationale_rows"][0][
        "limitation_note"
    ] = "This candidate is a representative benchmark subset."

    with pytest.raises(ValidationError, match="scoring or ranking language"):
        ProgrambenchLocalMatrixInclusionRequest.model_validate(payload)


def test_pb_matrix_inclusion_0a_rejects_future_artifact_guardrail_gap() -> None:
    payload = _load_matrix_inclusion_fixture(
        "programbench_local_matrix_inclusion_non_authority_guardrail_v266_reference.json"
    )
    payload["forbidden_future_artifact_kinds"].remove(
        "programbench_local_matrix_revision_registration@1"
    )

    with pytest.raises(ValidationError, match="missing future artifact kinds"):
        ProgrambenchLocalMatrixInclusionNonAuthorityGuardrail.model_validate(payload)


def test_pb_matrix_inclusion_0a_rejects_forbidden_refs_case_insensitively() -> None:
    payload = _load_matrix_inclusion_fixture(
        "programbench_local_matrix_inclusion_request_v266_reference.json"
    )
    payload["requested_case_lineage_refs"] = ["HIDDEN-TEST:pb-matrix-inclusion-0a:leak"]
    payload["selection_rationale_rows"][0]["candidate_case_lineage_refs"] = [
        "HIDDEN-TEST:pb-matrix-inclusion-0a:leak"
    ]

    with pytest.raises(ValidationError, match="forbidden matrix-inclusion refs"):
        ProgrambenchLocalMatrixInclusionRequest.model_validate(payload)


def test_pb_matrix_inclusion_0a_rejects_forbidden_authority_row_scoring_language() -> None:
    payload = _load_matrix_inclusion_fixture(
        "programbench_local_matrix_inclusion_non_authority_guardrail_v266_reference.json"
    )
    payload["forbidden_authority_rows"][0][
        "limitation_note"
    ] = "This would imply a pass rate."

    with pytest.raises(ValidationError, match="scoring or ranking language"):
        ProgrambenchLocalMatrixInclusionNonAuthorityGuardrail.model_validate(payload)


def test_pb_matrix_inclusion_0a_rejects_blocked_summary_row_mismatch() -> None:
    payload = _load_matrix_inclusion_fixture(
        "programbench_local_matrix_inclusion_eligibility_review_v266_reference.json"
    )
    payload["eligible_case_lineage_refs"] = []
    payload["eligibility_rows"][0]["eligibility_posture"] = "blocked_by_contamination"
    payload["eligibility_rows"][0]["blocker_refs"] = ["blocker:contamination"]
    payload["eligibility_status"] = "blocked"
    payload["blocker_refs"] = ["blocker:contamination"]
    payload["contamination_status"] = "contaminated"

    with pytest.raises(ValidationError, match="blocked_case_lineage_refs"):
        ProgrambenchLocalMatrixInclusionEligibilityReview.model_validate(payload)


def test_pb_matrix_inclusion_0a_bundle_rejects_unvalidated_second_requested_lineage() -> None:
    request, intake, eligibility, control, guardrail = _load_matrix_inclusion_rows()
    request_payload = request.model_dump(by_alias=True)
    request_payload["matrix_max_added_case_count"] = 2
    request_payload["requested_case_lineage_refs"] = [
        "case-lineage:pb-case-expansion-0c:diagnostic",
        "case-lineage:pb-case-expansion-0c:diagnostic-extra",
    ]
    request_payload["selection_rationale_rows"][0]["candidate_case_lineage_refs"] = [
        "case-lineage:pb-case-expansion-0c:diagnostic",
        "case-lineage:pb-case-expansion-0c:diagnostic-extra",
    ]
    request = ProgrambenchLocalMatrixInclusionRequest.model_validate(request_payload)
    (
        case_expansion_closeout,
        lineage_registration,
        readiness_summary,
        matrix_candidate_handoff,
    ) = _load_case_expansion_closeout_rows()

    with pytest.raises(ValueError, match="exactly one requested case lineage"):
        validate_pb_matrix_inclusion_0a_bundle(
            matrix_family_closeout=_load_matrix_closeout(),
            case_expansion_family_closeout=case_expansion_closeout,
            lineage_registration=lineage_registration,
            readiness_summary=readiness_summary,
            matrix_candidate_handoff=matrix_candidate_handoff,
            inclusion_request=request,
            candidate_intake=intake,
            eligibility_review=eligibility,
            control_contract=control,
            non_authority_guardrail=guardrail,
        )


def test_pb_matrix_inclusion_0a_rejects_lineage_hash_mismatch() -> None:
    request, intake, eligibility, control, guardrail = _load_matrix_inclusion_rows()
    intake_payload = intake.model_dump(by_alias=True)
    intake_payload["candidate_case_rows"][0][
        "source_boundary_hash"
    ] = "sha256:2525252525252525252525252525252525252525252525252525252525252525"
    bad_intake = ProgrambenchLocalMatrixCandidateIntake.model_validate(intake_payload)
    (
        case_expansion_closeout,
        lineage_registration,
        readiness_summary,
        matrix_candidate_handoff,
    ) = _load_case_expansion_closeout_rows()

    with pytest.raises(ValueError, match="source boundary hash"):
        validate_pb_matrix_inclusion_0a_bundle(
            matrix_family_closeout=_load_matrix_closeout(),
            case_expansion_family_closeout=case_expansion_closeout,
            lineage_registration=lineage_registration,
            readiness_summary=readiness_summary,
            matrix_candidate_handoff=matrix_candidate_handoff,
            inclusion_request=request,
            candidate_intake=bad_intake,
            eligibility_review=eligibility,
            control_contract=control,
            non_authority_guardrail=guardrail,
        )


def test_pb_matrix_inclusion_0a_schema_exports_are_current() -> None:
    export_schema_main()
    for schema_name, authoritative_path, mirror_path in _schema_pairs():
        assert authoritative_path.exists(), schema_name
        assert mirror_path.exists(), schema_name
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))
        assert authoritative == mirror
        assert authoritative["properties"]["schema"]["const"] == schema_name
