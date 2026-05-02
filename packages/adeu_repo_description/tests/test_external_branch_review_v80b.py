from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_EXTERNAL_BRANCH_EXCEPTION_REGISTER_SCHEMA,
    REPO_EXTERNAL_DATA_BOUNDARY_SCHEMA,
    REPO_EXTERNAL_RESULT_PROVENANCE_CONTRACT_SCHEMA,
    REPO_EXTERNAL_SUBMISSION_AUTHORITY_REVIEW_SCHEMA,
    REPO_EXTERNAL_TOOL_BOUNDARY_SCHEMA,
    RepoExternalBranchExceptionRegister,
    RepoExternalBranchNonActivationGuardrail,
    RepoExternalBranchReviewRequest,
    RepoExternalBranchSourceIndex,
    RepoExternalDataBoundary,
    RepoExternalResultProvenanceContract,
    RepoExternalSubmissionAuthorityReview,
    RepoExternalToolBoundary,
    derive_v80b_external_branch_boundary_bundle,
    validate_v80b_external_branch_boundary_bundle,
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


def _v80a_source_index() -> RepoExternalBranchSourceIndex:
    return RepoExternalBranchSourceIndex.model_validate(
        _load_fixture("vnext_plus224", "repo_external_branch_source_index_v224_reference.json")
    )


def _v80a_request() -> RepoExternalBranchReviewRequest:
    return RepoExternalBranchReviewRequest.model_validate(
        _load_fixture("vnext_plus224", "repo_external_branch_review_request_v224_reference.json")
    )


def _v80a_guardrail() -> RepoExternalBranchNonActivationGuardrail:
    return RepoExternalBranchNonActivationGuardrail.model_validate(
        _load_fixture(
            "vnext_plus224",
            "repo_external_branch_non_activation_guardrail_v224_reference.json",
        )
    )


def _data_boundary(
    name: str = "repo_external_data_boundary_v225_reference.json",
) -> RepoExternalDataBoundary:
    return RepoExternalDataBoundary.model_validate(_load_fixture("vnext_plus225", name))


def _tool_boundary(
    name: str = "repo_external_tool_boundary_v225_reference.json",
) -> RepoExternalToolBoundary:
    return RepoExternalToolBoundary.model_validate(_load_fixture("vnext_plus225", name))


def _submission_authority(
    name: str = "repo_external_submission_authority_review_v225_reference.json",
) -> RepoExternalSubmissionAuthorityReview:
    return RepoExternalSubmissionAuthorityReview.model_validate(
        _load_fixture("vnext_plus225", name)
    )


def _result_provenance(
    name: str = "repo_external_result_provenance_contract_v225_reference.json",
) -> RepoExternalResultProvenanceContract:
    return RepoExternalResultProvenanceContract.model_validate(_load_fixture("vnext_plus225", name))


def _exception_register(
    name: str = "repo_external_branch_exception_register_v225_reference.json",
) -> RepoExternalBranchExceptionRegister:
    return RepoExternalBranchExceptionRegister.model_validate(_load_fixture("vnext_plus225", name))


def _validate_reference_bundle_with(
    *,
    data_boundary: RepoExternalDataBoundary | None = None,
    tool_boundary: RepoExternalToolBoundary | None = None,
    submission_authority: RepoExternalSubmissionAuthorityReview | None = None,
    result_provenance: RepoExternalResultProvenanceContract | None = None,
    exception_register: RepoExternalBranchExceptionRegister | None = None,
) -> None:
    validate_v80b_external_branch_boundary_bundle(
        external_branch_source_index=_v80a_source_index(),
        external_branch_review_request=_v80a_request(),
        external_branch_non_activation_guardrail=_v80a_guardrail(),
        external_data_boundary=data_boundary or _data_boundary(),
        external_tool_boundary=tool_boundary or _tool_boundary(),
        external_submission_authority_review=submission_authority or _submission_authority(),
        external_result_provenance_contract=result_provenance or _result_provenance(),
        external_branch_exception_register=exception_register or _exception_register(),
    )


def test_v225_reference_bundle_validates() -> None:
    data_boundary = _data_boundary()
    tool_boundary = _tool_boundary()
    submission_authority = _submission_authority()
    result_provenance = _result_provenance()
    exception_register = _exception_register()

    assert data_boundary.schema == REPO_EXTERNAL_DATA_BOUNDARY_SCHEMA
    assert tool_boundary.schema == REPO_EXTERNAL_TOOL_BOUNDARY_SCHEMA
    assert submission_authority.schema == REPO_EXTERNAL_SUBMISSION_AUTHORITY_REVIEW_SCHEMA
    assert result_provenance.schema == REPO_EXTERNAL_RESULT_PROVENANCE_CONTRACT_SCHEMA
    assert exception_register.schema == REPO_EXTERNAL_BRANCH_EXCEPTION_REGISTER_SCHEMA
    assert {row.data_transfer_posture for row in data_boundary.data_boundary_rows} == {
        "no_external_data_transfer_performed_by_v80"
    }
    assert {row.endpoint_ref_posture for row in tool_boundary.tool_boundary_rows} == {
        "endpoint_identifier_only"
    }
    assert {row.external_tool_invocation_posture for row in tool_boundary.tool_boundary_rows} == {
        "no_external_tool_invocation_performed_by_v80"
    }
    assert {
        row.external_submission_posture
        for row in submission_authority.submission_authority_review_rows
    } == {"no_external_submission_performed_by_v80"}
    assert {
        row.result_truth_posture for row in result_provenance.result_provenance_contract_rows
    } == {"external_result_truth_not_claimed"}
    assert {row.exception_posture for row in exception_register.exception_rows} == {"blocking"}

    _validate_reference_bundle_with(
        data_boundary=data_boundary,
        tool_boundary=tool_boundary,
        submission_authority=submission_authority,
        result_provenance=result_provenance,
        exception_register=exception_register,
    )


def test_v225_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_external_data_boundary.v1.json").validate(
        _load_fixture("vnext_plus225", "repo_external_data_boundary_v225_reference.json")
    )
    _schema_validator("repo_external_tool_boundary.v1.json").validate(
        _load_fixture("vnext_plus225", "repo_external_tool_boundary_v225_reference.json")
    )
    _schema_validator("repo_external_submission_authority_review.v1.json").validate(
        _load_fixture(
            "vnext_plus225",
            "repo_external_submission_authority_review_v225_reference.json",
        )
    )
    _schema_validator("repo_external_result_provenance_contract.v1.json").validate(
        _load_fixture(
            "vnext_plus225",
            "repo_external_result_provenance_contract_v225_reference.json",
        )
    )
    _schema_validator("repo_external_branch_exception_register.v1.json").validate(
        _load_fixture(
            "vnext_plus225",
            "repo_external_branch_exception_register_v225_reference.json",
        )
    )


def test_v225_derivation_helper_matches_reference_fixtures() -> None:
    (
        _source_index,
        _request,
        _guardrail,
        data_boundary,
        tool_boundary,
        submission_authority,
        result_provenance,
        exception_register,
    ) = derive_v80b_external_branch_boundary_bundle(repo_root=_repo_root())

    assert data_boundary.model_dump(mode="json") == _load_fixture(
        "vnext_plus225",
        "repo_external_data_boundary_v225_reference.json",
    )
    assert tool_boundary.model_dump(mode="json") == _load_fixture(
        "vnext_plus225",
        "repo_external_tool_boundary_v225_reference.json",
    )
    assert submission_authority.model_dump(mode="json") == _load_fixture(
        "vnext_plus225",
        "repo_external_submission_authority_review_v225_reference.json",
    )
    assert result_provenance.model_dump(mode="json") == _load_fixture(
        "vnext_plus225",
        "repo_external_result_provenance_contract_v225_reference.json",
    )
    assert exception_register.model_dump(mode="json") == _load_fixture(
        "vnext_plus225",
        "repo_external_branch_exception_register_v225_reference.json",
    )


@pytest.mark.parametrize(
    ("fixture_name", "model_type", "match"),
    [
        (
            "repo_external_branch_v225_reject_data_boundary_transfers_external_data.json",
            RepoExternalDataBoundary,
            "must not transfer external data",
        ),
        (
            "repo_external_branch_v225_reject_external_tool_invokes_tool.json",
            RepoExternalToolBoundary,
            "must not invoke external tools",
        ),
        (
            "repo_external_branch_v225_reject_endpoint_access_permission.json",
            RepoExternalToolBoundary,
            "endpoint refs must remain identifier-only",
        ),
        (
            "repo_external_branch_v225_reject_submission_authority_submits.json",
            RepoExternalSubmissionAuthorityReview,
            "must not submit externally",
        ),
        (
            "repo_external_branch_v225_reject_result_provenance_claims_truth.json",
            RepoExternalResultProvenanceContract,
            "must not claim external result truth",
        ),
        (
            "repo_external_branch_v225_reject_withdrawal_requirement_as_action.json",
            RepoExternalResultProvenanceContract,
            "withdrawal requirement cannot become withdrawal action",
        ),
        (
            "repo_external_branch_v225_reject_blocking_exception_resolved_by_prose.json",
            RepoExternalBranchExceptionRegister,
            "cannot be resolved by prose",
        ),
        (
            "repo_external_branch_v225_reject_product_pressure_external_ready.json",
            RepoExternalBranchExceptionRegister,
            "must remain blocked or deferred",
        ),
        (
            "repo_external_branch_v225_reject_local_command_output_as_external_result.json",
            RepoExternalBranchExceptionRegister,
            "local command output cannot be external result evidence",
        ),
        (
            "repo_external_branch_v225_reject_historical_v43_as_current_authority.json",
            RepoExternalBranchExceptionRegister,
            "historical V43 context cannot be current external authority",
        ),
    ],
)
def test_v225_reject_fixtures_fail_model_validation(
    fixture_name: str,
    model_type: type[
        RepoExternalDataBoundary
        | RepoExternalToolBoundary
        | RepoExternalSubmissionAuthorityReview
        | RepoExternalResultProvenanceContract
        | RepoExternalBranchExceptionRegister
    ],
    match: str,
) -> None:
    with pytest.raises(ValidationError, match=match):
        model_type.model_validate(_load_fixture("vnext_plus225", fixture_name))


def test_v225_bundle_rejects_unknown_v80a_request_ref() -> None:
    data_boundary = _data_boundary(
        "repo_external_branch_v225_reject_data_boundary_unknown_request_ref.json"
    )

    with pytest.raises(ValueError, match="external data boundary request refs must be known"):
        _validate_reference_bundle_with(data_boundary=data_boundary)


def test_v225_bundle_rejects_unknown_source_ref() -> None:
    payload = _load_fixture(
        "vnext_plus225",
        "repo_external_branch_v225_reject_unknown_source_ref.json",
    )
    payload["external_data_boundary_id"] = _surface_id(
        "repo_external_data_boundary",
        REPO_EXTERNAL_DATA_BOUNDARY_SCHEMA,
        payload,
        "external_data_boundary_id",
    )
    data_boundary = RepoExternalDataBoundary.model_validate(payload)

    with pytest.raises(ValueError, match="external data boundary source refs must be known"):
        _validate_reference_bundle_with(data_boundary=data_boundary)


def test_v225_bundle_rejects_exception_row_without_request_refs() -> None:
    exception_register = _exception_register()
    exception_row = exception_register.exception_rows[0].model_copy(
        update={"external_branch_review_request_refs": []}
    )
    exception_register = exception_register.model_copy(update={"exception_rows": [exception_row]})

    with pytest.raises(
        ValueError, match="external branch exception request refs must be non-empty"
    ):
        _validate_reference_bundle_with(exception_register=exception_register)
