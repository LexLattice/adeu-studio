from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_LOCAL_CASE_INCLUSION_MANIFEST_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_LINEAGE_ELIGIBILITY_REVIEW_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_MATRIX_CONTROL_CONTRACT_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_MATRIX_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_MATRIX_REQUEST_SCHEMA,
    ProgrambenchLocalCaseInclusionManifest,
    ProgrambenchLocalCaseLineageEligibilityReview,
    ProgrambenchLocalCaseMatrixControlContract,
    ProgrambenchLocalCaseMatrixNonAuthorityGuardrail,
    ProgrambenchLocalCaseMatrixRequest,
    ProgrambenchLocalRetryFamilyCloseoutAlignment,
    ProgrambenchLocalTrialFamilyCloseoutAlignment,
    validate_pb_matrix_0a_case_matrix_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root_trial_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus256"


def _fixture_root_retry_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus259"


def _fixture_root_matrix_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus260"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_matrix_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_matrix_a(), name)


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (_repo_root() / "packages" / "adeu_benchmarking" / "schema" / schema_filename).read_text(
            encoding="utf-8"
        )
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _schema_pairs() -> list[tuple[str, Path, Path]]:
    root = _repo_root()
    return [
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_REQUEST_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_matrix_request.v1.json",
            root / "spec" / "programbench_local_case_matrix_request.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_INCLUSION_MANIFEST_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_inclusion_manifest.v1.json",
            root / "spec" / "programbench_local_case_inclusion_manifest.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_LINEAGE_ELIGIBILITY_REVIEW_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_lineage_eligibility_review.v1.json",
            root
            / "spec"
            / "programbench_local_case_lineage_eligibility_review.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_CONTROL_CONTRACT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_matrix_control_contract.v1.json",
            root / "spec" / "programbench_local_case_matrix_control_contract.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_matrix_non_authority_guardrail.v1.json",
            root
            / "spec"
            / "programbench_local_case_matrix_non_authority_guardrail.schema.json",
        ),
    ]


def _load_trial_closeout() -> ProgrambenchLocalTrialFamilyCloseoutAlignment:
    return ProgrambenchLocalTrialFamilyCloseoutAlignment.model_validate(
        _load_fixture(
            _fixture_root_trial_c(),
            "programbench_local_trial_family_closeout_alignment_v256_reference.json",
        )
    )


def _load_retry_closeout() -> ProgrambenchLocalRetryFamilyCloseoutAlignment:
    return ProgrambenchLocalRetryFamilyCloseoutAlignment.model_validate(
        _load_fixture(
            _fixture_root_retry_c(),
            "programbench_local_retry_family_closeout_alignment_v259_reference.json",
        )
    )


def _load_matrix_rows() -> tuple[
    ProgrambenchLocalCaseMatrixRequest,
    ProgrambenchLocalCaseInclusionManifest,
    ProgrambenchLocalCaseLineageEligibilityReview,
    ProgrambenchLocalCaseMatrixControlContract,
    ProgrambenchLocalCaseMatrixNonAuthorityGuardrail,
]:
    return (
        ProgrambenchLocalCaseMatrixRequest.model_validate(
            _load_matrix_fixture("programbench_local_case_matrix_request_v260_reference.json")
        ),
        ProgrambenchLocalCaseInclusionManifest.model_validate(
            _load_matrix_fixture(
                "programbench_local_case_inclusion_manifest_v260_reference.json"
            )
        ),
        ProgrambenchLocalCaseLineageEligibilityReview.model_validate(
            _load_matrix_fixture(
                "programbench_local_case_lineage_eligibility_review_v260_reference.json"
            )
        ),
        ProgrambenchLocalCaseMatrixControlContract.model_validate(
            _load_matrix_fixture(
                "programbench_local_case_matrix_control_contract_v260_reference.json"
            )
        ),
        ProgrambenchLocalCaseMatrixNonAuthorityGuardrail.model_validate(
            _load_matrix_fixture(
                "programbench_local_case_matrix_non_authority_guardrail_v260_reference.json"
            )
        ),
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_REQUEST_SCHEMA,
            "programbench_local_case_matrix_request.v1.json",
            "programbench_local_case_matrix_request_v260_reference.json",
            ProgrambenchLocalCaseMatrixRequest,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_INCLUSION_MANIFEST_SCHEMA,
            "programbench_local_case_inclusion_manifest.v1.json",
            "programbench_local_case_inclusion_manifest_v260_reference.json",
            ProgrambenchLocalCaseInclusionManifest,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_LINEAGE_ELIGIBILITY_REVIEW_SCHEMA,
            "programbench_local_case_lineage_eligibility_review.v1.json",
            "programbench_local_case_lineage_eligibility_review_v260_reference.json",
            ProgrambenchLocalCaseLineageEligibilityReview,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_CONTROL_CONTRACT_SCHEMA,
            "programbench_local_case_matrix_control_contract.v1.json",
            "programbench_local_case_matrix_control_contract_v260_reference.json",
            ProgrambenchLocalCaseMatrixControlContract,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            "programbench_local_case_matrix_non_authority_guardrail.v1.json",
            "programbench_local_case_matrix_non_authority_guardrail_v260_reference.json",
            ProgrambenchLocalCaseMatrixNonAuthorityGuardrail,
        ),
    ],
)
def test_pb_matrix_0a_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_matrix_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_matrix_0a_reference_bundle_preserves_local_non_scoring_boundary() -> None:
    request, manifest, eligibility, control, guardrail = _load_matrix_rows()

    validate_pb_matrix_0a_case_matrix_bundle(
        trial_family_closeout=_load_trial_closeout(),
        retry_family_closeout=_load_retry_closeout(),
        matrix_request=request,
        inclusion_manifest=manifest,
        lineage_eligibility_review=eligibility,
        matrix_control_contract=control,
        matrix_guardrail=guardrail,
    )

    assert request.aggregate_count_posture == "local_inventory_count_only"
    assert request.representativeness_posture == "not_representative_benchmark_sample"
    assert control.multi_profile_matrix_posture == "single_profile_matrix"
    assert guardrail.batch_execution_posture == (
        "no_batch_execution_authority_granted_by_pb_matrix_0a"
    )


def test_pb_matrix_0a_bundle_rejects_unreleased_retry_settlement() -> None:
    request, manifest, eligibility, control, guardrail = _load_matrix_rows()

    with pytest.raises(ValueError, match="PB-RETRY-0 closeout"):
        validate_pb_matrix_0a_case_matrix_bundle(
            trial_family_closeout=_load_trial_closeout(),
            retry_family_closeout=None,
            matrix_request=request,
            inclusion_manifest=manifest,
            lineage_eligibility_review=eligibility,
            matrix_control_contract=control,
            matrix_guardrail=guardrail,
        )


def test_pb_matrix_0a_bundle_rejects_case_count_drift() -> None:
    request, manifest, eligibility, control, guardrail = _load_matrix_rows()
    request = request.model_copy(update={"requested_case_count": 1})

    with pytest.raises(ValueError, match="requested case count"):
        validate_pb_matrix_0a_case_matrix_bundle(
            trial_family_closeout=_load_trial_closeout(),
            retry_family_closeout=_load_retry_closeout(),
            matrix_request=request,
            inclusion_manifest=manifest,
            lineage_eligibility_review=eligibility,
            matrix_control_contract=control,
            matrix_guardrail=guardrail,
        )


def test_pb_matrix_0a_bundle_requires_eligibility_row_for_each_manifest_candidate() -> None:
    request, manifest, eligibility, control, guardrail = _load_matrix_rows()
    blocked_candidate = manifest.case_candidate_rows[0].model_copy(
        update={
            "case_ref": "matrix-case:pb-matrix-0a:blocked",
            "case_contamination_posture": "contaminated",
            "inclusion_decision": "blocked",
            "inclusion_reason": "Local contamination blocker keeps this case out.",
        }
    )
    request = request.model_copy(
        update={
            "matrix_case_candidate_refs": [
                "matrix-case:pb-matrix-0a:blocked",
                "matrix-case:pb-matrix-0a:retry",
                "matrix-case:pb-matrix-0a:trial",
            ]
        }
    )
    manifest = manifest.model_copy(
        update={
            "case_candidate_rows": [blocked_candidate, *manifest.case_candidate_rows],
            "blocked_case_refs": ["matrix-case:pb-matrix-0a:blocked"],
        }
    )

    with pytest.raises(ValueError, match="cover every matrix case candidate"):
        validate_pb_matrix_0a_case_matrix_bundle(
            trial_family_closeout=_load_trial_closeout(),
            retry_family_closeout=_load_retry_closeout(),
            matrix_request=request,
            inclusion_manifest=manifest,
            lineage_eligibility_review=eligibility,
            matrix_control_contract=control,
            matrix_guardrail=guardrail,
        )


def test_pb_matrix_0a_control_rejects_multi_profile_single_comparability_posture() -> None:
    payload = _load_matrix_fixture(
        "programbench_local_case_matrix_control_contract_v260_reference.json"
    )
    payload["model_profile_refs"] = [
        "model-profile:pb-trial-0:reference",
        "model-profile:pb-trial-0:second",
    ]
    payload["multi_profile_matrix_posture"] = "comparability_accounting_only_no_ranking"

    with pytest.raises(ValidationError, match="comparability-only posture"):
        ProgrambenchLocalCaseMatrixControlContract.model_validate(payload)


def test_pb_matrix_0a_control_rejects_duplicate_forbidden_action_kinds() -> None:
    payload = _load_matrix_fixture(
        "programbench_local_case_matrix_control_contract_v260_reference.json"
    )
    payload["forbidden_matrix_action_rows"][1]["action_kind"] = "batch_command_execution"

    with pytest.raises(ValidationError, match="duplicate action kinds"):
        ProgrambenchLocalCaseMatrixControlContract.model_validate(payload)


def test_pb_matrix_0a_guardrail_rejects_duplicate_forbidden_authority_kinds() -> None:
    payload = _load_matrix_fixture(
        "programbench_local_case_matrix_non_authority_guardrail_v260_reference.json"
    )
    payload["non_authority_rows"][1]["authority_kind"] = "batch_execution"

    with pytest.raises(ValidationError, match="duplicate authority kinds"):
        ProgrambenchLocalCaseMatrixNonAuthorityGuardrail.model_validate(payload)


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_local_case_matrix_v260_reject_representative_claim.json",
            ProgrambenchLocalCaseMatrixRequest,
        ),
        (
            "programbench_local_case_matrix_v260_reject_hidden_case_ref.json",
            ProgrambenchLocalCaseInclusionManifest,
        ),
        (
            "programbench_local_case_matrix_v260_reject_multi_profile_without_controls.json",
            ProgrambenchLocalCaseMatrixControlContract,
        ),
        (
            "programbench_local_case_matrix_v260_reject_guardrail_future_artifact_gap.json",
            ProgrambenchLocalCaseMatrixNonAuthorityGuardrail,
        ),
    ],
)
def test_pb_matrix_0a_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_matrix_fixture(fixture_name))


def test_pb_matrix_0a_schema_exports_are_current() -> None:
    export_schema_main()
    for schema_name, authoritative, mirror in _schema_pairs():
        authoritative_payload = json.loads(authoritative.read_text(encoding="utf-8"))
        mirror_payload = json.loads(mirror.read_text(encoding="utf-8"))
        assert authoritative_payload == mirror_payload
        assert authoritative_payload["properties"]["schema"]["const"] == schema_name
