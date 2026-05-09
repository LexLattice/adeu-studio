from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_LOCAL_CASE_EXPANSION_CONTROL_CONTRACT_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_EXPANSION_ELIGIBILITY_REVIEW_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_EXPANSION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_EXPANSION_REQUEST_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_SOURCE_POOL_MANIFEST_SCHEMA,
    ProgrambenchLocalCaseExpansionControlContract,
    ProgrambenchLocalCaseExpansionEligibilityReview,
    ProgrambenchLocalCaseExpansionNonAuthorityGuardrail,
    ProgrambenchLocalCaseExpansionRequest,
    ProgrambenchLocalCaseMatrixFamilyCloseoutAlignment,
    ProgrambenchLocalCaseSourcePoolManifest,
    validate_pb_case_expansion_0a_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root_matrix_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus262"


def _fixture_root_case_expansion_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus263"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_case_expansion_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_case_expansion_a(), name)


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
            PROGRAMBENCH_LOCAL_CASE_EXPANSION_REQUEST_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_expansion_request.v1.json",
            root / "spec" / "programbench_local_case_expansion_request.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_SOURCE_POOL_MANIFEST_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_source_pool_manifest.v1.json",
            root / "spec" / "programbench_local_case_source_pool_manifest.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_EXPANSION_ELIGIBILITY_REVIEW_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_expansion_eligibility_review.v1.json",
            root
            / "spec"
            / "programbench_local_case_expansion_eligibility_review.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_EXPANSION_CONTROL_CONTRACT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_expansion_control_contract.v1.json",
            root
            / "spec"
            / "programbench_local_case_expansion_control_contract.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_EXPANSION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_expansion_non_authority_guardrail.v1.json",
            root
            / "spec"
            / "programbench_local_case_expansion_non_authority_guardrail.schema.json",
        ),
    ]


def _load_matrix_closeout() -> ProgrambenchLocalCaseMatrixFamilyCloseoutAlignment:
    return ProgrambenchLocalCaseMatrixFamilyCloseoutAlignment.model_validate(
        _load_fixture(
            _fixture_root_matrix_c(),
            "programbench_local_case_matrix_family_closeout_alignment_v262_reference.json",
        )
    )


def _load_case_expansion_rows() -> tuple[
    ProgrambenchLocalCaseExpansionRequest,
    ProgrambenchLocalCaseSourcePoolManifest,
    ProgrambenchLocalCaseExpansionEligibilityReview,
    ProgrambenchLocalCaseExpansionControlContract,
    ProgrambenchLocalCaseExpansionNonAuthorityGuardrail,
]:
    return (
        ProgrambenchLocalCaseExpansionRequest.model_validate(
            _load_case_expansion_fixture(
                "programbench_local_case_expansion_request_v263_reference.json"
            )
        ),
        ProgrambenchLocalCaseSourcePoolManifest.model_validate(
            _load_case_expansion_fixture(
                "programbench_local_case_source_pool_manifest_v263_reference.json"
            )
        ),
        ProgrambenchLocalCaseExpansionEligibilityReview.model_validate(
            _load_case_expansion_fixture(
                "programbench_local_case_expansion_eligibility_review_v263_reference.json"
            )
        ),
        ProgrambenchLocalCaseExpansionControlContract.model_validate(
            _load_case_expansion_fixture(
                "programbench_local_case_expansion_control_contract_v263_reference.json"
            )
        ),
        ProgrambenchLocalCaseExpansionNonAuthorityGuardrail.model_validate(
            _load_case_expansion_fixture(
                "programbench_local_case_expansion_non_authority_guardrail_v263_reference.json"
            )
        ),
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_LOCAL_CASE_EXPANSION_REQUEST_SCHEMA,
            "programbench_local_case_expansion_request.v1.json",
            "programbench_local_case_expansion_request_v263_reference.json",
            ProgrambenchLocalCaseExpansionRequest,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_SOURCE_POOL_MANIFEST_SCHEMA,
            "programbench_local_case_source_pool_manifest.v1.json",
            "programbench_local_case_source_pool_manifest_v263_reference.json",
            ProgrambenchLocalCaseSourcePoolManifest,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_EXPANSION_ELIGIBILITY_REVIEW_SCHEMA,
            "programbench_local_case_expansion_eligibility_review.v1.json",
            "programbench_local_case_expansion_eligibility_review_v263_reference.json",
            ProgrambenchLocalCaseExpansionEligibilityReview,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_EXPANSION_CONTROL_CONTRACT_SCHEMA,
            "programbench_local_case_expansion_control_contract.v1.json",
            "programbench_local_case_expansion_control_contract_v263_reference.json",
            ProgrambenchLocalCaseExpansionControlContract,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_EXPANSION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            "programbench_local_case_expansion_non_authority_guardrail.v1.json",
            "programbench_local_case_expansion_non_authority_guardrail_v263_reference.json",
            ProgrambenchLocalCaseExpansionNonAuthorityGuardrail,
        ),
    ],
)
def test_pb_case_expansion_0a_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_case_expansion_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_case_expansion_0a_reference_bundle_preserves_source_supply_boundary() -> None:
    request, manifest, eligibility, control, guardrail = _load_case_expansion_rows()

    validate_pb_case_expansion_0a_bundle(
        matrix_family_closeout=_load_matrix_closeout(),
        expansion_request=request,
        source_pool_manifest=manifest,
        eligibility_review=eligibility,
        control_contract=control,
        non_authority_guardrail=guardrail,
    )

    assert request.representativeness_posture == "not_representative_benchmark_sample"
    assert manifest.derived_summary_policy == "no_derived_summary_laundering"
    assert eligibility.eligible_candidate_case_idea_refs == request.candidate_case_idea_refs
    assert guardrail.batch_execution_posture == (
        "no_batch_execution_authority_granted_by_pb_case_expansion_0a"
    )


def test_pb_case_expansion_0a_bundle_rejects_missing_matrix_closeout_ref() -> None:
    request, manifest, eligibility, control, guardrail = _load_case_expansion_rows()
    eligibility = eligibility.model_copy(update={"released_family_closeout_refs": ["other"]})

    with pytest.raises(ValueError, match="PB-MATRIX-0 closeout"):
        validate_pb_case_expansion_0a_bundle(
            matrix_family_closeout=_load_matrix_closeout(),
            expansion_request=request,
            source_pool_manifest=manifest,
            eligibility_review=eligibility,
            control_contract=control,
            non_authority_guardrail=guardrail,
        )


def test_pb_case_expansion_0a_bundle_rejects_case_count_drift() -> None:
    request, manifest, eligibility, control, guardrail = _load_case_expansion_rows()
    request = request.model_copy(update={"requested_case_count": 1})

    with pytest.raises(ValueError, match="requested case count"):
        validate_pb_case_expansion_0a_bundle(
            matrix_family_closeout=_load_matrix_closeout(),
            expansion_request=request,
            source_pool_manifest=manifest,
            eligibility_review=eligibility,
            control_contract=control,
            non_authority_guardrail=guardrail,
        )


def test_pb_case_expansion_0a_bundle_requires_allowed_source_witness() -> None:
    request, manifest, eligibility, control, guardrail = _load_case_expansion_rows()
    manifest = manifest.model_copy(
        update={"allowed_source_refs": ["source:pb-case-expansion-0a:clean-probe-observation"]}
    )

    with pytest.raises(ValueError, match="allowed source witness"):
        validate_pb_case_expansion_0a_bundle(
            matrix_family_closeout=_load_matrix_closeout(),
            expansion_request=request,
            source_pool_manifest=manifest,
            eligibility_review=eligibility,
            control_contract=control,
            non_authority_guardrail=guardrail,
        )


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_local_case_expansion_v263_reject_representative_request.json",
            ProgrambenchLocalCaseExpansionRequest,
        ),
        (
            "programbench_local_case_expansion_v263_reject_hidden_label_laundering.json",
            ProgrambenchLocalCaseSourcePoolManifest,
        ),
        (
            "programbench_local_case_expansion_v263_reject_duplicate_without_rationale.json",
            ProgrambenchLocalCaseSourcePoolManifest,
        ),
    ],
)
def test_pb_case_expansion_0a_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_case_expansion_fixture(fixture_name))


def test_pb_case_expansion_0a_schema_exports_are_current() -> None:
    export_schema_main()
    for schema_name, authoritative, mirror in _schema_pairs():
        authoritative_payload = json.loads(authoritative.read_text(encoding="utf-8"))
        mirror_payload = json.loads(mirror.read_text(encoding="utf-8"))
        assert authoritative_payload == mirror_payload
        assert authoritative_payload["properties"]["schema"]["const"] == schema_name
