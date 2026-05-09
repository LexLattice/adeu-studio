from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_LOCAL_CASE_MATRIX_CONTAMINATION_REGISTER_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_MATRIX_COVERAGE_REGISTER_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_MATRIX_OBSERVATION_LEDGER_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_MATRIX_RESULT_PROJECTION_SCHEMA,
    ProgrambenchLocalCaseInclusionManifest,
    ProgrambenchLocalCaseLineageEligibilityReview,
    ProgrambenchLocalCaseMatrixContaminationRegister,
    ProgrambenchLocalCaseMatrixControlContract,
    ProgrambenchLocalCaseMatrixCoverageRegister,
    ProgrambenchLocalCaseMatrixNonAuthorityGuardrail,
    ProgrambenchLocalCaseMatrixObservationLedger,
    ProgrambenchLocalCaseMatrixRequest,
    ProgrambenchLocalCaseMatrixResultProjection,
    validate_pb_matrix_0b_projection_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root_matrix_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus260"


def _fixture_root_matrix_b() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus261"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_matrix_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_matrix_a(), name)


def _load_matrix_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_matrix_b(), name)


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
            PROGRAMBENCH_LOCAL_CASE_MATRIX_RESULT_PROJECTION_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_matrix_result_projection.v1.json",
            root / "spec" / "programbench_local_case_matrix_result_projection.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_OBSERVATION_LEDGER_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_matrix_observation_ledger.v1.json",
            root / "spec" / "programbench_local_case_matrix_observation_ledger.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_COVERAGE_REGISTER_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_matrix_coverage_register.v1.json",
            root / "spec" / "programbench_local_case_matrix_coverage_register.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_CONTAMINATION_REGISTER_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_matrix_contamination_register.v1.json",
            root / "spec" / "programbench_local_case_matrix_contamination_register.schema.json",
        ),
    ]


def _load_matrix_a_rows() -> tuple[
    ProgrambenchLocalCaseMatrixRequest,
    ProgrambenchLocalCaseInclusionManifest,
    ProgrambenchLocalCaseLineageEligibilityReview,
    ProgrambenchLocalCaseMatrixControlContract,
    ProgrambenchLocalCaseMatrixNonAuthorityGuardrail,
]:
    return (
        ProgrambenchLocalCaseMatrixRequest.model_validate(
            _load_matrix_a_fixture("programbench_local_case_matrix_request_v260_reference.json")
        ),
        ProgrambenchLocalCaseInclusionManifest.model_validate(
            _load_matrix_a_fixture("programbench_local_case_inclusion_manifest_v260_reference.json")
        ),
        ProgrambenchLocalCaseLineageEligibilityReview.model_validate(
            _load_matrix_a_fixture(
                "programbench_local_case_lineage_eligibility_review_v260_reference.json"
            )
        ),
        ProgrambenchLocalCaseMatrixControlContract.model_validate(
            _load_matrix_a_fixture(
                "programbench_local_case_matrix_control_contract_v260_reference.json"
            )
        ),
        ProgrambenchLocalCaseMatrixNonAuthorityGuardrail.model_validate(
            _load_matrix_a_fixture(
                "programbench_local_case_matrix_non_authority_guardrail_v260_reference.json"
            )
        ),
    )


def _load_matrix_b_rows() -> tuple[
    ProgrambenchLocalCaseMatrixResultProjection,
    ProgrambenchLocalCaseMatrixObservationLedger,
    ProgrambenchLocalCaseMatrixCoverageRegister,
    ProgrambenchLocalCaseMatrixContaminationRegister,
]:
    return (
        ProgrambenchLocalCaseMatrixResultProjection.model_validate(
            _load_matrix_b_fixture(
                "programbench_local_case_matrix_result_projection_v261_reference.json"
            )
        ),
        ProgrambenchLocalCaseMatrixObservationLedger.model_validate(
            _load_matrix_b_fixture(
                "programbench_local_case_matrix_observation_ledger_v261_reference.json"
            )
        ),
        ProgrambenchLocalCaseMatrixCoverageRegister.model_validate(
            _load_matrix_b_fixture(
                "programbench_local_case_matrix_coverage_register_v261_reference.json"
            )
        ),
        ProgrambenchLocalCaseMatrixContaminationRegister.model_validate(
            _load_matrix_b_fixture(
                "programbench_local_case_matrix_contamination_register_v261_reference.json"
            )
        ),
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_RESULT_PROJECTION_SCHEMA,
            "programbench_local_case_matrix_result_projection.v1.json",
            "programbench_local_case_matrix_result_projection_v261_reference.json",
            ProgrambenchLocalCaseMatrixResultProjection,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_OBSERVATION_LEDGER_SCHEMA,
            "programbench_local_case_matrix_observation_ledger.v1.json",
            "programbench_local_case_matrix_observation_ledger_v261_reference.json",
            ProgrambenchLocalCaseMatrixObservationLedger,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_COVERAGE_REGISTER_SCHEMA,
            "programbench_local_case_matrix_coverage_register.v1.json",
            "programbench_local_case_matrix_coverage_register_v261_reference.json",
            ProgrambenchLocalCaseMatrixCoverageRegister,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_CONTAMINATION_REGISTER_SCHEMA,
            "programbench_local_case_matrix_contamination_register.v1.json",
            "programbench_local_case_matrix_contamination_register_v261_reference.json",
            ProgrambenchLocalCaseMatrixContaminationRegister,
        ),
    ],
)
def test_pb_matrix_0b_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_matrix_b_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_matrix_0b_reference_bundle_projects_released_local_rows_only() -> None:
    request, manifest, eligibility, control, guardrail = _load_matrix_a_rows()
    projection, observation, coverage, contamination = _load_matrix_b_rows()

    validate_pb_matrix_0b_projection_bundle(
        matrix_request=request,
        inclusion_manifest=manifest,
        lineage_eligibility_review=eligibility,
        matrix_control_contract=control,
        matrix_guardrail=guardrail,
        result_projection=projection,
        observation_ledger=observation,
        coverage_register=coverage,
        contamination_register=contamination,
    )

    assert projection.projection_authority_posture == (
        "no_new_outcome_truth_created_by_pb_matrix_0b"
    )
    assert observation.non_ranking_posture == "local_observations_only_no_model_ranking"
    assert coverage.hidden_test_coverage_posture == "no_hidden_test_coverage_claimed"
    assert contamination.contamination_status == "clean"


def test_pb_matrix_0b_bundle_rejects_projection_case_outside_a_inclusion() -> None:
    request, manifest, eligibility, control, guardrail = _load_matrix_a_rows()
    projection = ProgrambenchLocalCaseMatrixResultProjection.model_validate(
        _load_matrix_b_fixture(
            "programbench_local_case_matrix_v261_reject_unincluded_projection_case.json"
        )
    )
    observation, coverage, contamination = _load_matrix_b_rows()[1:]

    with pytest.raises(ValueError, match="included cases must match A included cases"):
        validate_pb_matrix_0b_projection_bundle(
            matrix_request=request,
            inclusion_manifest=manifest,
            lineage_eligibility_review=eligibility,
            matrix_control_contract=control,
            matrix_guardrail=guardrail,
            result_projection=projection,
            observation_ledger=observation,
            coverage_register=coverage,
            contamination_register=contamination,
        )


def test_pb_matrix_0b_bundle_rejects_missing_projection_gap() -> None:
    request, manifest, eligibility, control, guardrail = _load_matrix_a_rows()
    projection, observation, coverage, contamination = _load_matrix_b_rows()
    projection = projection.model_copy(
        update={
            "projection_case_rows": projection.projection_case_rows[:1],
            "included_case_refs": ["matrix-case:pb-matrix-0a:retry"],
            "projected_case_result_rows": ["matrix-projection-row:pb-matrix-0b:retry"],
        }
    )

    with pytest.raises(ValueError, match="included cases must match A included cases"):
        validate_pb_matrix_0b_projection_bundle(
            matrix_request=request,
            inclusion_manifest=manifest,
            lineage_eligibility_review=eligibility,
            matrix_control_contract=control,
            matrix_guardrail=guardrail,
            result_projection=projection,
            observation_ledger=observation,
            coverage_register=coverage,
            contamination_register=contamination,
        )


def test_pb_matrix_0b_bundle_rejects_retry_projection_not_a_admitted_settlement() -> None:
    request, manifest, eligibility, control, guardrail = _load_matrix_a_rows()
    payload = _load_matrix_b_fixture(
        "programbench_local_case_matrix_result_projection_v261_reference.json"
    )
    payload["source_retry_settlement_refs"] = [
        "retry-remand-settlement:pb-retry-0c:other"
    ]
    for row in payload["projection_case_rows"]:
        if row["case_ref"] == "matrix-case:pb-matrix-0a:retry":
            row["source_result_ref"] = "retry-remand-settlement:pb-retry-0c:other"
    for row in payload["projection_basis_rows"]:
        if row["case_ref"] == "matrix-case:pb-matrix-0a:retry":
            row["source_result_ref"] = "retry-remand-settlement:pb-retry-0c:other"

    projection = ProgrambenchLocalCaseMatrixResultProjection.model_validate(payload)
    observation, coverage, contamination = _load_matrix_b_rows()[1:]

    with pytest.raises(ValueError, match="A-admitted settlement"):
        validate_pb_matrix_0b_projection_bundle(
            matrix_request=request,
            inclusion_manifest=manifest,
            lineage_eligibility_review=eligibility,
            matrix_control_contract=control,
            matrix_guardrail=guardrail,
            result_projection=projection,
            observation_ledger=observation,
            coverage_register=coverage,
            contamination_register=contamination,
        )


def test_pb_matrix_0b_projection_gap_refs_must_follow_row_order() -> None:
    payload = _load_matrix_b_fixture(
        "programbench_local_case_matrix_result_projection_v261_reference.json"
    )
    payload["projection_currentness"] = "projection_gap_declared"
    payload["projection_gap_reason"] = "missing_current_result"
    gap_refs_by_case = {
        "matrix-case:pb-matrix-0a:retry": "matrix-projection-gap:z",
        "matrix-case:pb-matrix-0a:trial": "matrix-projection-gap:a",
    }
    for row in payload["projection_case_rows"]:
        row["projection_currentness"] = "projection_gap_declared"
        row["projected_result_posture"] = "projection_gap"
        row["projection_gap_reason"] = "missing_current_result"
        row["projection_gap_ref"] = gap_refs_by_case[row["case_ref"]]
    payload["projection_gap_refs"] = [
        "matrix-projection-gap:a",
        "matrix-projection-gap:z",
    ]

    with pytest.raises(ValidationError, match="projection_gap_refs must match"):
        ProgrambenchLocalCaseMatrixResultProjection.model_validate(payload)


def test_pb_matrix_0b_observation_rows_require_exhaustive_blocked_reason_policy() -> None:
    payload = _load_matrix_b_fixture(
        "programbench_local_case_matrix_observation_ledger_v261_reference.json"
    )
    payload["observation_rows"][0]["observation_kind"] = "local_gap_observed"

    with pytest.raises(ValidationError, match="requires a blocked reason"):
        ProgrambenchLocalCaseMatrixObservationLedger.model_validate(payload)


def test_pb_matrix_0b_observation_refs_must_partition_row_state() -> None:
    payload = copy.deepcopy(
        _load_matrix_b_fixture(
            "programbench_local_case_matrix_observation_ledger_v261_reference.json"
        )
    )
    payload["observation_rows"][0]["observation_kind"] = "local_gap_observed"
    payload["observation_rows"][0]["blocked_observation_reason"] = "projection_gap"
    payload["blocked_observation_refs"] = [
        payload["observation_rows"][0]["observation_ref"]
    ]

    with pytest.raises(ValidationError, match="local_observation_refs must match"):
        ProgrambenchLocalCaseMatrixObservationLedger.model_validate(payload)


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_local_case_matrix_v261_reject_new_truth_projection.json",
            ProgrambenchLocalCaseMatrixResultProjection,
        ),
        (
            "programbench_local_case_matrix_v261_reject_model_ranking_observation.json",
            ProgrambenchLocalCaseMatrixObservationLedger,
        ),
        (
            "programbench_local_case_matrix_v261_reject_hidden_test_coverage.json",
            ProgrambenchLocalCaseMatrixCoverageRegister,
        ),
        (
            "programbench_local_case_matrix_v261_reject_contamination_detail_leak.json",
            ProgrambenchLocalCaseMatrixContaminationRegister,
        ),
    ],
)
def test_pb_matrix_0b_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_matrix_b_fixture(fixture_name))


def test_pb_matrix_0b_schema_exports_are_current() -> None:
    export_schema_main()
    for schema_name, authoritative, mirror in _schema_pairs():
        authoritative_payload = json.loads(authoritative.read_text(encoding="utf-8"))
        mirror_payload = json.loads(mirror.read_text(encoding="utf-8"))
        assert authoritative_payload == mirror_payload
        assert authoritative_payload["properties"]["schema"]["const"] == schema_name
