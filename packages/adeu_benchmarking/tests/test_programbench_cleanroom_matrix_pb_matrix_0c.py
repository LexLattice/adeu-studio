from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_LOCAL_CASE_MATRIX_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
    PROGRAMBENCH_LOCAL_CASE_MATRIX_SUMMARY_SCHEMA,
    PROGRAMBENCH_POST_CASE_MATRIX_HANDOFF_SCHEMA,
    ProgrambenchLocalCaseInclusionManifest,
    ProgrambenchLocalCaseLineageEligibilityReview,
    ProgrambenchLocalCaseMatrixContaminationRegister,
    ProgrambenchLocalCaseMatrixControlContract,
    ProgrambenchLocalCaseMatrixCoverageRegister,
    ProgrambenchLocalCaseMatrixFamilyCloseoutAlignment,
    ProgrambenchLocalCaseMatrixNonAuthorityGuardrail,
    ProgrambenchLocalCaseMatrixObservationLedger,
    ProgrambenchLocalCaseMatrixRequest,
    ProgrambenchLocalCaseMatrixResultProjection,
    ProgrambenchLocalCaseMatrixSummary,
    ProgrambenchPostCaseMatrixHandoff,
    validate_pb_matrix_0c_closeout_bundle,
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


def _fixture_root_matrix_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus262"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_matrix_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_matrix_a(), name)


def _load_matrix_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_matrix_b(), name)


def _load_matrix_c_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_matrix_c(), name)


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
            PROGRAMBENCH_LOCAL_CASE_MATRIX_SUMMARY_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_matrix_summary.v1.json",
            root / "spec" / "programbench_local_case_matrix_summary.schema.json",
        ),
        (
            PROGRAMBENCH_POST_CASE_MATRIX_HANDOFF_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_post_case_matrix_handoff.v1.json",
            root / "spec" / "programbench_post_case_matrix_handoff.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_case_matrix_family_closeout_alignment.v1.json",
            root / "spec" / "programbench_local_case_matrix_family_closeout_alignment.schema.json",
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


def _load_matrix_c_rows() -> tuple[
    ProgrambenchLocalCaseMatrixSummary,
    ProgrambenchPostCaseMatrixHandoff,
    ProgrambenchLocalCaseMatrixFamilyCloseoutAlignment,
]:
    return (
        ProgrambenchLocalCaseMatrixSummary.model_validate(
            _load_matrix_c_fixture("programbench_local_case_matrix_summary_v262_reference.json")
        ),
        ProgrambenchPostCaseMatrixHandoff.model_validate(
            _load_matrix_c_fixture("programbench_post_case_matrix_handoff_v262_reference.json")
        ),
        ProgrambenchLocalCaseMatrixFamilyCloseoutAlignment.model_validate(
            _load_matrix_c_fixture(
                "programbench_local_case_matrix_family_closeout_alignment_v262_reference.json"
            )
        ),
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_SUMMARY_SCHEMA,
            "programbench_local_case_matrix_summary.v1.json",
            "programbench_local_case_matrix_summary_v262_reference.json",
            ProgrambenchLocalCaseMatrixSummary,
        ),
        (
            PROGRAMBENCH_POST_CASE_MATRIX_HANDOFF_SCHEMA,
            "programbench_post_case_matrix_handoff.v1.json",
            "programbench_post_case_matrix_handoff_v262_reference.json",
            ProgrambenchPostCaseMatrixHandoff,
        ),
        (
            PROGRAMBENCH_LOCAL_CASE_MATRIX_FAMILY_CLOSEOUT_ALIGNMENT_SCHEMA,
            "programbench_local_case_matrix_family_closeout_alignment.v1.json",
            "programbench_local_case_matrix_family_closeout_alignment_v262_reference.json",
            ProgrambenchLocalCaseMatrixFamilyCloseoutAlignment,
        ),
    ],
)
def test_pb_matrix_0c_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_matrix_c_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_matrix_0c_reference_bundle_closes_local_matrix_only() -> None:
    request, manifest, eligibility, control, guardrail = _load_matrix_a_rows()
    projection, observation, coverage, contamination = _load_matrix_b_rows()
    summary, handoff, closeout = _load_matrix_c_rows()

    validate_pb_matrix_0c_closeout_bundle(
        matrix_request=request,
        inclusion_manifest=manifest,
        lineage_eligibility_review=eligibility,
        matrix_control_contract=control,
        matrix_guardrail=guardrail,
        result_projection=projection,
        observation_ledger=observation,
        coverage_register=coverage,
        contamination_register=contamination,
        matrix_summary=summary,
        post_case_matrix_handoff=handoff,
        family_closeout=closeout,
    )

    assert summary.local_matrix_posture == "local_matrix_complete_relative_to_declared_cases"
    assert handoff.future_family_selection_posture == "no_future_family_selected_by_pb_matrix_0c"
    assert closeout.benchmark_truth_posture == "not_benchmark_truth"


def test_pb_matrix_0c_summary_rejects_soft_scoring_language() -> None:
    with pytest.raises(ValidationError, match="benchmark-like scoring"):
        ProgrambenchLocalCaseMatrixSummary.model_validate(
            _load_matrix_c_fixture(
                "programbench_local_case_matrix_v262_reject_benchmark_like_summary.json"
            )
        )


def test_pb_matrix_0c_summary_rejects_complete_with_unresolved_case() -> None:
    with pytest.raises(ValidationError, match="complete local matrix summaries"):
        ProgrambenchLocalCaseMatrixSummary.model_validate(
            _load_matrix_c_fixture(
                "programbench_local_case_matrix_v262_reject_complete_with_unresolved_case.json"
            )
        )


def test_pb_matrix_0c_handoff_rejects_future_family_selection_authority() -> None:
    with pytest.raises(ValidationError):
        ProgrambenchPostCaseMatrixHandoff.model_validate(
            _load_matrix_c_fixture(
                "programbench_local_case_matrix_v262_reject_handoff_selects_future_family.json"
            )
        )


def test_pb_matrix_0c_closeout_rejects_missing_slice() -> None:
    with pytest.raises(ValidationError, match="at least 3"):
        ProgrambenchLocalCaseMatrixFamilyCloseoutAlignment.model_validate(
            _load_matrix_c_fixture(
                "programbench_local_case_matrix_v262_reject_closeout_missing_slice.json"
            )
        )


def test_pb_matrix_0c_bundle_rejects_summary_with_projection_gap() -> None:
    request, manifest, eligibility, control, guardrail = _load_matrix_a_rows()
    projection_payload = copy.deepcopy(
        _load_matrix_b_fixture(
            "programbench_local_case_matrix_result_projection_v261_reference.json"
        )
    )
    projection_payload["projection_gap_refs"] = ["matrix-projection-gap:pb-matrix-0b:trial"]
    projection_payload["projection_gap_reason"] = "missing_current_result"
    projection_payload["projection_case_rows"][1]["projection_currentness"] = (
        "projection_gap_declared"
    )
    projection_payload["projection_case_rows"][1]["projected_result_posture"] = "projection_gap"
    projection_payload["projection_case_rows"][1]["projection_gap_ref"] = (
        "matrix-projection-gap:pb-matrix-0b:trial"
    )
    projection_payload["projection_case_rows"][1]["projection_gap_reason"] = (
        "missing_current_result"
    )
    projection = ProgrambenchLocalCaseMatrixResultProjection.model_validate(projection_payload)
    observation, coverage, contamination = _load_matrix_b_rows()[1:]
    summary, handoff, closeout = _load_matrix_c_rows()

    with pytest.raises(ValueError, match="projected_case_refs must match current projections"):
        validate_pb_matrix_0c_closeout_bundle(
            matrix_request=request,
            inclusion_manifest=manifest,
            lineage_eligibility_review=eligibility,
            matrix_control_contract=control,
            matrix_guardrail=guardrail,
            result_projection=projection,
            observation_ledger=observation,
            coverage_register=coverage,
            contamination_register=contamination,
            matrix_summary=summary,
            post_case_matrix_handoff=handoff,
            family_closeout=closeout,
        )


def test_pb_matrix_0c_schema_exports_are_current() -> None:
    export_schema_main()
    for schema_name, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))
        assert authoritative == mirror
        assert authoritative["properties"]["schema"]["const"] == schema_name
