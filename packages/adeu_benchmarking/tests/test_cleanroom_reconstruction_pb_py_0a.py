from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAM_ODEU_CONCEPT_BOUNDARY_SEED_SCHEMA,
    PROGRAM_ODEU_CONCEPT_ID_VOCABULARY,
    PROGRAMBENCH_CLEANROOM_EVIDENCE_SOURCE_INDEX_SCHEMA,
    PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_PROFILE_SCHEMA,
    PROGRAMBENCH_LOCAL_CLEANROOM_FIXTURE_CONTRACT_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    ProgrambenchCleanroomEvidenceSourceIndex,
    ProgrambenchCleanroomReconstructionProfile,
    ProgrambenchLocalCleanroomFixtureContract,
    ProgrambenchReconstructionNonAuthorityGuardrail,
    ProgramOdeuConceptBoundarySeed,
    validate_pb_py_0a_cleanroom_reconstruction_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus242"


def _load_fixture(name: str) -> dict[str, Any]:
    payload = json.loads((_fixture_root() / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_benchmarking" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _schema_pairs() -> list[tuple[str, Path, Path]]:
    root = _repo_root()
    return [
        (
            PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_PROFILE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_cleanroom_reconstruction_profile.v1.json",
            root / "spec" / "programbench_cleanroom_reconstruction_profile.schema.json",
        ),
        (
            PROGRAM_ODEU_CONCEPT_BOUNDARY_SEED_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "program_odeu_concept_boundary_seed.v1.json",
            root / "spec" / "program_odeu_concept_boundary_seed.schema.json",
        ),
        (
            PROGRAMBENCH_CLEANROOM_EVIDENCE_SOURCE_INDEX_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_cleanroom_evidence_source_index.v1.json",
            root / "spec" / "programbench_cleanroom_evidence_source_index.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_non_authority_guardrail.v1.json",
            root / "spec" / "programbench_reconstruction_non_authority_guardrail.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_CLEANROOM_FIXTURE_CONTRACT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_cleanroom_fixture_contract.v1.json",
            root / "spec" / "programbench_local_cleanroom_fixture_contract.schema.json",
        ),
    ]


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_PROFILE_SCHEMA,
            "programbench_cleanroom_reconstruction_profile.v1.json",
            "programbench_cleanroom_reconstruction_profile_v242_reference.json",
            ProgrambenchCleanroomReconstructionProfile,
        ),
        (
            PROGRAM_ODEU_CONCEPT_BOUNDARY_SEED_SCHEMA,
            "program_odeu_concept_boundary_seed.v1.json",
            "program_odeu_concept_boundary_seed_v242_reference.json",
            ProgramOdeuConceptBoundarySeed,
        ),
        (
            PROGRAMBENCH_CLEANROOM_EVIDENCE_SOURCE_INDEX_SCHEMA,
            "programbench_cleanroom_evidence_source_index.v1.json",
            "programbench_cleanroom_evidence_source_index_v242_reference.json",
            ProgrambenchCleanroomEvidenceSourceIndex,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            "programbench_reconstruction_non_authority_guardrail.v1.json",
            "programbench_reconstruction_non_authority_guardrail_v242_reference.json",
            ProgrambenchReconstructionNonAuthorityGuardrail,
        ),
        (
            PROGRAMBENCH_LOCAL_CLEANROOM_FIXTURE_CONTRACT_SCHEMA,
            "programbench_local_cleanroom_fixture_contract.v1.json",
            "programbench_local_cleanroom_fixture_contract_v242_reference.json",
            ProgrambenchLocalCleanroomFixtureContract,
        ),
    ],
)
def test_pb_py_0a_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_py_0a_reference_bundle_preserves_cleanroom_boundary() -> None:
    profile = ProgrambenchCleanroomReconstructionProfile.model_validate(
        _load_fixture("programbench_cleanroom_reconstruction_profile_v242_reference.json")
    )
    concept_seed = ProgramOdeuConceptBoundarySeed.model_validate(
        _load_fixture("program_odeu_concept_boundary_seed_v242_reference.json")
    )
    source_index = ProgrambenchCleanroomEvidenceSourceIndex.model_validate(
        _load_fixture("programbench_cleanroom_evidence_source_index_v242_reference.json")
    )
    guardrail = ProgrambenchReconstructionNonAuthorityGuardrail.model_validate(
        _load_fixture("programbench_reconstruction_non_authority_guardrail_v242_reference.json")
    )
    fixture_contract = ProgrambenchLocalCleanroomFixtureContract.model_validate(
        _load_fixture("programbench_local_cleanroom_fixture_contract_v242_reference.json")
    )

    validate_pb_py_0a_cleanroom_reconstruction_bundle(
        profile=profile,
        concept_seed=concept_seed,
        source_index=source_index,
        guardrail=guardrail,
        fixture_contract=fixture_contract,
    )

    assert {row.phase for row in profile.phase_rows} == {
        "evaluation_phase",
        "inference_phase",
        "local_development_phase",
        "postmortem_phase",
    }
    assert profile.benchmark_truth_posture == "not_benchmark_truth"
    assert guardrail.python_realization_posture == (
        "no_python_realization_records_created_by_pb_py_0a"
    )
    assert fixture_contract.fixture_implementation_posture == (
        "contract_only_no_fixture_implemented_by_pb_py_0a"
    )


def test_pb_py_0a_concept_boundary_seed_is_complete_but_non_operational() -> None:
    concept_seed = ProgramOdeuConceptBoundarySeed.model_validate(
        _load_fixture("program_odeu_concept_boundary_seed_v242_reference.json")
    )

    assert [row.concept_id for row in concept_seed.concept_seed_rows] == (
        PROGRAM_ODEU_CONCEPT_ID_VOCABULARY
    )
    stderr_seed = next(
        row for row in concept_seed.concept_seed_rows if row.concept_id == "stderr_diagnostic"
    )
    assert "stdout_output" in stderr_seed.nearest_confusable_concept_ids
    assert "stdout_stderr_split_observation" in stderr_seed.required_witness_kind_refs
    assert (
        stderr_seed.implementation_authority_posture
        == "no_implementation_authority_granted_by_pb_py_0a"
    )


def test_pb_py_0a_source_index_keeps_forbidden_stores_unreachable() -> None:
    source_index = ProgrambenchCleanroomEvidenceSourceIndex.model_validate(
        _load_fixture("programbench_cleanroom_evidence_source_index_v242_reference.json")
    )
    forbidden_rows = [
        row
        for row in source_index.source_rows
        if row.cleanroom_visibility_class.startswith("forbidden_")
    ]
    assert forbidden_rows
    assert {row.worker_visibility_posture for row in forbidden_rows} == {"not_worker_visible"}
    assert {row.inference_admissibility_posture for row in forbidden_rows} == {
        "forbidden_for_inference"
    }
    assert {
        "registered_or_mounted_for_worker",
        "queried_by_worker",
        "exposed_to_worker",
    }.isdisjoint({row.source_access_posture for row in forbidden_rows})


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_cleanroom_reconstruction_v242_reject_forbidden_worker_visible.json",
            ProgrambenchCleanroomEvidenceSourceIndex,
        ),
        (
            "programbench_cleanroom_reconstruction_v242_reject_hidden_test_inference.json",
            ProgrambenchCleanroomEvidenceSourceIndex,
        ),
        (
            "programbench_cleanroom_reconstruction_v242_reject_public_descriptor_truth.json",
            ProgrambenchCleanroomEvidenceSourceIndex,
        ),
        (
            "programbench_cleanroom_reconstruction_v242_reject_fixture_contract_implemented.json",
            ProgrambenchLocalCleanroomFixtureContract,
        ),
        (
            "programbench_cleanroom_reconstruction_v242_reject_concept_seed_realization_authority.json",
            ProgramOdeuConceptBoundarySeed,
        ),
        (
            "programbench_cleanroom_reconstruction_v242_reject_guardrail_missing_slice_artifact_forbidden.json",
            ProgrambenchReconstructionNonAuthorityGuardrail,
        ),
        (
            "programbench_cleanroom_reconstruction_v242_reject_phase_collapse.json",
            ProgrambenchCleanroomReconstructionProfile,
        ),
    ],
)
def test_pb_py_0a_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_fixture(fixture_name))


def test_pb_py_0a_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative["properties"]["schema"]["const"] == expected_schema
        assert authoritative == mirror

        serialized = json.dumps(authoritative, sort_keys=True)
        assert _repo_root().as_posix() not in serialized
        assert not _WINDOWS_ABSOLUTE_PATH_RE.search(serialized)
