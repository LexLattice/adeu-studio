from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    CONCEPT_REALIZATION_RECORD_SCHEMA,
    PROGRAM_ODEU_CONCEPT_ID_VOCABULARY,
    PYTHON_REALIZATION_WITNESS_TEMPLATE_SCHEMA,
    PYTHON_RECONSTRUCTION_PLAN_SCHEMA,
    PYTHON_RECONSTRUCTION_REALIZATION_PACK_SCHEMA,
    ConceptRealizationRecord,
    ProgrambenchCleanroomEvidenceSourceIndex,
    ProgrambenchCleanroomReconstructionProfile,
    ProgrambenchLocalCleanroomFixtureContract,
    ProgrambenchReconstructionNonAuthorityGuardrail,
    ProgramOdeuConceptBoundarySeed,
    PythonRealizationWitnessTemplate,
    PythonReconstructionPlan,
    PythonReconstructionRealizationPack,
    validate_pb_py_0b_python_realization_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root(slice_ref: str) -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / slice_ref


def _load_fixture(slice_ref: str, name: str) -> dict[str, Any]:
    payload = json.loads((_fixture_root(slice_ref) / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture("vnext_plus242", name)


def _load_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture("vnext_plus243", name)


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
            CONCEPT_REALIZATION_RECORD_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "concept_realization_record.v1.json",
            root / "spec" / "concept_realization_record.schema.json",
        ),
        (
            PYTHON_RECONSTRUCTION_REALIZATION_PACK_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "python_reconstruction_realization_pack.v1.json",
            root / "spec" / "python_reconstruction_realization_pack.schema.json",
        ),
        (
            PYTHON_RECONSTRUCTION_PLAN_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "python_reconstruction_plan.v1.json",
            root / "spec" / "python_reconstruction_plan.schema.json",
        ),
        (
            PYTHON_REALIZATION_WITNESS_TEMPLATE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "python_realization_witness_template.v1.json",
            root / "spec" / "python_realization_witness_template.schema.json",
        ),
    ]


def _load_a_bundle() -> tuple[
    ProgrambenchCleanroomReconstructionProfile,
    ProgramOdeuConceptBoundarySeed,
    ProgrambenchCleanroomEvidenceSourceIndex,
    ProgrambenchReconstructionNonAuthorityGuardrail,
    ProgrambenchLocalCleanroomFixtureContract,
]:
    profile = ProgrambenchCleanroomReconstructionProfile.model_validate(
        _load_a_fixture("programbench_cleanroom_reconstruction_profile_v242_reference.json")
    )
    concept_seed = ProgramOdeuConceptBoundarySeed.model_validate(
        _load_a_fixture("program_odeu_concept_boundary_seed_v242_reference.json")
    )
    source_index = ProgrambenchCleanroomEvidenceSourceIndex.model_validate(
        _load_a_fixture("programbench_cleanroom_evidence_source_index_v242_reference.json")
    )
    guardrail = ProgrambenchReconstructionNonAuthorityGuardrail.model_validate(
        _load_a_fixture("programbench_reconstruction_non_authority_guardrail_v242_reference.json")
    )
    fixture_contract = ProgrambenchLocalCleanroomFixtureContract.model_validate(
        _load_a_fixture("programbench_local_cleanroom_fixture_contract_v242_reference.json")
    )
    return profile, concept_seed, source_index, guardrail, fixture_contract


def _load_b_bundle() -> tuple[
    list[ConceptRealizationRecord],
    PythonReconstructionRealizationPack,
    PythonReconstructionPlan,
    list[PythonRealizationWitnessTemplate],
]:
    realization_records = [
        ConceptRealizationRecord.model_validate(
            _load_b_fixture("concept_realization_record_v243_reference.json")
        )
    ]
    realization_pack = PythonReconstructionRealizationPack.model_validate(
        _load_b_fixture("python_reconstruction_realization_pack_v243_reference.json")
    )
    reconstruction_plan = PythonReconstructionPlan.model_validate(
        _load_b_fixture("python_reconstruction_plan_v243_reference.json")
    )
    witness_templates = [
        PythonRealizationWitnessTemplate.model_validate(
            _load_b_fixture("python_realization_witness_template_v243_reference.json")
        )
    ]
    return (
        realization_records,
        realization_pack,
        reconstruction_plan,
        witness_templates,
    )


def test_pb_py_0b_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()
    for schema_name, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))
        assert authoritative == mirror
        assert authoritative["properties"]["schema"]["const"] == schema_name


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            CONCEPT_REALIZATION_RECORD_SCHEMA,
            "concept_realization_record.v1.json",
            "concept_realization_record_v243_reference.json",
            ConceptRealizationRecord,
        ),
        (
            PYTHON_RECONSTRUCTION_REALIZATION_PACK_SCHEMA,
            "python_reconstruction_realization_pack.v1.json",
            "python_reconstruction_realization_pack_v243_reference.json",
            PythonReconstructionRealizationPack,
        ),
        (
            PYTHON_RECONSTRUCTION_PLAN_SCHEMA,
            "python_reconstruction_plan.v1.json",
            "python_reconstruction_plan_v243_reference.json",
            PythonReconstructionPlan,
        ),
        (
            PYTHON_REALIZATION_WITNESS_TEMPLATE_SCHEMA,
            "python_realization_witness_template.v1.json",
            "python_realization_witness_template_v243_reference.json",
            PythonRealizationWitnessTemplate,
        ),
    ],
)
def test_pb_py_0b_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_b_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_py_0b_reference_bundle_preserves_overlay_boundary() -> None:
    profile, concept_seed, source_index, guardrail, fixture_contract = _load_a_bundle()
    realization_records, realization_pack, reconstruction_plan, witness_templates = _load_b_bundle()

    validate_pb_py_0b_python_realization_bundle(
        profile=profile,
        concept_seed=concept_seed,
        source_index=source_index,
        guardrail=guardrail,
        fixture_contract=fixture_contract,
        realization_records=realization_records,
        realization_pack=realization_pack,
        reconstruction_plan=reconstruction_plan,
        witness_templates=witness_templates,
    )

    stderr_record = realization_records[0]
    assert stderr_record.concept_id == "stderr_diagnostic"
    assert stderr_record.concept_definition_posture == ("realization_option_not_concept_definition")
    assert stderr_record.concept_id in PROGRAM_ODEU_CONCEPT_ID_VOCABULARY
    assert realization_pack.fixture_authority_posture == ("no_fixture_implemented_by_pb_py_0b")
    assert reconstruction_plan.code_generation_posture == "no_code_generated_by_pb_py_0b"
    assert reconstruction_plan.execution_authority_posture == (
        "no_execution_authority_granted_by_pb_py_0b"
    )
    assert witness_templates[0].hidden_test_equivalence_posture == (
        "local_probe_not_hidden_test_equivalence"
    )


def test_pb_py_0b_realization_pack_records_all_stdlib_surfaces_without_execution() -> None:
    realization_pack = PythonReconstructionRealizationPack.model_validate(
        _load_b_fixture("python_reconstruction_realization_pack_v243_reference.json")
    )

    assert [row.stdlib_surface for row in realization_pack.stdlib_surface_rows] == [
        "argparse",
        "sys_argv",
        "sys_stdin",
        "sys_stdout",
        "sys_stderr",
        "pathlib",
        "open",
        "json",
        "csv",
        "configparser",
        "tomllib",
        "os_environ",
        "glob",
        "text_binary_mode",
        "subprocess_for_probe_only",
    ]
    subprocess_row = realization_pack.stdlib_surface_rows[-1]
    assert subprocess_row.stdlib_surface == "subprocess_for_probe_only"
    assert subprocess_row.surface_use_posture == ("probe_surface_only_no_execution_authority")


def test_pb_py_0b_bundle_rejects_missing_released_a_reference() -> None:
    profile, concept_seed, source_index, guardrail, fixture_contract = _load_a_bundle()
    realization_records, realization_pack, reconstruction_plan, witness_templates = _load_b_bundle()
    realization_pack_payload = realization_pack.model_dump(mode="json", by_alias=True)
    realization_pack_payload["source_profile_refs"] = ["profile:pb-py-0a:missing-profile"]
    realization_pack = PythonReconstructionRealizationPack.model_validate(realization_pack_payload)

    with pytest.raises(ValueError, match="released profile"):
        validate_pb_py_0b_python_realization_bundle(
            profile=profile,
            concept_seed=concept_seed,
            source_index=source_index,
            guardrail=guardrail,
            fixture_contract=fixture_contract,
            realization_records=realization_records,
            realization_pack=realization_pack,
            reconstruction_plan=reconstruction_plan,
            witness_templates=witness_templates,
        )


def test_pb_py_0b_bundle_rejects_unresolved_plan_realization_ref() -> None:
    profile, concept_seed, source_index, guardrail, fixture_contract = _load_a_bundle()
    realization_records, realization_pack, reconstruction_plan, witness_templates = _load_b_bundle()
    plan_payload = reconstruction_plan.model_dump(mode="json", by_alias=True)
    plan_payload["concept_realization_refs"] = ["realization:pb-py-0b:missing-realization"]
    reconstruction_plan = PythonReconstructionPlan.model_validate(plan_payload)

    with pytest.raises(ValueError, match="missing records"):
        validate_pb_py_0b_python_realization_bundle(
            profile=profile,
            concept_seed=concept_seed,
            source_index=source_index,
            guardrail=guardrail,
            fixture_contract=fixture_contract,
            realization_records=realization_records,
            realization_pack=realization_pack,
            reconstruction_plan=reconstruction_plan,
            witness_templates=witness_templates,
        )


def test_pb_py_0b_bundle_rejects_unresolved_witness_ref() -> None:
    profile, concept_seed, source_index, guardrail, fixture_contract = _load_a_bundle()
    realization_records, realization_pack, reconstruction_plan, witness_templates = _load_b_bundle()
    pack_payload = realization_pack.model_dump(mode="json", by_alias=True)
    pack_payload["witness_template_refs"] = ["witness-template:pb-py-0b:missing-template"]
    realization_pack = PythonReconstructionRealizationPack.model_validate(pack_payload)

    with pytest.raises(ValueError, match="missing templates"):
        validate_pb_py_0b_python_realization_bundle(
            profile=profile,
            concept_seed=concept_seed,
            source_index=source_index,
            guardrail=guardrail,
            fixture_contract=fixture_contract,
            realization_records=realization_records,
            realization_pack=realization_pack,
            reconstruction_plan=reconstruction_plan,
            witness_templates=witness_templates,
        )


def test_pb_py_0b_bundle_rejects_unresolved_required_witness_ref() -> None:
    profile, concept_seed, source_index, guardrail, fixture_contract = _load_a_bundle()
    realization_records, realization_pack, reconstruction_plan, witness_templates = _load_b_bundle()
    record_payload = realization_records[0].model_dump(mode="json", by_alias=True)
    record_payload["required_witness_refs"] = ["witness-template:pb-py-0b:missing-required-witness"]
    realization_records = [ConceptRealizationRecord.model_validate(record_payload)]

    with pytest.raises(ValueError, match="required witnesses missing"):
        validate_pb_py_0b_python_realization_bundle(
            profile=profile,
            concept_seed=concept_seed,
            source_index=source_index,
            guardrail=guardrail,
            fixture_contract=fixture_contract,
            realization_records=realization_records,
            realization_pack=realization_pack,
            reconstruction_plan=reconstruction_plan,
            witness_templates=witness_templates,
        )


def test_pb_py_0b_bundle_rejects_unresolved_nested_pack_source_ref() -> None:
    profile, concept_seed, source_index, guardrail, fixture_contract = _load_a_bundle()
    realization_records, realization_pack, reconstruction_plan, witness_templates = _load_b_bundle()
    pack_payload = realization_pack.model_dump(mode="json", by_alias=True)
    pack_payload["boundary_condition_rows"][0]["source_refs"] = [
        "source:pb-py-0b:missing-source-row"
    ]
    realization_pack = PythonReconstructionRealizationPack.model_validate(pack_payload)

    with pytest.raises(ValueError, match="source refs missing source rows"):
        validate_pb_py_0b_python_realization_bundle(
            profile=profile,
            concept_seed=concept_seed,
            source_index=source_index,
            guardrail=guardrail,
            fixture_contract=fixture_contract,
            realization_records=realization_records,
            realization_pack=realization_pack,
            reconstruction_plan=reconstruction_plan,
            witness_templates=witness_templates,
        )


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_python_realization_v243_reject_concept_definition_python_idiom.json",
            ConceptRealizationRecord,
        ),
        (
            "programbench_python_realization_v243_reject_plan_generated_code.json",
            PythonReconstructionPlan,
        ),
        (
            "programbench_python_realization_v243_reject_plan_shell_command.json",
            PythonReconstructionPlan,
        ),
        (
            "programbench_python_realization_v243_reject_plan_executable_path.json",
            PythonReconstructionPlan,
        ),
        (
            "programbench_python_realization_v243_reject_plan_execution_authority.json",
            PythonReconstructionPlan,
        ),
        (
            "programbench_python_realization_v243_reject_witness_hidden_test_equivalence.json",
            PythonRealizationWitnessTemplate,
        ),
        (
            "programbench_python_realization_v243_reject_subprocess_command_authority.json",
            PythonReconstructionRealizationPack,
        ),
        (
            "programbench_python_realization_v243_reject_fixture_implemented.json",
            PythonReconstructionRealizationPack,
        ),
    ],
)
def test_pb_py_0b_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_b_fixture(fixture_name))


def test_pb_py_0b_plan_rejects_commands_and_paths_programmatically() -> None:
    payload = deepcopy(_load_b_fixture("python_reconstruction_plan_v243_reference.json"))
    payload["planned_obligation_rows"][0]["obligation_statement"] = "make test"

    with pytest.raises(ValidationError, match="source code or command"):
        PythonReconstructionPlan.model_validate(payload)

    payload = deepcopy(_load_b_fixture("python_reconstruction_plan_v243_reference.json"))
    payload["planned_obligation_rows"][0]["obligation_statement"] = (
        "apps/api/example.py carries the diagnostic behavior"
    )

    with pytest.raises(ValidationError, match="executable file paths"):
        PythonReconstructionPlan.model_validate(payload)

    payload = deepcopy(_load_b_fixture("python_reconstruction_plan_v243_reference.json"))
    payload["planned_obligation_rows"][0]["obligation_statement"] = (
        "SCRIPT.PY carries the diagnostic behavior"
    )

    with pytest.raises(ValidationError, match="executable file paths"):
        PythonReconstructionPlan.model_validate(payload)

    payload = deepcopy(_load_b_fixture("python_reconstruction_plan_v243_reference.json"))
    payload["planned_obligation_rows"][0]["obligation_statement"] = (
        "Input / Output labels remain documentation text."
    )

    PythonReconstructionPlan.model_validate(payload)
