from __future__ import annotations

import json
import re
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_ADAPTER_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    PROGRAMBENCH_ADAPTER_WORKER_ACCESS_CONTRACT_SCHEMA,
    PROGRAMBENCH_CLEANROOM_TASK_INTAKE_SCHEMA,
    PROGRAMBENCH_TASK_ARTIFACT_MANIFEST_SCHEMA,
    PROGRAMBENCH_TASK_VISIBILITY_MANIFEST_SCHEMA,
    ProgrambenchAdapterNonAuthorityGuardrail,
    ProgrambenchAdapterWorkerAccessContract,
    ProgrambenchCleanroomTaskIntake,
    ProgrambenchTaskArtifactManifest,
    ProgrambenchTaskVisibilityManifest,
    validate_pb_adapter_0a_task_intake_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus245"


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
            PROGRAMBENCH_CLEANROOM_TASK_INTAKE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_cleanroom_task_intake.v1.json",
            root / "spec" / "programbench_cleanroom_task_intake.schema.json",
        ),
        (
            PROGRAMBENCH_TASK_ARTIFACT_MANIFEST_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_task_artifact_manifest.v1.json",
            root / "spec" / "programbench_task_artifact_manifest.schema.json",
        ),
        (
            PROGRAMBENCH_TASK_VISIBILITY_MANIFEST_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_task_visibility_manifest.v1.json",
            root / "spec" / "programbench_task_visibility_manifest.schema.json",
        ),
        (
            PROGRAMBENCH_ADAPTER_WORKER_ACCESS_CONTRACT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_adapter_worker_access_contract.v1.json",
            root / "spec" / "programbench_adapter_worker_access_contract.schema.json",
        ),
        (
            PROGRAMBENCH_ADAPTER_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_adapter_non_authority_guardrail.v1.json",
            root / "spec" / "programbench_adapter_non_authority_guardrail.schema.json",
        ),
    ]


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_CLEANROOM_TASK_INTAKE_SCHEMA,
            "programbench_cleanroom_task_intake.v1.json",
            "programbench_cleanroom_task_intake_v245_reference.json",
            ProgrambenchCleanroomTaskIntake,
        ),
        (
            PROGRAMBENCH_TASK_ARTIFACT_MANIFEST_SCHEMA,
            "programbench_task_artifact_manifest.v1.json",
            "programbench_task_artifact_manifest_v245_reference.json",
            ProgrambenchTaskArtifactManifest,
        ),
        (
            PROGRAMBENCH_TASK_VISIBILITY_MANIFEST_SCHEMA,
            "programbench_task_visibility_manifest.v1.json",
            "programbench_task_visibility_manifest_v245_reference.json",
            ProgrambenchTaskVisibilityManifest,
        ),
        (
            PROGRAMBENCH_ADAPTER_WORKER_ACCESS_CONTRACT_SCHEMA,
            "programbench_adapter_worker_access_contract.v1.json",
            "programbench_adapter_worker_access_contract_v245_reference.json",
            ProgrambenchAdapterWorkerAccessContract,
        ),
        (
            PROGRAMBENCH_ADAPTER_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            "programbench_adapter_non_authority_guardrail.v1.json",
            "programbench_adapter_non_authority_guardrail_v245_reference.json",
            ProgrambenchAdapterNonAuthorityGuardrail,
        ),
    ],
)
def test_pb_adapter_0a_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_adapter_0a_reference_bundle_preserves_cleanroom_membrane() -> None:
    task_intake = ProgrambenchCleanroomTaskIntake.model_validate(
        _load_fixture("programbench_cleanroom_task_intake_v245_reference.json")
    )
    artifact_manifest = ProgrambenchTaskArtifactManifest.model_validate(
        _load_fixture("programbench_task_artifact_manifest_v245_reference.json")
    )
    visibility_manifest = ProgrambenchTaskVisibilityManifest.model_validate(
        _load_fixture("programbench_task_visibility_manifest_v245_reference.json")
    )
    worker_access_contract = ProgrambenchAdapterWorkerAccessContract.model_validate(
        _load_fixture("programbench_adapter_worker_access_contract_v245_reference.json")
    )
    guardrail = ProgrambenchAdapterNonAuthorityGuardrail.model_validate(
        _load_fixture("programbench_adapter_non_authority_guardrail_v245_reference.json")
    )

    validate_pb_adapter_0a_task_intake_bundle(
        task_intake=task_intake,
        artifact_manifest=artifact_manifest,
        visibility_manifest=visibility_manifest,
        worker_access_contract=worker_access_contract,
        guardrail=guardrail,
    )

    assert artifact_manifest.reference_executable_hash.startswith("sha256:")
    assert visibility_manifest.forbidden_store_reachability_posture == (
        "forbidden_and_hidden_stores_unreachable_during_inference"
    )
    assert (
        worker_access_contract.allowed_command_posture
        == "no_command_execution_authority_by_pb_adapter_0a"
    )
    assert guardrail.benchmark_truth_posture == "not_benchmark_truth"


def test_pb_adapter_0a_bundle_rejects_hidden_or_forbidden_allowed_inference_ref() -> None:
    task_intake = ProgrambenchCleanroomTaskIntake.model_validate(
        _load_fixture("programbench_cleanroom_task_intake_v245_reference.json")
    )
    artifact_manifest = ProgrambenchTaskArtifactManifest.model_validate(
        _load_fixture("programbench_task_artifact_manifest_v245_reference.json")
    )
    visibility_manifest = ProgrambenchTaskVisibilityManifest.model_validate(
        _load_fixture("programbench_task_visibility_manifest_v245_reference.json")
    )
    contract_payload = deepcopy(
        _load_fixture("programbench_adapter_worker_access_contract_v245_reference.json")
    )
    contract_payload["allowed_inference_source_refs"].append("store:hidden-evaluator")
    contract_payload["forbidden_inference_source_refs"].remove("store:hidden-evaluator")
    worker_access_contract = ProgrambenchAdapterWorkerAccessContract.model_validate(
        contract_payload
    )
    guardrail = ProgrambenchAdapterNonAuthorityGuardrail.model_validate(
        _load_fixture("programbench_adapter_non_authority_guardrail_v245_reference.json")
    )

    with pytest.raises(ValueError, match="allows hidden or forbidden"):
        validate_pb_adapter_0a_task_intake_bundle(
            task_intake=task_intake,
            artifact_manifest=artifact_manifest,
            visibility_manifest=visibility_manifest,
            worker_access_contract=worker_access_contract,
            guardrail=guardrail,
        )


def test_pb_adapter_0a_bundle_rejects_artifact_identity_drift() -> None:
    task_intake = ProgrambenchCleanroomTaskIntake.model_validate(
        _load_fixture("programbench_cleanroom_task_intake_v245_reference.json")
    )
    artifact_payload = deepcopy(
        _load_fixture("programbench_task_artifact_manifest_v245_reference.json")
    )
    artifact_payload["usage_docs_hash_rows"][0]["artifact_ref"] = "artifact:usage-doc:drifted"
    artifact_manifest = ProgrambenchTaskArtifactManifest.model_validate(artifact_payload)
    visibility_manifest = ProgrambenchTaskVisibilityManifest.model_validate(
        _load_fixture("programbench_task_visibility_manifest_v245_reference.json")
    )
    worker_access_contract = ProgrambenchAdapterWorkerAccessContract.model_validate(
        _load_fixture("programbench_adapter_worker_access_contract_v245_reference.json")
    )
    guardrail = ProgrambenchAdapterNonAuthorityGuardrail.model_validate(
        _load_fixture("programbench_adapter_non_authority_guardrail_v245_reference.json")
    )

    with pytest.raises(ValueError, match="exactly the task intake usage docs"):
        validate_pb_adapter_0a_task_intake_bundle(
            task_intake=task_intake,
            artifact_manifest=artifact_manifest,
            visibility_manifest=visibility_manifest,
            worker_access_contract=worker_access_contract,
            guardrail=guardrail,
        )


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_cleanroom_adapter_v245_reject_official_participation.json",
            ProgrambenchCleanroomTaskIntake,
        ),
        (
            "programbench_cleanroom_adapter_v245_reject_forbidden_worker_visible.json",
            ProgrambenchTaskVisibilityManifest,
        ),
        (
            "programbench_cleanroom_adapter_v245_reject_hidden_summary_cleanroom_visible.json",
            ProgrambenchTaskVisibilityManifest,
        ),
        (
            "programbench_cleanroom_adapter_v245_reject_command_authority.json",
            ProgrambenchAdapterWorkerAccessContract,
        ),
        (
            "programbench_cleanroom_adapter_v245_reject_probe_authority.json",
            ProgrambenchAdapterWorkerAccessContract,
        ),
        (
            "programbench_cleanroom_adapter_v245_reject_guardrail_missing_future_slice_artifact.json",
            ProgrambenchAdapterNonAuthorityGuardrail,
        ),
    ],
)
def test_pb_adapter_0a_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_fixture(fixture_name))


def test_pb_adapter_0a_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative["properties"]["schema"]["const"] == expected_schema
        assert authoritative == mirror

        serialized = json.dumps(authoritative, sort_keys=True)
        assert _repo_root().as_posix() not in serialized
        assert not _WINDOWS_ABSOLUTE_PATH_RE.search(serialized)
