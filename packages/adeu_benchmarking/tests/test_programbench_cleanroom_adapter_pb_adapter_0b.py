from __future__ import annotations

import json
import re
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_ADAPTER_PROBE_PLAN_SCHEMA,
    PROGRAMBENCH_FILESYSTEM_SIDE_EFFECT_OBSERVATION_SCHEMA,
    PROGRAMBENCH_IO_ARTIFACT_OBSERVATION_INDEX_SCHEMA,
    PROGRAMBENCH_PROBE_OBSERVATION_LOG_SCHEMA,
    ProgrambenchAdapterNonAuthorityGuardrail,
    ProgrambenchAdapterProbePlan,
    ProgrambenchAdapterWorkerAccessContract,
    ProgrambenchCleanroomTaskIntake,
    ProgrambenchFilesystemSideEffectObservation,
    ProgrambenchIOArtifactObservationIndex,
    ProgrambenchProbeObservationLog,
    ProgrambenchTaskArtifactManifest,
    ProgrambenchTaskVisibilityManifest,
    validate_pb_adapter_0b_probe_observation_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus245"


def _fixture_root_b() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus246"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_a(), name)


def _load_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_b(), name)


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
            PROGRAMBENCH_ADAPTER_PROBE_PLAN_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_adapter_probe_plan.v1.json",
            root / "spec" / "programbench_adapter_probe_plan.schema.json",
        ),
        (
            PROGRAMBENCH_PROBE_OBSERVATION_LOG_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_probe_observation_log.v1.json",
            root / "spec" / "programbench_probe_observation_log.schema.json",
        ),
        (
            PROGRAMBENCH_IO_ARTIFACT_OBSERVATION_INDEX_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_io_artifact_observation_index.v1.json",
            root / "spec" / "programbench_io_artifact_observation_index.schema.json",
        ),
        (
            PROGRAMBENCH_FILESYSTEM_SIDE_EFFECT_OBSERVATION_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_filesystem_side_effect_observation.v1.json",
            root / "spec" / "programbench_filesystem_side_effect_observation.schema.json",
        ),
    ]


def _load_a_bundle() -> tuple[
    ProgrambenchCleanroomTaskIntake,
    ProgrambenchTaskArtifactManifest,
    ProgrambenchTaskVisibilityManifest,
    ProgrambenchAdapterWorkerAccessContract,
    ProgrambenchAdapterNonAuthorityGuardrail,
]:
    return (
        ProgrambenchCleanroomTaskIntake.model_validate(
            _load_a_fixture("programbench_cleanroom_task_intake_v245_reference.json")
        ),
        ProgrambenchTaskArtifactManifest.model_validate(
            _load_a_fixture("programbench_task_artifact_manifest_v245_reference.json")
        ),
        ProgrambenchTaskVisibilityManifest.model_validate(
            _load_a_fixture("programbench_task_visibility_manifest_v245_reference.json")
        ),
        ProgrambenchAdapterWorkerAccessContract.model_validate(
            _load_a_fixture("programbench_adapter_worker_access_contract_v245_reference.json")
        ),
        ProgrambenchAdapterNonAuthorityGuardrail.model_validate(
            _load_a_fixture("programbench_adapter_non_authority_guardrail_v245_reference.json")
        ),
    )


def _load_b_bundle() -> tuple[
    ProgrambenchAdapterProbePlan,
    list[ProgrambenchProbeObservationLog],
    ProgrambenchIOArtifactObservationIndex,
    list[ProgrambenchFilesystemSideEffectObservation],
]:
    return (
        ProgrambenchAdapterProbePlan.model_validate(
            _load_b_fixture("programbench_adapter_probe_plan_v246_reference.json")
        ),
        [
            ProgrambenchProbeObservationLog.model_validate(
                _load_b_fixture("programbench_probe_observation_log_v246_reference.json")
            )
        ],
        ProgrambenchIOArtifactObservationIndex.model_validate(
            _load_b_fixture("programbench_io_artifact_observation_index_v246_reference.json")
        ),
        [
            ProgrambenchFilesystemSideEffectObservation.model_validate(
                _load_b_fixture(
                    "programbench_filesystem_side_effect_observation_v246_reference.json"
                )
            )
        ],
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_ADAPTER_PROBE_PLAN_SCHEMA,
            "programbench_adapter_probe_plan.v1.json",
            "programbench_adapter_probe_plan_v246_reference.json",
            ProgrambenchAdapterProbePlan,
        ),
        (
            PROGRAMBENCH_PROBE_OBSERVATION_LOG_SCHEMA,
            "programbench_probe_observation_log.v1.json",
            "programbench_probe_observation_log_v246_reference.json",
            ProgrambenchProbeObservationLog,
        ),
        (
            PROGRAMBENCH_IO_ARTIFACT_OBSERVATION_INDEX_SCHEMA,
            "programbench_io_artifact_observation_index.v1.json",
            "programbench_io_artifact_observation_index_v246_reference.json",
            ProgrambenchIOArtifactObservationIndex,
        ),
        (
            PROGRAMBENCH_FILESYSTEM_SIDE_EFFECT_OBSERVATION_SCHEMA,
            "programbench_filesystem_side_effect_observation.v1.json",
            "programbench_filesystem_side_effect_observation_v246_reference.json",
            ProgrambenchFilesystemSideEffectObservation,
        ),
    ],
)
def test_pb_adapter_0b_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_b_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_adapter_0b_reference_bundle_preserves_probe_observation_boundary() -> None:
    (
        task_intake,
        artifact_manifest,
        visibility_manifest,
        worker_access_contract,
        guardrail,
    ) = _load_a_bundle()
    (
        probe_plan,
        observation_logs,
        io_artifact_index,
        filesystem_side_effect_observations,
    ) = _load_b_bundle()

    validate_pb_adapter_0b_probe_observation_bundle(
        task_intake=task_intake,
        artifact_manifest=artifact_manifest,
        visibility_manifest=visibility_manifest,
        worker_access_contract=worker_access_contract,
        guardrail=guardrail,
        probe_plan=probe_plan,
        observation_logs=observation_logs,
        io_artifact_index=io_artifact_index,
        filesystem_side_effect_observations=filesystem_side_effect_observations,
    )

    assert probe_plan.probe_phase_posture == "plan_only_no_execution_by_this_row"
    assert probe_plan.network_policy == "network_disabled_during_probe"
    assert observation_logs[0].hidden_test_equivalence_posture == (
        "local_probe_not_hidden_test_equivalence"
    )
    assert io_artifact_index.artifact_truth_posture == (
        "local_probe_artifacts_not_benchmark_truth"
    )
    assert filesystem_side_effect_observations[0].path_scope_posture == (
        "within_allowed_write_scope"
    )


def test_pb_adapter_0b_bundle_requires_released_a_access_contract_ref() -> None:
    (
        task_intake,
        artifact_manifest,
        visibility_manifest,
        worker_access_contract,
        guardrail,
    ) = _load_a_bundle()
    (
        probe_plan,
        observation_logs,
        io_artifact_index,
        filesystem_side_effect_observations,
    ) = _load_b_bundle()
    drifted_plan = probe_plan.model_copy(
        update={"worker_access_contract_ref": "worker-access-contract:missing"}
    )

    with pytest.raises(ValueError, match="released worker access contract"):
        validate_pb_adapter_0b_probe_observation_bundle(
            task_intake=task_intake,
            artifact_manifest=artifact_manifest,
            visibility_manifest=visibility_manifest,
            worker_access_contract=worker_access_contract,
            guardrail=guardrail,
            probe_plan=drifted_plan,
            observation_logs=observation_logs,
            io_artifact_index=io_artifact_index,
            filesystem_side_effect_observations=filesystem_side_effect_observations,
        )


def test_pb_adapter_0b_bundle_rejects_unplanned_observation_command_shape() -> None:
    (
        task_intake,
        artifact_manifest,
        visibility_manifest,
        worker_access_contract,
        guardrail,
    ) = _load_a_bundle()
    (
        probe_plan,
        observation_logs,
        io_artifact_index,
        filesystem_side_effect_observations,
    ) = _load_b_bundle()
    drifted_observation = observation_logs[0].model_copy(
        update={"command_shape_ref": "command-shape:pb-adapter-0b:unplanned"}
    )

    with pytest.raises(ValueError, match="allowed probe command rows"):
        validate_pb_adapter_0b_probe_observation_bundle(
            task_intake=task_intake,
            artifact_manifest=artifact_manifest,
            visibility_manifest=visibility_manifest,
            worker_access_contract=worker_access_contract,
            guardrail=guardrail,
            probe_plan=probe_plan,
            observation_logs=[drifted_observation],
            io_artifact_index=io_artifact_index,
            filesystem_side_effect_observations=filesystem_side_effect_observations,
        )


def test_pb_adapter_0b_bundle_rejects_unknown_io_artifact_observation_ref() -> None:
    (
        task_intake,
        artifact_manifest,
        visibility_manifest,
        worker_access_contract,
        guardrail,
    ) = _load_a_bundle()
    (
        probe_plan,
        observation_logs,
        io_artifact_index,
        filesystem_side_effect_observations,
    ) = _load_b_bundle()
    drifted_index = io_artifact_index.model_copy(
        update={"probe_observation_refs": ["probe-observation:pb-adapter-0b:missing"]}
    )

    with pytest.raises(ValueError, match="cover exactly the probe observations"):
        validate_pb_adapter_0b_probe_observation_bundle(
            task_intake=task_intake,
            artifact_manifest=artifact_manifest,
            visibility_manifest=visibility_manifest,
            worker_access_contract=worker_access_contract,
            guardrail=guardrail,
            probe_plan=probe_plan,
            observation_logs=observation_logs,
            io_artifact_index=drifted_index,
            filesystem_side_effect_observations=filesystem_side_effect_observations,
        )


def test_pb_adapter_0b_bundle_requires_side_effect_coverage_for_each_observation() -> None:
    (
        task_intake,
        artifact_manifest,
        visibility_manifest,
        worker_access_contract,
        guardrail,
    ) = _load_a_bundle()
    (
        probe_plan,
        observation_logs,
        io_artifact_index,
        filesystem_side_effect_observations,
    ) = _load_b_bundle()
    second_observation = observation_logs[0].model_copy(
        update={
            "probe_observation_ref": "probe-observation:pb-adapter-0b:toy-cli-version",
            "stdout_observation_ref": "stdout:pb-adapter-0b:toy-cli-version",
            "stderr_observation_ref": "stderr:pb-adapter-0b:toy-cli-version",
            "exit_code_observation_ref": "exit-code:pb-adapter-0b:toy-cli-version",
        }
    )
    expanded_index = io_artifact_index.model_copy(
        update={
            "probe_observation_refs": [
                "probe-observation:pb-adapter-0b:toy-cli-help",
                "probe-observation:pb-adapter-0b:toy-cli-version",
            ]
        }
    )

    with pytest.raises(ValueError, match="filesystem side effects must cover exactly"):
        validate_pb_adapter_0b_probe_observation_bundle(
            task_intake=task_intake,
            artifact_manifest=artifact_manifest,
            visibility_manifest=visibility_manifest,
            worker_access_contract=worker_access_contract,
            guardrail=guardrail,
            probe_plan=probe_plan,
            observation_logs=[observation_logs[0], second_observation],
            io_artifact_index=expanded_index,
            filesystem_side_effect_observations=filesystem_side_effect_observations,
        )


def test_pb_adapter_0b_bundle_rejects_duplicate_side_effect_observation_coverage() -> None:
    (
        task_intake,
        artifact_manifest,
        visibility_manifest,
        worker_access_contract,
        guardrail,
    ) = _load_a_bundle()
    (
        probe_plan,
        observation_logs,
        io_artifact_index,
        filesystem_side_effect_observations,
    ) = _load_b_bundle()
    duplicate_side_effect = filesystem_side_effect_observations[0].model_copy(
        update={"side_effect_observation_ref": "side-effect:pb-adapter-0b:duplicate"}
    )

    with pytest.raises(ValueError, match="filesystem side-effect observation refs"):
        validate_pb_adapter_0b_probe_observation_bundle(
            task_intake=task_intake,
            artifact_manifest=artifact_manifest,
            visibility_manifest=visibility_manifest,
            worker_access_contract=worker_access_contract,
            guardrail=guardrail,
            probe_plan=probe_plan,
            observation_logs=observation_logs,
            io_artifact_index=io_artifact_index,
            filesystem_side_effect_observations=[
                filesystem_side_effect_observations[0],
                duplicate_side_effect,
            ],
        )


def test_pb_adapter_0b_io_artifact_index_rejects_cross_category_overlap() -> None:
    payload = deepcopy(
        _load_b_fixture("programbench_io_artifact_observation_index_v246_reference.json")
    )
    payload["generated_output_artifact_refs"] = payload["stdout_artifact_refs"]

    with pytest.raises(ValidationError, match="artifact refs must not overlap"):
        ProgrambenchIOArtifactObservationIndex.model_validate(payload)


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_cleanroom_adapter_v246_reject_raw_shell_command.json",
            ProgrambenchAdapterProbePlan,
        ),
        (
            "programbench_cleanroom_adapter_v246_reject_hidden_evaluator_observation.json",
            ProgrambenchProbeObservationLog,
        ),
        (
            "programbench_cleanroom_adapter_v246_reject_hidden_test_equivalence.json",
            ProgrambenchProbeObservationLog,
        ),
        (
            "programbench_cleanroom_adapter_v246_reject_benchmark_truth_artifact_index.json",
            ProgrambenchIOArtifactObservationIndex,
        ),
        (
            "programbench_cleanroom_adapter_v246_reject_side_effect_outside_scope.json",
            ProgrambenchFilesystemSideEffectObservation,
        ),
        (
            "programbench_cleanroom_adapter_v246_reject_official_probe_authority.json",
            ProgrambenchAdapterProbePlan,
        ),
    ],
)
def test_pb_adapter_0b_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_b_fixture(fixture_name))


def test_pb_adapter_0b_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative["properties"]["schema"]["const"] == expected_schema
        assert authoritative == mirror

        serialized = json.dumps(authoritative, sort_keys=True)
        assert _repo_root().as_posix() not in serialized
        assert not _WINDOWS_ABSOLUTE_PATH_RE.search(serialized)
