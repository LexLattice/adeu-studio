from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_CANDIDATE_MATERIALIZATION_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_OUTPUT_CAPTURE_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_SANDBOX_APPLICATION_TRACE_SCHEMA,
    PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_WORKER_INVOCATION_RECORD_SCHEMA,
    ProgrambenchReconstructionAttemptCandidateMaterialization,
    ProgrambenchReconstructionAttemptDispatchPreflight,
    ProgrambenchReconstructionAttemptNonAuthorityGuardrail,
    ProgrambenchReconstructionAttemptOutputCapture,
    ProgrambenchReconstructionAttemptRequest,
    ProgrambenchReconstructionAttemptSandboxApplicationTrace,
    ProgrambenchReconstructionAttemptWorkerInputPacket,
    ProgrambenchReconstructionAttemptWorkerInvocationRecord,
    ProgrambenchReconstructionRunBudget,
    ProgrambenchReconstructionSandboxPolicy,
    validate_pb_attempt_0b_invocation_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root_recon_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus248"


def _fixture_root_attempt_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus251"


def _fixture_root_attempt_b() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus252"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_recon_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_recon_a(), name)


def _load_attempt_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_attempt_a(), name)


def _load_attempt_b_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_attempt_b(), name)


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
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_WORKER_INVOCATION_RECORD_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_attempt_worker_invocation_record.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_attempt_worker_invocation_record.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_OUTPUT_CAPTURE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_attempt_output_capture.v1.json",
            root / "spec" / "programbench_reconstruction_attempt_output_capture.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_CANDIDATE_MATERIALIZATION_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_attempt_candidate_materialization.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_attempt_candidate_materialization.schema.json",
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_SANDBOX_APPLICATION_TRACE_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_reconstruction_attempt_sandbox_application_trace.v1.json",
            root
            / "spec"
            / "programbench_reconstruction_attempt_sandbox_application_trace.schema.json",
        ),
    ]


def _load_attempt_a_rows() -> tuple[
    ProgrambenchReconstructionAttemptRequest,
    ProgrambenchReconstructionAttemptWorkerInputPacket,
    ProgrambenchReconstructionAttemptDispatchPreflight,
    ProgrambenchReconstructionAttemptNonAuthorityGuardrail,
]:
    return (
        ProgrambenchReconstructionAttemptRequest.model_validate(
            _load_attempt_a_fixture(
                "programbench_reconstruction_attempt_request_v251_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptWorkerInputPacket.model_validate(
            _load_attempt_a_fixture(
                "programbench_reconstruction_attempt_worker_input_packet_v251_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptDispatchPreflight.model_validate(
            _load_attempt_a_fixture(
                "programbench_reconstruction_attempt_dispatch_preflight_v251_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptNonAuthorityGuardrail.model_validate(
            _load_attempt_a_fixture(
                "programbench_reconstruction_attempt_non_authority_guardrail_v251_reference.json"
            )
        ),
    )


def _load_attempt_b_rows() -> tuple[
    ProgrambenchReconstructionAttemptWorkerInvocationRecord,
    ProgrambenchReconstructionAttemptOutputCapture,
    ProgrambenchReconstructionAttemptCandidateMaterialization,
    ProgrambenchReconstructionAttemptSandboxApplicationTrace,
]:
    return (
        ProgrambenchReconstructionAttemptWorkerInvocationRecord.model_validate(
            _load_attempt_b_fixture(
                "programbench_reconstruction_attempt_worker_invocation_record_v252_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptOutputCapture.model_validate(
            _load_attempt_b_fixture(
                "programbench_reconstruction_attempt_output_capture_v252_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptCandidateMaterialization.model_validate(
            _load_attempt_b_fixture(
                "programbench_reconstruction_attempt_candidate_materialization_v252_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptSandboxApplicationTrace.model_validate(
            _load_attempt_b_fixture(
                "programbench_reconstruction_attempt_sandbox_application_trace_v252_reference.json"
            )
        ),
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_WORKER_INVOCATION_RECORD_SCHEMA,
            "programbench_reconstruction_attempt_worker_invocation_record.v1.json",
            "programbench_reconstruction_attempt_worker_invocation_record_v252_reference.json",
            ProgrambenchReconstructionAttemptWorkerInvocationRecord,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_OUTPUT_CAPTURE_SCHEMA,
            "programbench_reconstruction_attempt_output_capture.v1.json",
            "programbench_reconstruction_attempt_output_capture_v252_reference.json",
            ProgrambenchReconstructionAttemptOutputCapture,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_CANDIDATE_MATERIALIZATION_SCHEMA,
            "programbench_reconstruction_attempt_candidate_materialization.v1.json",
            "programbench_reconstruction_attempt_candidate_materialization_v252_reference.json",
            ProgrambenchReconstructionAttemptCandidateMaterialization,
        ),
        (
            PROGRAMBENCH_RECONSTRUCTION_ATTEMPT_SANDBOX_APPLICATION_TRACE_SCHEMA,
            "programbench_reconstruction_attempt_sandbox_application_trace.v1.json",
            "programbench_reconstruction_attempt_sandbox_application_trace_v252_reference.json",
            ProgrambenchReconstructionAttemptSandboxApplicationTrace,
        ),
    ],
)
def test_pb_attempt_0b_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_attempt_b_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_attempt_0b_reference_bundle_preserves_local_only_boundary() -> None:
    attempt_request, worker_input_packet, dispatch_preflight, guardrail = _load_attempt_a_rows()
    sandbox_policy = ProgrambenchReconstructionSandboxPolicy.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_sandbox_policy_v248_reference.json")
    )
    run_budget = ProgrambenchReconstructionRunBudget.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_run_budget_v248_reference.json")
    )
    (
        worker_invocation_record,
        output_capture,
        candidate_materialization,
        sandbox_application_trace,
    ) = _load_attempt_b_rows()

    validate_pb_attempt_0b_invocation_bundle(
        attempt_request=attempt_request,
        worker_input_packet=worker_input_packet,
        dispatch_preflight=dispatch_preflight,
        guardrail=guardrail,
        sandbox_policy=sandbox_policy,
        run_budget=run_budget,
        worker_invocation_record=worker_invocation_record,
        output_capture=output_capture,
        candidate_materialization=candidate_materialization,
        sandbox_application_trace=sandbox_application_trace,
    )

    assert worker_invocation_record.input_packet_hash == (
        worker_input_packet.worker_input_manifest_hash
    )
    assert output_capture.forbidden_content_screening_posture == "passed"
    assert candidate_materialization.materialized_inside_write_scope is True
    assert sandbox_application_trace.network_attestation_ref == (
        "attestation:pb-attempt-0b:network-disabled"
    )


def test_pb_attempt_0b_bundle_rejects_blocked_preflight() -> None:
    attempt_request, worker_input_packet, dispatch_preflight, guardrail = _load_attempt_a_rows()
    sandbox_policy = ProgrambenchReconstructionSandboxPolicy.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_sandbox_policy_v248_reference.json")
    )
    run_budget = ProgrambenchReconstructionRunBudget.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_run_budget_v248_reference.json")
    )
    blocked_preflight = dispatch_preflight.model_copy(
        update={"preflight_posture": "blocked_no_dispatch_eligible"}
    )
    (
        worker_invocation_record,
        output_capture,
        candidate_materialization,
        sandbox_application_trace,
    ) = _load_attempt_b_rows()

    with pytest.raises(ValueError, match="passed A preflight"):
        validate_pb_attempt_0b_invocation_bundle(
            attempt_request=attempt_request,
            worker_input_packet=worker_input_packet,
            dispatch_preflight=blocked_preflight,
            guardrail=guardrail,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            worker_invocation_record=worker_invocation_record,
            output_capture=output_capture,
            candidate_materialization=candidate_materialization,
            sandbox_application_trace=sandbox_application_trace,
        )


def test_pb_attempt_0b_bundle_rejects_unreleased_preflight_ref() -> None:
    attempt_request, worker_input_packet, dispatch_preflight, guardrail = _load_attempt_a_rows()
    sandbox_policy = ProgrambenchReconstructionSandboxPolicy.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_sandbox_policy_v248_reference.json")
    )
    run_budget = ProgrambenchReconstructionRunBudget.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_run_budget_v248_reference.json")
    )
    invocation_model = ProgrambenchReconstructionAttemptWorkerInvocationRecord
    worker_invocation_record = invocation_model.model_validate(
        _load_attempt_b_fixture(
            "programbench_reconstruction_attempt_v252_reject_invocation_without_released_preflight.json"
        )
    )
    (
        _worker_invocation_record,
        output_capture,
        candidate_materialization,
        sandbox_application_trace,
    ) = _load_attempt_b_rows()

    with pytest.raises(ValueError, match="dispatch preflight"):
        validate_pb_attempt_0b_invocation_bundle(
            attempt_request=attempt_request,
            worker_input_packet=worker_input_packet,
            dispatch_preflight=dispatch_preflight,
            guardrail=guardrail,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            worker_invocation_record=worker_invocation_record,
            output_capture=output_capture,
            candidate_materialization=candidate_materialization,
            sandbox_application_trace=sandbox_application_trace,
        )


def test_pb_attempt_0b_bundle_rejects_forbidden_output_materialization() -> None:
    attempt_request, worker_input_packet, dispatch_preflight, guardrail = _load_attempt_a_rows()
    sandbox_policy = ProgrambenchReconstructionSandboxPolicy.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_sandbox_policy_v248_reference.json")
    )
    run_budget = ProgrambenchReconstructionRunBudget.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_run_budget_v248_reference.json")
    )
    (
        worker_invocation_record,
        _output_capture,
        candidate_materialization,
        sandbox_application_trace,
    ) = _load_attempt_b_rows()
    output_capture = ProgrambenchReconstructionAttemptOutputCapture.model_validate(
        _load_attempt_b_fixture(
            "programbench_reconstruction_attempt_v252_reject_forbidden_output_materialized.json"
        )
    )

    with pytest.raises(ValueError, match="forbidden-content screening"):
        validate_pb_attempt_0b_invocation_bundle(
            attempt_request=attempt_request,
            worker_input_packet=worker_input_packet,
            dispatch_preflight=dispatch_preflight,
            guardrail=guardrail,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            worker_invocation_record=worker_invocation_record,
            output_capture=output_capture,
            candidate_materialization=candidate_materialization,
            sandbox_application_trace=sandbox_application_trace,
        )


def test_pb_attempt_0b_rejects_inconsistent_blocked_screening_posture() -> None:
    payload = _load_attempt_b_fixture(
        "programbench_reconstruction_attempt_v252_reject_forbidden_output_materialized.json"
    )
    payload["forbidden_content_screening_posture"] = "blocked_hidden_evidence"

    with pytest.raises(ValidationError, match="requires a matching blocked row"):
        ProgrambenchReconstructionAttemptOutputCapture.model_validate(payload)


def test_pb_attempt_0b_bundle_rejects_materialization_hash_not_from_screened_output() -> None:
    attempt_request, worker_input_packet, dispatch_preflight, guardrail = _load_attempt_a_rows()
    sandbox_policy = ProgrambenchReconstructionSandboxPolicy.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_sandbox_policy_v248_reference.json")
    )
    run_budget = ProgrambenchReconstructionRunBudget.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_run_budget_v248_reference.json")
    )
    worker_invocation_record, output_capture, candidate_materialization, sandbox_trace = (
        _load_attempt_b_rows()
    )
    mismatched_materialization = candidate_materialization.model_copy(
        update={
            "materialization_input_hash": (
                "sha256:9999999999999999999999999999999999999999999999999999999999999999"
            )
        }
    )

    with pytest.raises(ValueError, match="screened candidate-file output hash"):
        validate_pb_attempt_0b_invocation_bundle(
            attempt_request=attempt_request,
            worker_input_packet=worker_input_packet,
            dispatch_preflight=dispatch_preflight,
            guardrail=guardrail,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            worker_invocation_record=worker_invocation_record,
            output_capture=output_capture,
            candidate_materialization=mismatched_materialization,
            sandbox_application_trace=sandbox_trace,
        )


def test_pb_attempt_0b_bundle_rejects_materialization_outside_write_scope() -> None:
    attempt_request, worker_input_packet, dispatch_preflight, guardrail = _load_attempt_a_rows()
    sandbox_policy = ProgrambenchReconstructionSandboxPolicy.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_sandbox_policy_v248_reference.json")
    )
    run_budget = ProgrambenchReconstructionRunBudget.model_validate(
        _load_recon_a_fixture("programbench_reconstruction_run_budget_v248_reference.json")
    )
    worker_invocation_record, output_capture, _candidate_materialization, _trace = (
        _load_attempt_b_rows()
    )
    materialization_model = ProgrambenchReconstructionAttemptCandidateMaterialization
    candidate_materialization = materialization_model.model_validate(
        _load_attempt_b_fixture(
            "programbench_reconstruction_attempt_v252_reject_materialization_outside_write_scope.json"
        )
    )
    sandbox_application_trace = (
        ProgrambenchReconstructionAttemptSandboxApplicationTrace.model_validate(
            _load_attempt_b_fixture(
                "programbench_reconstruction_attempt_sandbox_application_trace_v252_reference.json"
            )
            | {
                "candidate_materialization_ref": (
                    "candidate-materialization:pb-attempt-0b:outside-write-scope"
                )
            }
        )
    )

    with pytest.raises(ValueError, match="write scope"):
        validate_pb_attempt_0b_invocation_bundle(
            attempt_request=attempt_request,
            worker_input_packet=worker_input_packet,
            dispatch_preflight=dispatch_preflight,
            guardrail=guardrail,
            sandbox_policy=sandbox_policy,
            run_budget=run_budget,
            worker_invocation_record=worker_invocation_record,
            output_capture=output_capture,
            candidate_materialization=candidate_materialization,
            sandbox_application_trace=sandbox_application_trace,
        )


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_reconstruction_attempt_v252_reject_hidden_test_access.json",
            ProgrambenchReconstructionAttemptWorkerInvocationRecord,
        ),
        (
            "programbench_reconstruction_attempt_v252_reject_official_submission_posture.json",
            ProgrambenchReconstructionAttemptCandidateMaterialization,
        ),
    ],
)
def test_pb_attempt_0b_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_attempt_b_fixture(fixture_name))


def test_pb_attempt_0b_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative["properties"]["schema"]["const"] == expected_schema
        assert authoritative == mirror

        serialized = json.dumps(authoritative, sort_keys=True)
        assert _repo_root().as_posix() not in serialized
        assert not _WINDOWS_ABSOLUTE_PATH_RE.search(serialized)
