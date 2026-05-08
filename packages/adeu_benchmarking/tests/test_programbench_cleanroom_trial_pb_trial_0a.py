from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_LOCAL_RECONSTRUCTION_TRIAL_DOCKET_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_EXECUTION_RUNBOOK_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    PROGRAMBENCH_LOCAL_TRIAL_SANDBOX_READINESS_REVIEW_SCHEMA,
    ProgrambenchLocalReconstructionTrialDocket,
    ProgrambenchLocalTrialExecutionRunbook,
    ProgrambenchLocalTrialNonAuthorityGuardrail,
    ProgrambenchLocalTrialSandboxReadinessReview,
    ProgrambenchReconstructionAttemptDispatchPreflight,
    ProgrambenchReconstructionAttemptFamilyCloseoutAlignment,
    ProgrambenchReconstructionAttemptNonAuthorityGuardrail,
    ProgrambenchReconstructionAttemptRequest,
    ProgrambenchReconstructionAttemptResultReview,
    ProgrambenchReconstructionAttemptWorkerInputPacket,
    validate_pb_trial_0a_trial_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError

_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root_attempt_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus251"


def _fixture_root_attempt_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus253"


def _fixture_root_trial_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus254"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_attempt_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_attempt_a(), name)


def _load_attempt_c_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_attempt_c(), name)


def _load_trial_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_trial_a(), name)


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
            PROGRAMBENCH_LOCAL_RECONSTRUCTION_TRIAL_DOCKET_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_reconstruction_trial_docket.v1.json",
            root / "spec" / "programbench_local_reconstruction_trial_docket.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_EXECUTION_RUNBOOK_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_trial_execution_runbook.v1.json",
            root / "spec" / "programbench_local_trial_execution_runbook.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_SANDBOX_READINESS_REVIEW_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_trial_sandbox_readiness_review.v1.json",
            root / "spec" / "programbench_local_trial_sandbox_readiness_review.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_trial_non_authority_guardrail.v1.json",
            root / "spec" / "programbench_local_trial_non_authority_guardrail.schema.json",
        ),
    ]


def _load_attempt_rows() -> tuple[
    ProgrambenchReconstructionAttemptRequest,
    ProgrambenchReconstructionAttemptWorkerInputPacket,
    ProgrambenchReconstructionAttemptDispatchPreflight,
    ProgrambenchReconstructionAttemptNonAuthorityGuardrail,
    ProgrambenchReconstructionAttemptResultReview,
    ProgrambenchReconstructionAttemptFamilyCloseoutAlignment,
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
        ProgrambenchReconstructionAttemptResultReview.model_validate(
            _load_attempt_c_fixture(
                "programbench_reconstruction_attempt_result_review_v253_reference.json"
            )
        ),
        ProgrambenchReconstructionAttemptFamilyCloseoutAlignment.model_validate(
            _load_attempt_c_fixture(
                "programbench_reconstruction_attempt_family_closeout_alignment_v253_reference.json"
            )
        ),
    )


def _load_trial_rows() -> tuple[
    ProgrambenchLocalReconstructionTrialDocket,
    ProgrambenchLocalTrialExecutionRunbook,
    ProgrambenchLocalTrialSandboxReadinessReview,
    ProgrambenchLocalTrialNonAuthorityGuardrail,
]:
    return (
        ProgrambenchLocalReconstructionTrialDocket.model_validate(
            _load_trial_a_fixture(
                "programbench_local_reconstruction_trial_docket_v254_reference.json"
            )
        ),
        ProgrambenchLocalTrialExecutionRunbook.model_validate(
            _load_trial_a_fixture("programbench_local_trial_execution_runbook_v254_reference.json")
        ),
        ProgrambenchLocalTrialSandboxReadinessReview.model_validate(
            _load_trial_a_fixture(
                "programbench_local_trial_sandbox_readiness_review_v254_reference.json"
            )
        ),
        ProgrambenchLocalTrialNonAuthorityGuardrail.model_validate(
            _load_trial_a_fixture(
                "programbench_local_trial_non_authority_guardrail_v254_reference.json"
            )
        ),
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_LOCAL_RECONSTRUCTION_TRIAL_DOCKET_SCHEMA,
            "programbench_local_reconstruction_trial_docket.v1.json",
            "programbench_local_reconstruction_trial_docket_v254_reference.json",
            ProgrambenchLocalReconstructionTrialDocket,
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_EXECUTION_RUNBOOK_SCHEMA,
            "programbench_local_trial_execution_runbook.v1.json",
            "programbench_local_trial_execution_runbook_v254_reference.json",
            ProgrambenchLocalTrialExecutionRunbook,
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_SANDBOX_READINESS_REVIEW_SCHEMA,
            "programbench_local_trial_sandbox_readiness_review.v1.json",
            "programbench_local_trial_sandbox_readiness_review_v254_reference.json",
            ProgrambenchLocalTrialSandboxReadinessReview,
        ),
        (
            PROGRAMBENCH_LOCAL_TRIAL_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            "programbench_local_trial_non_authority_guardrail.v1.json",
            "programbench_local_trial_non_authority_guardrail_v254_reference.json",
            ProgrambenchLocalTrialNonAuthorityGuardrail,
        ),
    ],
)
def test_pb_trial_0a_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_trial_a_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_trial_0a_reference_bundle_preserves_non_execution_boundary() -> None:
    (
        attempt_request,
        worker_input_packet,
        dispatch_preflight,
        attempt_guardrail,
        prior_attempt_result_review,
        attempt_family_closeout,
    ) = _load_attempt_rows()
    (
        trial_docket,
        execution_runbook,
        sandbox_readiness_review,
        trial_guardrail,
    ) = _load_trial_rows()

    validate_pb_trial_0a_trial_bundle(
        attempt_request=attempt_request,
        worker_input_packet=worker_input_packet,
        dispatch_preflight=dispatch_preflight,
        attempt_guardrail=attempt_guardrail,
        prior_attempt_result_review=prior_attempt_result_review,
        attempt_family_closeout=attempt_family_closeout,
        trial_docket=trial_docket,
        execution_runbook=execution_runbook,
        sandbox_readiness_review=sandbox_readiness_review,
        trial_guardrail=trial_guardrail,
    )

    assert trial_docket.prior_attempt_result_review_context_ref == (
        "attempt-result-review:pb-attempt-0c:reference"
    )
    assert execution_runbook.runbook_scope_posture == (
        "execution_plan_only_no_dispatch_by_pb_trial_0a"
    )
    assert sandbox_readiness_review.readiness_posture == (
        "ready_for_later_local_trial_execution_review"
    )
    assert trial_guardrail.retry_authority_posture == ("no_retry_authority_granted_by_pb_trial_0a")


def test_pb_trial_0a_rejects_missing_attempt_closeout_in_bundle() -> None:
    (
        attempt_request,
        worker_input_packet,
        dispatch_preflight,
        attempt_guardrail,
        prior_attempt_result_review,
        attempt_family_closeout,
    ) = _load_attempt_rows()
    trial_docket = ProgrambenchLocalReconstructionTrialDocket.model_validate(
        _load_trial_a_fixture("programbench_local_trial_v254_reject_missing_attempt_closeout.json")
    )
    (
        _trial_docket,
        execution_runbook,
        sandbox_readiness_review,
        trial_guardrail,
    ) = _load_trial_rows()

    with pytest.raises(ValueError, match="attempt family closeout"):
        validate_pb_trial_0a_trial_bundle(
            attempt_request=attempt_request,
            worker_input_packet=worker_input_packet,
            dispatch_preflight=dispatch_preflight,
            attempt_guardrail=attempt_guardrail,
            prior_attempt_result_review=prior_attempt_result_review,
            attempt_family_closeout=attempt_family_closeout,
            trial_docket=trial_docket,
            execution_runbook=execution_runbook,
            sandbox_readiness_review=sandbox_readiness_review,
            trial_guardrail=trial_guardrail,
        )


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_local_trial_v254_reject_multiple_attempt_requests.json",
            ProgrambenchLocalReconstructionTrialDocket,
        ),
        (
            "programbench_local_trial_v254_reject_hidden_test_ref_in_docket.json",
            ProgrambenchLocalReconstructionTrialDocket,
        ),
        (
            "programbench_local_trial_v254_reject_runbook_dispatch_authority.json",
            ProgrambenchLocalTrialExecutionRunbook,
        ),
        (
            "programbench_local_trial_v254_reject_prior_result_review_as_trial_outcome.json",
            ProgrambenchLocalReconstructionTrialDocket,
        ),
        (
            "programbench_local_trial_v254_reject_ready_with_non_closed_tool_manifest.json",
            ProgrambenchLocalTrialSandboxReadinessReview,
        ),
        (
            "programbench_local_trial_v254_reject_readiness_claims_execution_authority.json",
            ProgrambenchLocalTrialSandboxReadinessReview,
        ),
        (
            "programbench_local_trial_v254_reject_retry_authority.json",
            ProgrambenchLocalTrialNonAuthorityGuardrail,
        ),
    ],
)
def test_pb_trial_0a_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_trial_a_fixture(fixture_name))


def test_pb_trial_0a_bundle_rejects_prior_attempt_review_as_trial_outcome_context() -> None:
    (
        attempt_request,
        worker_input_packet,
        dispatch_preflight,
        attempt_guardrail,
        prior_attempt_result_review,
        attempt_family_closeout,
    ) = _load_attempt_rows()
    (
        trial_docket,
        execution_runbook,
        sandbox_readiness_review,
        trial_guardrail,
    ) = _load_trial_rows()
    drifted_result_review = prior_attempt_result_review.model_copy(
        update={"attempt_request_ref": "attempt-request:pb-attempt-0a:other"}
    )

    with pytest.raises(ValueError, match="prior attempt result review"):
        validate_pb_trial_0a_trial_bundle(
            attempt_request=attempt_request,
            worker_input_packet=worker_input_packet,
            dispatch_preflight=dispatch_preflight,
            attempt_guardrail=attempt_guardrail,
            prior_attempt_result_review=drifted_result_review,
            attempt_family_closeout=attempt_family_closeout,
            trial_docket=trial_docket,
            execution_runbook=execution_runbook,
            sandbox_readiness_review=sandbox_readiness_review,
            trial_guardrail=trial_guardrail,
        )


def test_pb_trial_0a_bundle_rejects_contamination_blocked_attempt_context() -> None:
    (
        attempt_request,
        worker_input_packet,
        dispatch_preflight,
        attempt_guardrail,
        prior_attempt_result_review,
        attempt_family_closeout,
    ) = _load_attempt_rows()
    (
        trial_docket,
        execution_runbook,
        sandbox_readiness_review,
        trial_guardrail,
    ) = _load_trial_rows()
    contamination_blocked_result = prior_attempt_result_review.model_copy(
        update={
            "local_attempt_posture": "attempt_blocked_by_contamination",
            "carried_blocker_refs": ["contamination:pb-attempt-0c:hidden-evidence"],
        }
    )

    with pytest.raises(ValueError, match="remand or inconclusive"):
        validate_pb_trial_0a_trial_bundle(
            attempt_request=attempt_request,
            worker_input_packet=worker_input_packet,
            dispatch_preflight=dispatch_preflight,
            attempt_guardrail=attempt_guardrail,
            prior_attempt_result_review=contamination_blocked_result,
            attempt_family_closeout=attempt_family_closeout,
            trial_docket=trial_docket,
            execution_runbook=execution_runbook,
            sandbox_readiness_review=sandbox_readiness_review,
            trial_guardrail=trial_guardrail,
        )


def test_pb_trial_0a_schema_exports_mirror_root_spec_files() -> None:
    export_schema_main()

    for expected_schema, authoritative_path, mirror_path in _schema_pairs():
        authoritative = json.loads(authoritative_path.read_text(encoding="utf-8"))
        mirror = json.loads(mirror_path.read_text(encoding="utf-8"))

        assert authoritative["properties"]["schema"]["const"] == expected_schema
        assert authoritative == mirror

        serialized = json.dumps(authoritative, sort_keys=True)
        assert _repo_root().as_posix() not in serialized
        assert not _WINDOWS_ABSOLUTE_PATH_RE.search(serialized)
