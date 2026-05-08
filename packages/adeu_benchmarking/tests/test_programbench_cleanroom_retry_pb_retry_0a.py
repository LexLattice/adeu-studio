from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_benchmarking import (
    PROGRAMBENCH_LOCAL_RETRY_ELIGIBILITY_REVIEW_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_LINEAGE_REGISTRY_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_NON_AUTHORITY_GUARDRAIL_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_REQUEST_SCHEMA,
    PROGRAMBENCH_LOCAL_RETRY_SCOPE_CONTRACT_SCHEMA,
    PROGRAMBENCH_TRIAL_REMAND_SOURCE_INDEX_SCHEMA,
    ProgrambenchLocalRetryEligibilityReview,
    ProgrambenchLocalRetryLineageRegistry,
    ProgrambenchLocalRetryNonAuthorityGuardrail,
    ProgrambenchLocalRetryRequest,
    ProgrambenchLocalRetryScopeContract,
    ProgrambenchLocalTrialFamilyCloseoutAlignment,
    ProgrambenchLocalTrialObservationSummary,
    ProgrambenchLocalTrialOutcomeAudit,
    ProgrambenchLocalTrialRemandDecision,
    ProgrambenchTrialRemandSourceIndex,
    validate_pb_retry_0a_retry_bundle,
)
from adeu_benchmarking.export_schema import main as export_schema_main
from adeu_ir.repo import repo_root
from jsonschema import Draft202012Validator
from pydantic import BaseModel, ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _fixture_root_trial_c() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus256"


def _fixture_root_retry_a() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "benchmarking" / "vnext_plus257"


def _load_fixture(root: Path, name: str) -> dict[str, Any]:
    payload = json.loads((root / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _load_trial_c_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_trial_c(), name)


def _load_retry_a_fixture(name: str) -> dict[str, Any]:
    return _load_fixture(_fixture_root_retry_a(), name)


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
            PROGRAMBENCH_LOCAL_RETRY_REQUEST_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_retry_request.v1.json",
            root / "spec" / "programbench_local_retry_request.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_LINEAGE_REGISTRY_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_retry_lineage_registry.v1.json",
            root / "spec" / "programbench_local_retry_lineage_registry.schema.json",
        ),
        (
            PROGRAMBENCH_TRIAL_REMAND_SOURCE_INDEX_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_trial_remand_source_index.v1.json",
            root / "spec" / "programbench_trial_remand_source_index.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_ELIGIBILITY_REVIEW_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_retry_eligibility_review.v1.json",
            root / "spec" / "programbench_local_retry_eligibility_review.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_SCOPE_CONTRACT_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_retry_scope_contract.v1.json",
            root / "spec" / "programbench_local_retry_scope_contract.schema.json",
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            root
            / "packages"
            / "adeu_benchmarking"
            / "schema"
            / "programbench_local_retry_non_authority_guardrail.v1.json",
            root / "spec" / "programbench_local_retry_non_authority_guardrail.schema.json",
        ),
    ]


def _load_remanded_trial_rows() -> tuple[
    ProgrambenchLocalTrialOutcomeAudit,
    ProgrambenchLocalTrialObservationSummary,
    ProgrambenchLocalTrialRemandDecision,
    ProgrambenchLocalTrialFamilyCloseoutAlignment,
]:
    outcome_payload = _load_trial_c_fixture(
        "programbench_local_trial_outcome_audit_v256_reference.json"
    )
    outcome_payload["local_outcome_posture"] = "trial_remand_recommended"
    outcome_payload["carried_blocker_refs"] = ["remand-row:pb-trial-0c:runbook-gap"]
    outcome = ProgrambenchLocalTrialOutcomeAudit.model_validate(outcome_payload)

    observation_payload = _load_trial_c_fixture(
        "programbench_local_trial_observation_summary_v256_reference.json"
    )
    observation_payload["observed_result_posture"] = "trial_remand_recommended"
    observation = ProgrambenchLocalTrialObservationSummary.model_validate(observation_payload)

    remand_payload = _load_trial_c_fixture(
        "programbench_local_trial_remand_decision_v256_reference.json"
    )
    remand_payload["remand_decision_rows"] = [
        {
            "evidence_refs": ["trial-runbook:pb-trial-0a:reference"],
            "limitation_note": "Local runbook satisfaction gap remains open.",
            "remand_decision_row_ref": "remand-row:pb-trial-0c:runbook-gap",
            "remand_posture": "local_pressure_only_no_retry_authority",
            "remand_source_kind": "runbook_satisfaction_gap",
        }
    ]
    remand_payload["remand_source_kinds"] = ["runbook_satisfaction_gap"]
    remand = ProgrambenchLocalTrialRemandDecision.model_validate(remand_payload)

    closeout = ProgrambenchLocalTrialFamilyCloseoutAlignment.model_validate(
        _load_trial_c_fixture("programbench_local_trial_family_closeout_alignment_v256_reference.json")
    )
    return outcome, observation, remand, closeout


def _load_accepted_trial_rows() -> tuple[
    ProgrambenchLocalTrialOutcomeAudit,
    ProgrambenchLocalTrialObservationSummary,
    ProgrambenchLocalTrialRemandDecision,
    ProgrambenchLocalTrialFamilyCloseoutAlignment,
]:
    return (
        ProgrambenchLocalTrialOutcomeAudit.model_validate(
            _load_trial_c_fixture("programbench_local_trial_outcome_audit_v256_reference.json")
        ),
        ProgrambenchLocalTrialObservationSummary.model_validate(
            _load_trial_c_fixture("programbench_local_trial_observation_summary_v256_reference.json")
        ),
        ProgrambenchLocalTrialRemandDecision.model_validate(
            _load_trial_c_fixture("programbench_local_trial_remand_decision_v256_reference.json")
        ),
        ProgrambenchLocalTrialFamilyCloseoutAlignment.model_validate(
            _load_trial_c_fixture("programbench_local_trial_family_closeout_alignment_v256_reference.json")
        ),
    )


def _load_retry_rows() -> tuple[
    ProgrambenchLocalRetryRequest,
    ProgrambenchLocalRetryLineageRegistry,
    ProgrambenchTrialRemandSourceIndex,
    ProgrambenchLocalRetryEligibilityReview,
    ProgrambenchLocalRetryScopeContract,
    ProgrambenchLocalRetryNonAuthorityGuardrail,
]:
    return (
        ProgrambenchLocalRetryRequest.model_validate(
            _load_retry_a_fixture("programbench_local_retry_request_v257_reference.json")
        ),
        ProgrambenchLocalRetryLineageRegistry.model_validate(
            _load_retry_a_fixture("programbench_local_retry_lineage_registry_v257_reference.json")
        ),
        ProgrambenchTrialRemandSourceIndex.model_validate(
            _load_retry_a_fixture("programbench_trial_remand_source_index_v257_reference.json")
        ),
        ProgrambenchLocalRetryEligibilityReview.model_validate(
            _load_retry_a_fixture("programbench_local_retry_eligibility_review_v257_reference.json")
        ),
        ProgrambenchLocalRetryScopeContract.model_validate(
            _load_retry_a_fixture("programbench_local_retry_scope_contract_v257_reference.json")
        ),
        ProgrambenchLocalRetryNonAuthorityGuardrail.model_validate(
            _load_retry_a_fixture("programbench_local_retry_non_authority_guardrail_v257_reference.json")
        ),
    )


@pytest.mark.parametrize(
    ("schema_name", "schema_filename", "fixture_name", "model"),
    [
        (
            PROGRAMBENCH_LOCAL_RETRY_REQUEST_SCHEMA,
            "programbench_local_retry_request.v1.json",
            "programbench_local_retry_request_v257_reference.json",
            ProgrambenchLocalRetryRequest,
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_LINEAGE_REGISTRY_SCHEMA,
            "programbench_local_retry_lineage_registry.v1.json",
            "programbench_local_retry_lineage_registry_v257_reference.json",
            ProgrambenchLocalRetryLineageRegistry,
        ),
        (
            PROGRAMBENCH_TRIAL_REMAND_SOURCE_INDEX_SCHEMA,
            "programbench_trial_remand_source_index.v1.json",
            "programbench_trial_remand_source_index_v257_reference.json",
            ProgrambenchTrialRemandSourceIndex,
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_ELIGIBILITY_REVIEW_SCHEMA,
            "programbench_local_retry_eligibility_review.v1.json",
            "programbench_local_retry_eligibility_review_v257_reference.json",
            ProgrambenchLocalRetryEligibilityReview,
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_SCOPE_CONTRACT_SCHEMA,
            "programbench_local_retry_scope_contract.v1.json",
            "programbench_local_retry_scope_contract_v257_reference.json",
            ProgrambenchLocalRetryScopeContract,
        ),
        (
            PROGRAMBENCH_LOCAL_RETRY_NON_AUTHORITY_GUARDRAIL_SCHEMA,
            "programbench_local_retry_non_authority_guardrail.v1.json",
            "programbench_local_retry_non_authority_guardrail_v257_reference.json",
            ProgrambenchLocalRetryNonAuthorityGuardrail,
        ),
    ],
)
def test_pb_retry_0a_reference_fixtures_validate_against_schema(
    schema_name: str,
    schema_filename: str,
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    payload = _load_retry_a_fixture(fixture_name)
    assert payload["schema"] == schema_name
    _schema_validator(schema_filename).validate(payload)
    model.model_validate(payload)


def test_pb_retry_0a_reference_bundle_preserves_non_dispatch_boundary() -> None:
    outcome, observation, remand, closeout = _load_remanded_trial_rows()
    request, registry, source_index, eligibility, scope, guardrail = _load_retry_rows()

    validate_pb_retry_0a_retry_bundle(
        trial_outcome_audit=outcome,
        trial_observation_summary=observation,
        trial_remand_decision=remand,
        trial_family_closeout=closeout,
        retry_request=request,
        retry_lineage_registry=registry,
        remand_source_index=source_index,
        retry_eligibility_review=eligibility,
        retry_scope_contract=scope,
        retry_guardrail=guardrail,
    )

    assert request.retry_dispatch_authority_posture == (
        "no_retry_dispatch_authority_granted_by_pb_retry_0a"
    )
    assert registry.eligible_retry_request_refs == [request.retry_request_ref]
    assert eligibility.eligibility_posture == "eligible_for_later_local_retry_dispatch_review"
    assert scope.retry_depth_limit == 1
    assert guardrail.second_retry_posture == "no_second_retry_authority_granted_by_pb_retry_0a"


def test_pb_retry_0a_bundle_rejects_locally_accepted_trial() -> None:
    outcome, observation, remand, closeout = _load_accepted_trial_rows()
    request, registry, source_index, eligibility, scope, guardrail = _load_retry_rows()

    with pytest.raises(ValueError, match="locally accepted"):
        validate_pb_retry_0a_retry_bundle(
            trial_outcome_audit=outcome,
            trial_observation_summary=observation,
            trial_remand_decision=remand,
            trial_family_closeout=closeout,
            retry_request=request,
            retry_lineage_registry=registry,
            remand_source_index=source_index,
            retry_eligibility_review=eligibility,
            retry_scope_contract=scope,
            retry_guardrail=guardrail,
        )


def test_pb_retry_0a_bundle_rejects_existing_prior_retry() -> None:
    outcome, observation, remand, closeout = _load_remanded_trial_rows()
    request, registry, source_index, eligibility, scope, guardrail = _load_retry_rows()
    registry = registry.model_copy(update={"existing_retry_request_refs": ["retry-request:old"]})

    with pytest.raises(ValueError, match="prior retry request"):
        validate_pb_retry_0a_retry_bundle(
            trial_outcome_audit=outcome,
            trial_observation_summary=observation,
            trial_remand_decision=remand,
            trial_family_closeout=closeout,
            retry_request=request,
            retry_lineage_registry=registry,
            remand_source_index=source_index,
            retry_eligibility_review=eligibility,
            retry_scope_contract=scope,
            retry_guardrail=guardrail,
        )


@pytest.mark.parametrize(
    ("fixture_name", "model"),
    [
        (
            "programbench_local_retry_v257_reject_duplicate_single_retry.json",
            ProgrambenchLocalRetryLineageRegistry,
        ),
        (
            "programbench_local_retry_v257_reject_hidden_source_ref.json",
            ProgrambenchTrialRemandSourceIndex,
        ),
        (
            "programbench_local_retry_v257_reject_hidden_content_summary.json",
            ProgrambenchTrialRemandSourceIndex,
        ),
        (
            "programbench_local_retry_v257_reject_scope_widens_tools.json",
            ProgrambenchLocalRetryScopeContract,
        ),
        (
            "programbench_local_retry_v257_reject_guardrail_dispatch_authority.json",
            ProgrambenchLocalRetryNonAuthorityGuardrail,
        ),
    ],
)
def test_pb_retry_0a_reject_fixtures_fail_closed(
    fixture_name: str,
    model: type[BaseModel],
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_retry_a_fixture(fixture_name))


def test_pb_retry_0a_schema_exports_are_current() -> None:
    export_schema_main()
    for schema_name, authoritative, mirror in _schema_pairs():
        authoritative_payload = json.loads(authoritative.read_text(encoding="utf-8"))
        mirror_payload = json.loads(mirror.read_text(encoding="utf-8"))
        assert authoritative_payload == mirror_payload
        assert authoritative_payload["properties"]["schema"]["const"] == schema_name
