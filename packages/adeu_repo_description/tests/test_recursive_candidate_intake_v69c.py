from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CANDIDATE_INTAKE_PRE_V70_HANDOFF_SCHEMA,
    REPO_OPERATOR_INGRESS_CANDIDATE_BINDING_SCHEMA,
    REPO_RECURSIVE_WORKFLOW_RESIDUE_INTAKE_REPORT_SCHEMA,
    RepoCandidateIntakePreV70Handoff,
    RepoOperatorIngressCandidateBinding,
    RepoRecursiveWorkflowResidueIntakeReport,
    derive_v69c_repo_candidate_intake_handoff_bundle,
)
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v193_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus193"


def _load_v193(name: str) -> dict[str, Any]:
    return json.loads((_v193_root() / name).read_text(encoding="utf-8"))


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_repo_description" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_v193_reference_operator_ingress_binding_validates() -> None:
    payload = _load_v193("repo_operator_ingress_candidate_binding_v193_reference.json")
    validated = RepoOperatorIngressCandidateBinding.model_validate(payload)

    assert validated.schema == REPO_OPERATOR_INGRESS_CANDIDATE_BINDING_SCHEMA
    assert len(validated.binding_rows) == 1
    row = validated.binding_rows[0]
    assert row.origin_class == "operator_turn"
    assert row.source_presence_posture == "operator_turn_not_committed"
    assert "transcript_truth" in row.forbidden_roles
    assert "dispatch_authority" in row.forbidden_roles


def test_v193_reference_recursive_residue_report_validates() -> None:
    payload = _load_v193("repo_recursive_workflow_residue_intake_report_v193_reference.json")
    validated = RepoRecursiveWorkflowResidueIntakeReport.model_validate(payload)

    assert validated.schema == REPO_RECURSIVE_WORKFLOW_RESIDUE_INTAKE_REPORT_SCHEMA
    assert {row.residue_kind for row in validated.residue_rows} == {
        "model_output_comparison_candidate",
        "operator_cognition_changed_by_artifact",
        "product_projection_candidate",
        "self_evidencing_workflow_type_emergence",
        "support_schema_created_by_prior_reasoning",
        "tool_applicability_pressure",
    }
    assert all(
        "non-self-validation" in row.non_self_validation_guardrail
        for row in validated.residue_rows
    )


def test_v193_reference_pre_v70_handoff_validates() -> None:
    payload = _load_v193("repo_candidate_intake_pre_v70_handoff_v193_reference.json")
    validated = RepoCandidateIntakePreV70Handoff.model_validate(payload)

    assert validated.schema == REPO_CANDIDATE_INTAKE_PRE_V70_HANDOFF_SCHEMA
    assert {row.handoff_target for row in validated.handoff_rows} == {
        "future_family_review",
        "v70_adversarial_review",
        "v70_evidence_classification",
    }
    model_row = next(
        row for row in validated.handoff_rows if row.candidate_origin_class == "model_output"
    )
    assert model_row.adversarial_review_needed is True


def test_v193_exported_schemas_accept_reference_fixtures() -> None:
    _schema_validator("repo_operator_ingress_candidate_binding.v1.json").validate(
        _load_v193("repo_operator_ingress_candidate_binding_v193_reference.json")
    )
    _schema_validator("repo_recursive_workflow_residue_intake_report.v1.json").validate(
        _load_v193("repo_recursive_workflow_residue_intake_report_v193_reference.json")
    )
    _schema_validator("repo_candidate_intake_pre_v70_handoff.v1.json").validate(
        _load_v193("repo_candidate_intake_pre_v70_handoff_v193_reference.json")
    )


def test_v193_derivation_helper_matches_reference_fixtures() -> None:
    binding, residue, handoff = derive_v69c_repo_candidate_intake_handoff_bundle(
        repo_root=_repo_root()
    )

    assert binding.model_dump(mode="json") == _load_v193(
        "repo_operator_ingress_candidate_binding_v193_reference.json"
    )
    assert residue.model_dump(mode="json") == _load_v193(
        "repo_recursive_workflow_residue_intake_report_v193_reference.json"
    )
    assert handoff.model_dump(mode="json") == _load_v193(
        "repo_candidate_intake_pre_v70_handoff_v193_reference.json"
    )


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_candidate_intake_v193_reject_operator_turn_as_authority.json",
            "operator, transcript, and model sources",
        ),
        (
            "repo_candidate_intake_v193_reject_transcript_as_truth.json",
            "operator ingress binding",
        ),
        (
            "repo_candidate_intake_v193_reject_candidate_binding_empty_source_refs.json",
            "at least 1 item",
        ),
        (
            "repo_candidate_intake_v193_reject_source_absence_outside_source_register.json",
            "source register rows",
        ),
        (
            "repo_candidate_intake_v193_reject_operator_binding_runtime_permission.json",
            "operator ingress binding",
        ),
    ],
)
def test_v193_rejects_invalid_operator_binding_fixtures(
    fixture_name: str, match: str
) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoOperatorIngressCandidateBinding.model_validate(_load_v193(fixture_name))


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_candidate_intake_v193_reject_recursive_residue_as_self_validation.json",
            "self-validation",
        ),
        (
            "repo_candidate_intake_v193_reject_missing_non_self_validation_guardrail.json",
            "non-self-validation",
        ),
    ],
)
def test_v193_rejects_invalid_residue_report_fixtures(fixture_name: str, match: str) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoRecursiveWorkflowResidueIntakeReport.model_validate(_load_v193(fixture_name))


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_candidate_intake_v193_reject_handoff_contains_v70_verdict.json",
            "evidence classification",
        ),
        (
            "repo_candidate_intake_v193_reject_handoff_reason_verdict_language.json",
            "evidence verdict language",
        ),
        (
            "repo_candidate_intake_v193_reject_v70_handoff_empty_evidence_needed.json",
            "requires evidence_needed",
        ),
        (
            "repo_candidate_intake_v193_reject_model_output_without_adversarial_review.json",
            "adversarial review",
        ),
        (
            "repo_candidate_intake_v193_reject_direct_later_family_handoff.json",
            "handoff target",
        ),
        (
            "repo_candidate_intake_v193_reject_product_wedge_selects_v74.json",
            "handoff target",
        ),
    ],
)
def test_v193_rejects_invalid_pre_v70_handoff_fixtures(
    fixture_name: str, match: str
) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoCandidateIntakePreV70Handoff.model_validate(_load_v193(fixture_name))
