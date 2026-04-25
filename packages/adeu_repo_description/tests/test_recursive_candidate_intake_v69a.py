from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from adeu_ir.repo import repo_root
from adeu_repo_description import (
    REPO_CANDIDATE_NON_ADOPTION_GUARDRAIL_SCHEMA,
    REPO_CANDIDATE_SOURCE_REGISTER_SCHEMA,
    REPO_RECURSIVE_CANDIDATE_INTAKE_RECORD_SCHEMA,
    RepoCandidateNonAdoptionGuardrail,
    RepoCandidateSourceRegister,
    RepoRecursiveCandidateIntakeRecord,
    compute_repo_recursive_candidate_intake_id,
    materialize_repo_recursive_candidate_intake_payload,
)
from jsonschema import Draft202012Validator
from pydantic import ValidationError


def _repo_root() -> Path:
    return repo_root(anchor=Path(__file__))


def _v191_root() -> Path:
    return _repo_root() / "apps" / "api" / "fixtures" / "repo_description" / "vnext_plus191"


def _load_v191(name: str) -> dict[str, Any]:
    return json.loads((_v191_root() / name).read_text(encoding="utf-8"))


def _schema_validator(schema_filename: str) -> Draft202012Validator:
    schema = json.loads(
        (
            _repo_root() / "packages" / "adeu_repo_description" / "schema" / schema_filename
        ).read_text(encoding="utf-8")
    )
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _source_register_payload(reference: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": REPO_CANDIDATE_SOURCE_REGISTER_SCHEMA,
        "source_register_id": "source-register:v191-reference",
        "intake_id": reference["intake_id"],
        "snapshot_id": reference["snapshot_id"],
        "source_rows": reference["source_rows"],
    }


def _guardrail_payload(reference: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": REPO_CANDIDATE_NON_ADOPTION_GUARDRAIL_SCHEMA,
        "guardrail_register_id": "guardrail-register:v191-reference",
        "intake_id": reference["intake_id"],
        "snapshot_id": reference["snapshot_id"],
        "role_guardrail_rows": reference["role_guardrail_rows"],
    }


def test_v191_reference_candidate_intake_fixture_validates() -> None:
    payload = _load_v191("repo_recursive_candidate_intake_v191_reference.json")
    validated = RepoRecursiveCandidateIntakeRecord.model_validate(payload)

    assert validated.schema == REPO_RECURSIVE_CANDIDATE_INTAKE_RECORD_SCHEMA
    assert len(validated.candidate_rows) == 6
    assert {row.candidate_ref for row in validated.candidate_rows} == {
        "candidate:evidence:V68_substrate_for_V69",
        "candidate:internal:odeu_conceptual_diff_report@1",
        "candidate:internal:odeu_conceptual_diff_schema_support",
        "candidate:internal:self_evidencing_workflow_type_emergence",
        "candidate:internal:typed_adjudication_product_wedge",
        "candidate:planning:V69_candidate_intake_family",
    }
    product = next(
        row
        for row in validated.candidate_rows
        if row.candidate_ref == "candidate:internal:typed_adjudication_product_wedge"
    )
    assert product.primary_odeu_lane == "utility"
    assert product.odeu_lanes == ["deontic", "epistemic", "utility"]


def test_v191_candidate_intake_id_is_deterministic() -> None:
    payload = _load_v191("repo_recursive_candidate_intake_v191_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("intake_id")

    assert compute_repo_recursive_candidate_intake_id(without_id) == payload["intake_id"]


def test_v191_materialize_candidate_intake_payload_matches_reference() -> None:
    payload = _load_v191("repo_recursive_candidate_intake_v191_reference.json")
    without_id = deepcopy(payload)
    without_id.pop("intake_id")

    assert materialize_repo_recursive_candidate_intake_payload(without_id) == payload


def test_v191_exported_schema_accepts_reference_fixture() -> None:
    _schema_validator("repo_recursive_candidate_intake_record.v1.json").validate(
        _load_v191("repo_recursive_candidate_intake_v191_reference.json")
    )


def test_v191_source_and_guardrail_register_surfaces_validate() -> None:
    payload = _load_v191("repo_recursive_candidate_intake_v191_reference.json")

    source_register = RepoCandidateSourceRegister.model_validate(_source_register_payload(payload))
    guardrail_register = RepoCandidateNonAdoptionGuardrail.model_validate(
        _guardrail_payload(payload)
    )

    assert source_register.schema == REPO_CANDIDATE_SOURCE_REGISTER_SCHEMA
    assert guardrail_register.schema == REPO_CANDIDATE_NON_ADOPTION_GUARDRAIL_SCHEMA
    assert len(source_register.source_rows) == len(payload["source_rows"])
    assert len(guardrail_register.role_guardrail_rows) == len(payload["role_guardrail_rows"])


def test_v191_exported_source_and_guardrail_schemas_accept_reference_surfaces() -> None:
    payload = _load_v191("repo_recursive_candidate_intake_v191_reference.json")

    _schema_validator("repo_candidate_source_register.v1.json").validate(
        _source_register_payload(payload)
    )
    _schema_validator("repo_candidate_non_adoption_guardrail.v1.json").validate(
        _guardrail_payload(payload)
    )


def test_v191_eventual_family_hint_is_not_downstream_selection() -> None:
    payload = _load_v191("repo_recursive_candidate_intake_v191_reference.json")
    product_guardrail = next(
        row
        for row in payload["role_guardrail_rows"]
        if row["candidate_ref"] == "candidate:internal:typed_adjudication_product_wedge"
    )

    assert product_guardrail["required_next_review_surface"] == "future_family_review"
    assert product_guardrail["eventual_family_hint"] == "v74_operator_projection_review"
    assert "product_authorization" in product_guardrail["forbidden_roles"]


@pytest.mark.parametrize(
    ("fixture_name", "match"),
    [
        (
            "repo_recursive_candidate_intake_v191_reject_missing_source_binding.json",
            "at least 1 item",
        ),
        (
            "repo_recursive_candidate_intake_v191_reject_unknown_source_ref.json",
            "candidate source_refs",
        ),
        (
            "repo_recursive_candidate_intake_v191_reject_support_doc_as_released_schema.json",
            "released schema authority",
        ),
        (
            "repo_recursive_candidate_intake_v191_reject_selector_as_lock_authority.json",
            "planning selector",
        ),
        (
            "repo_recursive_candidate_intake_v191_reject_review_feedback_as_ratification.json",
            "adoption, selection, or release authority",
        ),
        (
            "repo_recursive_candidate_intake_v191_reject_operator_turn_invents_unsourced_candidate.json",
            "operator_turn candidates require",
        ),
        (
            "repo_recursive_candidate_intake_v191_reject_duplicate_without_equivalence.json",
            "duplicate candidates",
        ),
        (
            "repo_recursive_candidate_intake_v191_reject_missing_non_adoption_guardrail.json",
            "non_adoption_guardrail must be non-empty",
        ),
        (
            "repo_recursive_candidate_intake_v191_reject_embedded_v70_evidence_classification.json",
            "evidence classification",
        ),
        (
            "repo_recursive_candidate_intake_v191_reject_candidate_authorizes_v72_release.json",
            "adoption, selection, or release authority",
        ),
        (
            "repo_recursive_candidate_intake_v191_reject_product_projection_selected_by_intake.json",
            "adoption, selection, or release authority",
        ),
        (
            "repo_recursive_candidate_intake_v191_reject_model_output_without_self_validation_forbidden.json",
            "model_output candidate",
        ),
        (
            "repo_recursive_candidate_intake_v191_reject_mixed_lane_without_multi_lane_profile.json",
            "primary_odeu_lane=mixed",
        ),
        (
            "repo_recursive_candidate_intake_v191_reject_future_hint_without_review_intermediary.json",
            "eventual family hints",
        ),
    ],
)
def test_v191_rejects_invalid_candidate_intake_fixtures(fixture_name: str, match: str) -> None:
    with pytest.raises(ValidationError, match=match):
        RepoRecursiveCandidateIntakeRecord.model_validate(_load_v191(fixture_name))
