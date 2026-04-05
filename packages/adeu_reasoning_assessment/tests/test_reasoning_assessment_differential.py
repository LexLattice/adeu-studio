from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_reasoning_assessment import (
    ReasoningTemplateProbe,
    StructuralFailureTaxonomy,
    StructuralReasoningDifferential,
    StructuralReasoningTrace,
    canonical_json,
    diagnose_condition_pair_differential,
)

V44C_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v44c"


def _load_json(name: str) -> object:
    return json.loads((V44C_FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _load_bundle(
    name: str,
) -> tuple[
    dict[str, ReasoningTemplateProbe],
    dict[str, StructuralReasoningTrace],
    dict[str, StructuralFailureTaxonomy],
]:
    payload = _load_json(name)
    assert isinstance(payload, dict)
    return (
        {
            role: ReasoningTemplateProbe.model_validate(value)
            for role, value in payload["condition_probes"].items()
        },
        {
            role: StructuralReasoningTrace.model_validate(value)
            for role, value in payload["condition_traces"].items()
        },
        {
            role: StructuralFailureTaxonomy.model_validate(value)
            for role, value in payload["condition_taxonomies"].items()
        },
    )


def test_reference_differential_fixtures_validate() -> None:
    for fixture_name in (
        "reference_structural_reasoning_differential_knowledge_deficit.json",
        "reference_structural_reasoning_differential_procedural_discipline_deficit.json",
        "reference_structural_reasoning_differential_mixed_or_ambiguous.json",
        "reference_structural_reasoning_differential_paired_condition_insufficient.json",
    ):
        StructuralReasoningDifferential.model_validate(_load_json(fixture_name))


def test_diagnose_condition_pair_differential_matches_reference_fixtures() -> None:
    cases = [
        (
            "reference_differential_input_knowledge_deficit.json",
            "reference_structural_reasoning_differential_knowledge_deficit.json",
        ),
        (
            "reference_differential_input_procedural_discipline_deficit.json",
            "reference_structural_reasoning_differential_procedural_discipline_deficit.json",
        ),
        (
            "reference_differential_input_mixed_or_ambiguous.json",
            "reference_structural_reasoning_differential_mixed_or_ambiguous.json",
        ),
        (
            "reference_differential_input_paired_condition_insufficient.json",
            "reference_structural_reasoning_differential_paired_condition_insufficient.json",
        ),
    ]

    for input_name, expected_name in cases:
        condition_probes, condition_traces, condition_taxonomies = _load_bundle(input_name)
        observed = diagnose_condition_pair_differential(
            condition_probes=condition_probes,
            condition_traces=condition_traces,
            condition_taxonomies=condition_taxonomies,
        )
        expected = StructuralReasoningDifferential.model_validate(_load_json(expected_name))

        observed_payload = observed.model_dump(mode="json", by_alias=True, exclude_none=True)
        expected_payload = expected.model_dump(mode="json", by_alias=True, exclude_none=True)
        assert canonical_json(observed_payload) == canonical_json(expected_payload)


def test_missing_required_starter_role_fails_closed() -> None:
    condition_probes, condition_traces, condition_taxonomies = _load_bundle(
        "reject_differential_input_missing_required_role.json"
    )

    with pytest.raises(ValueError, match="missing required starter condition role"):
        diagnose_condition_pair_differential(
            condition_probes=condition_probes,
            condition_traces=condition_traces,
            condition_taxonomies=condition_taxonomies,
        )


def test_incompatible_pair_compatibility_fails_closed() -> None:
    condition_probes, condition_traces, condition_taxonomies = _load_bundle(
        "reject_differential_input_incompatible_pair_compatibility.json"
    )

    with pytest.raises(ValueError, match="paired_suite_key"):
        diagnose_condition_pair_differential(
            condition_probes=condition_probes,
            condition_traces=condition_traces,
            condition_taxonomies=condition_taxonomies,
        )


def test_mapping_matrix_covers_all_starter_judgments() -> None:
    payload = _load_json("reference_v44c_differential_mapping_matrix.json")
    assert isinstance(payload, dict)
    rows = payload["fixtures"]
    assert isinstance(rows, list)

    seen_judgments: set[str] = set()
    for row in rows:
        input_fixture_name = row["input_fixture_name"]
        differential_fixture_name = row["differential_fixture_name"]
        assert (V44C_FIXTURE_ROOT / input_fixture_name).is_file()
        assert (V44C_FIXTURE_ROOT / differential_fixture_name).is_file()
        seen_judgments.add(row["expected_differential_judgment"])
        assert row["expected_differential_status"] == "paired_conditions_complete"

    assert seen_judgments == {
        "knowledge_deficit_supported",
        "procedural_discipline_deficit_supported",
        "mixed_or_ambiguous",
        "paired_condition_insufficient",
    }
