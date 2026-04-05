from __future__ import annotations

import json
from pathlib import Path

import pytest
from adeu_reasoning_assessment import (
    ReasoningProbeSuite,
    ReasoningTemplateProbe,
    RecursiveReasoningAssessment,
    StructuralFailureTaxonomy,
    StructuralReasoningTrace,
    assess_recursive_reasoning,
    canonical_json,
)

V44D_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v44d"
V44E_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v44e"


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def _load_suite() -> ReasoningProbeSuite:
    return ReasoningProbeSuite.model_validate(
        _load_json(V44D_FIXTURE_ROOT, "reference_reasoning_probe_suite.json")
    )


def _load_recursive_bundle(
    name: str,
) -> tuple[
    ReasoningTemplateProbe,
    StructuralReasoningTrace,
    StructuralFailureTaxonomy,
    ReasoningTemplateProbe,
    StructuralReasoningTrace,
    StructuralFailureTaxonomy,
]:
    payload = _load_json(V44E_FIXTURE_ROOT, name)
    assert isinstance(payload, dict)
    return (
        ReasoningTemplateProbe.model_validate(payload["baseline_probe"]),
        StructuralReasoningTrace.model_validate(payload["baseline_trace"]),
        StructuralFailureTaxonomy.model_validate(payload["baseline_taxonomy"]),
        ReasoningTemplateProbe.model_validate(payload["recursive_probe"]),
        StructuralReasoningTrace.model_validate(payload["recursive_trace"]),
        StructuralFailureTaxonomy.model_validate(payload["recursive_taxonomy"]),
    )


def test_reference_recursive_assessment_fixtures_validate() -> None:
    for fixture_name in (
        "reference_recursive_reasoning_assessment_lawful.json",
        "reference_recursive_reasoning_assessment_structurally_degraded.json",
        "reference_recursive_reasoning_assessment_invalid_early_closure.json",
        "reference_recursive_reasoning_assessment_insufficient.json",
    ):
        RecursiveReasoningAssessment.model_validate(_load_json(V44E_FIXTURE_ROOT, fixture_name))


def test_assess_recursive_reasoning_matches_reference_fixtures() -> None:
    suite = _load_suite()
    cases = [
        (
            "reference_recursive_input_lawful.json",
            "reference_recursive_reasoning_assessment_lawful.json",
        ),
        (
            "reference_recursive_input_structurally_degraded.json",
            "reference_recursive_reasoning_assessment_structurally_degraded.json",
        ),
        (
            "reference_recursive_input_invalid_early_closure.json",
            "reference_recursive_reasoning_assessment_invalid_early_closure.json",
        ),
        (
            "reference_recursive_input_insufficient.json",
            "reference_recursive_reasoning_assessment_insufficient.json",
        ),
    ]

    for input_name, expected_name in cases:
        (
            baseline_probe,
            baseline_trace,
            baseline_taxonomy,
            recursive_probe,
            recursive_trace,
            recursive_taxonomy,
        ) = _load_recursive_bundle(input_name)
        observed = assess_recursive_reasoning(
            suite=suite,
            baseline_probe=baseline_probe,
            baseline_trace=baseline_trace,
            baseline_taxonomy=baseline_taxonomy,
            recursive_probe=recursive_probe,
            recursive_trace=recursive_trace,
            recursive_taxonomy=recursive_taxonomy,
        )
        expected = RecursiveReasoningAssessment.model_validate(
            _load_json(V44E_FIXTURE_ROOT, expected_name)
        )

        observed_payload = observed.model_dump(mode="json", by_alias=True, exclude_none=True)
        expected_payload = expected.model_dump(mode="json", by_alias=True, exclude_none=True)
        assert canonical_json(observed_payload) == canonical_json(expected_payload)


def test_missing_return_to_parent_fails_closed() -> None:
    suite = _load_suite()
    (
        baseline_probe,
        baseline_trace,
        baseline_taxonomy,
        recursive_probe,
        recursive_trace,
        recursive_taxonomy,
    ) = _load_recursive_bundle("reject_recursive_input_missing_return_to_parent.json")

    with pytest.raises(ValueError, match="return_to_parent"):
        assess_recursive_reasoning(
            suite=suite,
            baseline_probe=baseline_probe,
            baseline_trace=baseline_trace,
            baseline_taxonomy=baseline_taxonomy,
            recursive_probe=recursive_probe,
            recursive_trace=recursive_trace,
            recursive_taxonomy=recursive_taxonomy,
        )


def test_non_local_rewrite_fails_closed() -> None:
    suite = _load_suite()
    (
        baseline_probe,
        baseline_trace,
        baseline_taxonomy,
        recursive_probe,
        recursive_trace,
        recursive_taxonomy,
    ) = _load_recursive_bundle("reject_recursive_input_non_local_rewrite.json")

    with pytest.raises(ValueError, match="non_local_rewrite"):
        assess_recursive_reasoning(
            suite=suite,
            baseline_probe=baseline_probe,
            baseline_trace=baseline_trace,
            baseline_taxonomy=baseline_taxonomy,
            recursive_probe=recursive_probe,
            recursive_trace=recursive_trace,
            recursive_taxonomy=recursive_taxonomy,
        )


def test_mapping_matrix_covers_all_recursive_statuses_and_judgments() -> None:
    payload = _load_json(V44E_FIXTURE_ROOT, "reference_v44e_recursive_mapping_matrix.json")
    assert isinstance(payload, dict)
    assert payload["hierarchy_posture"] == "single_level_parent_child"

    cases = payload["cases"]
    assert isinstance(cases, list)

    seen_statuses: set[str] = set()
    seen_judgments: set[str] = set()
    for row in cases:
        input_fixture = row["input_fixture"]
        output_fixture = row["expected_output_fixture"]
        assert (V44E_FIXTURE_ROOT / input_fixture).is_file()
        assert (V44E_FIXTURE_ROOT / output_fixture).is_file()
        seen_statuses.add(row["recursive_status"])
        seen_judgments.add(row["closure_judgment"])

    assert seen_statuses == {
        "recursive_closure_stable",
        "recursive_closure_degraded",
        "recursive_early_closure_invalid",
    }
    assert seen_judgments == {
        "recursive_extension_lawful",
        "recursive_extension_structurally_degraded",
        "recursive_extension_invalid_early_closure",
        "recursive_extension_insufficient",
    }
