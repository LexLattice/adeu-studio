from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

import pytest
from adeu_reasoning_assessment import (
    ReasoningTemplateProbe,
    StructuralFailureTaxonomy,
    StructuralReasoningTrace,
    canonical_json,
    compute_structural_break_ref,
    compute_trace_id,
    normalize_trace_to_taxonomy,
)
from pydantic import ValidationError

V44A_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v44a"
V44B_FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v44b"


def _load_json(root: Path, name: str) -> object:
    return json.loads((root / name).read_text(encoding="utf-8"))


def test_reference_taxonomy_fixtures_validate() -> None:
    for fixture_name in (
        "reference_structural_failure_taxonomy_clean.json",
        "reference_structural_failure_taxonomy_blocked.json",
        "reference_structural_failure_taxonomy_plan_spine_drift.json",
        "reference_structural_failure_taxonomy_active_step_decomposition_failure.json",
        "reference_structural_failure_taxonomy_reintegration_failure.json",
        "reference_structural_failure_taxonomy_invalid_early_closure.json",
    ):
        StructuralFailureTaxonomy.model_validate(_load_json(V44B_FIXTURE_ROOT, fixture_name))


def test_normalize_trace_to_taxonomy_matches_reference_fixtures() -> None:
    hier_probe = ReasoningTemplateProbe.model_validate(
        _load_json(V44A_FIXTURE_ROOT, "reference_reasoning_template_probe_hierarchical.json")
    )
    flat_probe = ReasoningTemplateProbe.model_validate(
        _load_json(V44A_FIXTURE_ROOT, "reference_reasoning_template_probe_flat.json")
    )

    cases = [
        (
            hier_probe,
            V44A_FIXTURE_ROOT,
            "reference_structural_reasoning_trace_clean.json",
            "reference_structural_failure_taxonomy_clean.json",
        ),
        (
            flat_probe,
            V44A_FIXTURE_ROOT,
            "reference_structural_reasoning_trace_blocked.json",
            "reference_structural_failure_taxonomy_blocked.json",
        ),
        (
            hier_probe,
            V44B_FIXTURE_ROOT,
            "reference_structural_reasoning_trace_plan_spine_drift.json",
            "reference_structural_failure_taxonomy_plan_spine_drift.json",
        ),
        (
            hier_probe,
            V44B_FIXTURE_ROOT,
            "reference_structural_reasoning_trace_active_step_decomposition_failure.json",
            "reference_structural_failure_taxonomy_active_step_decomposition_failure.json",
        ),
        (
            hier_probe,
            V44B_FIXTURE_ROOT,
            "reference_structural_reasoning_trace_reintegration_failure.json",
            "reference_structural_failure_taxonomy_reintegration_failure.json",
        ),
        (
            flat_probe,
            V44B_FIXTURE_ROOT,
            "reference_structural_reasoning_trace_invalid_early_closure.json",
            "reference_structural_failure_taxonomy_invalid_early_closure.json",
        ),
    ]

    for probe, trace_root, trace_name, taxonomy_name in cases:
        trace = StructuralReasoningTrace.model_validate(_load_json(trace_root, trace_name))
        expected = StructuralFailureTaxonomy.model_validate(
            _load_json(V44B_FIXTURE_ROOT, taxonomy_name)
        )

        observed = normalize_trace_to_taxonomy(probe=probe, trace=trace)
        observed_payload = observed.model_dump(mode="json", by_alias=True, exclude_none=True)
        expected_payload = expected.model_dump(mode="json", by_alias=True, exclude_none=True)
        assert canonical_json(observed_payload) == canonical_json(expected_payload)


def test_event_order_first_occurrence_controls_failure_family_order() -> None:
    hier_probe = ReasoningTemplateProbe.model_validate(
        _load_json(V44A_FIXTURE_ROOT, "reference_reasoning_template_probe_hierarchical.json")
    )
    base_payload = _load_json(V44A_FIXTURE_ROOT, "reference_structural_reasoning_trace_clean.json")
    assert isinstance(base_payload, dict)

    plan_spine_break = {
        "step_ref": "decompose_active_step",
        "lane_ref": "E",
        "break_tags": ["plan_spine_drift"],
        "supporting_event_indexes": [8],
        "detail": "The parent plan step drifts before reintegration completes.",
    }
    reintegration_break = {
        "step_ref": "reintegrate_findings",
        "lane_ref": "D",
        "break_tags": ["reintegration_failure"],
        "supporting_event_indexes": [10],
        "detail": "The later reintegration step fails after the earlier plan-spine drift.",
    }

    payload = deepcopy(base_payload)
    payload["terminal_trace_status"] = "completed_with_structural_break"
    payload["structural_breaks"] = [
        {
            "break_ref": compute_structural_break_ref(plan_spine_break),
            **plan_spine_break,
        },
        {
            "break_ref": compute_structural_break_ref(reintegration_break),
            **reintegration_break,
        },
    ]
    trace_basis = {
        "schema": payload["schema"],
        "probe_ref": payload["probe_ref"],
        "subject_label": payload["subject_label"],
        "trace_events": [
            {
                "event_index": item["event_index"],
                "event_kind": item["event_kind"],
                "step_ref": item["step_ref"],
                "lane_ref": item.get("lane_ref"),
                "target_step_ref": item.get("target_step_ref"),
                "break_tags": item.get("break_tags", []),
            }
            for item in payload["trace_events"]
        ],
        "terminal_trace_status": payload["terminal_trace_status"],
        "structural_breaks": [plan_spine_break, reintegration_break],
        "open_questions": payload["open_questions"],
    }
    payload["trace_id"] = compute_trace_id(trace_basis)
    trace = StructuralReasoningTrace.model_validate(payload)

    taxonomy = normalize_trace_to_taxonomy(probe=hier_probe, trace=trace)
    assert taxonomy.failure_families == ["plan_spine_drift", "reintegration_failure"]
    assert taxonomy.primary_failure_family == "plan_spine_drift"
    assert taxonomy.supporting_event_indexes == [8, 10]


def test_unsupported_break_tag_fails_closed() -> None:
    hier_probe = ReasoningTemplateProbe.model_validate(
        _load_json(V44A_FIXTURE_ROOT, "reference_reasoning_template_probe_hierarchical.json")
    )
    trace = StructuralReasoningTrace.model_validate(
        _load_json(
            V44B_FIXTURE_ROOT,
            "reject_structural_reasoning_trace_unsupported_break_tag.json",
        )
    )

    with pytest.raises(ValueError, match="unsupported structural break tag"):
        normalize_trace_to_taxonomy(probe=hier_probe, trace=trace)


def test_blocked_taxonomy_with_failure_family_fails_closed() -> None:
    with pytest.raises(ValidationError):
        StructuralFailureTaxonomy.model_validate(
            _load_json(
                V44B_FIXTURE_ROOT,
                "reject_structural_failure_taxonomy_blocked_with_failure_family.json",
            )
        )


def test_mapping_matrix_covers_hierarchy_aware_failure_families() -> None:
    payload = _load_json(V44B_FIXTURE_ROOT, "reference_v44b_taxonomy_mapping_matrix.json")
    assert isinstance(payload, dict)

    rows = payload["fixtures"]
    assert isinstance(rows, list)
    seen_families: set[str] = set()
    for row in rows:
        fixture_name = row["trace_fixture_name"]
        assert (V44B_FIXTURE_ROOT / fixture_name).is_file()
        expected = row["expected_failure_families"]
        assert isinstance(expected, list)
        seen_families.update(expected)
        primary = row["primary_failure_family"]
        assert primary in expected

    assert {
        "plan_spine_drift",
        "active_step_decomposition_failure",
        "reintegration_failure",
    } <= seen_families
