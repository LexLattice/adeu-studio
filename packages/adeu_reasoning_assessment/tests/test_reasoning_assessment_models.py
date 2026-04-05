from __future__ import annotations

import json
import re
from pathlib import Path

import pytest
from adeu_ir.repo import repo_root
from adeu_reasoning_assessment import (
    ADEU_REASONING_PROBE_SUITE_SCHEMA,
    ADEU_REASONING_TEMPLATE_PROBE_SCHEMA,
    ADEU_RECURSIVE_REASONING_ASSESSMENT_SCHEMA,
    ADEU_STRUCTURAL_FAILURE_TAXONOMY_SCHEMA,
    ADEU_STRUCTURAL_REASONING_DIFFERENTIAL_SCHEMA,
    ADEU_STRUCTURAL_REASONING_TRACE_SCHEMA,
    ReasoningTemplateProbe,
    StructuralReasoningTrace,
    compute_structural_break_ref,
    compute_trace_id,
    validate_trace_against_probe,
)
from adeu_reasoning_assessment.export_schema import main as export_schema_main
from pydantic import ValidationError

FIXTURE_ROOT = Path(__file__).parent / "fixtures" / "v44a"
_WINDOWS_ABSOLUTE_PATH_RE = re.compile(r"[A-Za-z]:\\")
EXPECTED_FAILURE_SURFACES = {
    "lane_collapse",
    "branch_collapse",
    "plan_spine_drift",
    "active_step_decomposition_failure",
    "reintegration_failure",
    "invalid_early_closure",
    "non_local_repair_drift",
}


def _load_json(name: str) -> object:
    return json.loads((FIXTURE_ROOT / name).read_text(encoding="utf-8"))


def _schema_pairs() -> list[tuple[str, Path, Path]]:
    root = repo_root(anchor=Path(__file__))
    return [
        (
            ADEU_REASONING_PROBE_SUITE_SCHEMA,
            root
            / "packages"
            / "adeu_reasoning_assessment"
            / "schema"
            / "adeu_reasoning_probe_suite.v1.json",
            root / "spec" / "adeu_reasoning_probe_suite.schema.json",
        ),
        (
            ADEU_RECURSIVE_REASONING_ASSESSMENT_SCHEMA,
            root
            / "packages"
            / "adeu_reasoning_assessment"
            / "schema"
            / "adeu_recursive_reasoning_assessment.v1.json",
            root / "spec" / "adeu_recursive_reasoning_assessment.schema.json",
        ),
        (
            ADEU_REASONING_TEMPLATE_PROBE_SCHEMA,
            root
            / "packages"
            / "adeu_reasoning_assessment"
            / "schema"
            / "adeu_reasoning_template_probe.v1.json",
            root / "spec" / "adeu_reasoning_template_probe.schema.json",
        ),
        (
            ADEU_STRUCTURAL_REASONING_TRACE_SCHEMA,
            root
            / "packages"
            / "adeu_reasoning_assessment"
            / "schema"
            / "adeu_structural_reasoning_trace.v1.json",
            root / "spec" / "adeu_structural_reasoning_trace.schema.json",
        ),
        (
            ADEU_STRUCTURAL_FAILURE_TAXONOMY_SCHEMA,
            root
            / "packages"
            / "adeu_reasoning_assessment"
            / "schema"
            / "adeu_structural_failure_taxonomy.v1.json",
            root / "spec" / "adeu_structural_failure_taxonomy.schema.json",
        ),
        (
            ADEU_STRUCTURAL_REASONING_DIFFERENTIAL_SCHEMA,
            root
            / "packages"
            / "adeu_reasoning_assessment"
            / "schema"
            / "adeu_structural_reasoning_differential.v1.json",
            root / "spec" / "adeu_structural_reasoning_differential.schema.json",
        ),
    ]


def test_reference_probes_and_traces_validate() -> None:
    flat_probe = ReasoningTemplateProbe.model_validate(
        _load_json("reference_reasoning_template_probe_flat.json")
    )
    hierarchical_probe = ReasoningTemplateProbe.model_validate(
        _load_json("reference_reasoning_template_probe_hierarchical.json")
    )
    clean_trace = StructuralReasoningTrace.model_validate(
        _load_json("reference_structural_reasoning_trace_clean.json")
    )
    blocked_trace = StructuralReasoningTrace.model_validate(
        _load_json("reference_structural_reasoning_trace_blocked.json")
    )

    assert flat_probe.hierarchy_posture == "flat"
    assert hierarchical_probe.hierarchy_posture == "single_level_parent_child"
    assert blocked_trace.terminal_trace_status == "blocked"

    validate_trace_against_probe(probe=hierarchical_probe, trace=clean_trace)
    validate_trace_against_probe(probe=flat_probe, trace=blocked_trace)


def test_probe_canonicalizes_template_step_order_before_id_check() -> None:
    payload = _load_json("reference_reasoning_template_probe_flat.json")
    assert isinstance(payload, dict)
    reversed_payload = dict(payload)
    reversed_payload["template_steps"] = list(reversed(payload["template_steps"]))

    validated = ReasoningTemplateProbe.model_validate(reversed_payload)

    assert [step.step_ref for step in validated.template_steps] == [
        "observe_frame",
        "assemble_claim",
        "report_result",
    ]
    assert validated.probe_id == payload["probe_id"]


def test_trace_id_changes_when_structural_break_is_added() -> None:
    payload = _load_json("reference_structural_reasoning_trace_clean.json")
    assert isinstance(payload, dict)
    event = {
        "event_index": len(payload["trace_events"]),
        "event_kind": "step_complete",
        "step_ref": "reintegrate_findings",
        "lane_ref": "D",
        "break_tags": [],
    }
    break_record = {
        "step_ref": "reintegrate_findings",
        "lane_ref": "D",
        "break_tags": ["rejoin_failed"],
        "supporting_event_indexes": [event["event_index"]],
        "detail": "The trace completed the final step only after an explicit reintegration break.",
    }

    mutated = dict(payload)
    mutated["trace_events"] = [*payload["trace_events"], event]
    mutated["terminal_trace_status"] = "completed_with_structural_break"
    mutated["structural_breaks"] = [
        {
            **break_record,
            "break_ref": "PLACEHOLDER",
        }
    ]
    mutated["trace_id"] = "PLACEHOLDER"
    mutated["structural_breaks"][0]["break_ref"] = compute_structural_break_ref(break_record)
    mutated["trace_id"] = compute_trace_id(
        {
            "schema": mutated["schema"],
            "probe_ref": mutated["probe_ref"],
            "subject_label": mutated["subject_label"],
            "trace_events": [
                {
                    "event_index": item["event_index"],
                    "event_kind": item["event_kind"],
                    "step_ref": item["step_ref"],
                    "lane_ref": item.get("lane_ref"),
                    "target_step_ref": item.get("target_step_ref"),
                    "break_tags": item.get("break_tags", []),
                }
                for item in mutated["trace_events"]
            ],
            "terminal_trace_status": mutated["terminal_trace_status"],
            "structural_breaks": [break_record],
            "open_questions": mutated["open_questions"],
        }
    )

    validated = StructuralReasoningTrace.model_validate(mutated)
    reference = StructuralReasoningTrace.model_validate(payload)
    assert validated.trace_id != reference.trace_id


@pytest.mark.parametrize(
    "fixture_name, model",
    [
        (
            "reject_structural_reasoning_trace_invalid_early_closure_posture.json",
            StructuralReasoningTrace,
        ),
    ],
)
def test_reject_fixture_fails_closed_during_model_validation(
    fixture_name: str, model: type[StructuralReasoningTrace]
) -> None:
    with pytest.raises(ValidationError):
        model.model_validate(_load_json(fixture_name))


def test_hierarchical_return_fixture_fails_closed_against_probe() -> None:
    hierarchical_probe = ReasoningTemplateProbe.model_validate(
        _load_json("reference_reasoning_template_probe_hierarchical.json")
    )
    invalid_trace = StructuralReasoningTrace.model_validate(
        _load_json("reject_structural_reasoning_trace_invalid_return_to_parent.json")
    )

    with pytest.raises(ValueError, match="return_to_parent"):
        validate_trace_against_probe(probe=hierarchical_probe, trace=invalid_trace)


def test_completed_trace_missing_trailing_plan_step_fails_closed() -> None:
    hierarchical_probe = ReasoningTemplateProbe.model_validate(
        _load_json("reference_reasoning_template_probe_hierarchical.json")
    )
    payload = _load_json("reference_structural_reasoning_trace_clean.json")
    assert isinstance(payload, dict)

    truncated_events = payload["trace_events"][:-2]
    truncated_payload = {
        **payload,
        "trace_events": truncated_events,
        "trace_id": compute_trace_id(
            {
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
                    for item in truncated_events
                ],
                "terminal_trace_status": payload["terminal_trace_status"],
                "structural_breaks": payload["structural_breaks"],
                "open_questions": payload["open_questions"],
            }
        ),
    }
    truncated_trace = StructuralReasoningTrace.model_validate(truncated_payload)

    with pytest.raises(ValueError, match="full top-level plan spine"):
        validate_trace_against_probe(probe=hierarchical_probe, trace=truncated_trace)


def test_fixture_expectation_matrix_is_compact_and_complete() -> None:
    payload = _load_json("reference_v44a_fixture_expectation_matrix.json")
    assert isinstance(payload, dict)
    rows = payload["fixtures"]
    assert isinstance(rows, list)

    seen_surfaces: set[str] = set()
    for row in rows:
        fixture_name = row["fixture_name"]
        assert (FIXTURE_ROOT / fixture_name).is_file()
        exposed = set(row["expected_failure_surfaces"])
        assert exposed <= EXPECTED_FAILURE_SURFACES
        seen_surfaces.update(exposed)
    assert seen_surfaces == EXPECTED_FAILURE_SURFACES


def test_authoritative_and_mirror_schema_are_byte_identical() -> None:
    for _, authoritative, mirror in _schema_pairs():
        assert authoritative.read_bytes() == mirror.read_bytes()


def test_schema_export_rerun_is_clean_and_deterministic() -> None:
    before = {
        path: path.read_bytes()
        for _schema, authoritative, mirror in _schema_pairs()
        for path in (authoritative, mirror)
    }
    export_schema_main()
    after_first = {path: path.read_bytes() for path in before}
    export_schema_main()
    after_second = {path: path.read_bytes() for path in before}
    assert before == after_first == after_second


def test_exported_schema_has_stable_contract_markers() -> None:
    payloads = {
        schema_label: json.loads(authoritative.read_text(encoding="utf-8"))
        for schema_label, authoritative, _mirror in _schema_pairs()
    }
    assert (
        payloads[ADEU_REASONING_PROBE_SUITE_SCHEMA]["properties"]["schema"]["const"]
        == ADEU_REASONING_PROBE_SUITE_SCHEMA
    )
    assert (
        payloads[ADEU_RECURSIVE_REASONING_ASSESSMENT_SCHEMA]["properties"]["schema"]["const"]
        == ADEU_RECURSIVE_REASONING_ASSESSMENT_SCHEMA
    )
    assert (
        payloads[ADEU_REASONING_TEMPLATE_PROBE_SCHEMA]["properties"]["schema"]["const"]
        == ADEU_REASONING_TEMPLATE_PROBE_SCHEMA
    )
    assert (
        payloads[ADEU_STRUCTURAL_REASONING_TRACE_SCHEMA]["properties"]["schema"]["const"]
        == ADEU_STRUCTURAL_REASONING_TRACE_SCHEMA
    )


def test_exported_schema_has_no_absolute_path_material() -> None:
    root = repo_root(anchor=Path(__file__))
    root_text = root.as_posix()

    def _check_node(node: object) -> None:
        if isinstance(node, dict):
            for value in node.values():
                _check_node(value)
            return
        if isinstance(node, list):
            for item in node:
                _check_node(item)
            return
        if not isinstance(node, str):
            return
        normalized = node.replace("\\", "/")
        assert root_text not in normalized
        assert not normalized.startswith("/home/")
        assert not normalized.startswith("/Users/")
        assert _WINDOWS_ABSOLUTE_PATH_RE.search(node) is None

    for _, authoritative, mirror in _schema_pairs():
        _check_node(json.loads(authoritative.read_text(encoding="utf-8")))
        _check_node(json.loads(mirror.read_text(encoding="utf-8")))
