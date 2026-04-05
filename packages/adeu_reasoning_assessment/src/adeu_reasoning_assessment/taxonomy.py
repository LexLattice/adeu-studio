from __future__ import annotations

from typing import Final

from .models import (
    FailureFamily,
    ReasoningTemplateProbe,
    StructuralFailureTaxonomy,
    StructuralReasoningTrace,
    compute_taxonomy_id,
    validate_trace_against_probe,
)

BREAK_TAG_TO_FAILURE_FAMILY: Final[dict[str, FailureFamily]] = {
    "lane_collapse": "lane_collapse",
    "branch_collapse": "branch_collapse",
    "plan_spine_drift": "plan_spine_drift",
    "active_step_decomposition_failure": "active_step_decomposition_failure",
    "reintegration_failure": "reintegration_failure",
    "non_local_repair_drift": "non_local_repair_drift",
}


def normalize_trace_to_taxonomy(
    *,
    probe: ReasoningTemplateProbe,
    trace: StructuralReasoningTrace,
) -> StructuralFailureTaxonomy:
    validate_trace_against_probe(probe=probe, trace=trace)

    if trace.terminal_trace_status == "completed_clean":
        return _build_taxonomy(
            probe_ref=probe.probe_id,
            trace_ref=trace.trace_id,
            taxonomy_status="completed_clean_no_failure",
            terminal_trace_status=trace.terminal_trace_status,
            failure_families=[],
            primary_failure_family=None,
            supporting_break_refs=[],
            supporting_event_indexes=[],
            open_questions=[],
        )

    if trace.terminal_trace_status == "blocked":
        return _build_taxonomy(
            probe_ref=probe.probe_id,
            trace_ref=trace.trace_id,
            taxonomy_status="blocked_lawful_insufficiency",
            terminal_trace_status=trace.terminal_trace_status,
            failure_families=[],
            primary_failure_family=None,
            supporting_break_refs=[],
            supporting_event_indexes=[],
            open_questions=trace.open_questions,
        )

    if trace.terminal_trace_status == "invalid_early_closure":
        supporting_indexes = [
            event.event_index
            for event in trace.trace_events
            if event.event_kind == "invalid_early_closure"
        ]
        return _build_taxonomy(
            probe_ref=probe.probe_id,
            trace_ref=trace.trace_id,
            taxonomy_status="normalized_structural_failure",
            terminal_trace_status=trace.terminal_trace_status,
            failure_families=["invalid_early_closure"],
            primary_failure_family="invalid_early_closure",
            supporting_break_refs=[],
            supporting_event_indexes=supporting_indexes,
            open_questions=trace.open_questions,
        )

    encountered: list[tuple[int, FailureFamily, str]] = []
    for break_record in trace.structural_breaks:
        first_event_index = break_record.supporting_event_indexes[0]
        for break_tag in break_record.break_tags:
            family = BREAK_TAG_TO_FAILURE_FAMILY.get(break_tag)
            if family is None:
                raise ValueError(f"unsupported structural break tag: {break_tag}")
            encountered.append((first_event_index, family, break_record.break_ref))

    if not encountered:
        raise ValueError(
            "completed_with_structural_break trace must map at least one failure family"
        )

    failure_families: list[FailureFamily] = []
    supporting_break_refs: list[str] = []
    for _event_index, family, break_ref in sorted(encountered, key=lambda item: (item[0], item[1])):
        if family not in failure_families:
            failure_families.append(family)
        if break_ref not in supporting_break_refs:
            supporting_break_refs.append(break_ref)

    supporting_event_indexes = sorted(
        {
            event_index
            for break_record in trace.structural_breaks
            for event_index in break_record.supporting_event_indexes
        }
    )

    return _build_taxonomy(
        probe_ref=probe.probe_id,
        trace_ref=trace.trace_id,
        taxonomy_status="normalized_structural_failure",
        terminal_trace_status=trace.terminal_trace_status,
        failure_families=failure_families,
        primary_failure_family=failure_families[0],
        supporting_break_refs=supporting_break_refs,
        supporting_event_indexes=supporting_event_indexes,
        open_questions=trace.open_questions,
    )


def _build_taxonomy(
    *,
    probe_ref: str,
    trace_ref: str,
    taxonomy_status: str,
    terminal_trace_status: str,
    failure_families: list[str],
    primary_failure_family: str | None,
    supporting_break_refs: list[str],
    supporting_event_indexes: list[int],
    open_questions: list[str],
) -> StructuralFailureTaxonomy:
    basis = {
        "schema": "adeu_structural_failure_taxonomy@1",
        "probe_ref": probe_ref,
        "trace_ref": trace_ref,
        "taxonomy_status": taxonomy_status,
        "terminal_trace_status": terminal_trace_status,
        "failure_families": failure_families,
        "primary_failure_family": primary_failure_family,
        "supporting_break_refs": supporting_break_refs,
        "supporting_event_indexes": supporting_event_indexes,
        "open_questions": open_questions,
    }
    return StructuralFailureTaxonomy.model_validate(
        {
            **basis,
            "taxonomy_id": compute_taxonomy_id(basis),
        }
    )


__all__ = [
    "BREAK_TAG_TO_FAILURE_FAMILY",
    "normalize_trace_to_taxonomy",
]
