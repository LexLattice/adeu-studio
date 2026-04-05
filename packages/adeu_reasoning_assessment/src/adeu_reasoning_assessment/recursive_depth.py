from __future__ import annotations

from typing import Final

from .models import (
    ReasoningProbeSuite,
    ReasoningTemplateProbe,
    RecursiveReasoningAssessment,
    RecursiveSupportingTraceEventRef,
    StructuralFailureTaxonomy,
    StructuralReasoningTrace,
    compute_probe_suite_member_ref,
    compute_recursive_assessment_id,
    validate_trace_against_probe,
)
from .probe_library import NON_LOCAL_REWRITE_ALLOWED

REQUIRED_RECURSIVE_DEPTH_MODE: Final[str] = "single_bounded_recursive_reentry"
RECURSIVE_TRACE_ROLES: Final[tuple[str, str]] = ("baseline", "recursive_extension")


def assess_recursive_reasoning(
    *,
    suite: ReasoningProbeSuite,
    baseline_probe: ReasoningTemplateProbe,
    baseline_trace: StructuralReasoningTrace,
    baseline_taxonomy: StructuralFailureTaxonomy,
    recursive_probe: ReasoningTemplateProbe,
    recursive_trace: StructuralReasoningTrace,
    recursive_taxonomy: StructuralFailureTaxonomy,
) -> RecursiveReasoningAssessment:
    validate_trace_against_probe(probe=baseline_probe, trace=baseline_trace)
    validate_trace_against_probe(probe=recursive_probe, trace=recursive_trace)
    _validate_taxonomy_refs(
        probe=baseline_probe,
        trace=baseline_trace,
        taxonomy=baseline_taxonomy,
    )
    _validate_taxonomy_refs(
        probe=recursive_probe,
        trace=recursive_trace,
        taxonomy=recursive_taxonomy,
    )

    suite_member = _select_suite_member(suite=suite, baseline_probe=baseline_probe)
    if _contains_non_local_recursive_rewrite(recursive_probe):
        raise ValueError("recursive probe may not allow non_local_rewrite posture")
    _assert_probe_lineage_compatible(
        baseline_probe=baseline_probe,
        recursive_probe=recursive_probe,
    )

    recursive_activation_index = _recursive_activation_index(
        probe=recursive_probe,
        trace=recursive_trace,
    )
    recursive_return_index = _recursive_return_index(
        probe=recursive_probe,
        trace=recursive_trace,
        recursive_activation_index=recursive_activation_index,
    )

    recursive_status = _determine_recursive_status(
        baseline_taxonomy=baseline_taxonomy,
        recursive_trace=recursive_trace,
        recursive_taxonomy=recursive_taxonomy,
    )
    baseline_admissible = _baseline_is_admissible(
        baseline_trace=baseline_trace,
        baseline_taxonomy=baseline_taxonomy,
    )
    closure_judgment = _determine_closure_judgment(
        recursive_status=recursive_status,
        baseline_admissible=baseline_admissible,
    )
    supporting_failure_families = _supporting_failure_families(
        baseline_taxonomy=baseline_taxonomy,
        recursive_status=recursive_status,
        recursive_taxonomy=recursive_taxonomy,
    )
    supporting_trace_event_refs = _supporting_trace_event_refs(
        recursive_status=recursive_status,
        closure_judgment=closure_judgment,
        recursive_trace=recursive_trace,
        recursive_taxonomy=recursive_taxonomy,
        recursive_activation_index=recursive_activation_index,
        recursive_return_index=recursive_return_index,
    )
    open_questions = sorted(
        {
            *baseline_taxonomy.open_questions,
            *recursive_taxonomy.open_questions,
        }
    )

    suite_member_ref = compute_probe_suite_member_ref(
        suite_id=suite.suite_id,
        probe_ref=suite_member.probe_ref,
    )
    basis = {
        "schema": "adeu_recursive_reasoning_assessment@1",
        "suite_member_ref": suite_member_ref,
        "baseline_probe_ref": baseline_probe.probe_id,
        "baseline_trace_ref": baseline_trace.trace_id,
        "baseline_taxonomy_ref": baseline_taxonomy.taxonomy_id,
        "recursive_probe_ref": recursive_probe.probe_id,
        "recursive_trace_ref": recursive_trace.trace_id,
        "recursive_taxonomy_ref": recursive_taxonomy.taxonomy_id,
        "recursive_depth_mode": REQUIRED_RECURSIVE_DEPTH_MODE,
        "recursive_status": recursive_status,
        "closure_judgment": closure_judgment,
        "supporting_trace_event_refs": [
            ref.model_dump(mode="json") for ref in supporting_trace_event_refs
        ],
        "supporting_failure_families": supporting_failure_families,
        "open_questions": open_questions,
    }
    return RecursiveReasoningAssessment.model_validate(
        {
            **basis,
            "assessment_id": compute_recursive_assessment_id(basis),
        }
    )


def _validate_taxonomy_refs(
    *,
    probe: ReasoningTemplateProbe,
    trace: StructuralReasoningTrace,
    taxonomy: StructuralFailureTaxonomy,
) -> None:
    if taxonomy.probe_ref != probe.probe_id:
        raise ValueError("taxonomy.probe_ref must match probe.probe_id")
    if taxonomy.trace_ref != trace.trace_id:
        raise ValueError("taxonomy.trace_ref must match trace.trace_id")


def _select_suite_member(
    *,
    suite: ReasoningProbeSuite,
    baseline_probe: ReasoningTemplateProbe,
):
    matches = [
        member
        for member in suite.suite_members
        if member.probe_ref == baseline_probe.probe_id
    ]
    if not matches:
        raise ValueError("baseline probe must be present in the released V44-D suite")
    return matches[0]


def _probe_lineage_basis(probe: ReasoningTemplateProbe) -> dict[str, object]:
    return {
        "template_class": probe.template_class,
        "lane_order": probe.lane_order,
        "template_steps": [step.identity_basis() for step in probe.template_steps],
        "acceptance_posture": probe.acceptance_posture.identity_basis(),
        "hierarchy_posture": probe.hierarchy_posture,
        "plan_spine_step_ids": probe.plan_spine_step_ids,
        "active_plan_step_ref": probe.active_plan_step_ref,
        "child_step_refs": probe.child_step_refs,
        "child_order_policy": probe.child_order_policy,
        "return_to_parent_required": probe.return_to_parent_required,
    }


def _assert_probe_lineage_compatible(
    *,
    baseline_probe: ReasoningTemplateProbe,
    recursive_probe: ReasoningTemplateProbe,
) -> None:
    if _probe_lineage_basis(baseline_probe) != _probe_lineage_basis(recursive_probe):
        raise ValueError(
            "baseline and recursive probes must share one released procedural lineage"
        )


def _contains_non_local_recursive_rewrite(probe: ReasoningTemplateProbe) -> bool:
    return any(
        NON_LOCAL_REWRITE_ALLOWED in step.local_constraints for step in probe.template_steps
    )


def _recursive_activation_index(
    *,
    probe: ReasoningTemplateProbe,
    trace: StructuralReasoningTrace,
) -> int:
    activation_indexes = [
        event.event_index
        for event in trace.trace_events
        if event.event_kind == "step_activate"
        and event.step_ref == probe.active_plan_step_ref
    ]
    if len(activation_indexes) != 2:
        raise ValueError(
            "recursive trace must carry exactly one bounded recursive re-entry activation"
        )
    return activation_indexes[1]


def _recursive_return_index(
    *,
    probe: ReasoningTemplateProbe,
    trace: StructuralReasoningTrace,
    recursive_activation_index: int,
) -> int:
    return_indexes = [
        event.event_index
        for event in trace.trace_events
        if event.event_kind == "return_to_parent"
        and event.target_step_ref == probe.active_plan_step_ref
        and event.event_index > recursive_activation_index
    ]
    if not return_indexes:
        raise ValueError("recursive trace missing explicit recursive return_to_parent evidence")
    return return_indexes[-1]


def _baseline_is_admissible(
    *,
    baseline_trace: StructuralReasoningTrace,
    baseline_taxonomy: StructuralFailureTaxonomy,
) -> bool:
    if baseline_trace.terminal_trace_status == "invalid_early_closure":
        return False
    if baseline_taxonomy.taxonomy_status == "blocked_lawful_insufficiency":
        return False
    if baseline_taxonomy.open_questions:
        return False
    return True


def _terminal_status_rank(status: str) -> int:
    order = {
        "completed_clean": 0,
        "completed_with_structural_break": 1,
        "blocked": 2,
        "invalid_early_closure": 3,
    }
    return order.get(status, len(order))


def _determine_recursive_status(
    *,
    baseline_taxonomy: StructuralFailureTaxonomy,
    recursive_trace: StructuralReasoningTrace,
    recursive_taxonomy: StructuralFailureTaxonomy,
) -> str:
    if recursive_trace.terminal_trace_status == "invalid_early_closure":
        return "recursive_early_closure_invalid"
    if recursive_taxonomy.taxonomy_status == "blocked_lawful_insufficiency":
        raise ValueError("recursive extension may not remain blocked in the V44-E starter slice")

    baseline_failure_families = set(baseline_taxonomy.failure_families)
    recursive_failure_families = set(recursive_taxonomy.failure_families)
    if (
        _terminal_status_rank(recursive_trace.terminal_trace_status)
        > _terminal_status_rank(baseline_taxonomy.terminal_trace_status)
    ):
        return "recursive_closure_degraded"
    if recursive_failure_families - baseline_failure_families:
        return "recursive_closure_degraded"
    return "recursive_closure_stable"


def _determine_closure_judgment(
    *,
    recursive_status: str,
    baseline_admissible: bool,
) -> str:
    if recursive_status == "recursive_early_closure_invalid":
        return "recursive_extension_invalid_early_closure"
    if not baseline_admissible:
        return "recursive_extension_insufficient"
    if recursive_status == "recursive_closure_degraded":
        return "recursive_extension_structurally_degraded"
    return "recursive_extension_lawful"


def _supporting_failure_families(
    *,
    baseline_taxonomy: StructuralFailureTaxonomy,
    recursive_status: str,
    recursive_taxonomy: StructuralFailureTaxonomy,
) -> list[str]:
    if recursive_status == "recursive_early_closure_invalid":
        return ["invalid_early_closure"]
    if recursive_status != "recursive_closure_degraded":
        return []

    baseline_failures = set(baseline_taxonomy.failure_families)
    ordered_new = [
        family
        for family in recursive_taxonomy.failure_families
        if family not in baseline_failures
    ]
    return ordered_new or list(recursive_taxonomy.failure_families)


def _supporting_trace_event_refs(
    *,
    recursive_status: str,
    closure_judgment: str,
    recursive_trace: StructuralReasoningTrace,
    recursive_taxonomy: StructuralFailureTaxonomy,
    recursive_activation_index: int,
    recursive_return_index: int,
) -> list[RecursiveSupportingTraceEventRef]:
    if (
        closure_judgment == "recursive_extension_insufficient"
        and recursive_status == "recursive_closure_stable"
    ):
        return []

    indexes: list[int] = [recursive_activation_index, recursive_return_index]
    if recursive_status == "recursive_closure_degraded":
        indexes.extend(recursive_taxonomy.supporting_event_indexes)
    elif recursive_status == "recursive_early_closure_invalid":
        indexes.extend(recursive_taxonomy.supporting_event_indexes)

    ordered_indexes: list[int] = []
    for event_index in sorted(set(indexes)):
        if event_index not in ordered_indexes:
            ordered_indexes.append(event_index)
    return [
        RecursiveSupportingTraceEventRef(
            trace_role="recursive_extension",
            trace_ref=recursive_trace.trace_id,
            event_index=event_index,
        )
        for event_index in ordered_indexes
    ]


__all__ = [
    "RECURSIVE_TRACE_ROLES",
    "REQUIRED_RECURSIVE_DEPTH_MODE",
    "assess_recursive_reasoning",
]
