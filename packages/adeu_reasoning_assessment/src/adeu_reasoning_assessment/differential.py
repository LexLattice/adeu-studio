from __future__ import annotations

from typing import Final

from .models import (
    CONDITION_ROLE_VOCABULARY,
    ConditionRole,
    ReasoningTemplateProbe,
    StructuralFailureTaxonomy,
    StructuralReasoningDifferential,
    StructuralReasoningTrace,
    SupportingTraceEventRef,
    compute_differential_id,
    validate_trace_against_probe,
)

REQUIRED_STARTER_ROLES: Final[tuple[ConditionRole, ConditionRole]] = (
    "supplied_knowledge",
    "withheld_knowledge",
)


def diagnose_condition_pair_differential(
    *,
    condition_probes: dict[ConditionRole, ReasoningTemplateProbe],
    condition_traces: dict[ConditionRole, StructuralReasoningTrace],
    condition_taxonomies: dict[ConditionRole, StructuralFailureTaxonomy],
) -> StructuralReasoningDifferential:
    if set(condition_probes) != set(condition_traces) or set(condition_probes) != set(
        condition_taxonomies
    ):
        raise ValueError(
            "condition roles must match across condition_probes, condition_traces, and "
            "condition_taxonomies"
        )

    missing_roles = [
        role for role in REQUIRED_STARTER_ROLES if role not in condition_probes
    ]
    if missing_roles:
        raise ValueError("missing required starter condition role")

    ordered_roles = [
        role for role in CONDITION_ROLE_VOCABULARY if role in condition_probes
    ]
    paired_suite_key: str | None = None
    variant_keys: set[str] = set()
    lineage_basis: dict[str, object] | None = None

    for role in ordered_roles:
        probe = condition_probes[role]
        trace = condition_traces[role]
        taxonomy = condition_taxonomies[role]

        validate_trace_against_probe(probe=probe, trace=trace)
        if taxonomy.probe_ref != probe.probe_id:
            raise ValueError("taxonomy.probe_ref must match probe.probe_id")
        if taxonomy.trace_ref != trace.trace_id:
            raise ValueError("taxonomy.trace_ref must match trace.trace_id")

        compatibility = probe.paired_condition_compatibility
        if compatibility.mode != "paired_reference":
            raise ValueError("paired probes must declare paired_reference compatibility")

        assert compatibility.paired_suite_key is not None
        assert compatibility.condition_variant_key is not None

        if paired_suite_key is None:
            paired_suite_key = compatibility.paired_suite_key
        elif compatibility.paired_suite_key != paired_suite_key:
            raise ValueError(
                "paired probes must share one paired_suite_key across admitted conditions"
            )

        if compatibility.condition_variant_key in variant_keys:
            raise ValueError(
                "paired probes must carry unique condition_variant_key values"
            )
        variant_keys.add(compatibility.condition_variant_key)

        current_basis = _probe_template_lineage_basis(probe)
        if lineage_basis is None:
            lineage_basis = current_basis
        elif current_basis != lineage_basis:
            raise ValueError(
                "paired probes must share one released probe-template lineage"
            )

    assert paired_suite_key is not None
    probe_template_ref = f"reasoning_probe_template:{paired_suite_key}"
    differential_status = "paired_conditions_complete"
    differential_judgment = _determine_differential_judgment(
        supplied=condition_taxonomies["supplied_knowledge"],
        withheld=condition_taxonomies["withheld_knowledge"],
    )

    supporting_roles = _supporting_roles_for_judgment(
        judgment=differential_judgment,
        ordered_roles=ordered_roles,
        condition_taxonomies=condition_taxonomies,
    )
    supporting_failure_families = _ordered_supporting_failure_families(
        ordered_roles=ordered_roles,
        supporting_roles=supporting_roles,
        condition_taxonomies=condition_taxonomies,
    )
    supporting_trace_event_refs = _ordered_supporting_trace_event_refs(
        ordered_roles=ordered_roles,
        supporting_roles=supporting_roles,
        condition_traces=condition_traces,
        condition_taxonomies=condition_taxonomies,
    )
    open_questions = _ordered_open_questions(
        ordered_roles=ordered_roles,
        condition_taxonomies=condition_taxonomies,
    )

    basis = {
        "schema": "adeu_structural_reasoning_differential@1",
        "probe_template_ref": probe_template_ref,
        "condition_trace_refs": {
            role: condition_traces[role].trace_id for role in ordered_roles
        },
        "condition_taxonomy_refs": {
            role: condition_taxonomies[role].taxonomy_id for role in ordered_roles
        },
        "condition_roles_present": ordered_roles,
        "differential_status": differential_status,
        "differential_judgment": differential_judgment,
        "supporting_failure_families": supporting_failure_families,
        "supporting_trace_event_refs": [
            ref.model_dump(mode="json") for ref in supporting_trace_event_refs
        ],
        "open_questions": open_questions,
    }
    return StructuralReasoningDifferential.model_validate(
        {
            **basis,
            "differential_id": compute_differential_id(basis),
        }
    )


def _probe_template_lineage_basis(probe: ReasoningTemplateProbe) -> dict[str, object]:
    compatibility = probe.paired_condition_compatibility
    assert compatibility.paired_suite_key is not None
    return {
        "paired_suite_key": compatibility.paired_suite_key,
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


def _determine_differential_judgment(
    *,
    supplied: StructuralFailureTaxonomy,
    withheld: StructuralFailureTaxonomy,
) -> str:
    if (
        supplied.taxonomy_status == "completed_clean_no_failure"
        and withheld.taxonomy_status == "blocked_lawful_insufficiency"
    ):
        return "knowledge_deficit_supported"

    if supplied.taxonomy_status == "normalized_structural_failure":
        return "procedural_discipline_deficit_supported"

    if (
        supplied.taxonomy_status == "blocked_lawful_insufficiency"
        and withheld.taxonomy_status == "blocked_lawful_insufficiency"
    ):
        return "paired_condition_insufficient"

    return "mixed_or_ambiguous"


def _supporting_roles_for_judgment(
    *,
    judgment: str,
    ordered_roles: list[ConditionRole],
    condition_taxonomies: dict[ConditionRole, StructuralFailureTaxonomy],
) -> set[ConditionRole]:
    if judgment in ("knowledge_deficit_supported", "paired_condition_insufficient"):
        return set()
    return {
        role
        for role in ordered_roles
        if condition_taxonomies[role].taxonomy_status == "normalized_structural_failure"
    }


def _ordered_supporting_failure_families(
    *,
    ordered_roles: list[ConditionRole],
    supporting_roles: set[ConditionRole],
    condition_taxonomies: dict[ConditionRole, StructuralFailureTaxonomy],
) -> list[str]:
    ordered: list[str] = []
    for role in ordered_roles:
        if role not in supporting_roles:
            continue
        for family in condition_taxonomies[role].failure_families:
            if family not in ordered:
                ordered.append(family)
    return ordered


def _ordered_supporting_trace_event_refs(
    *,
    ordered_roles: list[ConditionRole],
    supporting_roles: set[ConditionRole],
    condition_traces: dict[ConditionRole, StructuralReasoningTrace],
    condition_taxonomies: dict[ConditionRole, StructuralFailureTaxonomy],
) -> list[SupportingTraceEventRef]:
    ordered: list[SupportingTraceEventRef] = []
    seen: set[tuple[ConditionRole, str, int]] = set()
    for role in ordered_roles:
        if role not in supporting_roles:
            continue
        trace_ref = condition_traces[role].trace_id
        for event_index in condition_taxonomies[role].supporting_event_indexes:
            key = (role, trace_ref, event_index)
            if key in seen:
                continue
            seen.add(key)
            ordered.append(
                SupportingTraceEventRef(
                    condition_role=role,
                    trace_ref=trace_ref,
                    event_index=event_index,
                )
            )
    return ordered


def _ordered_open_questions(
    *,
    ordered_roles: list[ConditionRole],
    condition_taxonomies: dict[ConditionRole, StructuralFailureTaxonomy],
) -> list[str]:
    ordered: list[str] = []
    for role in ordered_roles:
        for question in condition_taxonomies[role].open_questions:
            if question not in ordered:
                ordered.append(question)
    return ordered


__all__ = ["REQUIRED_STARTER_ROLES", "diagnose_condition_pair_differential"]
