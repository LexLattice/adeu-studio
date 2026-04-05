from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from .models import (
    ADEU_STRUCTURAL_FAILURE_TAXONOMY_SCHEMA,
    ADEU_STRUCTURAL_REASONING_DIFFERENTIAL_SCHEMA,
    ConsumerCompatibilityRef,
    ReasoningProbeSuite,
    ReasoningProbeSuiteMember,
    ReasoningTemplateProbe,
    RepairLocalityPosture,
    SurfaceVariationKind,
    compute_probe_suite_hash,
    compute_probe_suite_id,
)

PROCEDURE_PRESERVATION_REQUIRED = "procedure_preservation_required"
NON_LOCAL_REPAIR_FORBIDDEN = "no_non_local_repair"
NON_LOCAL_REWRITE_ALLOWED = "non_local_rewrite_allowed"
SURFACE_VARIATION_KIND_PREFIX = "surface_variation_kind:"


@dataclass(frozen=True)
class ProbeSuiteMemberSpec:
    probe: ReasoningTemplateProbe
    consumer_compatibility_refs: tuple[ConsumerCompatibilityRef, ...]
    surface_variation_kind: SurfaceVariationKind | None = None
    repair_locality_posture: RepairLocalityPosture | None = None
    paired_condition_compatible: bool = False


def build_reasoning_probe_suite(
    *,
    suite_label: str,
    member_specs: Sequence[ProbeSuiteMemberSpec],
) -> ReasoningProbeSuite:
    canonical_specs = _canonical_member_specs(member_specs)
    suite_members = [_build_probe_suite_member(spec) for spec in canonical_specs]
    basis = {
        "schema": "adeu_reasoning_probe_suite@1",
        "suite_label": suite_label,
        "suite_members": [
            {
                "probe_ref": member.probe_ref,
                "template_class": member.template_class,
                "surface_variation_kind": member.surface_variation_kind,
                "repair_locality_posture": member.repair_locality_posture,
                "consumer_compatibility_refs": member.consumer_compatibility_refs,
                "paired_condition_compatible": member.paired_condition_compatible,
            }
            for member in suite_members
        ],
        "template_classes_included": _unique_template_classes(canonical_specs),
        "accepted_surface_variation_kinds": _unique_surface_variation_kinds(canonical_specs),
        "repair_locality_posture": "local_only",
    }
    return ReasoningProbeSuite.model_validate(
        {
            **basis,
            "suite_id": compute_probe_suite_id(basis),
            "suite_hash": compute_probe_suite_hash(basis),
        }
    )


def _build_probe_suite_member(spec: ProbeSuiteMemberSpec) -> ReasoningProbeSuiteMember:
    probe = spec.probe
    compatibility_refs = tuple(spec.consumer_compatibility_refs)
    if (
        ADEU_STRUCTURAL_REASONING_DIFFERENTIAL_SCHEMA in compatibility_refs
        and probe.paired_condition_compatibility.mode != "paired_reference"
    ):
        raise ValueError(
            "differential-compatible suite members must consume paired_reference probes"
        )
    if spec.paired_condition_compatible and (
        probe.paired_condition_compatibility.mode != "paired_reference"
    ):
        raise ValueError(
            "paired_condition_compatible suite members must consume paired_reference probes"
        )

    if probe.template_class == "invariance_under_surface_variation":
        _assert_invariance_probe(
            probe,
            surface_variation_kind=spec.surface_variation_kind,
        )
    if probe.template_class == "local_repair_continuation":
        _assert_local_repair_probe(
            probe,
            repair_locality_posture=spec.repair_locality_posture,
        )

    return ReasoningProbeSuiteMember.model_validate(
        {
            "probe_ref": probe.probe_id,
            "template_class": probe.template_class,
            "surface_variation_kind": spec.surface_variation_kind,
            "repair_locality_posture": spec.repair_locality_posture,
            "consumer_compatibility_refs": list(compatibility_refs),
            "paired_condition_compatible": spec.paired_condition_compatible,
        }
    )


def _canonical_member_specs(
    member_specs: Sequence[ProbeSuiteMemberSpec],
) -> list[ProbeSuiteMemberSpec]:
    return sorted(
        member_specs,
        key=lambda spec: (
            _template_class_order(spec.probe.template_class),
            _surface_variation_order(spec.surface_variation_kind),
            spec.probe.probe_id,
        ),
    )


def _unique_template_classes(member_specs: Sequence[ProbeSuiteMemberSpec]) -> list[str]:
    ordered: list[str] = []
    for spec in member_specs:
        if spec.probe.template_class not in ordered:
            ordered.append(spec.probe.template_class)
    return ordered


def _unique_surface_variation_kinds(
    member_specs: Sequence[ProbeSuiteMemberSpec],
) -> list[str]:
    ordered: list[str] = []
    for spec in member_specs:
        if spec.surface_variation_kind is None:
            continue
        if spec.surface_variation_kind not in ordered:
            ordered.append(spec.surface_variation_kind)
    return ordered


def _template_class_order(value: str) -> tuple[int, str]:
    order = {
        "lane_preserving_decomposition": 0,
        "branching_under_uncertainty": 1,
        "local_repair_continuation": 2,
        "invariance_under_surface_variation": 3,
    }
    return (order.get(value, len(order)), value)


def _surface_variation_order(value: SurfaceVariationKind | None) -> tuple[int, int, str]:
    if value is None:
        return (0, -1, "")
    order = {
        "paraphrase_preserving": 0,
        "presentation_shift_preserving": 1,
    }
    return (1, order.get(value, len(order)), value)


def _all_constraints(probe: ReasoningTemplateProbe) -> set[str]:
    return {
        constraint
        for step in probe.template_steps
        for constraint in step.local_constraints
    }


def _active_step_constraints(probe: ReasoningTemplateProbe) -> set[str]:
    for step in probe.template_steps:
        if step.step_ref == probe.active_plan_step_ref:
            return set(step.local_constraints)
    raise ValueError("probe active_plan_step_ref must resolve to one template step")


def _assert_invariance_probe(
    probe: ReasoningTemplateProbe,
    *,
    surface_variation_kind: SurfaceVariationKind | None,
) -> None:
    if surface_variation_kind is None:
        raise ValueError("invariance suite members require surface_variation_kind")

    if surface_variation_kind not in {
        "paraphrase_preserving",
        "presentation_shift_preserving",
    }:
        raise ValueError("unsupported surface_variation_kind for V44-D invariance member")

    constraints = _all_constraints(probe)
    if PROCEDURE_PRESERVATION_REQUIRED not in constraints:
        raise ValueError(
            "invariance suite members require explicit procedure_preservation_required anchors"
        )
    expected_surface_anchor = f"{SURFACE_VARIATION_KIND_PREFIX}{surface_variation_kind}"
    if expected_surface_anchor not in constraints:
        raise ValueError(
            "invariance suite members require explicit surface_variation_kind anchors"
        )


def _assert_local_repair_probe(
    probe: ReasoningTemplateProbe,
    *,
    repair_locality_posture: RepairLocalityPosture | None,
) -> None:
    if repair_locality_posture != "local_only":
        raise ValueError(
            "local_repair_continuation suite members require repair_locality_posture local_only"
        )

    active_constraints = _active_step_constraints(probe)
    if NON_LOCAL_REPAIR_FORBIDDEN not in active_constraints:
        raise ValueError(
            "local_repair_continuation suite members require no_non_local_repair anchors"
        )
    if NON_LOCAL_REWRITE_ALLOWED in _all_constraints(probe):
        raise ValueError(
            "local_repair_continuation suite members may not allow non_local_rewrite"
        )


def supported_consumer_compatibility_refs(*, paired_condition_compatible: bool) -> tuple[
    ConsumerCompatibilityRef, ...
]:
    if paired_condition_compatible:
        return (
            ADEU_STRUCTURAL_FAILURE_TAXONOMY_SCHEMA,
            ADEU_STRUCTURAL_REASONING_DIFFERENTIAL_SCHEMA,
        )
    return (ADEU_STRUCTURAL_FAILURE_TAXONOMY_SCHEMA,)


__all__ = [
    "NON_LOCAL_REPAIR_FORBIDDEN",
    "NON_LOCAL_REWRITE_ALLOWED",
    "PROCEDURE_PRESERVATION_REQUIRED",
    "ProbeSuiteMemberSpec",
    "SURFACE_VARIATION_KIND_PREFIX",
    "build_reasoning_probe_suite",
    "supported_consumer_compatibility_refs",
]
