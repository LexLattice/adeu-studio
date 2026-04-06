from __future__ import annotations

import re
from typing import Iterable

from urm_runtime.hashing import sha256_canonical_json

from .models import (
    DistinctnessPosture,
    EdgeClassCatalog,
    EdgeTaxonomyRevisionJudgment,
    ReusePosture,
    TaxonomyNodeLifecycle,
    TaxonomyRevisionDecision,
    compute_edge_taxonomy_revision_judgment_id,
)
from .taxonomy import build_starter_edge_class_catalog, catalog_nodes_by_ref

_SLUG_TOKEN_RE = re.compile(r"[A-Za-z0-9]+")
_DISTINCTNESS_SCORE = {
    "same": 0,
    "attribute_refinement_only": 1,
    "adjacent_but_representable": 2,
    "distinct": 3,
}


def _edge_ref_parts(edge_class_ref: str) -> list[str]:
    assert edge_class_ref.startswith("edge_class:")
    return edge_class_ref.split(":", 1)[1].split("/")


def _edge_ref_depth(edge_class_ref: str) -> int:
    return len(_edge_ref_parts(edge_class_ref))


def _family_ref(edge_class_ref: str) -> str:
    family = _edge_ref_parts(edge_class_ref)[0]
    return f"edge_class:{family}"


def _parent_ref(edge_class_ref: str) -> str | None:
    parts = _edge_ref_parts(edge_class_ref)
    if len(parts) == 1:
        return None
    return f"edge_class:{'/'.join(parts[:-1])}"


def _common_prefix_ref(edge_class_refs: list[str]) -> str | None:
    if not edge_class_refs:
        return None
    parts_lists = [_edge_ref_parts(edge_ref) for edge_ref in edge_class_refs]
    prefix: list[str] = []
    for index in range(min(len(parts) for parts in parts_lists)):
        candidate = parts_lists[0][index]
        if any(parts[index] != candidate for parts in parts_lists[1:]):
            break
        prefix.append(candidate)
    if not prefix:
        return None
    return f"edge_class:{'/'.join(prefix)}"


def _slugify_label(value: str) -> str:
    tokens = [token.lower() for token in _SLUG_TOKEN_RE.findall(value)]
    normalized = [token for token in tokens if token]
    if not normalized:
        raise ValueError("candidate_label must include at least one alphanumeric token")
    slug = "_".join(normalized)
    if slug[0].isdigit():
        slug = f"edge_{slug}"
    return slug


def _join_edge_ref(parent_edge_class_ref: str, slug: str) -> str:
    return f"{parent_edge_class_ref}/{slug}"


def _maturity_posture(
    *,
    decision: TaxonomyRevisionDecision,
    evidence_count: int,
    reuse_posture: ReusePosture,
) -> TaxonomyNodeLifecycle:
    if decision == "instance_of_existing_class":
        return "stabilized"
    if decision == "split_existing_class":
        return "split"
    if decision == "defer_candidate":
        return "candidate"
    if evidence_count >= 5 and reuse_posture == "recurrent_pattern":
        return "stabilized"
    return "candidate"


def _judgment_posture(
    *,
    decision: TaxonomyRevisionDecision,
    evidence_count: int,
    applicability_pattern_distinctness: DistinctnessPosture,
    probe_pattern_distinctness: DistinctnessPosture,
) -> str:
    if decision == "defer_candidate":
        return "inferred_heuristically"
    if decision == "instance_of_existing_class" and evidence_count >= 3 and {
        applicability_pattern_distinctness,
        probe_pattern_distinctness,
    } <= {"same", "attribute_refinement_only"}:
        return "settled"
    return "adjudicated"


def _choose_specialization_parent(
    *,
    nearest_refs: list[str],
    nodes_by_ref: dict[str, object],
) -> str | None:
    if not nearest_refs:
        return None
    if len(nearest_refs) != 1:
        return None
    nearest_ref = nearest_refs[0]
    node = nodes_by_ref[nearest_ref]
    depth = _edge_ref_depth(nearest_ref)
    if getattr(node, "node_kind") in {"family", "subfamily"} and depth < 3:
        return nearest_ref
    return None


def _decision_from_signals(
    *,
    nearest_refs: list[str],
    applicability_pattern_distinctness: DistinctnessPosture,
    probe_pattern_distinctness: DistinctnessPosture,
    representable_without_information_loss: bool,
    reuse_posture: ReusePosture,
    evidence_count: int,
    nodes_by_ref: dict[str, object],
) -> tuple[TaxonomyRevisionDecision, str | None]:
    max_distinctness = max(
        _DISTINCTNESS_SCORE[applicability_pattern_distinctness],
        _DISTINCTNESS_SCORE[probe_pattern_distinctness],
    )
    if evidence_count <= 1 and reuse_posture == "single_symbol":
        return "defer_candidate", None

    if representable_without_information_loss:
        if max_distinctness <= _DISTINCTNESS_SCORE["attribute_refinement_only"]:
            return "instance_of_existing_class", None
        specialization_parent = _choose_specialization_parent(
            nearest_refs=nearest_refs,
            nodes_by_ref=nodes_by_ref,
        )
        if (
            max_distinctness == _DISTINCTNESS_SCORE["adjacent_but_representable"]
            and reuse_posture != "single_symbol"
            and evidence_count >= 3
            and specialization_parent is not None
        ):
            return "specialize_under_existing_class", specialization_parent
        return "instance_of_existing_class", None

    if reuse_posture == "single_symbol" and evidence_count < 3:
        return "defer_candidate", None

    family_refs = {_family_ref(edge_ref) for edge_ref in nearest_refs}
    if len(family_refs) > 1:
        if max_distinctness == _DISTINCTNESS_SCORE["distinct"] and evidence_count >= 4:
            return "new_top_level_family", None
        return "defer_candidate", None

    common_parent = _common_prefix_ref(nearest_refs)
    if common_parent is not None:
        common_depth = _edge_ref_depth(common_parent)
        min_depth = min(_edge_ref_depth(edge_ref) for edge_ref in nearest_refs)
        if len(nearest_refs) > 1 and common_depth <= min_depth - 2 and evidence_count >= 3:
            return "new_intermediate_node", common_parent

    exact_parent_refs = {_parent_ref(edge_ref) for edge_ref in nearest_refs}
    exact_parent_refs.discard(None)
    if len(exact_parent_refs) == 1:
        exact_parent = next(iter(exact_parent_refs))
        if len(nearest_refs) == 1 and _edge_ref_depth(nearest_refs[0]) == 3 and evidence_count >= 4:
            if max_distinctness == _DISTINCTNESS_SCORE["distinct"]:
                return "split_existing_class", exact_parent
        if evidence_count >= 2:
            return "new_sibling_under_existing_parent", exact_parent

    specialization_parent = _choose_specialization_parent(
        nearest_refs=nearest_refs,
        nodes_by_ref=nodes_by_ref,
    )
    if specialization_parent is not None and evidence_count >= 2:
        return "specialize_under_existing_class", specialization_parent

    if len(family_refs) == 1 and evidence_count >= 4:
        family_ref = next(iter(family_refs))
        return "new_sibling_under_existing_parent", family_ref

    return "defer_candidate", None


def judge_edge_taxonomy_revision(
    *,
    candidate_label: str,
    nearest_existing_edge_class_refs: list[str],
    observed_symbol_ids: list[str],
    applicability_cue_tags: Iterable[str],
    probe_signature_tags: Iterable[str],
    applicability_pattern_distinctness: DistinctnessPosture,
    probe_pattern_distinctness: DistinctnessPosture,
    representable_without_information_loss: bool,
    reuse_posture: ReusePosture,
    evidence_count: int,
    edge_class_catalog: EdgeClassCatalog | None = None,
    candidate_slug: str | None = None,
) -> EdgeTaxonomyRevisionJudgment:
    catalog = edge_class_catalog or build_starter_edge_class_catalog()
    nodes_by_ref = catalog_nodes_by_ref(catalog)
    nearest_refs = sorted(set(nearest_existing_edge_class_refs))
    if not nearest_refs:
        raise ValueError("nearest_existing_edge_class_refs must not be empty")
    missing_refs = [edge_ref for edge_ref in nearest_refs if edge_ref not in nodes_by_ref]
    if missing_refs:
        raise ValueError(f"unknown nearest_existing_edge_class_ref: {missing_refs[0]}")

    decision, proposed_parent_edge_class_ref = _decision_from_signals(
        nearest_refs=nearest_refs,
        applicability_pattern_distinctness=applicability_pattern_distinctness,
        probe_pattern_distinctness=probe_pattern_distinctness,
        representable_without_information_loss=representable_without_information_loss,
        reuse_posture=reuse_posture,
        evidence_count=evidence_count,
        nodes_by_ref=nodes_by_ref,
    )
    slug = candidate_slug or _slugify_label(candidate_label)
    proposed_edge_class_ref: str | None = None
    if decision == "new_top_level_family":
        proposed_edge_class_ref = f"edge_class:{slug}"
    elif decision in {
        "specialize_under_existing_class",
        "new_sibling_under_existing_parent",
        "new_intermediate_node",
    }:
        assert proposed_parent_edge_class_ref is not None
        parent_depth = _edge_ref_depth(proposed_parent_edge_class_ref)
        if parent_depth >= 3:
            raise ValueError(
                f"{decision} cannot propose a child beneath an archetype parent"
            )
        proposed_edge_class_ref = _join_edge_ref(proposed_parent_edge_class_ref, slug)

    proposed_lifecycle_posture = _maturity_posture(
        decision=decision,
        evidence_count=evidence_count,
        reuse_posture=reuse_posture,
    )
    judgment_posture = _judgment_posture(
        decision=decision,
        evidence_count=evidence_count,
        applicability_pattern_distinctness=applicability_pattern_distinctness,
        probe_pattern_distinctness=probe_pattern_distinctness,
    )

    rationale_parts = [
        f"applicability_distinctness={applicability_pattern_distinctness}",
        f"probe_distinctness={probe_pattern_distinctness}",
        f"representable_without_information_loss={str(representable_without_information_loss).lower()}",
        f"reuse_posture={reuse_posture}",
        f"evidence_count={evidence_count}",
        f"decision={decision}",
    ]
    if proposed_parent_edge_class_ref is not None:
        rationale_parts.append(f"proposed_parent={proposed_parent_edge_class_ref}")
    if proposed_edge_class_ref is not None:
        rationale_parts.append(f"proposed_edge_class_ref={proposed_edge_class_ref}")
    rationale = "; ".join(rationale_parts)

    payload = {
        "schema": "adeu_edge_taxonomy_revision_judgment@1",
        "bound_edge_class_catalog_ref": catalog.catalog_id,
        "candidate_label": candidate_label,
        "nearest_existing_edge_class_refs": nearest_refs,
        "observed_symbol_ids": sorted(set(observed_symbol_ids)),
        "applicability_cue_tags": sorted(set(applicability_cue_tags)),
        "probe_signature_tags": sorted(set(probe_signature_tags)),
        "applicability_pattern_distinctness": applicability_pattern_distinctness,
        "probe_pattern_distinctness": probe_pattern_distinctness,
        "representable_without_information_loss": representable_without_information_loss,
        "reuse_posture": reuse_posture,
        "evidence_count": evidence_count,
        "decision": decision,
        "proposed_parent_edge_class_ref": proposed_parent_edge_class_ref,
        "proposed_edge_class_ref": proposed_edge_class_ref,
        "proposed_lifecycle_posture": proposed_lifecycle_posture,
        "judgment_posture": judgment_posture,
        "rationale": rationale,
    }
    payload["judgment_hash"] = sha256_canonical_json(payload)
    payload["judgment_id"] = compute_edge_taxonomy_revision_judgment_id(payload)
    return EdgeTaxonomyRevisionJudgment.model_validate(payload)


__all__ = [
    "judge_edge_taxonomy_revision",
]
