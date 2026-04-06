from __future__ import annotations

from collections import defaultdict
from typing import Any

from .models import (
    ADEU_EDGE_CLASS_CATALOG_SCHEMA,
    ADEU_EDGE_PROBE_TEMPLATE_CATALOG_SCHEMA,
    EdgeClassCatalog,
    EdgeClassNode,
    EdgeProbeTemplate,
    EdgeProbeTemplateCatalog,
    compute_edge_class_catalog_id,
    compute_edge_probe_template_catalog_id,
)

STARTER_EDGE_CATALOG_NAME = "adeu_edge_ledger.v53a_starter_taxonomy"
STARTER_EDGE_CATALOG_VERSION = "0.1.0"
STARTER_EDGE_CATALOG_POSTURE = "starter_taxonomy_over_released_v50_pilot_scope"
STARTER_PROBE_CATALOG_NAME = "adeu_edge_ledger.v53a_starter_probe_templates"
STARTER_PROBE_CATALOG_VERSION = "0.1.0"

_STARTER_TAXONOMY: dict[str, dict[str, Any]] = {
    "input_domain": {
        "summary": (
            "Edges arising from what inputs exist, which may be absent, and which shapes are "
            "admitted."
        ),
        "subfamilies": {
            "absence_nullability": {
                "summary": "Inputs or fields whose absence changes behavior or validity.",
                "archetype": {
                    "slug": "none_missing_input",
                    "summary": (
                        "A required input, field, or argument may be missing, None, or unresolved."
                    ),
                    "required": [],
                    "supporting": [
                        "feature:missing_terms",
                        "feature:none_compare",
                        "feature:optional_annotation",
                        "feature:ref_or_path_name",
                    ],
                    "structural_safety": [
                        "feature:model_validator",
                        "feature:raises_value_error",
                    ],
                    "test_tokens": ["missing", "none", "optional", "required"],
                    "probes": ["probe:fail_closed_rejection", "probe:null_absence_matrix"],
                },
            },
            "cardinality_shape": {
                "summary": (
                    "Collections or text-like inputs whose empty or degenerate form matters."
                ),
                "archetype": {
                    "slug": "empty_collection_or_text",
                    "summary": (
                        "Empty lists, empty strings, or degenerate source sets may violate the "
                        "contract."
                    ),
                    "required": [],
                    "supporting": [
                        "feature:collection_like",
                        "feature:len_call",
                        "feature:sorted_unique_pattern",
                        "feature:strip_or_replace",
                    ],
                    "structural_safety": ["feature:raises_value_error"],
                    "test_tokens": ["duplicate", "duplicates", "empty", "source_set"],
                    "probes": ["probe:shape_and_cardinality_matrix"],
                },
            },
        },
    },
    "boundary_order": {
        "summary": "Edges caused by boundaries, ordering laws, and partition cut points.",
        "subfamilies": {
            "numeric_interval": {
                "summary": (
                    "Numeric, index, or interval boundaries that may exclude or admit "
                    "the wrong region."
                ),
                "archetype": {
                    "slug": "inclusive_exclusive_boundary",
                    "summary": (
                        "A boundary check may be off by one or mis-handle inclusion versus "
                        "exclusion."
                    ),
                    "required": [],
                    "supporting": [
                        "feature:boundary_terms",
                        "feature:compare_ops",
                        "feature:scope_terms",
                    ],
                    "structural_safety": ["feature:raises_value_error"],
                    "test_tokens": ["boundary", "escape", "outside", "within"],
                    "probes": ["probe:boundary_partition", "probe:dependency_boundary_fault"],
                },
            },
            "ordering_permutation": {
                "summary": "Order-sensitive behavior that may drift under sorting or permutation.",
                "archetype": {
                    "slug": "stable_ordering_preservation",
                    "summary": (
                        "Canonical order should be stable under replay and not depend on "
                        "incidental input order."
                    ),
                    "required": [],
                    "supporting": [
                        "feature:canonicalization_name",
                        "feature:sorted_call",
                        "feature:sorted_unique_pattern",
                    ],
                    "structural_safety": ["feature:sorted_call"],
                    "test_tokens": ["canonicalizes", "order", "sort", "sorted"],
                    "probes": ["probe:ordering_permutation", "probe:round_trip_and_idempotence"],
                },
            },
        },
    },
    "control_partition": {
        "summary": "Edges in branch partitioning, variant handling, and guard placement.",
        "subfamilies": {
            "branch_exhaustiveness": {
                "summary": (
                    "Branches or vocabularies that must remain exhaustive over admitted variants."
                ),
                "archetype": {
                    "slug": "unhandled_variant",
                    "summary": (
                        "A newly introduced or unexpected variant is not handled explicitly and "
                        "falls into undefined behavior."
                    ),
                    "required": [],
                    "supporting": [
                        "feature:literal_like",
                        "feature:membership_check",
                        "feature:raises_value_error",
                    ],
                    "structural_safety": ["feature:raises_value_error"],
                    "test_tokens": ["class", "unknown", "unsupported", "variant"],
                    "probes": ["probe:branch_partition_matrix", "probe:fail_closed_rejection"],
                },
            },
            "guard_short_circuit": {
                "summary": "Guards or early exits that should precede boundary actions.",
                "archetype": {
                    "slug": "guard_before_side_effect",
                    "summary": (
                        "Validation or scope guards should fire before any file or subprocess "
                        "boundary executes."
                    ),
                    "required": ["feature:side_effect_boundary"],
                    "supporting": [
                        "feature:has_if",
                        "feature:has_try",
                        "feature:raises_value_error",
                    ],
                    "structural_safety": ["feature:raises_value_error"],
                    "test_tokens": ["before", "blocked", "outside", "scope"],
                    "probes": ["probe:dependency_boundary_fault", "probe:state_sequence_replay"],
                },
            },
        },
    },
    "state_sequence": {
        "summary": "Edges caused by mutation, aliasing, or repeated application over time.",
        "subfamilies": {
            "mutation_aliasing": {
                "summary": "State may be shared, mutated, or copied incorrectly across references.",
                "archetype": {
                    "slug": "copy_isolation",
                    "summary": (
                        "A defensive copy is required to avoid aliasing or accidental mutation "
                        "across stages."
                    ),
                    "required": [],
                    "supporting": ["feature:deepcopy_call"],
                    "structural_safety": ["feature:deepcopy_call"],
                    "test_tokens": ["copy", "deepcopy", "isolation"],
                    "probes": ["probe:state_sequence_replay"],
                },
            },
            "temporal_reentry": {
                "summary": (
                    "Repeated application or stage ordering should preserve the intended contract."
                ),
                "archetype": {
                    "slug": "repeat_application_idempotence",
                    "summary": (
                        "Applying canonicalization, materialization, or hashing twice should not "
                        "drift the result."
                    ),
                    "required": [],
                    "supporting": [
                        "feature:canonicalization_name",
                        "feature:compute_name",
                        "feature:materialization_name",
                        "feature:model_dump_call",
                    ],
                    "structural_safety": ["feature:sorted_call"],
                    "test_tokens": ["canonicalizes", "hash", "materialize", "replays"],
                    "probes": [
                        "probe:identity_hash_consistency",
                        "probe:round_trip_and_idempotence",
                    ],
                },
            },
        },
    },
    "canonicalization_representation": {
        "summary": (
            "Edges where different surface forms should collapse to one canonical representation."
        ),
        "subfamilies": {
            "normalization_canonical_form": {
                "summary": "Text, paths, and refs may need canonical normalization.",
                "archetype": {
                    "slug": "path_or_text_normalization",
                    "summary": (
                        "Paths or textual refs should normalize into one repo-safe canonical form."
                    ),
                    "required": [],
                    "supporting": [
                        "feature:normalize_name",
                        "feature:path_like",
                        "feature:scope_terms",
                        "feature:strip_or_replace",
                    ],
                    "structural_safety": [
                        "feature:raises_value_error",
                        "feature:strip_or_replace",
                    ],
                    "test_tokens": ["canonicalizes", "normalized", "path", "scope"],
                    "probes": ["probe:fail_closed_rejection", "probe:normalization_round_trip"],
                },
            },
            "serialization_identity": {
                "summary": "Canonical serialization and identity must round-trip cleanly.",
                "archetype": {
                    "slug": "round_trip_serialization",
                    "summary": (
                        "Canonicalization or materialization should round-trip through validated "
                        "payload form without semantic loss."
                    ),
                    "required": [],
                    "supporting": [
                        "feature:canonicalization_name",
                        "feature:json_loads_or_dumps",
                        "feature:materialization_name",
                        "feature:model_dump_call",
                        "feature:model_validate_call",
                    ],
                    "structural_safety": [
                        "feature:model_dump_call",
                        "feature:model_validate_call",
                    ],
                    "test_tokens": ["fixture", "materialize", "replays", "validates"],
                    "probes": ["probe:round_trip_and_idempotence"],
                },
            },
        },
    },
    "contract_invariant": {
        "summary": (
            "Edges where stable contract law, identity, or cross-field invariants must hold."
        ),
        "subfamilies": {
            "cross_field_binding": {
                "summary": "Multiple fields or refs must remain jointly consistent.",
                "archetype": {
                    "slug": "cross_field_consistency",
                    "summary": (
                        "One field constrains another and the relationship must stay internally "
                        "consistent."
                    ),
                    "required": [],
                    "supporting": [
                        "feature:cross_field_terms",
                        "feature:has_compare",
                        "feature:model_validator",
                    ],
                    "structural_safety": ["feature:model_validator"],
                    "test_tokens": ["coverage", "drift", "lineage", "missing"],
                    "probes": ["probe:cross_field_invariant", "probe:fail_closed_rejection"],
                },
            },
            "vocabulary_order_identity": {
                "summary": (
                    "Vocabularies, unique lists, and identities should remain frozen and canonical."
                ),
                "archetype": {
                    "slug": "ordered_unique_sequence_invariant",
                    "summary": (
                        "A list should be unique and canonicalized into a stable order before "
                        "identity or equality claims are made."
                    ),
                    "required": [],
                    "supporting": [
                        "feature:set_call",
                        "feature:sorted_call",
                        "feature:sorted_unique_pattern",
                    ],
                    "structural_safety": ["feature:set_call", "feature:sorted_call"],
                    "test_tokens": ["canonicalization", "duplicate", "order", "sorted"],
                    "probes": ["probe:cross_field_invariant", "probe:ordering_permutation"],
                },
            },
        },
    },
    "dependency_boundary": {
        "summary": "Edges at file, subprocess, parse, and validation boundaries.",
        "subfamilies": {
            "filesystem_external_tool": {
                "summary": (
                    "Local file and subprocess boundaries may fail or return unexpected shapes."
                ),
                "archetype": {
                    "slug": "file_exists_and_kind",
                    "summary": (
                        "A referenced file may not exist, may be the wrong kind, or may sit "
                        "outside the declared scope."
                    ),
                    "required": [],
                    "supporting": [
                        "feature:exists_or_is_file",
                        "feature:file_read_boundary",
                        "feature:path_like",
                        "feature:raises_value_error",
                    ],
                    "structural_safety": ["feature:exists_or_is_file"],
                    "test_tokens": ["exists", "file", "missing", "reference"],
                    "probes": ["probe:dependency_boundary_fault"],
                },
            },
            "parse_validation_boundary": {
                "summary": (
                    "Parsing and schema validation boundaries may reject malformed "
                    "or drifted payloads."
                ),
                "archetype": {
                    "slug": "schema_validation_rejection",
                    "summary": (
                        "A parse or model-validation boundary should reject invalid payloads "
                        "instead of coercing them silently."
                    ),
                    "required": [],
                    "supporting": [
                        "feature:json_loads_or_dumps",
                        "feature:model_dump_call",
                        "feature:model_validate_call",
                        "feature:raises_value_error",
                    ],
                    "structural_safety": ["feature:model_validate_call"],
                    "test_tokens": ["rejects", "schema", "validates", "validation"],
                    "probes": ["probe:dependency_boundary_fault", "probe:fail_closed_rejection"],
                },
            },
        },
    },
    "failure_path": {
        "summary": "Edges on the rejection path, mismatch path, or fail-closed fallback path.",
        "subfamilies": {
            "rejection_fail_closed": {
                "summary": "Invalid states should reject cleanly and remain fail-closed.",
                "archetype": {
                    "slug": "raises_on_invalid_input",
                    "summary": (
                        "Invalid input should raise or reject rather than proceeding with a latent "
                        "bad state."
                    ),
                    "required": [],
                    "supporting": [
                        "feature:model_validator",
                        "feature:raises_value_error",
                        "feature:validation_name",
                    ],
                    "structural_safety": ["feature:raises_value_error"],
                    "test_tokens": ["missing", "raises", "rejects", "unsupported"],
                    "probes": ["probe:fail_closed_rejection"],
                },
            },
            "fallback_underdetermination": {
                "summary": (
                    "Errors should not be silently repaired or softened into untyped success."
                ),
                "archetype": {
                    "slug": "no_silent_repair",
                    "summary": (
                        "A malformed or out-of-bound condition should not be auto-repaired into "
                        "apparent success."
                    ),
                    "required": [],
                    "supporting": [
                        "feature:error_message_string",
                        "feature:except_block",
                        "feature:raises_value_error",
                    ],
                    "structural_safety": ["feature:raises_value_error"],
                    "test_tokens": ["absolute", "no", "outside", "rejects"],
                    "probes": ["probe:fail_closed_rejection"],
                },
            },
        },
    },
}

_PROBE_TEMPLATES: dict[str, dict[str, Any]] = {
    "null_absence_matrix": {
        "strategy_kind": "absence_matrix",
        "execution_postures": ["example_tests", "property_based"],
        "short_label": "Null or missing matrix",
        "summary": "Probe required, optional, and absent variants over one symbol boundary.",
        "required_signal_tags": ["feature:none_compare", "feature:optional_annotation"],
    },
    "shape_and_cardinality_matrix": {
        "strategy_kind": "shape_matrix",
        "execution_postures": ["example_tests", "property_based"],
        "short_label": "Shape and cardinality matrix",
        "summary": (
            "Probe empty, singleton, and degenerate shapes over collections or text-like inputs."
        ),
        "required_signal_tags": ["feature:collection_like"],
    },
    "boundary_partition": {
        "strategy_kind": "boundary_partition",
        "execution_postures": ["example_tests", "property_based"],
        "short_label": "Boundary partition",
        "summary": "Probe values immediately below, at, and above a decisive boundary.",
        "required_signal_tags": ["feature:compare_ops"],
    },
    "ordering_permutation": {
        "strategy_kind": "ordering_permutation",
        "execution_postures": ["example_tests", "metamorphic"],
        "short_label": "Ordering permutation",
        "summary": "Probe whether order-sensitive inputs preserve or normalize order lawfully.",
        "required_signal_tags": ["feature:sorted_call"],
    },
    "branch_partition_matrix": {
        "strategy_kind": "branch_partition",
        "execution_postures": ["example_tests", "property_based"],
        "short_label": "Branch partition matrix",
        "summary": (
            "Probe admitted and non-admitted branch variants against explicit mode vocabularies."
        ),
        "required_signal_tags": ["feature:literal_like"],
    },
    "state_sequence_replay": {
        "strategy_kind": "state_sequence",
        "execution_postures": ["example_tests", "metamorphic"],
        "short_label": "State-sequence replay",
        "summary": (
            "Replay the same or slightly permuted sequence to expose aliasing or sequencing drift."
        ),
        "required_signal_tags": ["feature:side_effect_boundary"],
    },
    "normalization_round_trip": {
        "strategy_kind": "round_trip",
        "execution_postures": ["example_tests", "metamorphic"],
        "short_label": "Normalization round-trip",
        "summary": "Round-trip through normalization to ensure canonical surface forms are stable.",
        "required_signal_tags": ["feature:strip_or_replace"],
    },
    "round_trip_and_idempotence": {
        "strategy_kind": "round_trip",
        "execution_postures": ["example_tests", "metamorphic"],
        "short_label": "Round-trip and idempotence",
        "summary": (
            "Check whether canonicalization or materialization replays without semantic drift."
        ),
        "required_signal_tags": ["feature:model_validate_call"],
    },
    "identity_hash_consistency": {
        "strategy_kind": "hash_consistency",
        "execution_postures": ["example_tests", "metamorphic"],
        "short_label": "Identity and hash consistency",
        "summary": (
            "Probe whether derived hashes or IDs change only when semantic basis fields change."
        ),
        "required_signal_tags": ["feature:hashlib_or_sha"],
    },
    "cross_field_invariant": {
        "strategy_kind": "cross_field_invariant",
        "execution_postures": ["example_tests", "property_based"],
        "short_label": "Cross-field invariant",
        "summary": "Probe multi-field or multi-ref invariants that should hold jointly.",
        "required_signal_tags": ["feature:model_validator"],
    },
    "dependency_boundary_fault": {
        "strategy_kind": "dependency_boundary",
        "execution_postures": ["example_tests", "review_only"],
        "short_label": "Dependency boundary fault",
        "summary": "Exercise filesystem, subprocess, or parse boundaries under error conditions.",
        "required_signal_tags": ["feature:side_effect_boundary"],
    },
    "fail_closed_rejection": {
        "strategy_kind": "fail_closed_rejection",
        "execution_postures": ["example_tests", "review_only"],
        "short_label": "Fail-closed rejection",
        "summary": (
            "Check that invalid states reject explicitly without soft degradation or silent repair."
        ),
        "required_signal_tags": ["feature:raises_value_error"],
    },
}


def edge_class_ref(
    *, family: str, subfamily: str | None = None, archetype: str | None = None
) -> str:
    parts = [family]
    if subfamily is not None:
        parts.append(subfamily)
    if archetype is not None:
        parts.append(archetype)
    return f"edge_class:{'/'.join(parts)}"


def probe_template_ref(slug: str) -> str:
    return f"probe:{slug}"


def build_starter_edge_class_catalog() -> EdgeClassCatalog:
    nodes: list[EdgeClassNode] = []
    for family_slug, family_payload in _STARTER_TAXONOMY.items():
        family_ref = edge_class_ref(family=family_slug)
        nodes.append(
            EdgeClassNode.model_validate(
                {
                    "edge_class_ref": family_ref,
                    "parent_edge_class_ref": None,
                    "node_kind": "family",
                    "short_label": family_slug.replace("_", " "),
                    "summary": family_payload["summary"],
                    "required_cue_tags": [],
                    "supporting_cue_tags": [],
                    "structural_safety_cue_tags": [],
                    "test_token_tags": [],
                    "default_probe_template_refs": [],
                    "lifecycle_posture": "stabilized",
                }
            )
        )
        for subfamily_slug, subfamily_payload in family_payload["subfamilies"].items():
            subfamily_ref = edge_class_ref(family=family_slug, subfamily=subfamily_slug)
            nodes.append(
                EdgeClassNode.model_validate(
                    {
                        "edge_class_ref": subfamily_ref,
                        "parent_edge_class_ref": family_ref,
                        "node_kind": "subfamily",
                        "short_label": subfamily_slug.replace("_", " "),
                        "summary": subfamily_payload["summary"],
                        "required_cue_tags": [],
                        "supporting_cue_tags": [],
                        "structural_safety_cue_tags": [],
                        "test_token_tags": [],
                        "default_probe_template_refs": [],
                        "lifecycle_posture": "stabilized",
                    }
                )
            )
            archetype_payload = subfamily_payload["archetype"]
            nodes.append(
                EdgeClassNode.model_validate(
                    {
                        "edge_class_ref": edge_class_ref(
                            family=family_slug,
                            subfamily=subfamily_slug,
                            archetype=archetype_payload["slug"],
                        ),
                        "parent_edge_class_ref": subfamily_ref,
                        "node_kind": "archetype",
                        "short_label": archetype_payload["slug"].replace("_", " "),
                        "summary": archetype_payload["summary"],
                        "required_cue_tags": sorted(archetype_payload["required"]),
                        "supporting_cue_tags": sorted(archetype_payload["supporting"]),
                        "structural_safety_cue_tags": sorted(
                            archetype_payload["structural_safety"]
                        ),
                        "test_token_tags": sorted(archetype_payload["test_tokens"]),
                        "default_probe_template_refs": sorted(archetype_payload["probes"]),
                        "lifecycle_posture": "stabilized",
                    }
                )
            )

    nodes = sorted(nodes, key=lambda item: item.edge_class_ref)
    payload = {
        "schema": ADEU_EDGE_CLASS_CATALOG_SCHEMA,
        "catalog_name": STARTER_EDGE_CATALOG_NAME,
        "catalog_version": STARTER_EDGE_CATALOG_VERSION,
        "catalog_posture": STARTER_EDGE_CATALOG_POSTURE,
        "nodes": [node.model_dump(mode="json", exclude_none=True) for node in nodes],
    }
    payload["catalog_hash"] = compute_catalog_hash(payload)
    payload["catalog_id"] = compute_edge_class_catalog_id(payload)
    return EdgeClassCatalog.model_validate(payload)


def build_starter_edge_probe_template_catalog(
    *,
    edge_class_catalog: EdgeClassCatalog | None = None,
) -> EdgeProbeTemplateCatalog:
    catalog = edge_class_catalog or build_starter_edge_class_catalog()
    probe_to_classes: dict[str, set[str]] = defaultdict(set)
    for node in catalog.nodes:
        if node.node_kind != "archetype":
            continue
        for probe_ref in node.default_probe_template_refs:
            probe_to_classes[probe_ref].add(node.edge_class_ref)

    probe_templates = [
        EdgeProbeTemplate.model_validate(
            {
                "probe_template_ref": probe_template_ref(slug),
                "strategy_kind": definition["strategy_kind"],
                "execution_postures": definition["execution_postures"],
                "short_label": definition["short_label"],
                "summary": definition["summary"],
                "suited_edge_class_refs": sorted(probe_to_classes[probe_template_ref(slug)]),
                "required_signal_tags": sorted(definition["required_signal_tags"]),
                "lifecycle_posture": "stabilized",
            }
        )
        for slug, definition in sorted(_PROBE_TEMPLATES.items())
    ]

    payload = {
        "schema": ADEU_EDGE_PROBE_TEMPLATE_CATALOG_SCHEMA,
        "catalog_name": STARTER_PROBE_CATALOG_NAME,
        "catalog_version": STARTER_PROBE_CATALOG_VERSION,
        "bound_edge_class_catalog_ref": catalog.catalog_id,
        "probe_templates": [
            probe.model_dump(mode="json", exclude_none=True) for probe in probe_templates
        ],
    }
    payload["catalog_hash"] = compute_catalog_hash(payload)
    payload["catalog_id"] = compute_edge_probe_template_catalog_id(payload)
    catalog_model = EdgeProbeTemplateCatalog.model_validate(payload)
    validate_probe_template_catalog_binding(
        edge_class_catalog=catalog,
        probe_template_catalog=catalog_model,
    )
    return catalog_model


def catalog_nodes_by_ref(edge_class_catalog: EdgeClassCatalog) -> dict[str, EdgeClassNode]:
    return {node.edge_class_ref: node for node in edge_class_catalog.nodes}


def leaf_edge_class_refs(edge_class_catalog: EdgeClassCatalog) -> list[str]:
    return [
        node.edge_class_ref for node in edge_class_catalog.nodes if node.node_kind == "archetype"
    ]


def validate_probe_template_catalog_binding(
    *,
    edge_class_catalog: EdgeClassCatalog,
    probe_template_catalog: EdgeProbeTemplateCatalog,
) -> EdgeProbeTemplateCatalog:
    if probe_template_catalog.bound_edge_class_catalog_ref != edge_class_catalog.catalog_id:
        raise ValueError("probe template catalog must bind to the supplied edge class catalog")
    archetype_refs = set(leaf_edge_class_refs(edge_class_catalog))
    probe_refs = {probe.probe_template_ref for probe in probe_template_catalog.probe_templates}
    for probe in probe_template_catalog.probe_templates:
        if not set(probe.suited_edge_class_refs) <= archetype_refs:
            raise ValueError(
                "probe template suited_edge_class_refs must resolve to catalog archetypes"
            )
    for node in edge_class_catalog.nodes:
        if node.node_kind != "archetype":
            continue
        if not set(node.default_probe_template_refs) <= probe_refs:
            raise ValueError(
                "archetype default_probe_template_refs must resolve inside the probe catalog"
            )
    return probe_template_catalog


def compute_catalog_hash(payload_without_hash: dict[str, Any]) -> str:
    from .models import _sha256_canonical_payload

    return _sha256_canonical_payload(payload_without_hash)


__all__ = [
    "STARTER_EDGE_CATALOG_NAME",
    "STARTER_EDGE_CATALOG_POSTURE",
    "STARTER_EDGE_CATALOG_VERSION",
    "STARTER_PROBE_CATALOG_NAME",
    "STARTER_PROBE_CATALOG_VERSION",
    "build_starter_edge_class_catalog",
    "build_starter_edge_probe_template_catalog",
    "catalog_nodes_by_ref",
    "edge_class_ref",
    "leaf_edge_class_refs",
    "probe_template_ref",
    "validate_probe_template_catalog_binding",
]
