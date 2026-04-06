from __future__ import annotations

from collections import defaultdict
from typing import Any

from urm_runtime.hashing import sha256_canonical_json

from .models import (
    EdgeClassCatalog,
    EdgeClassNode,
    EdgeProbeTemplate,
    EdgeProbeTemplateCatalog,
    compute_edge_class_catalog_id,
    compute_edge_probe_template_catalog_id,
)

STARTER_EDGE_CATALOG_NAME = "adeu_edge_ledger.v0_starter_taxonomy"
STARTER_EDGE_CATALOG_VERSION = "0.1.0"
STARTER_EDGE_CATALOG_POSTURE = "bounded_repo_native_starter_taxonomy"
STARTER_PROBE_CATALOG_NAME = "adeu_edge_ledger.v0_probe_templates"
STARTER_PROBE_CATALOG_VERSION = "0.1.0"


_STARTER_TAXONOMY: dict[str, dict[str, Any]] = {
    "input_domain": {
        "summary": "Edges arising from what inputs exist, which may be absent, and which shapes are admitted.",
        "subfamilies": {
            "absence_nullability": {
                "summary": "Inputs or fields whose absence changes behavior or validity.",
                "archetypes": {
                    "none_missing_input": {
                        "summary": "A required input, field, or argument may be missing, None, or unresolved.",
                        "required": [],
                        "supporting": [
                            "feature:optional_annotation",
                            "feature:none_compare",
                            "feature:missing_terms",
                            "feature:ref_or_path_name",
                        ],
                        "structural_safety": [
                            "feature:raises_value_error",
                            "feature:model_validator",
                        ],
                        "test_tokens": ["missing", "none", "optional", "required"],
                        "probes": ["probe:null_absence_matrix", "probe:fail_closed_rejection"],
                    },
                    "optional_fragment_absence": {
                        "summary": "Optional fragments, refs, or fields may be absent while the surrounding payload remains valid.",
                        "required": [],
                        "supporting": [
                            "feature:optional_annotation",
                            "feature:fragment_or_ref_terms",
                            "feature:canonicalization_name",
                        ],
                        "structural_safety": ["feature:model_validator"],
                        "test_tokens": ["optional", "fragment", "ref", "absent"],
                        "probes": ["probe:null_absence_matrix"],
                    },
                },
            },
            "cardinality_shape": {
                "summary": "Collections or text-like inputs whose empty or degenerate form matters.",
                "archetypes": {
                    "empty_collection_or_text": {
                        "summary": "Empty lists, empty strings, or degenerate source sets may violate the contract.",
                        "required": [],
                        "supporting": [
                            "feature:collection_like",
                            "feature:len_call",
                            "feature:strip_or_replace",
                            "feature:sorted_unique_pattern",
                        ],
                        "structural_safety": ["feature:raises_value_error"],
                        "test_tokens": ["empty", "duplicate", "duplicates", "source_set"],
                        "probes": ["probe:shape_and_cardinality_matrix"],
                    },
                },
            },
        },
    },
    "boundary_order": {
        "summary": "Edges caused by boundaries, ordering laws, and partition cut points.",
        "subfamilies": {
            "numeric_interval": {
                "summary": "Numeric, index, or interval boundaries that may exclude or admit the wrong region.",
                "archetypes": {
                    "zero_negative_positive": {
                        "summary": "A numeric or count-like value crosses zero or another signed threshold.",
                        "required": [],
                        "supporting": [
                            "feature:numeric_annotation",
                            "feature:compare_to_zero",
                            "feature:len_call",
                        ],
                        "structural_safety": ["feature:raises_value_error"],
                        "test_tokens": ["zero", "negative", "positive"],
                        "probes": ["probe:boundary_partition"],
                    },
                    "inclusive_exclusive_boundary": {
                        "summary": "A boundary check may be off by one or mis-handle inclusion versus exclusion.",
                        "required": [],
                        "supporting": [
                            "feature:boundary_terms",
                            "feature:compare_ops",
                            "feature:scope_terms",
                        ],
                        "structural_safety": ["feature:raises_value_error"],
                        "test_tokens": ["outside", "within", "escape", "boundary"],
                        "probes": ["probe:boundary_partition", "probe:dependency_boundary_fault"],
                    },
                },
            },
            "ordering_permutation": {
                "summary": "Order-sensitive behavior that may drift under sorting or permutation.",
                "archetypes": {
                    "stable_ordering_preservation": {
                        "summary": "Canonical order should be stable under replay and not depend on incidental input order.",
                        "required": [],
                        "supporting": [
                            "feature:sorted_call",
                            "feature:sorted_unique_pattern",
                            "feature:canonicalization_name",
                        ],
                        "structural_safety": ["feature:sorted_call"],
                        "test_tokens": ["sort", "sorted", "order", "canonicalizes"],
                        "probes": ["probe:ordering_permutation", "probe:round_trip_and_idempotence"],
                    },
                },
            },
        },
    },
    "control_partition": {
        "summary": "Edges in branch partitioning, variant handling, and guard placement.",
        "subfamilies": {
            "branch_exhaustiveness": {
                "summary": "Branches or vocabularies that must remain exhaustive over admitted variants.",
                "archetypes": {
                    "boolean_flag_partition": {
                        "summary": "One mode, kind, or flag partition may route to the wrong branch or omit one branch.",
                        "required": [],
                        "supporting": [
                            "feature:has_if",
                            "feature:literal_like",
                            "feature:mode_or_kind_name",
                        ],
                        "structural_safety": ["feature:raises_value_error"],
                        "test_tokens": ["mode", "kind", "unsupported", "artifact_kind"],
                        "probes": ["probe:branch_partition_matrix"],
                    },
                    "unhandled_variant": {
                        "summary": "A newly introduced or unexpected variant is not handled explicitly and falls into undefined behavior.",
                        "required": [],
                        "supporting": [
                            "feature:literal_like",
                            "feature:membership_check",
                            "feature:raises_value_error",
                        ],
                        "structural_safety": ["feature:raises_value_error"],
                        "test_tokens": ["unsupported", "unknown", "variant", "class"],
                        "probes": ["probe:branch_partition_matrix", "probe:fail_closed_rejection"],
                    },
                },
            },
            "guard_short_circuit": {
                "summary": "Guards or early exits that should precede boundary actions.",
                "archetypes": {
                    "guard_before_side_effect": {
                        "summary": "Validation or scope guards should fire before any file or subprocess boundary executes.",
                        "required": ["feature:side_effect_boundary"],
                        "supporting": [
                            "feature:has_if",
                            "feature:raises_value_error",
                            "feature:has_try",
                        ],
                        "structural_safety": ["feature:raises_value_error"],
                        "test_tokens": ["blocked", "outside", "scope", "before"],
                        "probes": ["probe:state_sequence_replay", "probe:dependency_boundary_fault"],
                    },
                },
            },
        },
    },
    "state_sequence": {
        "summary": "Edges caused by mutation, aliasing, or repeated application over time.",
        "subfamilies": {
            "mutation_aliasing": {
                "summary": "State may be shared, mutated, or copied incorrectly across references.",
                "archetypes": {
                    "shared_reference_aliasing": {
                        "summary": "An update leaks across shared structures instead of staying local to one payload or instance.",
                        "required": [],
                        "supporting": [
                            "feature:attribute_assignment",
                            "feature:subscript_assignment",
                            "feature:collection_like",
                        ],
                        "structural_safety": [],
                        "test_tokens": ["shared", "alias", "mutation"],
                        "probes": ["probe:state_sequence_replay"],
                    },
                    "copy_isolation": {
                        "summary": "A defensive copy is required to avoid aliasing or accidental mutation across stages.",
                        "required": [],
                        "supporting": ["feature:deepcopy_call"],
                        "structural_safety": ["feature:deepcopy_call"],
                        "test_tokens": ["copy", "deepcopy", "isolation"],
                        "probes": ["probe:state_sequence_replay"],
                    },
                },
            },
            "temporal_reentry": {
                "summary": "Repeated application or stage ordering should preserve the intended contract.",
                "archetypes": {
                    "repeat_application_idempotence": {
                        "summary": "Applying canonicalization, materialization, or hashing twice should not drift the result.",
                        "required": [],
                        "supporting": [
                            "feature:canonicalization_name",
                            "feature:materialization_name",
                            "feature:compute_name",
                            "feature:model_dump_call",
                        ],
                        "structural_safety": ["feature:sorted_call"],
                        "test_tokens": ["replays", "canonicalizes", "materialize", "hash"],
                        "probes": ["probe:round_trip_and_idempotence", "probe:identity_hash_consistency"],
                    },
                },
            },
        },
    },
    "canonicalization_representation": {
        "summary": "Edges where different surface forms should collapse to one canonical representation.",
        "subfamilies": {
            "normalization_canonical_form": {
                "summary": "Text, paths, and refs may need canonical normalization.",
                "archetypes": {
                    "path_or_text_normalization": {
                        "summary": "Paths or textual refs should normalize into one repo-safe canonical form.",
                        "required": [],
                        "supporting": [
                            "feature:path_like",
                            "feature:strip_or_replace",
                            "feature:normalize_name",
                            "feature:scope_terms",
                        ],
                        "structural_safety": [
                            "feature:raises_value_error",
                            "feature:strip_or_replace",
                        ],
                        "test_tokens": ["path", "scope", "canonicalizes", "normalized"],
                        "probes": ["probe:normalization_round_trip", "probe:fail_closed_rejection"],
                    },
                    "whitespace_case_separator_canonicalization": {
                        "summary": "Whitespace, separators, or case should normalize rather than drifting identity.",
                        "required": [],
                        "supporting": [
                            "feature:strip_or_replace",
                            "feature:lower_or_upper",
                            "feature:startswith_or_endswith",
                        ],
                        "structural_safety": ["feature:strip_or_replace"],
                        "test_tokens": ["normalize", "separator", "whitespace", "case"],
                        "probes": ["probe:normalization_round_trip"],
                    },
                },
            },
            "serialization_identity": {
                "summary": "Canonical serialization and identity must round-trip cleanly.",
                "archetypes": {
                    "round_trip_serialization": {
                        "summary": "Canonicalization or materialization should round-trip through validated payload form without semantic loss.",
                        "required": [],
                        "supporting": [
                            "feature:model_validate_call",
                            "feature:model_dump_call",
                            "feature:json_loads_or_dumps",
                            "feature:canonicalization_name",
                            "feature:materialization_name",
                        ],
                        "structural_safety": [
                            "feature:model_validate_call",
                            "feature:model_dump_call",
                        ],
                        "test_tokens": ["replays", "fixture", "materialize", "validates"],
                        "probes": ["probe:round_trip_and_idempotence"],
                    },
                },
            },
        },
    },
    "contract_invariant": {
        "summary": "Edges where stable contract law, identity, or cross-field invariants must hold.",
        "subfamilies": {
            "cross_field_binding": {
                "summary": "Multiple fields or refs must remain jointly consistent.",
                "archetypes": {
                    "cross_field_consistency": {
                        "summary": "One field constrains another and the relationship must stay internally consistent.",
                        "required": [],
                        "supporting": [
                            "feature:model_validator",
                            "feature:cross_field_terms",
                            "feature:has_compare",
                        ],
                        "structural_safety": ["feature:model_validator"],
                        "test_tokens": ["drift", "lineage", "missing", "coverage"],
                        "probes": ["probe:cross_field_invariant", "probe:fail_closed_rejection"],
                    },
                    "source_ref_matches_scope": {
                        "summary": "Refs and paths must resolve inside the declared scope or request boundary.",
                        "required": [],
                        "supporting": [
                            "feature:ref_or_path_name",
                            "feature:scope_terms",
                            "feature:membership_check",
                            "feature:raises_value_error",
                        ],
                        "structural_safety": ["feature:raises_value_error"],
                        "test_tokens": ["scope", "boundary", "unbound", "outside"],
                        "probes": ["probe:cross_field_invariant", "probe:dependency_boundary_fault"],
                    },
                },
            },
            "vocabulary_order_identity": {
                "summary": "Vocabularies, unique lists, and identities should remain frozen and canonical.",
                "archetypes": {
                    "frozen_vocabulary_membership": {
                        "summary": "One value should belong to an explicit frozen vocabulary rather than an open-ended latent set.",
                        "required": [],
                        "supporting": [
                            "feature:literal_like",
                            "feature:membership_check",
                            "feature:raises_value_error",
                        ],
                        "structural_safety": ["feature:raises_value_error"],
                        "test_tokens": ["unsupported", "class", "kind", "mode"],
                        "probes": ["probe:branch_partition_matrix", "probe:fail_closed_rejection"],
                    },
                    "ordered_unique_sequence_invariant": {
                        "summary": "A list should be unique and canonicalized into a stable order before identity or equality claims are made.",
                        "required": [],
                        "supporting": [
                            "feature:sorted_call",
                            "feature:set_call",
                            "feature:sorted_unique_pattern",
                        ],
                        "structural_safety": ["feature:sorted_call", "feature:set_call"],
                        "test_tokens": ["duplicate", "sorted", "order", "canonicalization"],
                        "probes": ["probe:ordering_permutation", "probe:cross_field_invariant"],
                    },
                },
            },
        },
    },
    "dependency_boundary": {
        "summary": "Edges at file, subprocess, parse, and validation boundaries.",
        "subfamilies": {
            "filesystem_external_tool": {
                "summary": "Local file and subprocess boundaries may fail or return unexpected shapes.",
                "archetypes": {
                    "file_exists_and_kind": {
                        "summary": "A referenced file may not exist, may be the wrong kind, or may sit outside the declared scope.",
                        "required": [],
                        "supporting": [
                            "feature:path_like",
                            "feature:exists_or_is_file",
                            "feature:file_read_boundary",
                            "feature:raises_value_error",
                        ],
                        "structural_safety": ["feature:exists_or_is_file"],
                        "test_tokens": ["file", "missing", "exists", "reference"],
                        "probes": ["probe:dependency_boundary_fault"],
                    },
                    "git_command_failure_surface": {
                        "summary": "A git or subprocess call may fail, return unexpected output, or surface ambiguous stderr.",
                        "required": [],
                        "supporting": [
                            "feature:subprocess_boundary",
                            "feature:git_literal",
                            "feature:raises_value_error",
                        ],
                        "structural_safety": ["feature:raises_value_error"],
                        "test_tokens": ["git", "subprocess", "show"],
                        "probes": ["probe:dependency_boundary_fault", "probe:fail_closed_rejection"],
                    },
                },
            },
            "parse_validation_boundary": {
                "summary": "Parsing and schema validation boundaries may reject malformed or drifted payloads.",
                "archetypes": {
                    "schema_validation_rejection": {
                        "summary": "A parse or model-validation boundary should reject invalid payloads instead of coercing them silently.",
                        "required": [],
                        "supporting": [
                            "feature:model_validate_call",
                            "feature:model_dump_call",
                            "feature:json_loads_or_dumps",
                            "feature:raises_value_error",
                        ],
                        "structural_safety": ["feature:model_validate_call"],
                        "test_tokens": ["validates", "rejects", "schema", "validation"],
                        "probes": ["probe:dependency_boundary_fault", "probe:fail_closed_rejection"],
                    },
                },
            },
        },
    },
    "failure_path": {
        "summary": "Edges on the rejection path, mismatch path, or fail-closed fallback path.",
        "subfamilies": {
            "rejection_fail_closed": {
                "summary": "Invalid states should reject cleanly and remain fail-closed.",
                "archetypes": {
                    "raises_on_invalid_input": {
                        "summary": "Invalid input should raise or reject rather than proceeding with a latent bad state.",
                        "required": [],
                        "supporting": [
                            "feature:raises_value_error",
                            "feature:validation_name",
                            "feature:model_validator",
                        ],
                        "structural_safety": ["feature:raises_value_error"],
                        "test_tokens": ["rejects", "raises", "missing", "unsupported"],
                        "probes": ["probe:fail_closed_rejection"],
                    },
                    "fail_closed_on_mismatch": {
                        "summary": "Mismatches, drift, or authority-boundary failures should stop the flow instead of degrading to soft warnings.",
                        "required": [],
                        "supporting": [
                            "feature:mismatch_terms",
                            "feature:raises_value_error",
                            "feature:scope_terms",
                        ],
                        "structural_safety": ["feature:raises_value_error"],
                        "test_tokens": ["mismatch", "drift", "blocked", "outside"],
                        "probes": ["probe:fail_closed_rejection", "probe:dependency_boundary_fault"],
                    },
                },
            },
            "fallback_underdetermination": {
                "summary": "Errors should not be silently repaired or softened into untyped success.",
                "archetypes": {
                    "no_silent_repair": {
                        "summary": "A malformed or out-of-bound condition should not be auto-repaired into apparent success.",
                        "required": [],
                        "supporting": [
                            "feature:raises_value_error",
                            "feature:except_block",
                            "feature:error_message_string",
                        ],
                        "structural_safety": ["feature:raises_value_error"],
                        "test_tokens": ["rejects", "no", "absolute", "outside"],
                        "probes": ["probe:fail_closed_rejection", "probe:manual_adjudication"],
                    },
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
        "required_signal_tags": ["feature:optional_annotation", "feature:none_compare"],
    },
    "shape_and_cardinality_matrix": {
        "strategy_kind": "shape_matrix",
        "execution_postures": ["example_tests", "property_based"],
        "short_label": "Shape and cardinality matrix",
        "summary": "Probe empty, singleton, and degenerate shapes over collections or text-like inputs.",
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
        "summary": "Probe admitted and non-admitted branch variants against explicit mode vocabularies.",
        "required_signal_tags": ["feature:literal_like"],
    },
    "state_sequence_replay": {
        "strategy_kind": "state_sequence",
        "execution_postures": ["example_tests", "metamorphic"],
        "short_label": "State-sequence replay",
        "summary": "Replay the same or slightly permuted sequence to expose aliasing or sequencing drift.",
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
        "summary": "Check whether canonicalization or materialization replays without semantic drift.",
        "required_signal_tags": ["feature:model_validate_call"],
    },
    "identity_hash_consistency": {
        "strategy_kind": "hash_consistency",
        "execution_postures": ["example_tests", "metamorphic"],
        "short_label": "Identity and hash consistency",
        "summary": "Probe whether derived hashes or IDs change only when semantic basis fields change.",
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
        "summary": "Check that invalid states reject explicitly without soft degradation or silent repair.",
        "required_signal_tags": ["feature:raises_value_error"],
    },
    "manual_adjudication": {
        "strategy_kind": "manual_adjudication",
        "execution_postures": ["review_only"],
        "short_label": "Manual adjudication",
        "summary": "Flag cases that require human judgment or downstream probe design before status can advance.",
        "required_signal_tags": ["feature:except_block"],
    },
}


def edge_class_ref(*, family: str, subfamily: str | None = None, archetype: str | None = None) -> str:
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
            for archetype_slug, archetype_payload in subfamily_payload["archetypes"].items():
                nodes.append(
                    EdgeClassNode.model_validate(
                        {
                            "edge_class_ref": edge_class_ref(
                                family=family_slug,
                                subfamily=subfamily_slug,
                                archetype=archetype_slug,
                            ),
                            "parent_edge_class_ref": subfamily_ref,
                            "node_kind": "archetype",
                            "short_label": archetype_slug.replace("_", " "),
                            "summary": archetype_payload["summary"],
                            "required_cue_tags": sorted(archetype_payload["required"]),
                            "supporting_cue_tags": sorted(archetype_payload["supporting"]),
                            "structural_safety_cue_tags": sorted(archetype_payload["structural_safety"]),
                            "test_token_tags": sorted(archetype_payload["test_tokens"]),
                            "default_probe_template_refs": sorted(archetype_payload["probes"]),
                            "lifecycle_posture": "stabilized",
                        }
                    )
                )

    nodes = sorted(nodes, key=lambda item: item.edge_class_ref)
    payload = {
        "schema": "adeu_edge_class_catalog@1",
        "catalog_name": STARTER_EDGE_CATALOG_NAME,
        "catalog_version": STARTER_EDGE_CATALOG_VERSION,
        "catalog_posture": STARTER_EDGE_CATALOG_POSTURE,
        "nodes": [node.model_dump(mode="json", exclude_none=True) for node in nodes],
    }
    payload["catalog_hash"] = sha256_canonical_json(payload)
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
                "execution_postures": sorted(definition["execution_postures"]),
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
        "schema": "adeu_edge_probe_template_catalog@1",
        "catalog_name": STARTER_PROBE_CATALOG_NAME,
        "catalog_version": STARTER_PROBE_CATALOG_VERSION,
        "bound_edge_class_catalog_ref": catalog.catalog_id,
        "probe_templates": [
            probe.model_dump(mode="json", exclude_none=True) for probe in probe_templates
        ],
    }
    payload["catalog_hash"] = sha256_canonical_json(payload)
    payload["catalog_id"] = compute_edge_probe_template_catalog_id(payload)
    return EdgeProbeTemplateCatalog.model_validate(payload)


def catalog_nodes_by_ref(edge_class_catalog: EdgeClassCatalog) -> dict[str, EdgeClassNode]:
    return {node.edge_class_ref: node for node in edge_class_catalog.nodes}


def leaf_edge_class_refs(edge_class_catalog: EdgeClassCatalog) -> list[str]:
    return [
        node.edge_class_ref
        for node in edge_class_catalog.nodes
        if node.node_kind == "archetype"
    ]


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
]
