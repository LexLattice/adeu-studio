from __future__ import annotations

from adeu_edge_ledger import judge_edge_taxonomy_revision


def test_revision_judgment_can_classify_instance_of_existing_class(starter_catalogs) -> None:
    edge_catalog, _probe_catalog = starter_catalogs
    judgment = judge_edge_taxonomy_revision(
        edge_class_catalog=edge_catalog,
        candidate_label="git stderr ambiguity",
        nearest_existing_edge_class_refs=[
            "edge_class:dependency_boundary/filesystem_external_tool/git_command_failure_surface"
        ],
        observed_symbol_ids=["symbol:packages/example.py:helper:function"],
        applicability_cue_tags=["feature:git_literal", "feature:raises_value_error"],
        probe_signature_tags=["probe:dependency_boundary_fault"],
        applicability_pattern_distinctness="same",
        probe_pattern_distinctness="same",
        representable_without_information_loss=True,
        reuse_posture="recurrent_pattern",
        evidence_count=3,
    )

    assert judgment.decision == "instance_of_existing_class"
    assert judgment.proposed_edge_class_ref is None
    assert judgment.proposed_lifecycle_posture == "stabilized"
    assert judgment.judgment_posture == "settled"


def test_revision_judgment_can_add_new_sibling_under_existing_parent(starter_catalogs) -> None:
    edge_catalog, _probe_catalog = starter_catalogs
    judgment = judge_edge_taxonomy_revision(
        edge_class_catalog=edge_catalog,
        candidate_label="unicode locale normalization",
        nearest_existing_edge_class_refs=[
            "edge_class:canonicalization_representation/normalization_canonical_form/path_or_text_normalization"
        ],
        observed_symbol_ids=[
            "symbol:packages/example.py:normalize_path:function",
            "symbol:packages/example.py:normalize_title:function",
        ],
        applicability_cue_tags=["feature:normalize_name", "feature:lower_or_upper"],
        probe_signature_tags=["probe:normalization_round_trip"],
        applicability_pattern_distinctness="distinct",
        probe_pattern_distinctness="distinct",
        representable_without_information_loss=False,
        reuse_posture="recurrent_pattern",
        evidence_count=3,
    )

    assert judgment.decision == "new_sibling_under_existing_parent"
    assert (
        judgment.proposed_parent_edge_class_ref
        == "edge_class:canonicalization_representation/normalization_canonical_form"
    )
    assert (
        judgment.proposed_edge_class_ref
        == "edge_class:canonicalization_representation/normalization_canonical_form/unicode_locale_normalization"
    )
    assert judgment.proposed_lifecycle_posture == "candidate"


def test_revision_judgment_can_add_new_intermediate_node_within_one_family(
    starter_catalogs,
) -> None:
    edge_catalog, _probe_catalog = starter_catalogs
    judgment = judge_edge_taxonomy_revision(
        edge_class_catalog=edge_catalog,
        candidate_label="optional and empty inputs cluster",
        nearest_existing_edge_class_refs=[
            "edge_class:input_domain/absence_nullability/none_missing_input",
            "edge_class:input_domain/cardinality_shape/empty_collection_or_text",
        ],
        observed_symbol_ids=[
            "symbol:packages/example.py:missing_one:function",
            "symbol:packages/example.py:empty_two:function",
            "symbol:packages/example.py:empty_three:function",
        ],
        applicability_cue_tags=[
            "feature:collection_like",
            "feature:none_compare",
            "feature:optional_annotation",
        ],
        probe_signature_tags=["probe:null_absence_matrix", "probe:shape_and_cardinality_matrix"],
        applicability_pattern_distinctness="distinct",
        probe_pattern_distinctness="distinct",
        representable_without_information_loss=False,
        reuse_posture="recurrent_pattern",
        evidence_count=4,
    )

    assert judgment.decision == "new_intermediate_node"
    assert judgment.proposed_parent_edge_class_ref == "edge_class:input_domain"
    assert (
        judgment.proposed_edge_class_ref
        == "edge_class:input_domain/optional_and_empty_inputs_cluster"
    )


def test_revision_judgment_can_add_new_top_level_family(starter_catalogs) -> None:
    edge_catalog, _probe_catalog = starter_catalogs
    judgment = judge_edge_taxonomy_revision(
        edge_class_catalog=edge_catalog,
        candidate_label="identity drift cross round trip",
        nearest_existing_edge_class_refs=[
            "edge_class:canonicalization_representation/serialization_identity/round_trip_serialization",
            "edge_class:state_sequence/temporal_reentry/repeat_application_idempotence",
        ],
        observed_symbol_ids=[
            "symbol:packages/example.py:one:function",
            "symbol:packages/example.py:two:function",
            "symbol:packages/example.py:three:function",
            "symbol:packages/example.py:four:function",
        ],
        applicability_cue_tags=[
            "feature:hashlib_or_sha",
            "feature:model_dump_call",
            "feature:model_validate_call",
        ],
        probe_signature_tags=["probe:identity_hash_consistency", "probe:round_trip_and_idempotence"],
        applicability_pattern_distinctness="distinct",
        probe_pattern_distinctness="distinct",
        representable_without_information_loss=False,
        reuse_posture="recurrent_pattern",
        evidence_count=5,
    )

    assert judgment.decision == "new_top_level_family"
    assert judgment.proposed_parent_edge_class_ref is None
    assert judgment.proposed_edge_class_ref == "edge_class:identity_drift_cross_round_trip"
    assert judgment.proposed_lifecycle_posture == "stabilized"


def test_revision_judgment_can_specialize_under_existing_family(starter_catalogs) -> None:
    edge_catalog, _probe_catalog = starter_catalogs
    judgment = judge_edge_taxonomy_revision(
        edge_class_catalog=edge_catalog,
        candidate_label="payload absence branch",
        nearest_existing_edge_class_refs=["edge_class:input_domain"],
        observed_symbol_ids=[
            "symbol:packages/example.py:missing_one:function",
            "symbol:packages/example.py:missing_two:function",
            "symbol:packages/example.py:missing_three:function",
        ],
        applicability_cue_tags=["feature:optional_annotation", "feature:none_compare"],
        probe_signature_tags=["probe:null_absence_matrix"],
        applicability_pattern_distinctness="adjacent_but_representable",
        probe_pattern_distinctness="adjacent_but_representable",
        representable_without_information_loss=True,
        reuse_posture="multi_symbol_candidate",
        evidence_count=3,
    )

    assert judgment.decision == "specialize_under_existing_class"
    assert judgment.proposed_parent_edge_class_ref == "edge_class:input_domain"
    assert judgment.proposed_edge_class_ref == "edge_class:input_domain/payload_absence_branch"


def test_revision_judgment_can_mark_existing_archetype_for_split(starter_catalogs) -> None:
    edge_catalog, _probe_catalog = starter_catalogs
    judgment = judge_edge_taxonomy_revision(
        edge_class_catalog=edge_catalog,
        candidate_label="strict versus lossy normalization",
        nearest_existing_edge_class_refs=[
            "edge_class:canonicalization_representation/normalization_canonical_form/path_or_text_normalization"
        ],
        observed_symbol_ids=[
            "symbol:packages/example.py:normalize_one:function",
            "symbol:packages/example.py:normalize_two:function",
            "symbol:packages/example.py:normalize_three:function",
            "symbol:packages/example.py:normalize_four:function",
        ],
        applicability_cue_tags=["feature:normalize_name", "feature:strip_or_replace"],
        probe_signature_tags=["probe:normalization_round_trip"],
        applicability_pattern_distinctness="distinct",
        probe_pattern_distinctness="distinct",
        representable_without_information_loss=False,
        reuse_posture="recurrent_pattern",
        evidence_count=4,
    )

    assert judgment.decision == "split_existing_class"
    assert judgment.proposed_lifecycle_posture == "split"
