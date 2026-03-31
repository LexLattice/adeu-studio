# Locked Continuation vNext+99

Status: `V45-A` implementation contract.

## V99 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v45a_repo_self_description_schema_registry_contract@1",
  "target_arc": "vNext+99",
  "target_path": "V45-A",
  "target_scope": "schema_family_registry_and_schema_visible_entity_catalog_over_bounded_repo_snapshot",
  "implementation_packages": [
    "adeu_repo_description"
  ],
  "governing_released_stack": "V41_practical_analysis_and_released_meta_control_surfaces_on_main",
  "governing_stack_consumption_mode": "descriptive_consumption_not_recursive_governance_redefinition",
  "repo_entity_catalog_schema": "repo_entity_catalog@1",
  "repo_schema_family_registry_schema": "repo_schema_family_registry@1",
  "descriptive_plane_first_required": true,
  "schema_corpus_first_bounded_subcorpus_required": true,
  "schema_visible_entity_scope_required": true,
  "repo_visible_snapshot_scope_required": true,
  "explicit_stale_snapshot_semantics_required": true,
  "extraction_provenance_required": true,
  "multi_axis_entity_taxonomy_required": true,
  "schema_role_form_classification_required": true,
  "schema_role_form_precedence_required": true,
  "classification_policy_binding_required": true,
  "classification_policy_hash_required": true,
  "primary_carrier_class_required": true,
  "secondary_role_form_tags_allowed": true,
  "lineage_overlay_required": true,
  "family_cluster_required": true,
  "family_cluster_primary_carrier_and_lineage_non_equivalent_required": true,
  "named_residual_flags_required": true,
  "classification_posture_required": true,
  "classification_method_required": true,
  "inferred_to_adjudicated_promotion_law_required": true,
  "adjudicated_to_settled_promotion_law_required": true,
  "typed_evidence_kinds_required": true,
  "branch_local_schema_core_hypothesis": "common_core_plus_carrier_overlays_plus_lineage_overlays_plus_narrow_named_residuals",
  "bounded_reconstruction_subset_required": true,
  "bounded_reconstruction_round_trip_required": true,
  "round_trip_equivalence_mode": "canonical_normalized_semantic_equivalence",
  "entity_coverage_mode_required": true,
  "outputs_snapshot_bound_historical_when_stale_required": true,
  "authoritative_and_mirrored_schema_export_parity_required": true,
  "whole_repo_entity_exhaustiveness_forbidden": true,
  "naming_only_classification_forbidden": true,
  "recursive_governance_binding_deferred": true,
  "symbol_catalog_dependency_graph_deferred": true,
  "test_intent_matrix_deferred": true,
  "optimization_register_deferred": true,
  "mutation_entitlement_forbidden": true,
  "source_architecture_doc": "docs/DRAFT_REPO_SELF_DESCRIPTION_SPEC_v0.md",
  "decomposition_doc": "docs/DRAFT_V45_REPO_SELF_DESCRIPTION_DECOMPOSITION_v0.md",
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v28.md",
  "entity_taxonomy_doc": "docs/DRAFT_REPO_ENTITY_ROLE_TAXONOMY_v0.md",
  "schema_meta_core_doc": "docs/DRAFT_SCHEMA_META_CORE_v0.md",
  "schema_role_form_registry_doc": "docs/DRAFT_SCHEMA_ROLE_FORM_REGISTRY_v0.md"
}
```

## Slice

- Arc label: `vNext+99`
- Family label: `V45-A`
- Scope label: bounded schema-family registry and schema-visible repo entity catalog
  over one repo snapshot

## Objective

Release the first descriptive `V45-A` lane by materializing:

- one canonical `repo_schema_family_registry@1`;
- one bounded `repo_entity_catalog@1` scoped to schema-visible surfaces;
- one explicit reconstruction appendix over a representative schema subset;

while preserving epistemic posture, classification precedence, snapshot identity, and
fail-closed rejection of mutation or recursive-governance overreach.

This slice is descriptive consumption over the current repo state, not recursive
amendment or broad whole-repo inventory.

## Frozen Implementation Decisions

1. Descriptive-first strategy:
   - `V45-A` starts with schema-family registry and schema-visible entity catalog
     surfaces only;
   - recursive amendment, optimization entitlement, and broad whole-repo mutation logic
     remain deferred.
2. Snapshot authority strategy:
   - all emitted artifacts must bind to one explicit repo-visible snapshot identity and
     source-set posture;
   - stale-snapshot semantics must be explicit rather than implied;
   - outputs are valid for the bound snapshot only and become historical evidence rather
     than current repo truth once that snapshot is stale;
   - cross-snapshot comparison remains deferred to later `V45` lanes.
3. Entity taxonomy strategy:
   - entity classification must remain multi-axis across:
     - surface kind;
     - semantic role;
     - governance posture;
     - derivation posture;
     - mutation posture;
   - the first slice stays bounded to schema-visible and schema-adjacent surfaces;
   - the bounded issuance posture must be explicit in the artifact itself through an
     entity-coverage mode such as `bounded_schema_visible_slice`.
4. Schema registry strategy:
   - schema rows must carry one primary carrier class, optional secondary role-form
     tags, one lineage overlay, and named residual flags;
   - filename or naming-family cues are lower-precedence support only.
5. Registry layer distinction strategy:
   - `family_cluster` means observational grouping within the bounded schema corpus;
   - `primary_carrier_class` means dominant carrier-role posture for that schema row;
   - `lineage_overlay` means irreducible anchor or governance vocabulary family that
     persists even when carrier form is shared;
   - these three layers are non-equivalent and may not be silently collapsed into one
     another.
6. Classification precedence strategy:
   - schema role-form classification precedence is frozen to:
     - structural signature;
     - semantic function;
     - governance role;
     - lexical naming.
7. Classification policy strategy:
   - every emitted artifact must bind to one explicit classification-policy surface;
   - that policy binding must be immutable and inspectable through reference plus
     content hash posture;
   - `classification_policy_ref` may not point at interpretive air.
8. Epistemic posture strategy:
   - classifications must distinguish:
     - observed;
     - derived deterministically;
     - inferred heuristically;
     - adjudicated;
     - settled;
   - promotion law from inferred to adjudicated and adjudicated to settled must be
     explicit and inspectable;
   - `inferred -> adjudicated` must name admissible evidence kinds and an explicit
     adjudicator posture;
   - `adjudicated -> settled` must name admissible evidence kinds and may not be used
     as a decorative confidence badge;
   - for `V45-A`, settled posture should remain bounded to the representative
     reconstruction subset or rows backed by an explicit policy-bound adjudication
     surface.
9. Evidence strategy:
   - `supporting_evidence_refs` must remain typed rather than free-form;
   - admissible evidence kinds for this slice are:
     - observed anchor tuple evidence;
     - structural signature evidence;
     - semantic function cue evidence;
     - governance cue evidence;
     - lexical cue evidence;
     - adjudication artifact evidence;
     - reconstruction subset evidence.
10. Schema-core strategy:
   - the current best branch-local schema-core hypothesis is:
     - common core envelope
     - plus carrier overlays
     - plus lineage overlays
     - plus narrow named residuals;
   - this remains a bounded working hypothesis rather than settled ADEU constitution.
11. Reconstruction strategy:
   - one bounded representative subset must be decomposed into:
     - core envelope features;
     - carrier overlay;
     - lineage overlay;
     - residuals;
   - each representative schema must reconstruct back explicitly from that
     decomposition;
   - reconstruction success is judged by canonical normalized semantic equivalence over
     the schema definition, not byte-for-byte formatting identity.
12. Anti-overreach strategy:
   - `V45-A` may not claim whole-repo exhaustive classification;
   - `V45-A` may not turn descriptive findings into amendment or optimization
     entitlement;
   - `V45-A` may not reopen released `V41` or released meta-control semantics.

## Required Deliverables

1. New typed descriptive surfaces:
   - canonical `repo_schema_family_registry@1` artifact;
   - canonical bounded `repo_entity_catalog@1` artifact;
   - authoritative and mirrored schema export parity.
2. Deterministic extraction entrypoint(s) that:
   - consume one explicit repo snapshot or bounded source-set;
   - derive schema-family registry rows and schema-visible entity-catalog rows;
   - emit classification posture, classification method, typed supporting evidence refs,
     and immutable classification-policy binding;
   - fail closed on missing snapshot anchors, precedence contradictions, or unresolved
     required taxonomy fields.
3. Top-level schema anchors for `repo_schema_family_registry@1`:
   - `schema`
   - `schema_family_registry_id`
   - `repo_snapshot_id`
   - `repo_snapshot_hash`
   - `snapshot_validity_posture`
   - `source_set`
   - `classification_policy_ref`
   - `classification_policy_hash`
   - `reconstruction_equivalence_mode`
   - `schema_entries`
   - `reconstruction_subset`
   - `evidence_refs`
   - per evidence ref anchors:
     - `evidence_ref`
     - `evidence_kind`
   - per schema entry anchors:
     - `schema_key`
     - `schema_path`
     - `schema_discriminator`
     - `family_cluster`
     - `primary_carrier_class`
     - `secondary_role_form_tags`
     - `lineage_overlay`
     - `core_envelope_features`
     - `residual_flags`
     - `classification_posture`
     - `classification_method`
     - `adjudicator_ref`
     - `supporting_evidence_refs`
4. Top-level schema anchors for `repo_entity_catalog@1`:
   - `schema`
   - `repo_entity_catalog_id`
   - `repo_snapshot_id`
   - `repo_snapshot_hash`
   - `snapshot_validity_posture`
   - `catalog_scope`
   - `entity_coverage_mode`
   - `classification_policy_ref`
   - `classification_policy_hash`
   - `entities`
   - `evidence_refs`
   - per evidence ref anchors:
     - `evidence_ref`
     - `evidence_kind`
   - per entity entry anchors:
     - `entity_ref`
     - `surface_kind`
     - `semantic_role`
     - `governance_posture`
     - `derivation_posture`
     - `mutation_posture`
     - `classification_posture`
     - `classification_method`
     - `adjudicator_ref`
     - `supporting_evidence_refs`
5. Deterministic laws that fail closed on at least:
   - any emitted artifact missing repo snapshot identity or hash binding;
   - any emitted artifact missing immutable classification-policy binding through
     reference plus hash;
   - any schema row missing primary carrier class, lineage overlay, or classification
     posture;
   - any schema row that silently collapses `family_cluster`, `primary_carrier_class`,
     and `lineage_overlay` into one interchangeable field;
   - any schema role-form classification justified only by lexical naming when stronger
     structural or semantic evidence is required;
   - any schema row that settles cleanly despite a precedence contradiction where
     lexical naming points one way and stronger structural or semantic evidence points
     another;
   - any schema row claiming settled posture without explicit adjudication support;
   - any supporting evidence ref emitted without one of the allowed typed evidence
     kinds for this slice;
   - any representative reconstruction row that does not reconstruct back to the
     concrete schema definition under canonical normalized semantic equivalence;
   - any entity row missing one of the five required taxonomy axes;
   - any entity-catalog artifact missing explicit bounded coverage mode for the first
     slice;
   - any descriptive output that launders mutation, recursive-amendment, or optimization
     entitlement from diagnostics alone;
   - any stale-snapshot output treated as current repo truth rather than historical
     evidence bound to its original snapshot;
   - any slice widening into symbol catalog, test-intent matrix, or optimization
     register release.
6. Committed reference fixtures under `apps/api/fixtures/repo_description/vnext_plus99/`:
   - one accepted schema-family registry reference fixture;
   - one accepted bounded entity-catalog reference fixture;
   - one rejected registry fixture with missing snapshot identity;
   - one rejected registry fixture with unresolved primary carrier class;
   - one rejected registry fixture with naming-only role-form classification;
   - one rejected registry fixture with settled posture but no admissible adjudication
     support;
   - one rejected registry fixture with precedence contradiction between lexical naming
     and stronger structural or semantic evidence;
   - one rejected entity-catalog fixture with missing taxonomy axis;
   - one rejected reconstruction appendix fixture with non-round-tripping decomposition.
7. Python tests covering:
   - schema/model validation for the two descriptive artifacts;
   - authoritative/mirrored schema parity;
   - deterministic replay for the accepted reference fixtures;
   - rejection of snapshot/precedence/posture/taxonomy/reconstruction contradictions.

## Hard Constraints

- `vNext+99` may not reopen or redefine released `V41` or released meta-control
  contracts.
- `vNext+99` may not widen into recursive amendment authority, optimization entitlement,
  symbol catalog release, test-intent matrix release, or mutation recommendation.
- `vNext+99` must keep descriptive findings non-promotional.
- `vNext+99` must keep schema role-form classification explicit, inspectable, and
  precedence-bound.
- `vNext+99` must keep classification-policy binding explicit and immutable.
- `vNext+99` must keep the schema-core hypothesis branch-local and auditable through a
  bounded reconstruction subset.
- `vNext+99` must keep round-trip reconstruction bound to canonical normalized semantic
  equivalence rather than byte identity.
- `vNext+99` may not treat lexical naming alone as sufficient schema-role authority.
- `vNext+99` must keep outputs snapshot-bound and historical when stale.
- `vNext+99` may not claim whole-repo exhaustive coverage from the first slice.

## PR Shape

- Single integrated PR within one arc.

Rationale:

- schema-registry schema release, bounded entity-catalog scaffolding, representative
  reconstruction appendix, fixture ladder, and fail-closed validation are one tightly
  coupled seam;
- splitting them across multiple PRs would create temporary contract drift for the same
  bounded `V45-A` lane.
