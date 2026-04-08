# Locked Continuation vNext+141

Status: `V53-A` implementation contract.

Authority layer: lock.

## V141 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v53a_edge_taxonomy_applicability_contract@1",
  "target_arc": "vNext+141",
  "target_path": "V53-A",
  "target_scope": "bounded_repo_owned_edge_taxonomy_and_symbol_applicability_substrate_over_released_v45_and_v50_architecture_ir_pilot_scope",
  "implementation_packages": [
    "adeu_edge_ledger"
  ],
  "governing_released_stack": "V45_repo_description_plus_V50A_symbol_census_coverage_plus_V50B_symbol_semantic_audit_on_main",
  "governing_stack_consumption_mode": "released_symbol_identity_scope_census_coverage_and_semantic_audit_consumption_only_not_reopened_v45_description_semantics_not_reopened_v50_scope_identity_coverage_or_semantic_audit_semantics",
  "source_intake_bundle": "examples/external_prototypes/adeu-edge-ledger-change-bundle",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "slice_support_mapping_doc": "docs/DRAFT_ADEU_EDGE_LEDGER_V53A_IMPLEMENTATION_MAPPING_v0.md",
  "edge_ledger_package_scaffold_required": true,
  "released_v45_symbol_identity_helper_reuse_required": true,
  "released_v50_scope_manifest_required": true,
  "released_v50_census_required": true,
  "released_v50_closed_clean_coverage_required": true,
  "released_v50_semantic_audit_required": true,
  "single_released_scope_manifest_input_initially_required": true,
  "single_released_census_input_initially_required": true,
  "single_released_closed_clean_coverage_input_initially_required": true,
  "single_released_semantic_audit_input_initially_required": true,
  "selected_schema_ids": [
    "adeu_edge_class_catalog@1",
    "adeu_edge_probe_template_catalog@1",
    "adeu_symbol_edge_applicability_frame@1"
  ],
  "starter_taxonomy_three_level_structure_required": true,
  "starter_catalogs_and_applicability_only_selected_here": true,
  "starter_applicability_frame_full_catalog_coverage_required": true,
  "starter_top_level_family_refs_frozen": [
    "input_domain",
    "boundary_order",
    "control_partition",
    "state_sequence",
    "canonicalization_representation",
    "contract_invariant",
    "dependency_boundary",
    "failure_path"
  ],
  "starter_node_kind_vocabulary_frozen": [
    "family",
    "subfamily",
    "archetype"
  ],
  "starter_lifecycle_posture_vocabulary_frozen": [
    "candidate",
    "stabilized",
    "split",
    "merged",
    "deprecated"
  ],
  "starter_probe_execution_postures_frozen": [
    "example_tests",
    "property_based",
    "metamorphic",
    "review_only"
  ],
  "starter_probe_strategy_kinds_frozen": [
    "absence_matrix",
    "shape_matrix",
    "boundary_partition",
    "ordering_permutation",
    "branch_partition",
    "state_sequence",
    "round_trip",
    "hash_consistency",
    "cross_field_invariant",
    "dependency_boundary",
    "fail_closed_rejection",
    "manual_adjudication"
  ],
  "starter_applicability_status_vocabulary_frozen": [
    "applicable",
    "not_applicable",
    "underdetermined"
  ],
  "starter_epistemic_posture_vocabulary_frozen": [
    "observed",
    "derived_deterministically",
    "inferred_heuristically",
    "adjudicated",
    "settled"
  ],
  "explicit_override_input_not_selected_here": true,
  "adjudication_ledger_deferred_to_v53b": true,
  "proof_grade_status_promotion_forbidden_in_v53a": true,
  "revision_register_deferred_to_v53c": true,
  "test_intent_integration_deferred_to_v53d": true,
  "authoritative_and_mirrored_schema_export_parity_required_if_schema_files_committed": true,
  "reference_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v36.md",
    "docs/DRAFT_ADEU_EDGE_LEDGER_V53_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_EDGE_LEDGER_V53A_IMPLEMENTATION_MAPPING_v0.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS101.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS121.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS122.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS123.md",
    "examples/external_prototypes/adeu-edge-ledger-change-bundle/ALIGNMENT.md",
    "examples/external_prototypes/adeu-edge-ledger-change-bundle/CLAIMED_SCOPE.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v36.md"
}
```

## Slice

- Arc label: `vNext+141`
- Family label: `V53-A`
- Scope label: bounded repo-owned edge taxonomy and symbol-applicability substrate
  over the released `adeu_architecture_ir` pilot scope already frozen by `V50`

## Objective

Release the bounded `V53-A` starter seam by creating the first repo-owned
`adeu_edge_ledger` package and freezing one adjacent taxonomy-plus-applicability layer
rich enough to:

- publish one stable edge-class catalog with explicit three-level taxonomy;
- publish one stable probe-template catalog bound to that taxonomy;
- publish one full symbol-local applicability frame over every admitted archetype for
  each admitted released `V50` symbol;
- consume released `V45` symbol identity and released `V50` scope / census / coverage
  / semantic-audit artifacts without reopening their semantics;
- keep adjudication, explicit override law, cumulative revision/register law, and
  test-intent integration deferred until later `V53` slices.

This slice is package-first, taxonomy-first, and applicability-first. It does not
authorize:

- `adeu_symbol_edge_adjudication_ledger@1`;
- explicit witness or checked-no-witness override channels;
- `covered_by_existing_tests` or `bounded_safe_by_structure` as released statuses;
- revision-register or split/merge history surfaces;
- direct joins to released `V45-D` test-intent artifacts;
- probe execution, mutation, CLI/API/web consumers, or repo-wide scope widening.

## Required Deliverables

The first `V53-A` release should add exactly these live implementation surfaces:

- `packages/adeu_edge_ledger/pyproject.toml`
- `packages/adeu_edge_ledger/src/adeu_edge_ledger/__init__.py`
- `packages/adeu_edge_ledger/src/adeu_edge_ledger/models.py`
- `packages/adeu_edge_ledger/src/adeu_edge_ledger/taxonomy.py`
- `packages/adeu_edge_ledger/src/adeu_edge_ledger/applicability.py`
- `packages/adeu_edge_ledger/src/adeu_edge_ledger/export_schema.py`
- package schema exports under:
  - `packages/adeu_edge_ledger/schema/`
- root schema mirrors under:
  - `spec/`
- targeted tests under:
  - `packages/adeu_edge_ledger/tests/`
- deterministic committed fixtures under:
  - `packages/adeu_edge_ledger/tests/fixtures/v53a/`

This slice should not add:

- `packages/adeu_edge_ledger/src/adeu_edge_ledger/adjudicate.py`
- `packages/adeu_edge_ledger/src/adeu_edge_ledger/revision.py`
- direct `V45-D` test-intent joins
- probe execution or witness artifact families
- API or web consumer surfaces
- a second package owner surface

## Frozen Implementation Decisions

1. Package ownership and authority posture:
   - `packages/adeu_edge_ledger` is the sole implementation owner in this slice;
   - the imported edge-ledger bundle remains shaping evidence only and may not be
     treated as live package or schema authority;
   - released `V45` and `V50` contracts remain upstream inputs only and may not be
     reopened or forked here.
2. Upstream released-input posture:
   - `V53-A` consumes exactly one released `adeu_symbol_audit_scope_manifest@1`, one
     released `adeu_symbol_census@1`, one released
     `adeu_symbol_audit_coverage_report@1` with `coverage_status = closed_clean`, and
     one released `adeu_symbol_semantic_audit@1`;
   - the consumed `scope_manifest_ref` / `census_hash` / `symbol_id` relationships
     must remain exact and fail closed on mismatch;
   - `V53-A` must import one canonical released symbol-id helper from the released
     `V45` / `V50` stack rather than duplicating symbol-id law locally.
3. Pilot-scope posture:
   - the starter slice remains bound to the released `V50` pilot scope only:
     - `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py`
     - `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_settlement.py`
     - `packages/adeu_architecture_ir/src/adeu_architecture_ir/export_schema.py`
   - no repo-wide or second-package scope widening is authorized in `V53-A`.
4. Output-family posture:
   - `V53-A` releases exactly three new repo-owned contracts:
     - `adeu_edge_class_catalog@1`
     - `adeu_edge_probe_template_catalog@1`
     - `adeu_symbol_edge_applicability_frame@1`
   - `V53-A` does not release:
     - `adeu_symbol_edge_adjudication_ledger@1`
     - `adeu_edge_taxonomy_revision_judgment@1`
5. Taxonomy posture:
   - the starter taxonomy must remain exactly three levels deep:
     - `family`
     - `subfamily`
     - `archetype`
   - the top-level family vocabulary must remain exactly:
     - `input_domain`
     - `boundary_order`
     - `control_partition`
     - `state_sequence`
     - `canonicalization_representation`
     - `contract_invariant`
     - `dependency_boundary`
     - `failure_path`
   - archetype nodes must carry explicit cue tags and default probe-template refs;
   - the starter catalog is a bounded serious taxonomy, not a flat witness label list.
6. Probe-template posture:
   - probe templates remain declarative and advisory in `V53-A`;
   - admitted execution postures remain exactly:
     - `example_tests`
     - `property_based`
     - `metamorphic`
     - `review_only`
   - admitted strategy kinds remain exactly the frozen starter vocabulary in the
     machine-checkable contract above;
   - no probe execution, witness artifact, or checked-no-witness artifact is selected
     here.
7. Applicability-frame posture:
   - every emitted applicability frame must bind:
     - one edge-class catalog ref
     - one probe-template catalog ref
     - one released scope manifest ref
     - one released census hash
     - one released semantic-audit hash
     - one released symbol id / module path / qualname / symbol kind tuple
   - every emitted applicability frame must materialize one row for every admitted
     archetype, not only positive matches;
   - every applicability row must carry:
     - `edge_class_ref`
     - `applicability_status`
     - `epistemic_posture`
     - `rationale`
   - optional support fields may include:
     - `matched_cue_tags`
     - `concrete_binding_refs`
     - `suggested_probe_template_refs`
8. Evidence and non-overclaim posture:
   - lexical test adjacency, test-token overlap, or structural-safety cues may support
     applicability reasoning only;
   - they may not be promoted in `V53-A` into released adjudication statuses or
     proof-grade safety claims;
   - explicit witness input, explicit checked-no-witness input, contradictory
     overrides, and out-of-frame overrides are all deferred to later `V53-B`
     constitutional selection rather than half-selected here.
9. Deferred-seam posture:
   - `V53-B` owns adjudication law and explicit fail-closed override law;
   - `V53-C` owns cumulative revision/register and split/merge/deprecate history;
   - `V53-D` owns any later bounded join to released `V45-D` test-intent surfaces or
     broader probe/test integration;
   - `V53-A` may constrain those later seams, but may not mint them.
10. Schema-export posture:
    - if schema files are committed, authoritative package exports and root `spec/`
      mirrors must match exactly;
    - repo-native schema export parity is required before the slice can be accepted.

## Bounded Starter Vocabularies

The first `V53-A` release should freeze bounded starter vocabularies rather than leave
taxonomy or applicability semantics to implementation taste.

The intended bounded starter vocabularies are:

- `node_kind`:
  - `family`
  - `subfamily`
  - `archetype`
- `lifecycle_posture`:
  - `candidate`
  - `stabilized`
  - `split`
  - `merged`
  - `deprecated`
- `probe_execution_posture`:
  - `example_tests`
  - `property_based`
  - `metamorphic`
  - `review_only`
- `probe_strategy_kind`:
  - `absence_matrix`
  - `shape_matrix`
  - `boundary_partition`
  - `ordering_permutation`
  - `branch_partition`
  - `state_sequence`
  - `round_trip`
  - `hash_consistency`
  - `cross_field_invariant`
  - `dependency_boundary`
  - `fail_closed_rejection`
  - `manual_adjudication`
- `applicability_status`:
  - `applicable`
  - `not_applicable`
  - `underdetermined`
- `epistemic_posture`:
  - `observed`
  - `derived_deterministically`
  - `inferred_heuristically`
  - `adjudicated`
  - `settled`
- `symbol_kind` admitted from the released `V50` stack:
  - `class`
  - `function`
  - `method`
  - `local_function`

Out-of-scope constructs in this slice are:

- adjudication statuses such as `covered_by_existing_tests`,
  `checked_no_witness_found`, `bounded_safe_by_structure`, or `witness_found`;
- explicit override or probe-outcome input;
- revision-judgment or cumulative-register status vocabularies;
- repo-wide scope widening;
- direct `V45-D` test-intent joins;
- probe execution or witness materialization surfaces.

## Selected Schema Anchors

The first `V53-A` release should freeze the following contract anchors.

1. `adeu_edge_class_catalog@1`
   - `schema`
   - `catalog_id`
   - `catalog_name`
   - `catalog_version`
   - `catalog_posture`
   - ordered `nodes`
   - `catalog_hash`
   - per node:
     - `edge_class_ref`
     - `parent_edge_class_ref`
     - `node_kind`
     - `short_label`
     - `summary`
     - `required_cue_tags`
     - `supporting_cue_tags`
     - `structural_safety_cue_tags`
     - `test_token_tags`
     - `default_probe_template_refs`
     - `lifecycle_posture`
2. `adeu_edge_probe_template_catalog@1`
   - `schema`
   - `catalog_id`
   - `catalog_name`
   - `catalog_version`
   - `bound_edge_class_catalog_ref`
   - ordered `probe_templates`
   - `catalog_hash`
   - per probe template:
     - `probe_template_ref`
     - `strategy_kind`
     - ordered `execution_postures`
     - `short_label`
     - `summary`
     - ordered `suited_edge_class_refs`
     - ordered `required_signal_tags`
     - `lifecycle_posture`
3. `adeu_symbol_edge_applicability_frame@1`
   - `schema`
   - `frame_id`
   - `bound_edge_class_catalog_ref`
   - `bound_probe_template_catalog_ref`
   - `scope_manifest_ref`
   - `census_hash`
   - `audit_hash`
   - `symbol_id`
   - `module_path`
   - `qualname`
   - `symbol_kind`
   - `frame_posture`
   - ordered `applicability_rows`
   - `frame_hash`
   - per applicability row:
     - `edge_class_ref`
     - `applicability_status`
     - `epistemic_posture`
     - ordered `matched_cue_tags`
     - ordered `concrete_binding_refs`
     - ordered `suggested_probe_template_refs`
     - `rationale`

## Acceptance-Fixture Set

The first `V53-A` release should include deterministic fixtures rich enough to prove:

- one accepted edge-class catalog fixture with lawful family/subfamily/archetype
  hierarchy and archetype-bound default probe refs;
- one accepted probe-template catalog fixture bound to that edge-class catalog;
- one accepted applicability-frame fixture whose rows positively exercise all three
  starter applicability statuses:
  - `applicable`
  - `not_applicable`
  - `underdetermined`
- one reject fixture proving non-`closed_clean` coverage input fails closed;
- one reject fixture proving local symbol-id drift or duplicate local identity law is
  not accepted;
- one reject fixture proving sparse applicability output that omits admitted
  archetypes fails closed;
- one reject fixture proving adjudication-only fields or explicit override inputs are
  not accepted in `V53-A`.

## Accept When

`V53-A` should be accepted only if all of the following are true:

- the three new starter contracts validate and export cleanly;
- `packages/adeu_edge_ledger` remains the only active implementation package for the
  slice;
- the starter taxonomy remains exactly three levels deep and keeps the frozen
  top-level family vocabulary;
- the probe-template catalog remains declarative and bound to the released taxonomy;
- every applicability frame binds one released `V50` artifact stack and one released
  symbol identity from the admitted pilot scope only;
- every applicability frame materializes a deterministic row for every admitted
  archetype rather than only positive matches;
- applicability reasoning stays explicit about epistemic posture and cue/rationale
  support;
- lexical test adjacency and structural-safety cues remain support for applicability
  reasoning only and are not promoted into adjudication or proof-grade status;
- the implementation reuses one released symbol-id helper rather than duplicating
  symbol identity law locally;
- targeted fixtures cover all starter applicability statuses plus fail-closed reject
  cases;
- root `spec/` mirrors match authoritative package schema exports.

## Do Not Accept If

Do not accept `V53-A` if:

- the slice ships `adeu_symbol_edge_adjudication_ledger@1` or
  `adeu_edge_taxonomy_revision_judgment@1`;
- explicit witness, checked-no-witness, contradictory override, or out-of-frame
  override inputs are admitted in the starter slice;
- the slice reopens released `V45` / `V50` scope, symbol-id, coverage, or semantic
  audit law;
- the slice widens beyond the exact released `adeu_architecture_ir` pilot scope;
- sparse positive-only applicability output replaces full archetype-addressable
  applicability frames;
- package-local test scanning, lexical adjacency, or structural cues are over-read as
  proof-grade safety or correctness claims;
- direct `V45-D` test-intent integration, probe execution, runtime mutation, API/web,
  or repo-wide scope widening appears in the starter lane.

## Local Gate

- run `make arc-start-check ARC=141`
