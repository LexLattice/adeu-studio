# Locked Continuation vNext+145

Status: `V53-C` implementation contract.

Authority layer: lock.

## V145 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v53c_edge_taxonomy_revision_register_contract@1",
  "target_arc": "vNext+145",
  "target_path": "V53-C",
  "target_scope": "bounded_repo_owned_cumulative_edge_taxonomy_revision_register_over_released_v53a_and_v53b_surfaces",
  "implementation_packages": [
    "adeu_edge_ledger"
  ],
  "governing_released_stack": "released_v53a_edge_class_catalog_plus_probe_template_catalog_plus_symbol_edge_applicability_frame_plus_released_v53b_symbol_edge_adjudication_ledger_on_arc_v53_r4",
  "governing_stack_consumption_mode": "released_v53a_and_v53b_consumption_only_not_reopened",
  "source_intake_bundle": "examples/external_prototypes/adeu-edge-ledger-change-bundle",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "family_support_mapping_doc": "docs/DRAFT_ADEU_EDGE_LEDGER_V53_IMPLEMENTATION_MAPPING_v0.md",
  "slice_support_mapping_doc": "docs/DRAFT_ADEU_EDGE_LEDGER_V53C_IMPLEMENTATION_MAPPING_v0.md",
  "released_v53a_edge_class_catalog_required": true,
  "released_v53a_probe_template_catalog_required": true,
  "released_v53a_symbol_edge_applicability_frame_required": true,
  "released_v53b_symbol_edge_adjudication_ledger_required": true,
  "single_released_symbol_edge_adjudication_ledger_input_initially_required": true,
  "prior_revision_register_input_optional_for_starter_append": true,
  "selected_schema_ids": [
    "adeu_edge_taxonomy_revision_register@1"
  ],
  "starter_revision_decision_vocabulary_frozen": [
    "stabilize_existing_class",
    "split_existing_class",
    "merge_existing_classes",
    "deprecate_existing_class"
  ],
  "starter_lineage_parent_ref_support_required": true,
  "starter_supporting_adjudication_row_refs_required": true,
  "starter_register_append_only_history_required": true,
  "starter_register_entry_ordering_law": "stable_append_order_with_duplicate_entry_ids_forbidden",
  "starter_unknown_parent_entry_ref_must_fail_closed": true,
  "starter_lineage_cycle_must_fail_closed": true,
  "starter_decision_shape_must_fail_closed": true,
  "starter_soft_evidence_promotion_forbidden": true,
  "starter_live_taxonomy_mutation_forbidden": true,
  "starter_probe_strategy_and_test_intent_integration_deferred_to_v53d": true,
  "authoritative_and_mirrored_schema_export_parity_required_if_schema_files_committed": true,
  "reference_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v36.md",
    "docs/DRAFT_ADEU_EDGE_LEDGER_V53_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_EDGE_LEDGER_V53C_IMPLEMENTATION_MAPPING_v0.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS141.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS143.md",
    "examples/external_prototypes/adeu-edge-ledger-change-bundle/ALIGNMENT.md",
    "examples/external_prototypes/adeu-edge-ledger-change-bundle/CLAIMED_SCOPE.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v36.md"
}
```

## Slice

- Arc label: `vNext+145`
- Family label: `V53-C`
- Scope label: bounded cumulative revision register / lineage lane over released
  `V53-A` taxonomy/applicability and released `V53-B` adjudication outputs only

## Objective

Release the bounded `V53-C` revision/register seam by adding one repo-owned
`adeu_edge_taxonomy_revision_register@1` contract rich enough to:

- consume one released `V53-B` symbol-edge adjudication ledger without reopening
  released `V53-A` or released `V53-B` law;
- accumulate ordered revision entries through append-only register semantics,
  optionally extending one prior released `V53-C` register;
- freeze one exact starter decision vocabulary for:
  - `stabilize_existing_class`
  - `split_existing_class`
  - `merge_existing_classes`
  - `deprecate_existing_class`
- freeze one exact fail-closed lineage law for:
  - unknown lineage parent refs
  - lineage cycles
  - decision-shape and lifecycle mismatches
- keep direct probe/test-intent widening deferred to `V53-D`.

This slice is register-first and lineage-first. It does not authorize:

- reopening released `V53-A` taxonomy/applicability law or released `V53-B`
  adjudication law;
- direct joins to released `V45-D` test-intent artifacts;
- probe strategy or witness-input widening beyond the released adjudication ledger;
- live taxonomy mutation helpers or automatic catalog rewrites;
- repo-wide scope widening or second-package ownership.

## Required Deliverables

The first `V53-C` release should add exactly these live implementation surfaces:

- `packages/adeu_edge_ledger/src/adeu_edge_ledger/models.py`
- `packages/adeu_edge_ledger/src/adeu_edge_ledger/revision.py`
- `packages/adeu_edge_ledger/src/adeu_edge_ledger/export_schema.py`
- package schema exports under:
  - `packages/adeu_edge_ledger/schema/`
- root schema mirrors under:
  - `spec/`
- targeted tests under:
  - `packages/adeu_edge_ledger/tests/`
- deterministic committed fixtures under:
  - `packages/adeu_edge_ledger/tests/fixtures/v53c/`

This slice should not add:

- direct `V45-D` test-intent joins;
- probe/test-intent execution helpers;
- live taxonomy migration helpers that rewrite released catalogs;
- repo-wide scope widening beyond released `V53-A` pilot scope and released `V53-B`
  consumption;
- second package owner surfaces or broader reviewer-platform work.

## Frozen Implementation Decisions

1. Package ownership and authority posture:
   - `packages/adeu_edge_ledger` remains the sole implementation owner in this slice;
   - the imported edge-ledger bundle remains shaping evidence only and may not be
     treated as live package or schema authority;
   - released `V53-A` and released `V53-B` contracts remain authoritative upstream
     inputs only and may not be reopened or weakened here.
2. Upstream released-input posture:
   - `V53-C` consumes one released `adeu_symbol_edge_adjudication_ledger@1`;
   - the consumed ledger must already bind one released `adeu_edge_class_catalog@1`,
     one released `adeu_edge_probe_template_catalog@1`, one released
     `adeu_symbol_edge_applicability_frame@1`, and one released symbol identity tuple;
   - starter `V53-C` may optionally extend one prior released `V53-C` register, but
     only if that prior register stays bound to the same released catalog/probe
     baseline family and remains append-compatible.
3. Output-family posture:
   - `V53-C` releases exactly one new repo-owned contract:
     - `adeu_edge_taxonomy_revision_register@1`
   - `V53-C` does not release:
     - direct `V45-D` test-intent integration surfaces
     - live taxonomy migration/execution helpers
     - second package owner surfaces
4. Register top-level posture:
   - every emitted revision register must bind:
     - one released edge-class catalog ref
     - one released probe-template catalog ref
     - one current released adjudication ledger ref
     - optional prior revision register ref
   - every emitted revision register must preserve prior entry order exactly when a
     prior register is extended and may not silently renumber, rewrite, or collapse
     preserved history;
   - every new register entry must carry:
     - `revision_entry_ref`
     - `revision_decision`
     - ordered `subject_edge_class_refs`
     - ordered `candidate_edge_class_refs`
     - `supporting_adjudication_ledger_ref`
     - ordered `supporting_adjudication_row_refs`
     - ordered `lineage_parent_entry_refs`
     - `proposed_lifecycle_posture`
     - `rationale`
5. Exact starter decision-shape law:
   - `stabilize_existing_class` must carry exactly one existing
     `subject_edge_class_ref`, empty `candidate_edge_class_refs`, and
     `proposed_lifecycle_posture = stabilized`;
   - `split_existing_class` must carry exactly one existing `subject_edge_class_ref`,
     non-empty `candidate_edge_class_refs`, and
     `proposed_lifecycle_posture = split`;
   - `merge_existing_classes` must carry at least two existing
     `subject_edge_class_refs`, exactly one `candidate_edge_class_ref`, and
     `proposed_lifecycle_posture = merged`;
   - `deprecate_existing_class` must carry exactly one existing
     `subject_edge_class_ref`, empty `candidate_edge_class_refs`, and
     `proposed_lifecycle_posture = deprecated`;
   - any other decision/posture/shape combination must fail closed.
6. Exact starter lineage law:
   - `revision_entry_ref` values must be unique within one emitted register;
   - `lineage_parent_entry_refs`, when present, must resolve only to earlier entries in
     the same emitted register or earlier entries carried through the bound prior
     register;
   - parent refs may not point forward, may not be duplicated, and may not form
     cycles;
   - starter append semantics must preserve all prior entry order and append new
     entries only after the preserved prefix.
7. Exact starter adjudication-support law:
   - every `supporting_adjudication_row_ref` must resolve against the bound released
     adjudication ledger;
   - starter revision entries may cite only adjudication rows whose
     `adjudication_status` is `witness_found`, `checked_no_witness_found`, or
     `deferred`;
   - `applicable_unchecked`, `underdetermined`, and `not_applicable` rows are
     insufficient by themselves to mint starter register entries;
   - lexical test adjacency, structural cue overlap, or implied test coverage remain
     insufficient by themselves to mint starter register entries.
8. Live-taxonomy-boundary law:
   - emitted register entries may propose cumulative history over released edge-class
     refs and candidate successor refs only;
   - emitted register entries may not mutate the released
     `adeu_edge_class_catalog@1` or `adeu_edge_probe_template_catalog@1` inside
     `V53-C`;
   - split/merge/deprecate history becomes typed register evidence first, not
     automatic catalog execution.
9. Fixture and testing posture:
   - starter fixtures must include positive reference registers for:
     - an initial register without prior history
     - an append-only extension over prior register history
     - one example each for `stabilize_existing_class`, `split_existing_class`,
       `merge_existing_classes`, and `deprecate_existing_class`
   - starter reject fixtures must include at least:
     - unknown lineage parent ref
     - lineage cycle
     - invalid decision-shape or lifecycle combination
     - unsupported adjudication row status used as sole register support
   - no starter fixture may rely on direct `V45-D` test-intent input or live taxonomy
     mutation side effects.

## Consequence

If `V53-C` lands as specified, ADEU will have:

- one repo-owned cumulative revision register surface downstream of released `V53-A`
  and released `V53-B`;
- one explicit append-only lineage law instead of isolated one-off revision judgments;
- one typed record of stabilize/split/merge/deprecate history over adjudicated edge
  findings;
- no direct probe/test-intent widening yet.

If this contract is violated, the implementation is not a bounded `V53-C` release. It
is either:

- an under-specified reopening of released `V53-A` or released `V53-B` law;
- an over-broad mutation lane disguised as register evidence; or
- a premature widening into `V53-D`.
