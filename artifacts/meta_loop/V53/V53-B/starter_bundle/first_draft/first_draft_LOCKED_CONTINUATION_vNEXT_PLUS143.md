# Locked Continuation vNext+143

Status: `V53-B` implementation contract.

Authority layer: lock.

## V143 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v53b_edge_adjudication_contract@1",
  "target_arc": "vNext+143",
  "target_path": "V53-B",
  "target_scope": "bounded_repo_owned_symbol_edge_adjudication_ledger_over_released_v53a_taxonomy_and_applicability",
  "implementation_packages": [
    "adeu_edge_ledger"
  ],
  "governing_released_stack": "released_v53a_edge_class_catalog_plus_probe_template_catalog_plus_symbol_edge_applicability_frame_on_arc_v53_r3",
  "governing_stack_consumption_mode": "released_v53a_taxonomy_probe_template_and_applicability_consumption_only_not_reopened",
  "source_intake_bundle": "examples/external_prototypes/adeu-edge-ledger-change-bundle",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "family_support_mapping_doc": "docs/DRAFT_ADEU_EDGE_LEDGER_V53_IMPLEMENTATION_MAPPING_v0.md",
  "slice_support_mapping_doc": "docs/DRAFT_ADEU_EDGE_LEDGER_V53B_IMPLEMENTATION_MAPPING_v0.md",
  "released_v53a_edge_class_catalog_required": true,
  "released_v53a_probe_template_catalog_required": true,
  "released_v53a_symbol_edge_applicability_frame_required": true,
  "single_released_symbol_edge_applicability_frame_input_initially_required": true,
  "selected_schema_ids": [
    "adeu_symbol_edge_adjudication_ledger@1"
  ],
  "starter_adjudication_status_vocabulary_frozen": [
    "not_applicable",
    "applicable_unchecked",
    "witness_found",
    "checked_no_witness_found",
    "underdetermined",
    "deferred"
  ],
  "starter_override_channels_frozen": [
    "witness_summaries",
    "checked_no_witness_edge_class_refs"
  ],
  "starter_status_support_field_shape_required": true,
  "starter_full_catalog_row_coverage_required": true,
  "starter_row_order_must_match_released_v53a_catalog_order": true,
  "starter_row_mapping_law_frozen": true,
  "starter_contradictory_override_input_must_fail_closed": true,
  "starter_out_of_frame_override_input_must_fail_closed": true,
  "starter_not_applicable_override_input_must_fail_closed": true,
  "starter_underdetermined_positive_promotion_forbidden": true,
  "starter_lexical_test_adjacency_not_sufficient_for_positive_status": true,
  "starter_structural_cue_overlap_not_sufficient_for_positive_status": true,
  "starter_forbidden_status_vocabulary_in_emitted_artifacts": [
    "covered_by_existing_tests",
    "bounded_safe_by_structure"
  ],
  "starter_revision_register_deferred_to_v53c": true,
  "starter_test_intent_integration_deferred_to_v53d": true,
  "authoritative_and_mirrored_schema_export_parity_required_if_schema_files_committed": true,
  "reference_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v36.md",
    "docs/DRAFT_ADEU_EDGE_LEDGER_V53_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_EDGE_LEDGER_V53B_IMPLEMENTATION_MAPPING_v0.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS141.md",
    "examples/external_prototypes/adeu-edge-ledger-change-bundle/ALIGNMENT.md",
    "examples/external_prototypes/adeu-edge-ledger-change-bundle/CLAIMED_SCOPE.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v36.md"
}
```

## Slice

- Arc label: `vNext+143`
- Family label: `V53-B`
- Scope label: bounded symbol-edge adjudication hardening over released `V53-A`
  taxonomy, probe-template, and applicability outputs only

## Objective

Release the bounded `V53-B` adjudication seam by adding one repo-owned
`adeu_symbol_edge_adjudication_ledger@1` contract rich enough to:

- consume one released `V53-A` symbol-edge applicability frame without reopening its
  row-decision law;
- materialize one full edge-class-addressable adjudication ledger over that released
  frame;
- freeze one exact fail-closed override law for:
  - contradictory explicit overrides
  - out-of-frame explicit overrides
  - applicability-violating explicit overrides
- freeze one exact evidence/status law that distinguishes:
  - explicit witness evidence
  - explicit checked-no-witness evidence
  - carried-forward non-adjudicated applicability
  without promoting lexical test adjacency or structural cue overlap into proof;
- keep cumulative revision/register semantics deferred to `V53-C` and any direct
  test-intent integration deferred to `V53-D`.

This slice is adjudication-first and evidence-law-first. It does not authorize:

- cumulative revision lineage/register surfaces;
- direct joins to released `V45-D` test-intent artifacts;
- release of `covered_by_existing_tests` or `bounded_safe_by_structure` as starter
  adjudication statuses;
- repo-wide scope widening or second-package ownership;
- probe execution, mutation, CLI/API/web consumers, or broader reviewer platform work.

## Required Deliverables

The first `V53-B` release should add exactly these live implementation surfaces:

- `packages/adeu_edge_ledger/src/adeu_edge_ledger/models.py`
- `packages/adeu_edge_ledger/src/adeu_edge_ledger/adjudication.py`
- `packages/adeu_edge_ledger/src/adeu_edge_ledger/export_schema.py`
- package schema exports under:
  - `packages/adeu_edge_ledger/schema/`
- root schema mirrors under:
  - `spec/`
- targeted tests under:
  - `packages/adeu_edge_ledger/tests/`
- deterministic committed fixtures under:
  - `packages/adeu_edge_ledger/tests/fixtures/v53b/`

This slice should not add:

- `packages/adeu_edge_ledger/src/adeu_edge_ledger/revision.py`
- direct `V45-D` test-intent joins
- repo-wide scope widening beyond the released `V53-A` pilot scope
- second package owner surfaces
- proof-grade or benchmark-style evidence consumers

## Frozen Implementation Decisions

1. Package ownership and authority posture:
   - `packages/adeu_edge_ledger` remains the sole implementation owner in this slice;
   - the imported edge-ledger bundle remains shaping evidence only and may not be
     treated as live package or schema authority;
   - released `V53-A` contracts remain authoritative upstream inputs only and may not
     be reopened or weakened here.
2. Upstream released-input posture:
   - `V53-B` consumes one released `adeu_symbol_edge_applicability_frame@1`;
   - the consumed frame must already bind one released `adeu_edge_class_catalog@1`,
     one released `adeu_edge_probe_template_catalog@1`, one released scope manifest
     ref, one released census hash, and one released semantic-audit hash;
   - `V53-B` may not reclassify released applicability rows or change the released
     row-order law.
3. Output-family posture:
   - `V53-B` releases exactly one new repo-owned contract:
     - `adeu_symbol_edge_adjudication_ledger@1`
   - `V53-B` does not release:
     - `adeu_edge_taxonomy_revision_judgment@1`
     - cumulative revision lineage/register surfaces
     - direct `V45-D` test-intent integration surfaces
4. Ledger row-shape posture:
   - every emitted adjudication ledger must bind:
     - one released applicability frame ref
     - one released edge-class catalog ref carried through that frame
     - one released probe-template catalog ref carried through that frame
     - one released symbol id / module path / qualname / symbol kind tuple carried
       through that frame
   - every emitted adjudication ledger must materialize one row for every admitted
     edge class in released `V53-A` catalog order, not only rows with explicit
     overrides;
   - every adjudication row must carry:
     - `edge_class_ref`
     - `source_applicability_status`
     - `adjudication_status`
     - ordered `supporting_witness_refs`
     - ordered `supporting_checked_no_witness_refs`
     - optional `deferral_reason`
5. Exact starter row-mapping law:
   - if the released source applicability row is `not_applicable`, the adjudication row
     must remain `not_applicable`;
   - if the released source applicability row is `applicable` and no explicit override
     evidence is supplied, the adjudication row must be `applicable_unchecked`;
   - if the released source applicability row is `applicable` and non-empty
     `witness_summaries` evidence is supplied for that edge class, the adjudication row
     must be `witness_found`;
   - if the released source applicability row is `applicable` and the edge class is
     present in `checked_no_witness_edge_class_refs`, the adjudication row must be
     `checked_no_witness_found`;
   - if the released source applicability row is `underdetermined` and no explicit
     override evidence is supplied, the adjudication row must remain
     `underdetermined`;
   - if the released source applicability row is `underdetermined` and any explicit
     override evidence is supplied, the adjudication row must be `deferred` with one
     explicit deferral reason stating that starter `V53-B` does not permit positive
     promotion from underdetermined applicability.
6. Exact starter support-field law:
   - `not_applicable`, `applicable_unchecked`, and `underdetermined` rows must carry:
     - empty `supporting_witness_refs`
     - empty `supporting_checked_no_witness_refs`
     - absent `deferral_reason`
   - `witness_found` rows must carry:
     - non-empty `supporting_witness_refs`
     - empty `supporting_checked_no_witness_refs`
     - absent `deferral_reason`
   - `checked_no_witness_found` rows must carry:
     - empty `supporting_witness_refs`
     - non-empty `supporting_checked_no_witness_refs`
     - absent `deferral_reason`
   - `deferred` rows must carry:
     - at least one non-empty explicit-evidence support field
     - present non-empty `deferral_reason`
7. Explicit override law:
   - every explicit override edge class must already exist in the bound released
     applicability frame;
   - the same edge class may not appear in both `witness_summaries` and
     `checked_no_witness_edge_class_refs`;
   - explicit override evidence is forbidden for any row whose source applicability
     status is `not_applicable`;
   - unknown or unbound explicit override refs must fail closed rather than being
     ignored;
   - explicit override input may not rewrite source applicability posture, only map it
     through the frozen starter adjudication law above.
8. Evidence semantics law:
   - lexical test-token adjacency alone is not sufficient to emit
     `witness_found` or `checked_no_witness_found`;
   - structural cue overlap or non-low-confidence semantic-audit posture alone is not
     sufficient to emit `witness_found` or `checked_no_witness_found`;
   - `covered_by_existing_tests` and `bounded_safe_by_structure` are not admitted
     starter adjudication statuses and may not appear in emitted `V53-B` artifacts;
   - positive adjudication statuses in starter `V53-B` require typed explicit evidence
     only.
9. Fixture and testing posture:
   - starter fixtures must include positive reference ledgers for:
     - `not_applicable`
     - `applicable_unchecked`
     - `witness_found`
     - `checked_no_witness_found`
     - `underdetermined`
     - `deferred`
   - starter reject fixtures must include at least:
     - contradictory explicit overrides
     - out-of-frame explicit overrides
     - applicability-violating overrides against `not_applicable`
   - no starter fixture may rely on lexical test adjacency or structural cue overlap
     alone to justify a positive adjudication status.

## Consequence

If `V53-B` lands as specified, ADEU will have:

- one repo-owned adjudication ledger surface downstream of released `V53-A`;
- one explicit constitutional override law instead of silent precedence or silent drop
  behavior;
- one exact boundary between carried-forward applicability, explicit witness evidence,
  explicit checked-no-witness evidence, and deferred underdetermined cases;
- no cumulative revision/register or test-intent widening yet.

If this contract is violated, the implementation is not a bounded `V53-B` release. It
is either:

- an under-specified reopening of released `V53-A` law;
- an over-broad promotion of soft evidence into proof-like status; or
- a premature widening into `V53-C` or `V53-D`.
