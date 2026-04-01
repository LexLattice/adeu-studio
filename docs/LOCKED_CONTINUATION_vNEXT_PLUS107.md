# Locked Continuation vNext+107

Status: `V47-B` implementation contract.

## V107 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v47b_authoritative_normative_markdown_hardening_contract@1",
  "target_arc": "vNext+107",
  "target_path": "V47-B",
  "target_scope": "bounded_anm_schema_example_and_vocabulary_hardening",
  "implementation_packages": [
    "adeu_semantic_source",
    "adeu_commitments_ir"
  ],
  "governing_released_stack": "V41_to_V47A_released_stack_plus_current_markdown_authority_doctrine_on_main",
  "governing_stack_consumption_mode": "released_v47a_substrate_hardening_only_not_coexistence_migration_or_execution_authority_minting",
  "requires_released_v47a_surfaces": true,
  "d1_normalized_ir_schema": "d1_normalized_ir@1",
  "predicate_contracts_bootstrap_schema": "predicate_contracts_bootstrap@1",
  "checker_fact_bundle_schema": "checker_fact_bundle@1",
  "policy_evaluation_result_set_schema": "policy_evaluation_result_set@1",
  "policy_obligation_ledger_schema": "policy_obligation_ledger@1",
  "starter_vocabulary_extension_required": true,
  "fact_kind_vocabulary_hardening_required": true,
  "provenance_mode_vocabulary_hardening_required": true,
  "schema_example_parity_required": true,
  "concrete_anm_examples_required": true,
  "compiled_companion_examples_required": true,
  "authoritative_and_mirrored_schema_export_parity_required": true,
  "schema_export_example_parity_required": true,
  "example_replay_determinism_required": true,
  "fact_bundle_union_examples_required": true,
  "result_set_and_ledger_mapping_examples_required": true,
  "zero_match_after_prior_instantiation_reconciliation_required": true,
  "clause_scope_and_subject_scoped_result_row_shape_separation_required": true,
  "no_prose_inference_outside_d1_required": true,
  "no_current_markdown_override_required": true,
  "no_repo_wide_migration_required": true,
  "no_imported_o_owned_selector_handles_yet": true,
  "no_imported_e_owned_predicate_registries_yet": true,
  "no_source_level_deferred_yet": true,
  "no_execution_or_approval_authority_minting": true,
  "source_architecture_doc": "docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md",
  "reference_docs": [
    "docs/DRAFT_D1_DIALECT_SPEC_v0.md",
    "docs/DRAFT_D1_NORMALIZED_IR_SPEC_v0.md",
    "docs/DRAFT_PREDICATE_CONTRACTS_BOOTSTRAP_SPEC_v0.md",
    "docs/DRAFT_CHECKER_FACT_BUNDLE_SPEC_v0.md",
    "docs/DRAFT_POLICY_EVALUATION_RESULT_SET_SPEC_v0.md",
    "docs/DRAFT_POLICY_OBLIGATION_LEDGER_SPEC_v0.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v30.md"
}
```

## Slice

- Arc label: `vNext+107`
- Family label: `V47-B`
- Scope label: bounded ANM schema/example and vocabulary hardening

## Objective

Release the bounded `V47-B` hardening lane by taking the shipped `V47-A` substrate and
making its first example/schema surface more explicit, auditable, and implementation-
ready through:

- widened but still bounded checker fact-kind vocabulary;
- widened but still bounded provenance-mode vocabulary;
- concrete ANM source examples with compiled companion artifacts;
- explicit schema/example parity over released `d1_normalized_ir@1`,
  `predicate_contracts_bootstrap@1`, `checker_fact_bundle@1`,
  `policy_evaluation_result_set@1`, and `policy_obligation_ledger@1`;
- deterministic replay over the accepted example family.

This slice is hardening-only. It does not widen into coexistence/migration doctrine,
imported selector/predicate ownership, execution authority, waiver/deferral issuance, or
repo-wide markdown conversion.

## Frozen Implementation Decisions

1. Family-boundary strategy:
   - `V47-B` hardens the already released `V47-A` chain only:
     - ANM source examples;
     - normalized `D-IR`;
     - bootstrap predicate contracts;
     - checker fact bundles;
     - policy evaluation result sets;
     - policy obligation ledgers;
   - it does not reopen first-slice substrate architecture or widen into later family
     seams.
2. Package-ownership strategy:
   - `adeu_semantic_source` remains the owner of bounded ANM / `D@1` example parsing and
     compilation entry;
   - `adeu_commitments_ir` remains the owner of typed IR, predicate-contract,
     fact-bundle, result-set, and ledger schema/model surfaces;
   - no new package ownership is selected in this slice.
3. Hardening strategy:
   - widen only the minimum vocabulary needed to make example/schema parity concrete and
     less illustrative;
   - every widened vocabulary item must be backed by:
     - schema surface;
     - accepted example coverage;
     - deterministic replay or model validation;
   - no vocabulary widening may silently change the released `V47-A` starter semantics.
4. Example strategy:
   - example ANM sources must stay bounded and legible;
   - each accepted example family must have explicit compiled companions;
   - compiled companions must remain semantically separated:
     - source markdown;
     - normalized `D-IR`;
     - checker facts;
     - evaluation results;
     - ledger state.
5. Coexistence strategy:
   - `V47-B` keeps the `V47-A` minimum coexistence freeze only:
     - no override of current markdown authority by existence alone;
     - no repo-wide migration;
     - companion posture remains allowed;
   - broader coexistence doctrine remains `V47-C`.
6. Anti-overreach strategy:
   - `V47-B` may not introduce imported O-owned selector handles or imported E-owned
     predicate registries;
   - `V47-B` may not introduce source-level `DEFERRED`;
   - `V47-B` may not mint execution, mutation, scheduling, waiver, deferral, or approval
     authority.

## Intended Hardening Targets

The intended `V47-B` hardening targets are:

- checker fact vocabulary:
  - freeze released `V47-A` items and add only bounded, explicitly typed additions
    required by accepted examples;
- provenance vocabulary:
  - freeze released `V47-A` items and add only bounded, explicitly typed additions
    required by accepted examples;
- example families:
  - at least one accepted standalone ANM example;
  - at least one accepted companion-posture ANM example;
  - at least one accepted example exercising clause-scope blocker posture;
  - at least one accepted example exercising zero-match posture;
  - at least one accepted example exercising prior-instantiation then later zero-match
    reconciliation posture;
- parity surfaces:
  - prose companion docs;
  - schema exports;
  - mirrored schema exports;
  - model validation;
  - accepted example replay;
  - reject example coverage for forbidden widening or malformed shape drift.

Any widening beyond those hardening targets should require a later bounded continuation.

## Required Deliverables

1. Hardened released surfaces:
   - authoritative/mirrored schema parity retained for all five `V47-A` typed artifacts;
   - explicit widened enums for released fact-kind and provenance-mode vocabularies;
   - concrete accepted example payloads for all five typed artifacts.
2. Concrete ANM source examples:
   - accepted standalone ANM source example(s);
   - accepted companion-posture ANM source example(s);
   - each with committed compiled companion artifacts.
3. Concrete compiled companion example set:
   - accepted `d1_normalized_ir@1` example(s);
   - accepted `predicate_contracts_bootstrap@1` example(s);
   - accepted `checker_fact_bundle@1` example(s);
   - accepted `policy_evaluation_result_set@1` example(s);
   - accepted `policy_obligation_ledger@1` example(s).
4. Deterministic replay and validation:
   - replay over accepted examples is deterministic;
   - reject examples fail closed on malformed widening or authority laundering;
   - schema/model validation stays exact with the hardened examples.
5. Hardened vocabulary/example doctrine:
   - released fact-kind and provenance-mode enums are spelled out exactly in code and
     examples;
   - example carriers remain typed unions rather than flat catch-all rows;
   - result-to-ledger mapping remains explicit in examples rather than inferred from
     prose;
   - clause-scope blocker rows remain distinct from subject-scoped result rows in
     examples rather than being flattened into one universal row shape.
6. Zero-match reconciliation doctrine:
   - accepted examples must show first-run zero-match notice posture with no first
     ledger row;
   - accepted examples must also show the later same-scope case where previously
     instantiated rows encounter zero-match and fail closed through explicit
     reconciliation posture rather than silent row disappearance.
7. Schema/export parity doctrine:
   - prose companion docs, authoritative schemas, mirrored exports, and committed
     examples must remain aligned on the same hardened vocabulary and shape grammar;
   - no release may silently widen examples beyond the exported schema surface.

## Acceptance

`V47-B` is complete when:

1. all five released `V47-A` typed artifacts retain authoritative/mirror schema parity
   after hardening;
2. widened checker fact-kind and provenance vocabularies are explicit, bounded, and
   backed by accepted examples;
3. accepted ANM examples compile deterministically into committed companion artifacts;
4. accepted examples cover:
   - standalone posture;
   - companion posture;
   - zero-match posture;
   - prior-instantiation then later zero-match reconciliation posture;
   - clause-scope blocker posture;
5. no accepted example collapses source, IR, facts, results, and ledger into one mixed
   artifact;
6. authoritative schemas, mirrored exports, and committed examples stay in exact parity
   for the hardened vocabulary and row-shape grammar;
7. clause-scope blocker rows remain encoded distinctly from subject-scoped result rows
   in accepted examples rather than being flattened into one universal row shape;
8. reject fixtures fail closed on:
   - prose-only obligation inference;
   - imported selector/predicate ownership widening;
   - source-level `DEFERRED`;
   - malformed fact-row or result-row shape drift;
   - schema/example parity drift;
   - authority laundering from facts, results, or ledger rows;
9. targeted Python tests cover:
   - example replay determinism;
   - schema export parity;
   - hardened enum exactness;
   - fail-closed reject fixtures.

## Do Not Ship

- broader current-markdown migration doctrine;
- imported O-owned selector handles;
- imported E-owned predicate registries;
- source-level `DEFERRED`;
- execution or approval authority;
- waiver or deferral minting by result/ledger artifact;
- unbounded checker-fact or provenance enum growth without example-backed lock binding.
