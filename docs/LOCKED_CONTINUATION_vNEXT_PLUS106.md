# Locked Continuation vNext+106

Status: `V47-A` implementation contract.

## V106 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v47a_authoritative_normative_markdown_substrate_contract@1",
  "target_arc": "vNext+106",
  "target_path": "V47-A",
  "target_scope": "bounded_authoritative_normative_markdown_and_d1_compilation_substrate",
  "implementation_packages": [
    "adeu_semantic_source",
    "adeu_commitments_ir"
  ],
  "governing_released_stack": "V41_to_V45F_released_stack_plus_current_markdown_authority_doctrine_on_main",
  "governing_stack_consumption_mode": "descriptive_and_authority_context_only_not_recursive_execution_or_mutation_authority_minting",
  "d1_normalized_ir_schema": "d1_normalized_ir@1",
  "predicate_contracts_bootstrap_schema": "predicate_contracts_bootstrap@1",
  "checker_fact_bundle_schema": "checker_fact_bundle@1",
  "policy_evaluation_result_set_schema": "policy_evaluation_result_set@1",
  "policy_obligation_ledger_schema": "policy_obligation_ledger@1",
  "markdown_native_container_required": true,
  "authoritative_dialect_blocks_required": true,
  "no_prose_inference_outside_d1_required": true,
  "bounded_d1_v0_surface_required": true,
  "normalized_ir_required": true,
  "bootstrap_predicate_contracts_required": true,
  "fact_only_checker_posture_required": true,
  "run_specific_result_set_required": true,
  "cross_run_ledger_required": true,
  "tiny_end_to_end_reference_chain_required": true,
  "minimal_checker_fact_kind_vocabulary_required": true,
  "minimal_provenance_mode_vocabulary_required": true,
  "starter_vocabulary_exact_match_required": true,
  "result_to_ledger_mapping_freeze_required": true,
  "clause_scope_blocker_result_rows_supported_required": true,
  "zero_match_notice_policy_required": true,
  "d1_selector_ref_surface_required": true,
  "tagged_fact_row_union_required": true,
  "minimal_non_override_no_migration_companion_allowed_boundary_required": true,
  "standalone_and_companion_source_posture_supported": true,
  "predicate_contract_bundle_scope_independent_required": true,
  "source_level_deferred_forbidden": true,
  "imported_o_owned_selector_handles_forbidden": true,
  "imported_e_owned_predicate_registries_forbidden": true,
  "automatic_waiver_issuance_forbidden": true,
  "automatic_deferral_issuance_forbidden": true,
  "ledger_authority_minting_forbidden": true,
  "checker_authority_minting_forbidden": true,
  "authoritative_and_mirrored_schema_export_parity_required": true,
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

- Arc label: `vNext+106`
- Family label: `V47-A`
- Scope label: bounded authoritative normative markdown and `D@1` compilation substrate

## Objective

Release the bounded `V47-A` substrate by materializing:

- one canonical `d1_normalized_ir@1`;
- one canonical `predicate_contracts_bootstrap@1`;
- one canonical `checker_fact_bundle@1`;
- one canonical `policy_evaluation_result_set@1`;
- one canonical `policy_obligation_ledger@1`;

plus one tiny end-to-end ANM reference chain over explicit markdown source with
authoritative `D@1` blocks, while preserving explicit no-prose-inference posture,
bounded `D@1 v0` syntax, explicit result-to-ledger mapping, explicit zero-match notice
policy, explicit checker-fact versus result-set versus ledger separation, and fail-closed
rejection of authority laundering, source-level deferral, hidden selector/predicate
ownership expansion, or execution entitlement minting.

This slice is substrate-first and non-executive. It is not recursive execution, mutation
permission, scheduler authority, approval posture, or repo-wide markdown migration.

## Frozen Implementation Decisions

1. Family-boundary strategy:
   - `V47-A` releases the bounded ANM artifact chain only:
     - source markdown with authoritative `D@1` blocks;
     - normalized `D-IR`;
     - bootstrap predicate contracts;
     - checker fact bundles;
     - policy evaluation result sets;
     - policy obligation ledger;
   - it does not widen into downstream policy consumers, recursive execution, or
     repo-wide migration.
2. Package-ownership strategy:
   - `adeu_semantic_source` owns bounded markdown / `D@1` parsing and compilation entry;
   - `adeu_commitments_ir` owns normalized IR, predicate-contract, fact-bundle,
     result-set, and ledger schema/model surfaces;
   - no additional package ownership is selected in this slice.
3. Source-authority strategy:
   - authoritative policy semantics compile only from explicit `D@1` blocks;
   - prose outside `D@1` remains readable context only and must never be compiled into
     obligation semantics;
   - the first release supports:
     - standalone ANM source docs;
     - companion ANM source docs beside existing markdown docs;
   - the first release freezes only the minimum coexistence boundary:
     - no override of current markdown authority by existence alone;
     - no repo-wide migration;
     - companion posture allowed.
4. `D@1` surface strategy:
   - bounded `D@1 v0` remains restricted to:
     - modal heads:
       - `MUST`
       - `MUST_NOT`
     - assertion constructors:
       - `REQUIRED`
       - `EXPLICIT`
       - `EXACTLY_ONE`
     - qualifiers:
       - `ONLY_IF`
       - `UNLESS`
   - no general boolean algebra, quantifiers, nested qualifier logic, or source-level
     `DEFERRED` is admitted in this slice.
5. Selector/predicate bootstrap strategy:
   - `ON` consumes bootstrap string selectors only in `V47-A`;
   - predicate semantics remain explicit through bootstrap predicate contracts only;
   - predicate-contract bundles remain semantic and scope-independent in `V47-A`:
     - they describe predicate identity, argument shape, evidence requirements, and
       failure conditions;
     - they do not carry run-specific operational scope;
   - imported O-owned selector handles and imported E-owned predicate registries remain
     later-lane work.
6. Result/ledger strategy:
   - evaluation result sets remain run-specific and immutable;
   - the ledger remains cross-run current-state projection only;
   - selector zero-match does not create a first ledger row;
   - `gated_off` does create or update a row when a subject was resolved;
   - clause-scope `unknown_resolution` without a formed `subject_ref` remains a blocking
     result posture rather than a fabricated ledger row.
7. Fact-only checker strategy:
   - checker bundles may emit typed observations and provenance only;
   - checker fact rows are a tagged union by `fact_type` rather than one flat row shape;
   - fact-kind-specific carriers such as `path`, `values`, or binding payloads must be
     required only when that fact kind needs them;
   - they may not define policy semantics, decide compliance, or mint authority.
8. Anti-overreach strategy:
   - `V47-A` may not mint waiver authority or deferral authority from result sets or
     ledger rows alone;
   - `V47-A` may not authorize execution, mutation, scheduling, or approval;
   - `V47-A` may not silently expand into current-markdown supersession.

## Bounded Starter Vocabularies

The first `V47-A` release should freeze bounded starter vocabularies for the tiny
reference chain rather than leaving them to implementation taste.

The intended bounded starter vocabularies are:

- `fact_type`:
  - `value_observation`
  - `binding_observation`
  - `carrier_read`
  - `path_presence_observation`
  - `path_cardinality_observation`
  - `explicit_carriage_observation`
- `provenance_mode`:
  - `direct`
  - `derived`
  - `absent`
  - `inconclusive`
- `applicability`:
  - `active`
  - `gated_off`
  - `excepted`
- `observed_outcome`:
  - `not_evaluated`
  - `pass`
  - `fail`
  - `unknown_evidence`
  - `unknown_resolution`
- `effective_verdict`:
  - `pass`
  - `fail`
  - `waived`
  - `deferred`
  - `gated_off`
  - `unknown_evidence`
  - `unknown_resolution`
- `ledger_state`:
  - `satisfied`
  - `violated`
  - `waived`
  - `deferred`
  - `gated_off`
  - `blocked_unknown_evidence`
  - `blocked_unknown_resolution`

Any widening beyond these starter vocabularies should require a later bounded
continuation rather than silent vocabulary creep.

## Required Deliverables

1. New typed substrate surfaces:
   - canonical `d1_normalized_ir@1` artifact;
   - canonical `predicate_contracts_bootstrap@1` artifact;
   - canonical `checker_fact_bundle@1` artifact;
   - canonical `policy_evaluation_result_set@1` artifact;
   - canonical `policy_obligation_ledger@1` artifact;
   - authoritative and mirrored schema export parity for all released typed artifacts.
2. Deterministic compilation entrypoint(s) that:
   - consume explicit markdown source with one or more authoritative `D@1` blocks;
   - reject prose-only obligation inference;
   - compile bounded `D@1 v0` clauses into normalized `D-IR`;
   - bind evaluation to one declared fact bundle and one declared predicate-contract
     bundle;
   - produce result sets and ledger updates deterministically for the accepted tiny
     reference chain;
   - fail closed on unsupported heads, constructors, qualifiers, boolean composition,
     hidden selector ownership expansion, or malformed authority blocks.
3. Top-level schema anchors for `d1_normalized_ir@1`:
   - `schema`
   - `d1_ir_id`
   - `source_doc_ref`
   - `source_doc_sha256`
   - `source_block_refs`
   - `selector_refs`
   - `selector_zero_match_policy`
   - `clauses`
   - `semantic_hash`
   - per selector ref anchors:
     - `selector_ref`
     - `selector_source_text`
     - `selector_kind`
   - per clause anchors:
     - `clause_ref`
     - `clause_label`
     - `modal`
     - `assertion_kind`
     - `normalized_predicate_id`
     - `subject_selector_ref`
     - `qualifiers`
     - `origin_block_ref`
4. Top-level schema anchors for `predicate_contracts_bootstrap@1`:
   - `schema`
   - `predicate_contract_bundle_id`
   - `contracts`
   - per contract anchors:
     - `predicate_id`
     - `owner_layer`
     - `version`
     - `argument_schema`
     - `required_evidence_kinds`
     - `truth_conditions`
     - `evidence_failure_conditions`
     - `resolution_failure_conditions`
5. Top-level schema anchors for `checker_fact_bundle@1`:
   - `schema`
   - `bundle_id`
   - `scope_snapshot`
   - `checker_profile`
   - `facts`
   - per fact anchors:
     - `fact_id`
     - `subject_ref`
     - `fact_type`
     - `provenance`
     - `checker_id`
     - `emitted_at`
     - fact-kind-specific payload anchors:
       - `path` when required by the fact kind
       - `values` when required by the fact kind
       - `binding_payload` when required by the fact kind
       - `carrier_payload` when required by the fact kind
     - per provenance anchors:
       - `carrier_ref`
       - `mode`
       - `notes`
6. Top-level schema anchors for `policy_evaluation_result_set@1`:
   - `schema`
   - `result_set_id`
   - `scope_snapshot`
   - `d_ir_ref`
   - `fact_bundle_ref`
   - `predicate_contract_ref`
   - `results`
   - per result anchors:
     - `result_id`
     - `clause_ref`
     - `clause_semantic_hash`
     - `subject_ref` when a subject was formed
     - `result_scope_kind`
     - `applicability`
     - `observed_outcome`
     - `effective_verdict`
     - `supporting_fact_refs`
     - `supporting_contract_refs`
     - `message`
     - result-scope rule:
       - `subject_scoped` rows require `subject_ref`
       - `clause_scope_blocker` rows omit `subject_ref` and remain ineligible for
         ledger-row fabrication
7. Top-level schema anchors for `policy_obligation_ledger@1`:
   - `schema`
   - `ledger_id`
   - `scope_snapshot`
   - `result_set_refs`
   - `rows`
   - per row anchors:
     - `obligation_id`
     - `clause_ref`
     - `clause_semantic_hash`
     - `subject_ref`
     - `latest_applicability`
     - `latest_observed_outcome`
     - `latest_effective_verdict`
     - `ledger_state`
     - `first_seen_run`
     - `latest_result_run`
     - `waiver_ref`
     - `deferral_ref`
     - `updated_at`
8. One accepted tiny reference chain proving at least:
   - standalone or companion markdown source with explicit `D@1` block;
   - deterministic `D-IR` compilation;
   - deterministic predicate-contract bundle;
   - deterministic checker fact bundle;
   - deterministic result-set emission;
   - deterministic ledger projection with explicit `gated_off` / zero-match distinction.
9. Accepted and reject fixtures proving at least:
   - accept canonical tiny reference chain;
   - reject prose-only obligation inference;
   - reject unsupported source-level `DEFERRED`;
   - reject unsupported boolean or nested clause logic;
   - reject checker fact bundle carrying verdict semantics;
   - reject checker fact row that omits required fact-kind-specific payload;
   - reject result-set row missing `applicability`, `observed_outcome`, or
     `effective_verdict`;
   - reject subject-scoped result row missing required `subject_ref`;
   - reject fabricated ledger row for clause-scope `unknown_resolution` without
     resolved subject.
10. Tests covering at least:
   - schema/model validation;
   - deterministic replay over committed accepted and rejected fixtures;
   - authoritative/mirrored schema export parity;
   - no-prose-inference enforcement;
   - result-to-ledger mapping enforcement;
   - fail-closed rejection of authority laundering from checker or ledger surfaces.

## Acceptance Gates

Accept this slice only if:

1. canonical `d1_normalized_ir@1`, `predicate_contracts_bootstrap@1`,
   `checker_fact_bundle@1`, `policy_evaluation_result_set@1`, and
   `policy_obligation_ledger@1` compile/export deterministically over one tiny accepted
   reference chain;
2. no policy semantics are inferred from prose outside explicit `D@1` surfaces;
3. bounded `D@1 v0` syntax remains enforced and unsupported source forms fail closed;
4. result sets preserve explicit `applicability`, `observed_outcome`, and
   `effective_verdict`;
5. ledger rows preserve explicit `latest_applicability`, `latest_observed_outcome`, and
   `latest_effective_verdict`;
6. selector zero-match remains distinct from `gated_off` and does not fabricate a first
   ledger row;
7. clause-scope `unknown_resolution` without a formed subject remains a result-only
   blocker rather than a fabricated ledger row;
8. checker fact bundles remain fact-only and cannot carry policy verdict or authority;
9. released fact-kind and provenance-mode vocabularies match the frozen starter
   vocabularies exactly in this slice;
10. result rows support both:
   - subject-scoped evaluations with `subject_ref`;
   - clause-scope blocker rows without `subject_ref`;
11. `d1_normalized_ir@1` preserves first-class selector refs and clause-to-selector
   linkage rather than hiding selector handling in prose or implementation folklore;
12. result sets and ledger rows do not mint waiver, deferral, execution, mutation, or
   approval authority by themselves;
13. schema export parity and committed fixture replay pass;
14. scoped Python tests cover the released parser/compiler/model surface.

Do not accept this slice if:

- obligations are inferred from prose outside `D@1`;
- the release collapses source, IR, facts, results, and ledger into one artifact or
  one mixed evaluator surface;
- source-level `DEFERRED`, imported O-owned selector handles, or imported E-owned
  predicate registries appear in the first release;
- result rows require `subject_ref` even for clause-scope blocker posture;
- checker fact rows pretend every fact kind carries the same universal payload shape;
- selector handling is left implicit in `D-IR` instead of being represented through
  explicit selector refs and clause linkage;
- checker bundles decide policy or ledgers are overread as approval artifacts;
- selector zero-match and `gated_off` are collapsed into one operational posture;
- clause-scope `unknown_resolution` fabricates ledger rows without a resolved subject;
- the first release silently widens into current-markdown override or repo-wide
  migration;
- the first release widens into recursive execution, mutation, scheduling, or approval
  authority.

## Local Gate

- run `make arc-start-check ARC=106` while the bundle remains docs-only;
- run targeted Python checks for the changed package surface once code work begins;
- do not treat this starter bundle as a substitute for the Python lane once source code
  changes begin.
