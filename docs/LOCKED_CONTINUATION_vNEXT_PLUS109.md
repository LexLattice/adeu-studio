# Locked Continuation vNext+109

Status: `V47-D` implementation contract.

## V109 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v47d_authoritative_normative_markdown_selector_predicate_ownership_transition_contract@1",
  "target_arc": "vNext+109",
  "target_path": "V47-D",
  "target_scope": "bounded_anm_selector_and_predicate_ownership_transition_doctrine",
  "implementation_packages": [
    "adeu_semantic_source",
    "adeu_commitments_ir"
  ],
  "governing_released_stack": "V41_to_V47C_released_stack_on_main",
  "governing_stack_consumption_mode": "released_anm_stack_ownership_transition_only_not_repo_wide_migration_downstream_consumer_widening_or_execution_authority_minting",
  "requires_released_v47a_surfaces": true,
  "requires_released_v47b_surfaces": true,
  "requires_released_v47c_surfaces": true,
  "anm_selector_predicate_ownership_profile_schema": "anm_selector_predicate_ownership_profile@1",
  "selector_owner_layer_explicit_required": true,
  "predicate_owner_layer_explicit_required": true,
  "owner_layer_vocabulary_normalization_required": true,
  "bootstrap_and_owned_ref_kind_explicit_required": true,
  "selector_row_mutual_exclusion_invariants_required": true,
  "predicate_row_mutual_exclusion_invariants_required": true,
  "bootstrap_to_owned_compatibility_matrix_required": true,
  "compatibility_matrix_four_combination_coverage_required": true,
  "mixed_ownership_anti_leakage_rules_required": true,
  "bootstrap_retirement_posture_required": true,
  "imported_ref_resolution_required": true,
  "imported_ref_identity_and_version_binding_required": true,
  "backward_compatible_bootstrap_replay_required": true,
  "no_silent_bootstrap_reinterpretation_required": true,
  "same_snapshot_identity_required": true,
  "artifact_local_source_scope_compatibility_required": true,
  "selector_and_predicate_transition_examples_required": true,
  "authoritative_and_mirrored_schema_export_parity_required": true,
  "no_repo_wide_markdown_migration_required": true,
  "no_source_level_deferred_yet": true,
  "no_execution_or_approval_authority_minting": true,
  "no_automatic_waiver_or_deferral_issuance": true,
  "no_downstream_policy_consumer_binding_yet": true,
  "required_released_contracts": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS107.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS108.md"
  ],
  "source_architecture_doc": "docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md",
  "reference_docs": [
    "docs/DRAFT_D1_DIALECT_SPEC_v0.md",
    "docs/DRAFT_D1_NORMALIZED_IR_SPEC_v0.md",
    "docs/DRAFT_PREDICATE_CONTRACTS_BOOTSTRAP_SPEC_v0.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v30.md"
}
```

## Slice

- Arc label: `vNext+109`
- Family label: `V47-D`
- Scope label: bounded ANM selector / predicate ownership transition doctrine

## Objective

Release the bounded `V47-D` ownership-transition lane by materializing one canonical
doctrine surface over the released `V47-A` + `V47-B` + `V47-C` stack that makes
explicit:

- when a selector ref remains a bootstrap string selector;
- when a selector ref is an imported O-owned selector handle;
- when a predicate ref remains bootstrap-owned;
- when a predicate ref is an imported E-owned predicate-registry binding;
- what compatibility posture holds between bootstrap and later owned surfaces;
- what anti-leakage and bootstrap-retirement rules prevent mixed ownership from quietly
  minting stronger authority.

This slice is ownership-transition-first and non-executive. It does not reopen ANM
source syntax, normalized `D-IR`, fact bundles, result sets, ledger semantics,
coexistence doctrine, or downstream policy-bearing consumer surfaces. It also does not
widen into repo-wide markdown migration, source-level `DEFERRED`, execution authority,
approval authority, or automatic waiver/deferral issuance.

## Frozen Implementation Decisions

1. Family-boundary strategy:
   - `V47-D` releases ownership-transition doctrine only over the already released
     `V47-A` + `V47-B` + `V47-C` stack;
   - it does not reopen substrate semantics, hardening semantics, or coexistence
     doctrine.
2. Package-ownership strategy:
   - `adeu_semantic_source` remains the owner of source-facing selector/predicate
     transition inputs and deterministic derivation hooks;
   - `adeu_commitments_ir` owns the typed ownership-transition profile and its schema
     surface;
   - no additional package ownership is selected in this slice.
3. Selector-transition strategy:
   - `V47-D` supports both:
     - `bootstrap_string_selector`
     - `imported_o_owned_selector_handle`
   - the owner-layer term `bootstrap` in `V47-D` is the same bootstrap owner-layer
     term already used by released bootstrap predicate-contract surfaces; it must not
     be treated as a new or distinct bootstrap doctrine.
   - selector ownership must explicitly state:
     - selector ref kind;
     - selector owner layer;
     - bootstrap source ref or imported handle ref;
     - compatibility posture;
     - bootstrap-retirement posture.
   - bootstrap string selectors may remain referenceable where no imported O-owned
     handle is yet selected, but they may not be silently reinterpreted as owned
     handles.
4. Predicate-transition strategy:
   - `V47-D` supports both:
     - bootstrap predicate contracts;
     - imported E-owned predicate-registry refs.
   - the owner-layer term `bootstrap` in predicate rows is the same bootstrap
     owner-layer term already used by released `predicate_contracts_bootstrap@1`
     artifacts; it must not be treated as a new or distinct bootstrap doctrine.
   - predicate ownership must explicitly state:
     - predicate ref kind;
     - predicate owner layer;
     - bootstrap contract ref or imported registry ref;
     - compatibility posture;
     - bootstrap-retirement posture.
   - bootstrap predicate contracts may remain referenceable where no imported E-owned
     predicate registry is yet selected, but they may not be silently promoted into
     owned registry semantics.
5. Compatibility strategy:
   - `V47-D` may state:
     - when bootstrap selectors/predicates remain acceptable;
     - when imported owned surfaces are preferred;
     - when mixed bootstrap/owned posture is allowed in one bounded stack;
     - what later lock-level action is required before bootstrap retirement becomes
       authoritative.
   - `compatibility_rules` must be a first-class typed matrix rather than a prose
     summary and must cover at least these four combinations:
     - bootstrap selector + bootstrap predicate
     - owned selector + bootstrap predicate
     - bootstrap selector + owned predicate
     - owned selector + owned predicate
   - each compatibility row must explicitly state:
     - whether the combination is allowed or forbidden;
     - the required `compatibility_posture`;
     - whether backward replay is preserved;
     - whether later lock is required before retirement or supersession;
     - whether mixed ownership is informationally allowed but normatively constrained.
   - `V47-D` may not infer compatibility from naming alone or from local code
     convention without explicit typed rows.
6. Anti-leakage strategy:
   - mixed ownership must fail closed when:
     - selector ownership and predicate ownership imply contradictory semantic layers;
     - an imported owned surface is used to mint execution, approval, migration, or
       supersession authority;
     - bootstrap retirement is claimed without explicit later-lock posture.
   - imported selector handles and imported predicate-registry refs must fail closed
     when:
     - the imported ref is dangling;
     - the imported ref is stale relative to the declared snapshot or source scope;
     - the imported ref resolves to an incompatible declared identity or version.
7. Anti-overreach strategy:
   - `V47-D` may not mint mutation, scheduling, execution, approval, waiver, or
     deferral authority;
   - `V47-D` may not silently widen into repo-wide markdown migration;
   - `V47-D` may not silently widen into downstream policy-bearing consumer doctrine.

## Bounded Ownership-Transition Vocabularies

The first `V47-D` release should freeze bounded ownership-transition vocabularies
rather than leave ownership posture to implementation taste.

The intended bounded starter vocabularies are:

- `selector_ref_kind`:
  - `bootstrap_string_selector`
  - `imported_o_owned_selector_handle`
- `selector_owner_layer`:
  - `bootstrap`
  - `o_owned`
- `predicate_ref_kind`:
  - `bootstrap_predicate_contract`
  - `imported_e_owned_predicate_ref`
- `predicate_owner_layer`:
  - `bootstrap`
  - `e_owned`
- `compatibility_posture`:
  - `bootstrap_only`
  - `bootstrap_compatible_with_owned_successor`
  - `owned_preferred_bootstrap_still_allowed`
  - `mixed_ownership_forbidden`
- `bootstrap_retirement_posture`:
  - `not_selected`
  - `later_lock_required`
  - `owned_successor_available_bootstrap_still_allowed`

Any widening beyond these starter vocabularies should require a later bounded
continuation rather than silent doctrine creep.

## Required Deliverables

1. New typed ownership-transition surface:
   - canonical `anm_selector_predicate_ownership_profile@1` artifact;
   - authoritative and mirrored schema export parity for that artifact.
2. Deterministic ownership-transition derivation entrypoint(s) that:
   - bind one declared snapshot identity;
   - consume one bounded source set over released `V47-A` + `V47-B` + `V47-C` artifact
     inputs;
   - classify selector and predicate refs into frozen bootstrap-vs-owned kinds;
   - preserve backward-compatible bootstrap replay explicitly;
   - fail closed on implicit ownership promotion, contradictory mixed ownership, or
     incompatible snapshot/source-scope bindings.
3. Top-level schema anchors for `anm_selector_predicate_ownership_profile@1`:
   - `schema`
   - `ownership_profile_id`
   - `snapshot_id`
   - `snapshot_sha256`
   - `source_scope_profile`
   - `released_stack_refs`
   - `selector_rows`
   - `predicate_rows`
   - `compatibility_rules`
   - `semantic_hash`
   - per selector row anchors:
     - `selector_ref`
     - `selector_ref_kind`
     - `selector_owner_layer`
     - `bootstrap_selector_source_ref`
     - `imported_selector_handle_ref`
     - `compatibility_posture`
     - `bootstrap_retirement_posture`
     - selector row invariants:
       - if `selector_ref_kind = bootstrap_string_selector`:
         - `bootstrap_selector_source_ref` required;
         - `imported_selector_handle_ref` forbidden;
         - `selector_owner_layer = bootstrap`
       - if `selector_ref_kind = imported_o_owned_selector_handle`:
         - `imported_selector_handle_ref` required;
         - `bootstrap_selector_source_ref` forbidden;
         - `selector_owner_layer = o_owned`
   - per predicate row anchors:
     - `predicate_ref`
     - `predicate_ref_kind`
     - `predicate_owner_layer`
     - `bootstrap_predicate_contract_ref`
     - `imported_predicate_registry_ref`
     - `compatibility_posture`
     - `bootstrap_retirement_posture`
     - predicate row invariants:
       - if `predicate_ref_kind = bootstrap_predicate_contract`:
         - `bootstrap_predicate_contract_ref` required;
         - `imported_predicate_registry_ref` forbidden;
         - `predicate_owner_layer = bootstrap`
       - if `predicate_ref_kind = imported_e_owned_predicate_ref`:
         - `imported_predicate_registry_ref` required;
         - `bootstrap_predicate_contract_ref` forbidden;
         - `predicate_owner_layer = e_owned`
   - per compatibility-rule row anchors:
     - `selector_ref_kind`
     - `predicate_ref_kind`
     - `combination_allowed`
     - `compatibility_posture`
     - `backward_replay_preserved`
     - `later_lock_required_before_retirement`
     - `mixed_ownership_normatively_constrained`
4. Accepted doctrine fixtures:
   - at least one accepted bootstrap-only ownership fixture;
   - at least one accepted mixed bootstrap/owned transition fixture;
   - at least one accepted imported selector-handle fixture;
   - at least one accepted imported predicate-registry fixture;
   - at least one accepted compatibility-matrix fixture.
5. Reject fixtures that fail closed on:
   - implicit reinterpretation of a bootstrap string selector as an owned handle;
   - implicit reinterpretation of a bootstrap predicate contract as an owned registry
     binding;
   - selector rows missing explicit owner layer or imported handle ref;
   - predicate rows missing explicit owner layer or imported registry ref;
   - contradictory mixed ownership posture;
   - dangling imported selector handles;
   - dangling imported predicate-registry refs;
   - stale imported refs that no longer resolve against the declared snapshot or
     source scope;
   - imported refs whose declared version or identity is incompatible with the
     ownership profile;
   - bootstrap retirement claims without explicit later-lock requirement;
   - execution, approval, migration, waiver, or deferral authority claims;
   - source rows bound to incompatible snapshot identity or source scope.
6. Deterministic targeted tests covering:
   - bootstrap-only replay retention;
   - explicit selector ownership transition;
   - explicit predicate ownership transition;
   - compatibility and anti-leakage validation;
   - schema export parity;
   - reject-fixture fail-closed behavior.

## Acceptance

`V47-D` is complete when:

1. `anm_selector_predicate_ownership_profile@1` ships with authoritative/mirror schema
   parity;
2. accepted fixtures show bootstrap-only and bounded owned-transition posture without
   ambiguity;
3. selector and predicate owner layers are always explicit rather than inferred;
4. compatibility posture is explicit, bounded, and carried by a four-combination
   matrix rather than prose alone;
5. imported owned refs resolve fail closed against the declared snapshot, source
   scope, and declared identity/version binding;
6. pure-bootstrap `V47-A` / `V47-B` / `V47-C` reference chains replay unchanged under
   `V47-D` without silent reinterpretation into owned semantics;
7. mixed ownership fails closed when contradictory or authority-laundering;
8. the shipped slice remains non-executive, non-migratory, and non-consumer-binding.

## Do Not Ship

Do not treat `V47-D` as authority to ship:

- repo-wide markdown migration;
- source-level `DEFERRED`;
- execution, approval, mutation, scheduling, waiver, or deferral authority;
- downstream consumer doctrine over descriptive, benchmark, or runtime artifact worlds;
- automatic supersession of current markdown authority;
- silent retirement of bootstrap selectors or predicate contracts.
