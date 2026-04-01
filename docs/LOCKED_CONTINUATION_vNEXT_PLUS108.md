# Locked Continuation vNext+108

Status: `V47-C` implementation contract.

## V108 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v47c_authoritative_normative_markdown_coexistence_contract@1",
  "target_arc": "vNext+108",
  "target_path": "V47-C",
  "target_scope": "bounded_anm_coexistence_and_companion_adoption_doctrine",
  "implementation_packages": [
    "adeu_semantic_source",
    "adeu_commitments_ir"
  ],
  "governing_released_stack": "V41_to_V47B_released_stack_plus_current_markdown_authority_doctrine_on_main",
  "governing_stack_consumption_mode": "released_anm_stack_coexistence_and_adoption_only_not_repo_wide_migration_ownership_transition_or_execution_authority_minting",
  "requires_released_v47a_surfaces": true,
  "requires_released_v47b_surfaces": true,
  "anm_markdown_coexistence_profile_schema": "anm_markdown_coexistence_profile@1",
  "bounded_standalone_vs_companion_doctrine_required": true,
  "current_markdown_non_override_rule_required": true,
  "companion_embedding_posture_required": true,
  "migration_discipline_required": true,
  "adoption_boundary_matrix_required": true,
  "same_snapshot_identity_required": true,
  "artifact_local_source_scope_compatibility_required": true,
  "supersession_field_consistency_required": true,
  "companion_embedding_semantics_explicit_required": true,
  "host_or_companion_linkage_validation_required": true,
  "allowed_constrain_actions_exact_enumeration_required": true,
  "adoption_boundary_action_vocabulary_consistency_required": true,
  "standalone_and_companion_example_classification_required": true,
  "deterministic_coexistence_profile_replay_required": true,
  "authoritative_and_mirrored_schema_export_parity_required": true,
  "no_current_markdown_supersession_by_existence_required": true,
  "no_repo_wide_migration_required": true,
  "no_imported_o_owned_selector_handles_yet": true,
  "no_imported_e_owned_predicate_registries_yet": true,
  "no_source_level_deferred_yet": true,
  "no_execution_or_approval_authority_minting": true,
  "no_automatic_waiver_or_deferral_issuance": true,
  "required_released_contracts": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS107.md"
  ],
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

- Arc label: `vNext+108`
- Family label: `V47-C`
- Scope label: bounded ANM coexistence and companion adoption doctrine

## Objective

Release the bounded `V47-C` coexistence and companion-doc adoption lane by
materializing one canonical doctrine surface over the released `V47-A` + `V47-B`
stack that makes explicit:

- standalone-vs-companion posture;
- current-markdown non-override posture;
- companion embedding rules for readable markdown containing authoritative `D@1`
  blocks;
- bounded migration discipline without repo-wide conversion;
- explicit adoption-boundary rows saying what the released ANM stack may constrain and
  what still requires later lock-level adoption.

This slice is adoption-first and non-executive. It does not reopen ANM source syntax,
normalized `D-IR`, predicate contracts, fact bundles, result sets, or ledger
semantics. It also does not widen into imported selector/predicate ownership
transition, source-level `DEFERRED`, execution authority, approval authority, or
automatic markdown supersession.

## Frozen Implementation Decisions

1. Family-boundary strategy:
   - `V47-C` releases coexistence/adoption doctrine only over the already released
     `V47-A` + `V47-B` stack;
   - it does not reopen substrate semantics or schema/example hardening.
2. Package-ownership strategy:
   - `adeu_semantic_source` remains the owner of source-posture and companion-posture
     classification inputs;
   - `adeu_commitments_ir` owns the typed coexistence/adoption profile and its schema
     surface;
   - no additional package ownership is selected in this slice.
3. Authority-layer strategy:
   - current markdown lock/planning authority remains controlling unless a later
     lock-level adoption surface explicitly says otherwise;
   - ANM companion posture may coexist with that authority but may not supersede it by
     existence alone;
   - `requires_later_lock_for_supersession` is an invariant carrier, not a second
     authority language:
     - when `current_markdown_authority_relation` is
       `later_lock_required_for_supersession`, it must be `true`;
     - otherwise it must be `false`;
   - released ANM artifacts may constrain later migration choices only through
     explicitly enumerated constrain actions.
4. Companion-posture strategy:
   - `V47-C` supports both:
     - standalone ANM source docs;
     - companion ANM posture inside or beside readable markdown;
   - companion posture must explicitly state:
     - the companion target or host relation;
     - the companion embedding posture;
     - the non-override rule;
     - the current-markdown authority relation.
   - companion rows must fail closed when:
     - the referenced host or companion surface is missing;
     - the referenced host or companion surface is stale relative to the declared
       snapshot or source scope;
     - the linkage implies incompatible authority posture.
5. Migration strategy:
   - `V47-C` may state:
     - when companion posture is allowed;
     - when standalone posture is preferred;
     - when current markdown remains controlling;
     - what observations may inform a later migration decision;
   - `V47-C` may not order repo-wide migration or automatic authority transfer.
6. Adoption-boundary strategy:
   - the released ANM stack may be referenced, embedded, or carried as companion
     authority input;
   - `allowed_now_actions`, `later_lock_required_actions`, and `forbidden_actions`
     must draw from the same frozen `allowed_constrain_action` vocabulary;
   - later lock-level adoption remains required for:
     - supersession of current markdown authority;
     - approval or execution authority;
     - selector/predicate ownership transition;
     - waiver or deferral issuance.
7. Anti-overreach strategy:
   - `V47-C` may not mint mutation, scheduling, execution, approval, waiver, or
     deferral authority;
   - `V47-C` may not silently widen into repo-wide migration doctrine;
   - `V47-C` may not silently import O-owned selector handles or E-owned predicate
     registries.

## Bounded Coexistence Vocabularies

The first `V47-C` release should freeze bounded coexistence vocabularies rather than
leave adoption posture to implementation taste.

The intended bounded starter vocabularies are:

- `source_posture`:
  - `standalone_anm`
  - `companion_anm`
- `current_markdown_authority_relation`:
  - `current_markdown_controlling`
  - `coexisting_non_override`
  - `later_lock_required_for_supersession`
- `migration_posture`:
  - `none`
  - `prefer_companion`
  - `prefer_standalone`
  - `defer_to_later_lock`
- `companion_embedding_posture`:
  - `not_applicable`
  - `embedded_in_host_markdown`
  - `adjacent_companion_document`
- `allowed_constrain_action`:
  - `reference_released_anm_artifact`
  - `embed_authoritative_d1_block`
  - `record_non_override_binding`
  - `emit_migration_signal`
- `adoption_boundary_posture`:
  - `allowed_now`
  - `allowed_with_later_lock`
  - `forbidden_in_v47c`

Any widening beyond these starter vocabularies should require a later bounded
continuation rather than silent doctrine creep.

## Required Deliverables

1. New typed coexistence surface:
   - canonical `anm_markdown_coexistence_profile@1` artifact;
   - authoritative and mirrored schema export parity for that artifact.
2. Deterministic coexistence/adoption classification entrypoint(s) that:
   - bind one declared snapshot identity;
   - consume one bounded source set over released `V47-A` + `V47-B` artifact inputs;
   - classify standalone-vs-companion posture deterministically;
   - preserve current-markdown non-override posture explicitly;
   - fail closed on missing, orphaned, stale, or contradictory host/companion
     relation, implicit supersession, or incompatible snapshot/source-scope bindings.
3. Top-level schema anchors for `anm_markdown_coexistence_profile@1`:
   - `schema`
   - `coexistence_profile_id`
   - `snapshot_id`
   - `snapshot_sha256`
   - `source_scope_profile`
   - `released_stack_refs`
   - `source_rows`
   - `migration_discipline`
   - `adoption_boundary_rows`
   - `semantic_hash`
   - per source row anchors:
     - `source_ref`
     - `source_posture`
     - `current_markdown_authority_relation`
     - `host_or_companion_ref`
     - `companion_embedding_posture`
     - `non_override_rule`
     - `allowed_constrain_actions`
     - `migration_posture`
     - `requires_later_lock_for_supersession`
   - per adoption-boundary row anchors:
     - `consumer_surface`
     - `adoption_boundary_posture`
     - `allowed_now_actions`
     - `later_lock_required_actions`
     - `forbidden_actions`
4. Accepted doctrine fixtures:
   - at least one accepted standalone posture fixture;
   - at least one accepted companion non-override posture fixture;
   - at least one accepted mixed source-scope fixture showing same-snapshot binding and
     artifact-local source-scope compatibility;
   - at least one accepted adoption-boundary matrix fixture.
5. Reject fixtures that fail closed on:
   - implicit current-markdown override;
   - repo-wide migration claims;
   - source rows bound to incompatible snapshot identity;
   - companion rows missing explicit host or companion linkage;
   - companion rows with orphaned, stale, or contradictory host linkage;
   - companion rows with inconsistent supersession fields;
   - allowed constrain actions outside the frozen enum;
   - adoption-boundary rows using action values outside the same frozen enum;
   - ownership-transition, execution, approval, waiver, or deferral authority claims.
6. Deterministic targeted tests covering:
   - standalone-vs-companion classification;
   - current-markdown non-override preservation;
   - same-snapshot and source-scope compatibility validation;
   - schema export parity;
   - reject-fixture fail-closed behavior.

## Acceptance

`V47-C` is complete when:

1. `anm_markdown_coexistence_profile@1` ships with authoritative/mirror schema parity;
2. accepted fixtures show both standalone and companion posture without ambiguity;
3. every companion example carries explicit non-override posture relative to current
   markdown authority;
4. migration discipline is explicit, bounded, and does not authorize repo-wide
   conversion;
5. adoption-boundary rows make explicit:
   - what the released ANM stack may constrain now;
   - what still requires later lock-level adoption;
   - what remains forbidden in `V47-C`;
6. every companion example carries explicit embedding semantics and valid
   host-or-companion linkage;
7. `requires_later_lock_for_supersession` remains exactly consistent with
   `current_markdown_authority_relation`;
8. adoption-boundary rows use the same frozen action vocabulary as source rows;
9. same-snapshot identity and artifact-local source-scope compatibility are enforced
   deterministically;
10. reject fixtures fail closed on implicit supersession, migration overreach,
   ownership-transition creep, orphaned or contradictory linkage, and authority
   laundering;
11. targeted Python tests cover classification, parity, compatibility, supersession
    invariants, and reject behavior.

## Do Not Ship

- repo-wide conversion of existing markdown authority docs;
- automatic supersession of current markdown authority by ANM source existence;
- imported O-owned selector handles;
- imported E-owned predicate registries;
- source-level `DEFERRED`;
- execution, mutation, scheduling, or approval authority;
- waiver or deferral minting by coexistence profile alone;
- unbounded coexistence, migration, or adoption vocabulary growth.
