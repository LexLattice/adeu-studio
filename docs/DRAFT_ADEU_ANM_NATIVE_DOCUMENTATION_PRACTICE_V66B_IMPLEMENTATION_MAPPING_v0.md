# Draft ADEU ANM Native Documentation Practice V66B Implementation Mapping v0

Status: support note for the `V66-B` starter implementation pass after `V66-A`
implementation merged on `main`.

Authority layer: support only.

This note does not authorize implementation by itself. It records how a bounded
`V66-B` slice should widen the already shipped `V66-A` ANM source-set /
authority-profile / class-policy basis into one explicit migration-binding and
reader-projection seam without reopening `V47` ANM language/compiler ownership,
silently superseding current markdown authority, minting generated-reader
authority, or turning semantic diff output into lock or runtime law.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v51.md`
- `docs/ARCHITECTURE_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_FAMILY_v0.md`
- `docs/DRAFT_ADEU_ANM_NATIVE_DOCUMENTATION_PRACTICE_V66_IMPLEMENTATION_MAPPING_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS182.md`

## Carry Forward Nearly As-Is

- the shipped `V66-A` starter basis only:
  - `anm_source_set_manifest@1`
  - `anm_doc_authority_profile@1`
  - `anm_doc_class_policy@1`
- the closed `V47-A` through `V47-F` ANM substrate:
  - explicit `D@1` blocks
  - typed D-AST
  - normalized `D-IR`
  - bootstrap predicate contracts
  - fact-only checker bundles
  - policy evaluation result sets
  - policy obligation ledgers
  - coexistence doctrine
  - selector / predicate ownership-transition doctrine
  - bounded policy-consumer bindings
- the rule that prose remains prose unless an explicit recognized authority block
  says otherwise
- the rule that current markdown remains controlling until explicit transition law
  says otherwise
- the rule that generated reader views are non-authoritative by default
- the rule that hidden cognition is not the governance surface

## Re-Author With Repo Alignment

Candidate new `V66-B` surfaces:

- `anm_migration_binding_profile@1`
- `anm_reader_projection_manifest@1`
- `anm_semantic_diff_report@1`

Those surfaces should consume, but not re-emit or mutate by default, the shipped
`V66-A` basis:

- `anm_source_set_manifest@1`
- `anm_doc_authority_profile@1`
- `anm_doc_class_policy@1`

Each emitted `V66-B` surface should carry exact consumed basis references and
hashes:

- `consumed_source_set_manifest_ref`
- `consumed_source_set_manifest_hash`
- `consumed_doc_class_policy_ref`
- `consumed_doc_class_policy_hash`
- `consumed_authority_profile_set_ref_or_hash`

Those starter surfaces should remain bounded to:

- the same shipped governed ANM source set only
- the same shipped document authority profiles only
- the same shipped document-class policy only
- one explicit host / companion migration-binding seam only
- one explicit generated reader-projection seam only
- one explicit semantic authority-surface diff seam only

They should decide only:

- which already registered host / companion relations remain:
  - non-overriding
  - transition-law-gated
  - explicit supersession-claim blocked
- which generated reader views correspond to which already governed ANM sources
- whether a generated reader projection is current, stale, or missing
- which semantic additions / removals / authority-surface changes are visible
  across the same governed source set

They should keep:

- no new `D@1` semantics
- no new modal heads
- no new selector or predicate ownership doctrine
- no compile-report artifact yet
- no prose-boundary notice set yet
- no implicit markdown supersession
- no generated-reader authority by implication
- no semantic diff authority by implication

`V66-B` should keep explicit:

- the shipped `V66-A` source set remains the only migration / reader basis here
- migration binding is not supersession law by itself
- generated reader projection is not authority by itself
- semantic diff is not lock or runtime law by itself
- explicit transition law remains required before markdown supersession
- a host / companion pair may be registered here without making the companion
  authoritative by proximity alone
- a generated projection may summarize a governed source without minting new
  obligations
- semantic diff may expose drift without changing authority posture by itself

## Starter Field Direction

Minimum `anm_migration_binding_profile@1` direction:

- top-level:
  - `schema_id`
  - `migration_binding_profile_id`
  - `consumed_source_set_manifest_ref`
  - `consumed_source_set_manifest_hash`
  - `consumed_doc_class_policy_ref`
  - `consumed_doc_class_policy_hash`
  - `consumed_authority_profile_set_ref_or_hash`
  - `binding_rows`
- each binding row:
  - `binding_id`
  - `host_doc_ref`
  - `companion_doc_ref`
  - `host_profile_ref`
  - `companion_profile_ref_or_none`
  - `binding_posture`
  - `current_markdown_authority_relation`
  - `supersession_claim_status`
  - `explicit_transition_law_ref_or_none`
  - `generated_reader_projection_refs_or_none`
  - `semantic_diff_ref_or_none`
- starter enums:
  - `binding_posture`:
    - `registered_non_overriding_companion`
    - `standalone_no_companion`
    - `invalid_or_contradictory`
  - `current_markdown_authority_relation`:
    - `current_markdown_controlling`
    - `anm_standalone_source_of_truth`
    - `generated_projection_non_authoritative`
    - `not_applicable`
  - `supersession_claim_status`:
    - `none`
    - `claimed_with_explicit_transition_law`
    - `claimed_without_transition_law_rejected`

Minimum `anm_reader_projection_manifest@1` direction:

- top-level:
  - `schema_id`
  - `projection_manifest_id`
  - `consumed_source_set_manifest_ref`
  - `consumed_source_set_manifest_hash`
  - `consumed_doc_class_policy_ref`
  - `consumed_doc_class_policy_hash`
  - `consumed_authority_profile_set_ref_or_hash`
  - `projection_rows`
- each projection row:
  - `projection_doc_ref`
  - `source_doc_ref`
  - `source_profile_ref`
  - `projection_required`
  - `projection_requirement_source`
  - `projection_status`
  - `projection_authority_posture`
  - `source_content_hash`
  - `projection_content_hash_or_none`
  - `drift_status`
- starter enums:
  - `projection_requirement_source`:
    - `doc_authority_profile`
    - `doc_class_policy`
    - `explicit_projection_manifest`
    - `not_required`
  - `projection_status`:
    - `current`
    - `stale`
    - `missing`
    - `not_required`
    - `invalid`
  - `projection_authority_posture`:
    - `non_authoritative_generated_view`
    - `invalid_claims_authority`
  - `drift_status`:
    - `in_sync`
    - `source_changed_projection_stale`
    - `projection_missing`
    - `hash_unavailable`
    - `not_required`

Minimum `anm_semantic_diff_report@1` direction:

- top-level:
  - `schema_id`
  - `diff_report_id`
  - `consumed_source_set_manifest_ref`
  - `consumed_source_set_manifest_hash`
  - `consumed_doc_class_policy_ref`
  - `consumed_doc_class_policy_hash`
  - `consumed_authority_profile_set_ref_or_hash`
  - `baseline_kind`
  - `baseline_artifact_ref_or_none`
  - `baseline_artifact_hash_or_none`
  - `current_artifact_ref`
  - `current_artifact_hash`
  - `change_rows`
- each change row:
  - `source_doc_ref`
  - `baseline_profile_ref_or_none`
  - `current_profile_ref`
  - `change_kind`
  - `surface_kind`
  - `path_or_axis`
  - `baseline_value_or_none`
  - `current_value_or_none`
  - `authority_effect_kind`
  - `authority_effect_summary_or_none`
- starter enums:
  - `baseline_kind`:
    - `none_initial_report`
    - `prior_committed_artifact`
    - `explicit_fixture_baseline`
  - `change_kind`:
    - `added`
    - `removed`
    - `changed`
    - `unchanged`
    - `initial`
  - `surface_kind`:
    - `source_set_entry`
    - `doc_authority_profile`
    - `doc_class_policy`
    - `migration_binding`
    - `reader_projection_manifest`
  - `authority_effect_kind`:
    - `review_visibility_only`
    - `no_authority_minted`
    - `invalid_authority_claim_rejected`

## Explicit Diff / Projection / Transition Rules

- semantic diff baseline must be explicit:
  - no implicit Git diff
  - no working-tree diff
  - no prose interpretation baseline
- `V66-B` semantic diff scope stays bounded to documentation-governance surfaces:
  - source-set entries
  - document authority profiles
  - class-policy rows
  - migration-binding rows
  - reader-projection rows
- `V66-B` semantic diff does not:
  - reinterpret arbitrary prose
  - reinterpret `D@1`
  - compute policy verdict changes
  - emit obligation-ledger changes
- `V66-B` owns the projection manifest and projection drift validation first:
  - helper-generated reader `.md` files may exist
  - the selected versioned artifact remains the manifest, not the generated prose
- a generated reader projection must stay excluded from governed ANM source:
  - source posture is `generated_projection`
  - it does not become governed source because it contains rendered, quoted,
    escaped, or copied authority-block text
  - generated projections may not be used as source inputs for `D@1` lowering
  - generated projections should carry a non-authoritative banner
- stale or missing reader projection fails closed only when projection is required:
  - requirement source must be explicit
  - optional projection absence is recorded, not overpromoted into blanket failure
- a valid transition-law reference must resolve to lock authority:
  - it must resolve to a lock-authority doc or clause
  - it must explicitly match the host doc, companion doc, and supersession scope
  - planning/support/generated/diff references do not satisfy transition law
  - unresolved transition law fails closed

## Do Not Import

- `V47` language widening
- selector or predicate ownership widening
- policy-consumer widening
- compile-report artifact doctrine
- prose-boundary notice doctrine
- repo-wide `.adeu.md` rename doctrine
- silent markdown supersession
- generated-reader authority
- semantic diff authority
