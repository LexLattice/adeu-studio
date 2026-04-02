# Locked Continuation vNext+111

Status: `V47-F` implementation contract.

## V111 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v47f_authoritative_normative_markdown_benchmark_consumer_contract@1",
  "target_arc": "vNext+111",
  "target_path": "V47-F",
  "target_scope": "bounded_anm_benchmark_world_policy_bearing_consumer_doctrine",
  "implementation_packages": [
    "adeu_semantic_source",
    "adeu_commitments_ir"
  ],
  "governing_released_stack": "V41_to_V47E_released_stack_plus_released_V42D_V42E_V42G4_benchmark_artifact_worlds_on_main",
  "governing_stack_consumption_mode": "released_anm_stack_benchmark_consumer_doctrine_only_not_v46_benchmark_family_release_repo_wide_migration_execution_authority_minting_or_approval_authority",
  "requires_released_v47a_surfaces": true,
  "requires_released_v47b_surfaces": true,
  "requires_released_v47c_surfaces": true,
  "requires_released_v47d_surfaces": true,
  "requires_released_v47e_surfaces": true,
  "requires_released_v42d_local_eval_world": true,
  "requires_released_v42e_scorecard_world": true,
  "requires_released_v42g4_behavior_evidence_world": true,
  "anm_benchmark_policy_consumer_binding_profile_schema": "anm_benchmark_policy_consumer_binding_profile@1",
  "benchmark_consumer_world_kind_explicit_required": true,
  "benchmark_consumer_ref_kind_explicit_required": true,
  "d1_clause_policy_source_binding_required": true,
  "exactly_one_policy_source_ref_per_benchmark_row_required": true,
  "policy_source_vs_supporting_evidence_separation_required": true,
  "result_and_ledger_support_only_rule_required": true,
  "support_surface_contradiction_fail_closed_required": true,
  "support_surface_target_and_lineage_coherence_required": true,
  "benchmark_consumer_authority_relation_explicit_required": true,
  "allowed_benchmark_consumer_action_exact_enumeration_required": true,
  "benchmark_row_action_vocabulary_consistency_required": true,
  "benchmark_row_action_bucket_disjointness_required": true,
  "benchmark_authority_relation_action_bucket_consistency_required": true,
  "benchmark_world_and_ref_kind_invariants_required": true,
  "benchmark_ref_resolution_required": true,
  "released_v42_benchmark_authority_profile_respect_required": true,
  "upstream_v47c_v47d_v47e_profile_respect_required": true,
  "dangling_or_stale_upstream_doctrine_resolution_fail_closed_required": true,
  "same_snapshot_identity_required": true,
  "artifact_local_source_scope_compatibility_required": true,
  "benchmark_consumer_examples_required": true,
  "authoritative_and_mirrored_schema_export_parity_required": true,
  "no_v46_benchmark_family_release_yet": true,
  "no_submission_or_tournament_authority_minting_required": true,
  "no_repo_wide_markdown_migration_required": true,
  "no_source_level_deferred_yet": true,
  "no_execution_or_approval_authority_minting": true,
  "no_automatic_waiver_or_deferral_issuance": true,
  "required_released_contracts": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS92.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS93.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS98.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS107.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS108.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS109.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS110.md"
  ],
  "source_architecture_doc": "docs/DRAFT_AUTHORITATIVE_NORMATIVE_MARKDOWN_SPEC_v0.md",
  "reference_docs": [
    "docs/DRAFT_D1_DIALECT_SPEC_v0.md",
    "docs/DRAFT_D1_NORMALIZED_IR_SPEC_v0.md",
    "docs/DRAFT_PREDICATE_CONTRACTS_BOOTSTRAP_SPEC_v0.md",
    "docs/DRAFT_NEXT_ARC_OPTIONS_v29.md"
  ],
  "planning_doc": "docs/DRAFT_NEXT_ARC_OPTIONS_v30.md"
}
```

## Slice

- Arc label: `vNext+111`
- Family label: `V47-F`
- Scope label: bounded ANM benchmark-world policy-bearing consumer doctrine

## Objective

Release the bounded `V47-F` benchmark-world consumer lane by materializing one
canonical doctrine surface over the released `V47-A` + `V47-B` + `V47-C` + `V47-D` +
`V47-E` stack and already released benchmark artifact worlds on `main` that makes
explicit:

- which benchmark consumer worlds are supported in this first slice;
- which benchmark consumer refs are admissible in those worlds;
- which bound policy sources remain authoritative;
- when evaluation-result or ledger refs may appear only as supporting evidence;
- which constrain-only actions are allowed now, which still require a later lock, and
  which remain forbidden;
- what anti-leakage rules prevent benchmark consumers from quietly minting official
  scorecard, leaderboard, submission, tournament, execution, approval, waiver,
  deferral, or migration authority.

This slice is benchmark-consumer-first and non-executive. It does not reopen ANM
source syntax, normalized `D-IR`, checker facts, result sets, ledger semantics,
coexistence doctrine, ownership-transition doctrine, or descriptive/runtime consumer
doctrine. It also does not widen into `V46` benchmark-family release, repo-wide
markdown migration, source-level `DEFERRED`, submission execution, tournament
orchestration, execution authority, approval authority, or automatic waiver/deferral
issuance.

## Frozen Implementation Decisions

1. Family-boundary strategy:
   - `V47-F` releases benchmark-world consumer doctrine only over the already released
     `V47-A` + `V47-B` + `V47-C` + `V47-D` + `V47-E` stack and already released
     benchmark artifacts on `main`;
   - it does not reopen substrate semantics, hardening semantics, coexistence
     doctrine, ownership-transition doctrine, or descriptive/runtime consumer
     doctrine.
2. Package-ownership strategy:
   - `adeu_semantic_source` remains the owner of source-facing benchmark consumer
     binding inputs and deterministic derivation hooks;
   - `adeu_commitments_ir` owns the typed benchmark-consumer profile and its schema
     surface;
   - no additional package ownership is selected in this slice.
3. Benchmark-world strategy:
   - the first `V47-F` release supports only:
     - `released_v42_local_eval_artifact_world`
     - `released_v42_scorecard_artifact_world`
     - `released_v42_behavior_evidence_artifact_world`
   - the first `V47-F` release does not widen into:
     - `adeu_arc_submission_execution_record@1`
     - tournament or competition operator surfaces
     - generic `V46` benchmark-family doctrine
   - benchmark-world consumer binding remains bounded to already released typed
     artifacts rather than a new benchmark family release.
4. Policy-source strategy:
   - benchmark consumer rows must bind exactly one explicit authoritative policy source
     from released `D-IR` clause refs;
   - the first `V47-F` release does not leave multi-clause aggregation semantics open:
     - no unordered clause sets;
     - no implicit precedence between multiple clause refs;
     - no alternative-clause carrier is selected in this slice;
   - result-set refs and ledger refs may appear only as supporting evidence:
     - they may constrain interpretation or fail-closed posture;
     - they may not replace bound `D-IR` clause refs as standalone policy authority;
   - no benchmark consumer row may treat result or ledger state as self-authorizing
     policy;
   - any supporting result refs or supporting ledger refs must resolve coherently to:
     - the same benchmark consumer target;
     - the same declared snapshot and source-scope-compatible baseline;
     - the same bound policy-source lineage where that lineage is represented;
   - irrelevant or merely non-contradictory support surfaces are invalid in this
     slice;
   - if supporting result refs, supporting ledger refs, and the bound clause source
     imply contradictory posture, the row must fail closed rather than selecting a
     winner implicitly.
5. Benchmark-authority strategy:
   - benchmark consumer binding must respect already released benchmark-world authority
     posture rather than bypassing it through raw ref binding:
     - released `adeu_arc_local_eval_record@1` artifacts remain local-eval evidence and
       may not be reinterpreted as official scorecard or leaderboard authority;
     - released `adeu_arc_scorecard_manifest@1` artifacts must retain their typed
       source-kind, authority, and limitation posture;
     - released `adeu_arc_behavior_evidence_bundle@1` artifacts must retain their typed
       claim-posture and authority-boundary posture and may not be overread as
       execution, approval, submission, or tournament authority;
   - if a benchmark consumer row can only be made valid by ignoring released `V42-D`,
     `V42-E`, or `V42-G4` doctrine, it must fail closed.
6. Benchmark-action strategy:
   - `V47-F` may state:
     - when released policy sources may be referenced against a typed benchmark world;
     - when a bounded benchmark conformance annotation may be emitted;
     - when a fail-closed benchmark consumer block may be recorded;
     - when a traceable benchmark policy binding may be attached;
   - `allowed_now_actions`, `later_lock_required_actions`, and `forbidden_actions`
     must draw from the same frozen `allowed_benchmark_consumer_action` vocabulary;
   - the same action may not appear in more than one action bucket for the same row;
   - action-bucket posture must remain consistent with
     `current_benchmark_consumer_authority_relation`:
     - if `current_benchmark_consumer_authority_relation =
       constrain_only_non_executive`, `later_lock_required_actions` must be empty;
     - if `current_benchmark_consumer_authority_relation =
       later_lock_required_for_effective_action`, `later_lock_required_actions` must be
       non-empty;
   - `V47-F` may not infer those actions from naming alone or from local code
     convention without explicit typed rows.
7. Upstream-profile strategy:
   - benchmark consumer binding must also respect already released upstream ANM profile
     surfaces where those surfaces are relevant to the bound benchmark ref:
     - coexistence/adoption posture from released `V47-C` may not be bypassed;
     - selector/predicate ownership-transition posture from released `V47-D` may not
       be bypassed;
     - released descriptive/runtime consumer doctrine from `V47-E` may constrain later
       benchmark binding posture where the same policy source or support surfaces are
       reused.
   - if a benchmark row can only be made valid by ignoring released `V47-C`, `V47-D`,
     or `V47-E` profile doctrine, it must fail closed.
   - if any relevant released `V42-*` or `V47-*` upstream doctrine surface is
     dangling, stale, or cannot be resolved against the declared snapshot and
     source-scope-compatible baseline, the benchmark row is invalid rather than
     implementation-defined.
8. Authority-layer strategy:
   - benchmark consumer posture remains constrain-only and non-executive in this
     slice;
   - if a benchmark consumer row implies execution, approval, migration, official
     leaderboard authority, submission authority, tournament authority, waiver, or
     deferral effect, it must fail closed unless a later lock-level surface explicitly
     grants that effect.
9. Anti-overreach strategy:
   - `V47-F` may not mint execution, approval, mutation, scheduling, waiver, or
     deferral authority;
   - `V47-F` may not silently widen into repo-wide markdown migration;
   - `V47-F` may not silently widen into `V46` benchmark-family release, submission
     execution, tournament orchestration, or benchmark operator doctrine.

## Bounded Benchmark Consumer Vocabularies

The first `V47-F` release should freeze bounded benchmark-consumer vocabularies rather
than leave benchmark posture to implementation taste.

The intended bounded starter vocabularies are:

- `benchmark_consumer_world_kind`:
  - `released_v42_local_eval_artifact_world`
  - `released_v42_scorecard_artifact_world`
  - `released_v42_behavior_evidence_artifact_world`
- `benchmark_consumer_ref_kind`:
  - `released_v42_local_eval_record_ref`
  - `released_v42_scorecard_manifest_ref`
  - `released_v42_behavior_evidence_bundle_ref`
- `policy_source_ref_kind`:
  - `d1_clause_ref`
- `current_benchmark_consumer_authority_relation`:
  - `constrain_only_non_executive`
  - `later_lock_required_for_effective_action`
- `allowed_benchmark_consumer_action`:
  - `reference_released_policy_source`
  - `emit_benchmark_conformance_annotation`
  - `record_fail_closed_benchmark_consumer_block`
  - `attach_traceable_benchmark_policy_binding`

Any widening beyond these starter vocabularies should require a later bounded
continuation rather than silent doctrine creep.

The first `V47-F` release also freezes these row invariants:

- if `benchmark_consumer_world_kind = released_v42_local_eval_artifact_world`:
  - `benchmark_consumer_ref_kind = released_v42_local_eval_record_ref`
- if `benchmark_consumer_world_kind = released_v42_scorecard_artifact_world`:
  - `benchmark_consumer_ref_kind = released_v42_scorecard_manifest_ref`
- if `benchmark_consumer_world_kind = released_v42_behavior_evidence_artifact_world`:
  - `benchmark_consumer_ref_kind = released_v42_behavior_evidence_bundle_ref`

## Required Deliverables

1. New typed benchmark-consumer surface:
   - canonical `anm_benchmark_policy_consumer_binding_profile@1` artifact;
   - authoritative and mirrored schema export parity for that artifact.
2. Deterministic benchmark-consumer derivation entrypoint(s) that:
   - bind one declared snapshot identity;
   - consume one bounded source set over released `V47-A` + `V47-B` + `V47-C` +
     `V47-D` + `V47-E` artifact inputs plus released benchmark artifact worlds;
   - classify supported benchmark consumer worlds and refs into the frozen starter
     vocabularies;
   - preserve explicit single-clause `D-IR` binding as the authoritative policy
     source;
   - respect released `V42-D`, `V42-E`, and `V42-G4` benchmark doctrine and released
     `V47-C`, `V47-D`, and `V47-E` profile doctrine where relevant rather than
     bypassing them through raw ref binding;
   - fail closed on unresolved benchmark refs, missing policy sources, contradictory
     supporting surfaces, local-eval-as-official-authority claims,
     scorecard-source-kind overreach, behavior-evidence narrative laundering, or
     incompatible snapshot/source-scope bindings.
3. Top-level schema anchors for `anm_benchmark_policy_consumer_binding_profile@1`:
   - `schema`
   - `benchmark_consumer_binding_profile_id`
   - `snapshot_id`
   - `snapshot_sha256`
   - `source_scope_profile`
   - `released_stack_refs`
   - `benchmark_consumer_rows`
   - `semantic_hash`
   - per benchmark consumer row anchors:
     - `benchmark_consumer_ref`
     - `benchmark_consumer_world_kind`
     - `benchmark_consumer_ref_kind`
     - `policy_source_ref`
     - `policy_source_ref_kind`
     - `supporting_result_refs`
     - `supporting_ledger_refs`
     - `current_benchmark_consumer_authority_relation`
     - `allowed_now_actions`
     - `later_lock_required_actions`
     - `forbidden_actions`
     - benchmark row invariants:
       - if `benchmark_consumer_world_kind = released_v42_local_eval_artifact_world`:
         - `benchmark_consumer_ref_kind = released_v42_local_eval_record_ref`
       - if `benchmark_consumer_world_kind = released_v42_scorecard_artifact_world`:
         - `benchmark_consumer_ref_kind = released_v42_scorecard_manifest_ref`
       - if `benchmark_consumer_world_kind = released_v42_behavior_evidence_artifact_world`:
         - `benchmark_consumer_ref_kind = released_v42_behavior_evidence_bundle_ref`
       - exactly one `policy_source_ref` is required per benchmark consumer row;
       - `supporting_result_refs` and `supporting_ledger_refs` must cohere to the same
         benchmark consumer target, same declared snapshot, and same bound
         policy-source lineage where that lineage is represented;
       - `allowed_now_actions`, `later_lock_required_actions`, and
         `forbidden_actions` must all draw from the same frozen
         `allowed_benchmark_consumer_action` vocabulary;
       - no action may appear in more than one of:
         - `allowed_now_actions`
         - `later_lock_required_actions`
         - `forbidden_actions`
       - if `current_benchmark_consumer_authority_relation =
         constrain_only_non_executive`:
         - `later_lock_required_actions` must be empty;
       - if `current_benchmark_consumer_authority_relation =
         later_lock_required_for_effective_action`:
         - `later_lock_required_actions` must be non-empty.
4. Accepted doctrine fixtures:
   - at least one accepted local-eval benchmark consumer fixture;
   - at least one accepted scorecard benchmark consumer fixture;
   - at least one accepted behavior-evidence benchmark consumer fixture;
   - at least one accepted fixture showing result/ledger refs used only as supporting
     evidence under one bound `D-IR` clause source;
   - at least one accepted constrain-action matrix fixture.
5. Reject fixtures that fail closed on:
   - benchmark consumer rows with supporting result/ledger refs but no bound `D-IR`
     clause source;
   - benchmark consumer rows with contradictory supporting result/ledger posture;
   - benchmark consumer rows with support surfaces that do not cohere to the same
     target, same declared snapshot, or same bound policy-source lineage;
   - unresolved released `V42-D` local eval refs;
   - unresolved released `V42-E` scorecard refs;
   - unresolved released `V42-G4` behavior-evidence refs;
   - benchmark consumer rows whose world kind and ref kind do not match the frozen row
     invariants;
   - benchmark consumer rows that bypass released `V42-D`, `V42-E`, or `V42-G4`
     authority doctrine where that doctrine is relevant to the bound benchmark ref;
   - benchmark consumer rows that bypass released `V47-C`, `V47-D`, or `V47-E` profile
     doctrine where that doctrine is relevant to the bound benchmark ref;
   - benchmark consumer rows whose relevant released `V42-*` or `V47-*` upstream
     doctrine joins are dangling, stale, or unresolved against the declared snapshot
     and source scope;
   - benchmark consumer rows that treat local eval as official scorecard or
     leaderboard authority;
   - benchmark consumer rows that overread scorecard source-kind or authority posture;
   - benchmark consumer rows that treat behavior evidence bundle narrative or claim
     posture as execution, approval, submission, or tournament authority;
   - benchmark consumer rows with overlapping action buckets or action buckets that are
     inconsistent with `current_benchmark_consumer_authority_relation`;
   - benchmark consumer actions outside the frozen enum;
   - consumer rows bound to incompatible snapshot identity or source scope.
6. Deterministic targeted tests covering:
   - local-eval benchmark consumer binding;
   - scorecard benchmark consumer binding;
   - behavior-evidence benchmark consumer binding;
   - support-only and contradiction validation;
   - upstream benchmark-profile and ANM-profile respect;
   - schema export parity;
   - reject-fixture fail-closed behavior.

## Acceptance

`V47-F` is complete when:

1. `anm_benchmark_policy_consumer_binding_profile@1` ships with authoritative/mirror
   schema parity;
2. accepted fixtures show local-eval, scorecard, and behavior-evidence benchmark
   consumer posture without ambiguity;
3. every accepted benchmark consumer row binds exactly one explicit `D-IR` clause
   source rather than multi-clause or support-surface authority;
4. result-set and ledger refs remain support-only and fail closed on contradiction;
5. support surfaces cohere to the same benchmark target, same declared snapshot, and
   same bound policy-source lineage where that lineage is represented;
6. benchmark refs and relevant upstream doctrine joins resolve fail closed against the
   declared snapshot and source scope;
7. benchmark consumer binding respects already released `V42-D`, `V42-E`, and
   `V42-G4` authority doctrine plus relevant released `V47-C`, `V47-D`, and `V47-E`
   profile doctrine;
8. benchmark action buckets are pairwise disjoint and stay consistent with
   `current_benchmark_consumer_authority_relation`;
9. benchmark consumers remain constrain-only and non-executive and do not mint
   official scorecard, leaderboard, submission, tournament, execution, or approval
   authority;
10. `V46` benchmark-family release remains deferred rather than being silently widened
    into this slice.

## Do Not Ship

Do not treat `V47-F` as authority to ship:

- `V46` benchmark-family release;
- repo-wide markdown migration;
- source-level `DEFERRED`;
- official scorecard, leaderboard, submission, or tournament authority;
- execution, approval, mutation, scheduling, waiver, or deferral authority;
- automatic supersession of current markdown authority;
- silent reinterpretation of local eval, scorecard, or behavior-evidence artifacts into
  stronger authority than their released doctrine permits.
