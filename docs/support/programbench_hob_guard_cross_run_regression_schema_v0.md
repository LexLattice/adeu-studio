# ProgramBench HOB Guard Cross-Run Regression Schema v0

Authority layer: support / proposed orchestrator guard schema.

Purpose: make the v23 cross-run regression-conservation rule executable before
implementation handoff. This schema does not decide program behavior, generate
ontology, run probes, or patch code. It records which previous runs own which
behavior leaves, which implementation owners can affect them, and which
preservation sentinels must be imported before a new patch batch is allowed.

This is an overlay on:

```text
docs/support/programbench_hob_guard_phase_transition_schema_v0.md
docs/support/programbench_hob_application_protocol_v2.md
docs/support/phase18_v23_cross_run_regression_conservation_patch.md
```

## 1. Core Invariant

```text
A new semantic axis may not be optimized until the orchestrator has proven which
previously green leaves share its implementation owners and has imported those
leaves as preservation obligations.
```

The key distinction is:

```text
semantic-pool independence
  !=
implementation-effect independence
```

Orthogonal semantic pools may discover obligations independently. A patch batch
is independent only if its implementation impact cone does not touch another
owned leaf, or if every touched owned leaf has a preservation sentinel.

## 2. Trigger

This guard is required before `P11_implementation_handoff_contract` when any of
the following is true:

```text
more than one prior run has official/local comparison data
a current run improves one semantic family while regressing another
a patch batch touches shared owners such as CLI, renderer, source router, value
  normalizer, config/db substrate, or diagnostic emitter
an implementation handoff uses outputs from multiple semantic pools
the run posture is product_repair_attempt or gold_attempt
```

If the guard is skipped, `P17_official_eval_experiment_or_gold_attempt` may only
be authorized as `method_test` or `scoped_experiment`.

## 3. Record: hob_guard_cross_run_delta_ledger@1

```yaml
schema: hob_guard_cross_run_delta_ledger@1
ledger_id: string
run_id: string
task_id: string
comparison_set_refs:
  - run_ref: string
    run_role:
      enum:
        - current_candidate
        - best_known_run
        - baseline_run
        - orthogonal_pool_run
        - post_eval_repair_run
    score: number | null
    passed: integer | null
    failed: integer | null
    skipped: integer | null
    evidence_authority:
      enum:
        - local_locked
        - reference_locked
        - official_eval_pressure
        - source_postmortem
        - method_test_pressure

delta_rows:
  - eval_row_id: string
    test_namespace: string | null
    previous_run_ref: string
    current_run_ref: string
    previous_status:
      enum: [pass, fail, skip, unknown]
    current_status:
      enum: [pass, fail, skip, unknown]
    delta_class:
      enum:
        - persistent_pass
        - new_win
        - regression
        - persistent_failure
        - status_unknown
    previous_owner_run: string | null
    current_owner_run: string | null
    hob_node_ref: string | null
    semantic_pool_refs:
      - string
    implementation_owner_refs:
      - string
    evidence_authority:
      enum:
        - local_locked
        - reference_locked
        - official_eval_pressure
        - source_postmortem
        - method_test_pressure
```

Validation rules:

```text
Every regression must have either a hob_node_ref or an explicit unknown-node
  blocker.
Every new_win that is reused in a later target must have an owner run.
Score deltas alone cannot satisfy this record; row-level deltas are required.
Official eval pressure cannot be promoted to clean first-pass evidence.
```

## 4. Record: hob_guard_win_owner_registry@1

```yaml
schema: hob_guard_win_owner_registry@1
registry_id: string
run_id: string
source_delta_ledger_ref: string

win_owner_rows:
  - leaf_ref: string
    best_known_owner_run: string
    best_known_evidence_refs:
      - string
    owned_surface:
      enum:
        - stdout
        - stderr
        - exit
        - file
        - resource
        - mode
        - renderer
        - diagnostic
        - state
        - row_universe
        - aggregation_denominator
    semantic_family: string
    implementation_owner:
      enum:
        - cli_parser
        - mode_dispatch
        - source_router
        - input_importer_registry
        - sql_binder
        - sqlite_executor
        - value_normalizer
        - renderer_registry
        - analyze_renderer
        - config_db_topology
        - diagnostic_emitter
        - output_file_router
        - unknown_owner
    preservation_status:
      enum:
        - must_preserve
        - may_defer_scoped
        - conflict_isolated
        - obsolete_by_better_rule
        - blocked_unknown_owner
    sentinel_probe_refs:
      - string
    deferral_or_conflict_warrant_ref: string | null
```

Validation rules:

```text
must_preserve rows require at least one sentinel_probe_ref before implementation.
blocked_unknown_owner blocks product_repair_attempt and gold_attempt.
may_defer_scoped requires an expected-risk warrant and cannot support gold-ready.
obsolete_by_better_rule requires a replacement leaf_ref and evidence ref.
```

## 5. Record: hob_guard_implementation_impact_cone@1

```yaml
schema: hob_guard_implementation_impact_cone@1
impact_cone_id: string
run_id: string
patch_batch_ref: string
planned_worker_baton_ref: string | null

touched_code_owners:
  - enum:
      - cli_parser
      - mode_dispatch
      - source_router
      - input_importer_registry
      - sql_binder
      - sqlite_executor
      - value_normalizer
      - renderer_registry
      - analyze_renderer
      - config_db_topology
      - diagnostic_emitter
      - output_file_router

affected_hob_nodes:
  - string

affected_semantic_pools:
  - string

imported_preservation_rows:
  - leaf_ref: string
    sentinel_probe_refs:
      - string
    import_reason:
      enum:
        - same_implementation_owner
        - observed_prior_regression
        - non_commutation_risk
        - compatibility_overlay
        - explicit_conflict_boundary

non_commutation_risk_refs:
  - string

impact_cone_status:
  enum:
    - clear
    - requires_more_sentinels
    - blocked_unknown_owner
    - blocked_unclassified_regression
    - blocked_checker_leak
```

Validation rules:

```text
Every touched_code_owner must import all must_preserve win-owner rows with that
  implementation_owner.
Every imported preservation row must have at least one sentinel probe or a
  scoped deferral warrant.
blocked statuses block P11 -> P12 except for method_test downgrade.
```

Default owner sentinel expectations:

```text
source_router:
  analyze, ordinary query, wildcard, compression, path identity, diagnostics.

renderer_registry:
  query renderers, analyze renderers, raw, TBLN, YAML, Markdown, ASCII,
  vertical, output-file routing.

cli_parser / mode_dispatch:
  help, unknown flags, flag precedence, analyze/config/debug/version modes,
  stdout/stderr/exit routing.

value_normalizer:
  nulls, numeric/string conversion, JSON/YAML/TBLN values, SQL aggregates,
  raw output.

config_db_topology:
  config mode, db list, driver naming, connection diagnostics, persistent state.
```

## 6. Record: hob_guard_axis_commutation_register@1

```yaml
schema: hob_guard_axis_commutation_register@1
register_id: string
run_id: string

axis_commutation_rows:
  - axis_a: string
    axis_b: string
    shared_owner:
      enum:
        - cli_parser
        - mode_dispatch
        - source_router
        - input_importer_registry
        - sql_binder
        - sqlite_executor
        - value_normalizer
        - renderer_registry
        - analyze_renderer
        - config_db_topology
        - diagnostic_emitter
        - output_file_router
    predicted_commutes:
      enum: [true, false, unknown]
    required_sentinel_refs:
      - string
    observed_result:
      enum:
        - not_observed
        - commuted
        - regressed_axis_a
        - regressed_axis_b
        - conflict
```

Validation rules:

```text
predicted_commutes = unknown requires sentinel coverage for both axes.
observed_result = regressed_axis_a or regressed_axis_b must feed the next
  cross_run_delta_ledger as regression evidence.
No implementation handoff may assume semantic-pool independence implies
  commutation.
```

## 7. Record: hob_guard_compatibility_overlay_map@1

```yaml
schema: hob_guard_compatibility_overlay_map@1
map_id: string
run_id: string

compatibility_overlay_rows:
  - overlay_ref: string
    base_mechanism_ref: string
    surface:
      enum:
        - help
        - analyze
        - renderer
        - config
        - diagnostic
        - output_option
        - file_side_effect
        - exit_precedence
    exactness_contract_refs:
      - string
    can_be_approximated: false
    sentinel_refs:
      - string
    owner_run_ref: string | null
    implementation_owner_ref: string
```

Validation rules:

```text
can_be_approximated must be false for compatibility overlays.
Every overlay used in a product repair handoff requires sentinels.
Mechanism-core patches cannot overwrite overlay rows without importing their
  sentinels into the impact cone.
```

## 8. Record: hob_guard_cross_run_merge_handoff@1

```yaml
schema: hob_guard_cross_run_merge_handoff@1
handoff_id: string
run_id: string
target_name: string
target_posture:
  enum:
    - scoped_repair
    - product_repair_attempt
    - gold_attempt
    - method_test

included_owner_rows:
  - leaf_ref: string
    source_run_ref: string
    inclusion_class:
      enum:
        - current_generative_core
        - best_hob_exactness_leaf
        - utility_discovered_leaf
        - public_schema_leaf
        - anti_replay_guard_leaf

explicit_deferrals:
  - leaf_ref: string
    deferral_class:
      enum:
        - scoped_deferred_with_expected_risk
        - gold_deferred_with_expected_risk
        - conflict_isolated
        - blocked_pending_equivalence
    warrant_ref: string

required_artifacts:
  - cross_run_delta_ledger
  - win_owner_registry
  - implementation_impact_cone
  - axis_commutation_register
  - compatibility_overlay_map
  - must_preserve_sentinel_manifest

handoff_status:
  enum:
    - ready_for_scoped_repair
    - ready_for_product_repair
    - ready_for_gold_attempt
    - blocked_missing_preservation
    - blocked_unclassified_regression
    - blocked_unknown_owner
```

Validation rules:

```text
The worker target is the merged target, not a named prior run family.
Any included leaf from an older run becomes a preservation obligation.
ready_for_gold_attempt requires no gold_deferred, unknown-owner, or red
  must-preserve sentinels.
ready_for_product_repair requires all must-preserve leaves in the impact cone
  to have sentinel coverage.
```

## 9. Integration With Phase Transitions

```text
P10 -> P11 requires:
  cross_run_delta_ledger if historical run data exists.
  win_owner_registry for every reused prior pass/win.
  compatibility_overlay_map for exact output/diagnostic surfaces.

P11 -> P12 requires:
  implementation_impact_cone clear for the worker batch.
  cross_run_merge_handoff ready at the declared posture.

P14 -> P15 requires:
  must-preserve sentinels are runnable locally.

P15 -> P16 requires:
  anti-replay still passes after preservation sentinels are added.

P16 -> P17 requires:
  regression conservation green for all must-preserve leaves, or official eval
  is downgraded to method_test/scoped_experiment.
```

## 10. Batch 0 Required Outputs

For the current `trdsql` family, Batch 0 should produce:

```text
cross_run_delta_ledger:
  current guarded v20
  best HOB phase21
  HOB phase9 baseline
  v19/v20 second-track wins

win_owner_registry:
  exactness owners for analyze/report, CLI/argparse, config/db diagnostics,
  TBLN/YAML/renderers, output options.

implementation_owner_map:
  source_router, renderer_registry, cli_parser/mode_dispatch,
  value_normalizer, config_db_topology, diagnostic_emitter.

compatibility_overlay_map:
  help/usage, analyze output, renderer byte grammar, config diagnostics,
  output option edge cases.

must_preserve_sentinel_manifest:
  all prior best-known leaves touched by the next patch impact cone.

open_conflict_ledger:
  leaves whose best known behavior conflicts across prior runs or evidence
  authorities.
```

No implementation worker should receive Batch 1 until Batch 0 exists.

## 11. Failure Classes

```text
cross_run_delta_ledger_missing
win_owner_registry_missing
prior_win_without_owner
regression_without_hob_node
regression_without_owner
must_preserve_without_sentinel
impact_cone_missing
impact_cone_unknown_owner
impact_cone_missing_prior_win_import
semantic_pool_used_as_patch_authority
implementation_owner_commutation_assumed
compatibility_overlay_missing
compatibility_overlay_approximated
cross_run_merge_handoff_missing
handoff_targets_prior_run_instead_of_merged_target
product_attempt_with_red_preservation_sentinel
gold_attempt_with_scoped_deferral
method_test_compared_as_product_progress
```

## 12. Bottom Line

```text
Run variation should become a constructive merge of partial leaf owners, not a
competition between alternative partial programs.
```

