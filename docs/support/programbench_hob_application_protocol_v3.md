# ProgramBench HOB Application Protocol v3

Authority layer: support.

This note is a support-layer overlay on
`docs/support/programbench_hob_application_protocol_v2.md`. It incorporates the
Phase 18 v23 correction: independent discovery lanes and prior repair runs must
be merged into one owner-aware preservation target before implementation.

## Controlling Artifacts

```text
base protocol:
  docs/support/programbench_hob_application_protocol_v0.md

question-card overlay:
  docs/support/programbench_hob_application_protocol_v1.md
  docs/support/programbench_hob_node_question_cards_v0.md

audit-to-tree hardening:
  docs/support/programbench_hob_application_protocol_v2.md
  docs/support/phase16_audit_of_audit_v18_patch.md

phase-transition guard:
  docs/support/programbench_hob_guard_phase_transition_schema_v0.md

cross-run preservation guard:
  docs/support/programbench_hob_guard_cross_run_regression_schema_v0.md
  docs/support/phase18_v23_cross_run_regression_conservation_patch.md

catalog:
  docs/support/programbench_hob_obligation_catalog_v0.json
```

## V3 Hardening Summary

V2 prevents broad post-eval buckets from becoming worker-ready before they are
lowered into numbered HOB obligations. V3 prevents each run family from becoming
an alternative partial program.

```text
orthogonal discovery lanes
  -> HOB node mapping
  -> cross-run win-owner registry
  -> implementation owner map
  -> impact cone
  -> preservation sentinels
  -> merged implementation target
```

The implementation worker should receive the merged target, not the output of a
single run family such as "v20", "HOB phase21", or "intent track".

## Cross-Run Preservation Gate

Trigger:

```text
historical run data exists and a new implementation handoff is planned.
```

Rule:

```text
Every prior best-known leaf that shares an implementation owner with the new
patch batch becomes a preservation obligation unless explicitly deferred,
conflict-isolated, or superseded with a warranted better rule.
```

Required artifacts:

```text
hob_guard_cross_run_delta_ledger@1
hob_guard_win_owner_registry@1
hob_guard_implementation_impact_cone@1
hob_guard_axis_commutation_register@1
hob_guard_compatibility_overlay_map@1
hob_guard_cross_run_merge_handoff@1
```

## Discovery Pool vs Implementation Owner

Orthogonal semantic pools remain independent for discovery. They are not
independent for implementation.

Forbidden shortcut:

```text
semantic pool output -> implementation patch
```

Required route:

```text
semantic pool output
  -> HOB mapping
  -> implementation owner mapping
  -> impact cone
  -> preservation sentinels
  -> implementation patch
```

If two semantic axes share an owner, they must be treated as potentially
non-commuting until sentinel evidence says otherwise.

## Compatibility Overlay Gate

Mechanism-core improvements must not overwrite compatibility exactness surfaces.
For ProgramBench reconstructions, the following are overlays unless proved
otherwise:

```text
help and usage text
unknown flag wording and exit behavior
stdout/stderr split
analyze/report output
renderer byte grammars
config/db diagnostics
output option edge cases
file side effects
exit precedence
```

Overlay leaves require exact sentinels. They cannot be approximated by a
mechanism-core rule alone.

## Batch 0 Contract

Before the next implementation patch on a task with prior evaluated runs:

```text
1. Build a row-level cross-run delta ledger.
2. Assign best-known owner runs to solved leaves.
3. Map solved leaves to implementation owners.
4. Identify compatibility overlays.
5. Compute the next patch impact cone.
6. Import all touched prior wins as preservation sentinels.
7. Build a merged target Omega*, with explicit deferrals and conflicts.
8. Block implementation if any touched must-preserve leaf has no sentinel.
```

For the current `trdsql` family, the first Batch 0 merge should include:

```text
current guarded v20 run:
  broad generative mechanism wins.

best HOB phase21 run:
  exactness and regression-conserving wins.

HOB phase9 baseline:
  initial HOB-owned leaves and comparison baseline.

v19/v20 second-track wins:
  utility-discovered user-job leaves.
```

## Readiness Consequences

```text
method_test:
  May proceed with incomplete preservation gates, but cannot be compared as
  product progress without regression accounting.

scoped_repair:
  May proceed when open preservation rows are explicitly outside scope and risk
  is recorded.

product_repair_attempt:
  Requires all must-preserve leaves in the patch impact cone to have green or
  runnable sentinels.

gold_attempt:
  Requires all visible, sealed, historical, and compatibility-overlay
  preservation sentinels to be green or conflict-isolated without gold claim.
```

## Worker Handoff Rule

The worker baton must name:

```text
merged target ref
patch impact cone ref
implementation owners touched
must-preserve sentinel refs
compatibility overlay refs
explicit non-goals / deferrals
forbidden strategy rows
```

The baton must not ask the worker to preserve "all previous behavior" in prose.
The preservation set must be concrete and owner-linked.

## Failure Classes

Add these blocking failures to the protocol:

```text
cross_run_delta_ledger_missing
win_owner_registry_missing
prior_win_without_owner
regression_without_hob_node
must_preserve_without_sentinel
impact_cone_missing
impact_cone_missing_prior_win_import
semantic_pool_used_as_patch_authority
implementation_owner_commutation_assumed
compatibility_overlay_missing
cross_run_merge_handoff_missing
handoff_targets_prior_run_instead_of_merged_target
method_test_compared_as_product_progress
```

## Bottom Line

```text
Run-to-run variation should become a merge of partial leaf owners, not a
competition between alternative partial implementations.
```

