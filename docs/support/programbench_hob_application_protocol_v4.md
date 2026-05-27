# ProgramBench HOB Application Protocol v4

Authority layer: support.

This note is a support-layer overlay on
`docs/support/programbench_hob_application_protocol_v3.md`. It incorporates the
Phase 56 v28 correction: after a high-score method gain, remaining official
failures must be re-entered as schema-level tail rows before implementation.

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

official-tail re-entry guard:
  docs/support/phase56_v28_schema_integration_review.md
  docs/support/principled_recursive_odeu_meta_program_experimental_v28.md

catalog:
  docs/support/programbench_hob_obligation_catalog_v0.json
```

## V4 Hardening Summary

V2 prevents broad post-eval buckets from becoming worker-ready before they are
lowered into numbered HOB obligations. V3 prevents each run family from becoming
an alternative partial program. V4 prevents scoped-green local matrices from
being promoted to gold-ready while official sibling tails remain.

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

## V4 Official Tail Re-Entry Gate

Trigger:

```text
An official eval after a scoped repair, method-test patch, or high-score method
gain leaves a compact failure tail clustered by public schema family or shared
implementation owner.
```

Required route:

```text
official failure cluster
  -> official_tail_reentry_row
  -> HOB node attachment
  -> gate classification
  -> preservation sentinel import
  -> worker baton, only if probe-ready or implementation-ready
```

Every remaining cluster must be classified as exactly one primary relation:

```text
new_parent_missing
missing_sibling_under_existing_parent
compatibility_overlay_conflict
target_substrate_equivalence
implementation_transfer_bug
post_eval_only_unknown
```

Blocking rule:

```text
No post-eval tail cluster may be handed to a worker as "fix this bucket" until
the tail row names its HOB nodes, owner, next gate, preservation sentinels, and
handoff posture.
```

## V4 Scoped-Green Tail Readiness

Add readiness state:

```text
scoped_green_with_official_sibling_tail
```

Meaning:

```text
The local/reference matrix is valuable enough to preserve, but official
pressure names sibling behavior under the same parent or owner. The subtree is
not gold-ready.
```

Promotion rule:

```text
scoped_green_with_official_sibling_tail cannot be promoted to gold_ready by
passing the existing local matrix. Promotion requires either sibling expansion
and closure, conflict isolation, target-substrate proof, or explicit deferral
with expected official risk.
```

## V4 Batch 0 Tail Compilation

Before the next implementation batch after a high-score tail:

```text
1. Import all regressions versus the selected preservation baseline as
   must-preserve sentinels.
2. Fill official_tail_reentry_row for every remaining cluster.
3. Attach each row to numbered HOB child nodes.
4. Mark each cluster's next gate:
   - compatibility overlay
   - target dependency equivalence
   - public sublanguage closure
   - scoped-to-gold sibling expansion
   - implementation transfer repair
5. Produce a concrete worker baton only after the target gate is probe-ready.
```

For `trdsql` Phase 56, the first tail compilation must cover:

```text
JSON/YAML value-domain and error grammar
jq selector sublanguage
zstd and compression ecology
fixed-width reader
CLI help argparse overlay
TBLN schema/type grammar
config/db state topology
row universe and input row shape
resource diagnostic and mutation overlays
analyze exactness
SQL numeric rendering
output router priority
```

## V4 Tail Worker Handoff Rule

The baton must name:

```text
handoff type
target cluster
target HOB nodes
primary gate
allowed owners
forbidden owners
pre-patch probes
reference observations
target-substrate observations
preservation sentinels
official tail rows used only as pressure
local matrix closure target
post-patch reporting requirements
```

The baton must not say:

```text
fix jq
fix JSON/YAML
fix compression
fix help
fix TBLN
```

It must say:

```text
close this numbered tail subtree, under this gate, through these owners, while
preserving these sentinels.
```

## V4 Additional Blocking Failures

```text
official_tail_reentry_missing
tail_cluster_used_as_worker_baton
scoped_green_promoted_with_official_tail
tail_cluster_without_hob_node
tail_cluster_without_primary_relation
compatibility_overlay_branch_discriminator_missing
target_dependency_without_packaged_proof
sublanguage_tail_without_child_matrix
tail_worker_baton_missing_preservation_sentinels
```

## Bottom Line

```text
Run-to-run variation should become a merge of partial leaf owners, not a
competition between alternative partial implementations.

After high-score method gains, official tails should become schema re-entry
rows, not broad patch queues.
```
