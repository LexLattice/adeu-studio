# Program ODEU Gold Scaffold Adversarial Bookkeeper v2

Status: support note.

Authority layer: support only.

Scope: adversarial checker for ProgramBench-style scaffold generation. This document tells a separate bookkeeper how to audit generator artifacts for forgotten primitives, fields, axes, probes, and D-ledger obligations.

Companion document:

```text
docs/support/Program_ODEU_Gold_Scaffold_Generator_Meta_Program_v2.md
```

## 0. Role Boundary

The bookkeeper is not the scaffold generator.

The bookkeeper's job is adversarial continuity:

```text
What did the generator discover?
What did it fail to obligationize?
What did it obligationize but later drop?
What did it probe without an axis?
What did it claim as ready without evidence?
```

The bookkeeper must not improve the scaffold by silently writing the missing rows itself. It should produce objections, required repairs, and minimal row templates that the generator must instantiate in a follow-up pass.

The bookkeeper is allowed to force tracking and probe allocation. It is not
allowed to mint implementation truth by pressure alone.

Authority ladder to preserve:

```text
discovered_candidate
obligationized_for_tracking
probe_required_pending_observation
locked_by_visible_spec
locked_by_observation
explicitly_deferred_with_reason
```

Bookkeeper objections may require:

```text
obligationized_for_tracking
probe_required_pending_observation
explicitly_deferred_with_reason
```

Bookkeeper objections must not require:

```text
locked_by_visible_spec
locked_by_observation
```

unless the visible packet or allowed observation actually supplies that authority.

## 1. Inputs

Expected generator packet:

```text
visible task packet
phase1_primitives_and_indications
phase2_generated_question_artifacts
phase3_axis_and_interaction_ledger
phase4_probe_allocation_plan
phase5_pre_observation_scaffold_candidate
generator_to_bookkeeper_handoff
```

If a file or section is missing, the bookkeeper must mark the packet:

```text
blocked_missing_required_artifact
```

## 2. Output Packet

The bookkeeper must produce:

```text
bookkeeper_shadow_inventory
bookkeeper_obligation_continuity_audit
bookkeeper_forgetting_objections
bookkeeper_probe_adequacy_audit
bookkeeper_upstream_discriminator_audit
bookkeeper_readiness_decision
```

All objections must use stable IDs:

```text
BK-FIELD-
BK-OBL-
BK-AXIS-
BK-PROBE-
BK-D-
BK-UD-
BK-READY-
```

## 3. Independent Visible-Packet Shadow Pass

Before auditing generator continuity, the bookkeeper must independently scan
the visible task packet for structural indications that the generator may have
missed.

This pass is adversarial and shallow. It does not replace scaffold generation,
but it must identify candidate obligations that should have appeared in the
generator packet.

Required checks:

```text
named external producers, commands, APIs, formats, schemas, runtimes
structured examples that may be incomplete samples
visible nested records or replacement/alias surfaces
visible filters, modes, and aggregate exits
visible byte/process/runtime surfaces
visible help/usage or dependency/toolchain notes
visible version, no-args, executable identity, or "run help for full usage" notes
renderer-heavy/golden-output surfaces
multi-mode interactions sharing renderer, path, follow, sort, slow, compare,
or progress behavior
```

For each named producer or public structured format, ask:

```text
What fields can this producer normally emit that the visible example omitted?
Could any omitted field affect membership, main/root status, replacement,
selection, validity, filtering, error status, deprecation/retraction,
runtime identity, aggregate exit, or parser/type-error text?
```

If the generator did not name a plausible omitted field that this pass finds,
create a blocking or warning objection:

```text
generator_failed_to_extract_candidate_obligation
```

The bookkeeper may use general programming knowledge about public formats and
standard tool outputs, but it must label the inference:

```text
visible_spec_explicit
producer_name_inference
program_class_inference
requires_observation
```

If a CLI visible packet points to help/full usage/version behavior, the
bookkeeper must verify that the generator produced a help/usage bootstrapping
surface before implementation handoff. Missing help/version/no-args bootstraps
are blocking unless the visible packet proves the program is not a CLI.

## 4. Shadow Inventory

Build a shadow inventory from every generator artifact, not only from the final scaffold.

Collect every row that names or implies:

```text
primitive
field
omitted producer-schema field
nested object
replacement/alias/shadowing surface
filter or membership gate
status/error/deprecation/retraction/lifecycle field
validation field
aggregate/exit field
renderer or formatter surface
runtime/parser/type-error surface
help/usage/control-plane surface
version/executable-identity surface
golden fixture morphology
mode-interaction closure row
upstream-discriminator repair row
observation question
probe obligation
D-ledger candidate
```

For each item, record:

```text
shadow_id
source_artifact_ref
source_row_ref
item_name
item_kind
first_seen_phase
evidence_authority
inferred_effect_class
observable_surface_hypothesis
behavior_bearing_posture
generator_status
authority_status
bookkeeper_status
```

Allowed `bookkeeper_status` values:

```text
tracked
needs_obligation
needs_axis
needs_probe
needs_D_row
needs_explicit_deferral
proven_pass_through
blocking_forgetting_error
```

## 5. Obligationization Audit

The bookkeeper must enforce this gate:

```text
Every plausible omitted producer-schema field must become an obligation,
split into obligations, be explicitly deferred, or be proven pass-through.
```

This is the rule that catches fields that appear in producer-schema expansion but disappear before axes or probes.

Behavior-bearing or potentially behavior-bearing effect classes:

```text
unknown_requires_probe
lifecycle_filter_field
control_field
subject_selection_field
validation_field
aggregate_field
identity_or_error_surface_field
renderer_or_formatter
dependency_or_runtime_surface
```

Field names that require challenge even when the generator labels them vague metadata:

```text
main
root
primary
selected
replace
replacement
alias
override
shadow
indirect
optional
test
error
status
state
deprecated
retracted
version
time
timestamp
path
dir
file
module
package
exit
ci
valid
invalid
```

For each challenged item, ask:

```text
Could this field remove a row without being displayed?
Could it alter the selected subject?
Could it alter display truth, control truth, validation truth, or aggregate truth?
Could it affect exit status or summary denominator?
Could it be observable only through parser/type-error text?
Could wrong type, missing, null, or empty value expose a distinct surface?
Could it interact with filters, modes, renderer, or process exit?
```

If any answer is "yes", "possibly", or "unknown", the item needs an obligation or explicit deferral. It may not remain inventory-only.

If the item is inferred from producer knowledge rather than directly specified
by the visible packet, the bookkeeper should normally require:

```text
probe_required_pending_observation
```

not:

```text
locked_by_visible_spec
locked_by_observation
```

## 6. Continuity Audit

For every shadow item, trace the chain:

```text
first_seen
  -> obligation row
  -> primitive or de-lumped row
  -> axis row
  -> interaction row, if applicable
  -> probe row
  -> D-ledger row or explicit deferral
```

Allowed terminal states:

```text
D_row_with_probe
explicitly_deferred_with_reason
proven_pass_through_with_reason
superseded_by_ref
split_into_children_all_tracked
```

Blocking terminal states:

```text
inventory_only
axis_only
probe_only
D_row_without_probe
deferred_without_reason
grouped_high_risk_row
silent_drop
speculative_candidate_promoted_to_locked_implementation_truth
```

The bookkeeper must treat a generator self-declaration like "all high-risk obligations are carried" as evidence to inspect, not evidence to accept.

It must also reject a repair packet that solves forgetting by over-promoting a
producer-name inference into a locked D-row. The proper repair is usually:

```text
candidate obligation + probe allocation + observation gate
```

not:

```text
unobserved implementation requirement
```

## 7. Forgotten-Field Pattern Checks

The bookkeeper must specifically scan for these patterns:

```text
field appears in field-effect inventory but not de-lumping
field appears in producer-schema omitted fields but not obligation ledger
field appears as unknown_requires_probe but no probe exists
field appears as pass-through metadata without proof
field appears in phase 2 but not phases 3, 4, or 5
nested object appears but child fields are not split
filter/membership field appears but no all-filtered probe exists
validation field appears but no missing/null/wrong-type lattice exists
runtime/error field appears but no process-surface probe exists
renderer field appears but no byte snapshot exists
aggregate/CI field appears but denominator is not named
CLI help/version/no-args surface appears but no HU/VE rows exist
observed help output names flags that are not obligationized
renderer-heavy program has byte probes but no golden-fixture morphology mesh
mode flags share renderer/path/follow/order/exit surfaces but no interaction rows exist
repair fixes one branch while regressing another, but no upstream-discriminator row exists
two failure groups alternate between green/red under broad patches
```

Any match requires either a blocking objection or a recorded non-blocking rationale.

## 8. Probe Adequacy Audit

A probe is adequate only if it traces to a source axis, interaction, or explicit external-surface obligation.

For every high-risk axis, check for:

```text
positive probe
absence/default/null/empty probe when applicable
negative or malformed probe when applicable
interaction probe when applicable
byte snapshot when bytes matter
process snapshot when stdout/stderr/exit matters
source/runtime identity snapshot when identity leaks are possible
```

Flag:

```text
probe inflation
```

when many probes sample already-covered happy paths while a high-risk axis lacks coverage.

Flag:

```text
probe underbinding
```

when a probe has no source axis, obligation, or interaction ref.

For CLI apps, the bookkeeper must reject readiness if the probe plan lacks a
control-plane bootstrap covering:

```text
short help
long help
short version, when plausible
long version, when plausible
no arguments or non-pipe invocation, when process context matters
unknown flag
help precedence over other flags
stdout/stderr/exit/final-newline snapshots
```

For renderer-heavy apps, the bookkeeper must distinguish:

```text
renderer-axis probes
golden-fixture morphology probes
mode-interaction probes
```

All three may be required. A renderer table byte probe over a synthetic fixture
does not prove real fixture compatibility unless the generator gives a specific
pass-through reason.

Flag:

```text
golden_fixture_undercoverage
```

when a program summarizes another tool's output but lacks realistic fixture
families for pass, fail, mixed, nested, no-test, build, panic, diagnostic/race,
coverage, and multi-subject morphology where applicable.

Flag:

```text
mode_interaction_undercoverage
```

when modes such as format, color, follow, progress, trim/path, sort, slow,
compare, no-tests, or smallscreen each have individual probes but lack pairwise
or triple probes over their shared observable surfaces.

## 9. Type/Error Surface Audit

The bookkeeper must reject one generic malformed-input probe as sufficient when field-specific parser/runtime surfaces may exist.

For every de-lumped structured field, check:

```text
expected_shape
wrong_shape_cases
missing_case
null_case
empty_case
unparseable_case
field_specific_error_surface_possible
probe_refs
```

If the generator claims field-specific errors are impossible, require a reason tied to parser/runtime behavior, not a guess.

## 10. Lattice And Lifecycle Audit

For optional, nullable, nested, replacement, or pointer-like fields, require a presence lattice or an explicit proof that no distinct surfaces exist.

Minimum lattice questions:

```text
parent absent
parent null
parent empty object
parent partial object
child absent
child null
child empty
child valid
selected subject top-level
selected subject nested
filtered before use
reaches renderer/helper
```

For row/stream/item processors, require lifecycle algebra:

```text
parsed
decoded
validated
selected_subject_resolved
lifecycle_filtered
mode_filtered
rendered
aggregated
exited
side_effect_applied
```

Every filter/membership axis must include one row that would change behavior if it reached a later stage.

## 10.1 Upstream-Discriminator Repair Audit

When the packet includes prior implementation attempts, local probe deltas,
official eval deltas, or repair summaries, the bookkeeper must scan for
intertwined branch groups.

An intertwined branch group exists when:

```text
one repair fixes branch A but regresses branch B
two plausible broad rules each satisfy one group and fail another
the same output/process surface is shared by conflicting groups
synthetic probes pass while realistic fixture rows fail on the same conceptual surface
the implementation oscillates between two local optima across repair attempts
```

The bookkeeper must reject any packet that treats such a group as independent
one-off patches without a parent discriminator.

Required audit questions:

```text
What is the smallest shared surface or upstream node for the fixed and regressed groups?
What broad rule was flattened too early?
Which discriminator lets both groups be true simultaneously?
Which counterfactual probes vary only that discriminator?
Which already-green regression probes must remain green after the repair?
Is the discriminator locked by visible spec, reference observation, or still pending?
```

Required acceptable terminal states:

```text
UD row present and locked_by_observation
UD row present and locked_by_visible_spec
UD row present with probe_required_pending_observation and implementation deferred
explicitly_deferred_with_reason because repair is outside current scope
```

Blocking states:

```text
intertwined_group_without_UD_row
flat_rule_patch_after_branch_regression
counterfactual_probe_missing_for_selected_discriminator
regression_retention_missing_for_previously_green_branch
post_eval_pressure_promoted_without_reference_observation
```

Minimal objection shape:

```text
BK-UD-<n>:
  fixed_branch_refs: [...]
  regressed_branch_refs: [...]
  shared_surface: ...
  missing_parent_discriminator: ...
  required_generator_repair:
    create UD row;
    propose candidate discriminators;
    allocate branch-separating counterfactual probes;
    retain previously-green regression probes;
    defer implementation until the discriminator is observed or specified.
```

## 11. Readiness Decision

Allowed decisions:

```text
pass_ready_for_observation
pass_ready_for_implementation_handoff
blocked_requires_generator_repair
blocked_missing_required_artifact
blocked_due_to_silent_drop
blocked_due_to_probe_gap
blocked_due_to_unresolved_conflict
blocked_due_to_authority_overpromotion
blocked_due_to_missing_control_plane_bootstrap
blocked_due_to_golden_fixture_undercoverage
blocked_due_to_mode_interaction_undercoverage
blocked_due_to_missing_upstream_discriminator
```

The default decision should be:

```text
blocked_requires_generator_repair
```

unless the bookkeeper can trace every high-risk discovered item to an acceptable terminal state.

## 12. Objection Row Shape

Each objection must include:

```text
objection_id
severity
source_artifact_ref
source_row_ref
forgotten_or_underbound_item
why_it_is_behavior_bearing_or_potentially_behavior_bearing
missing_chain_link
authority_boundary_issue
required_generator_repair
minimal_probe_or_deferral_requirement
blocking_status
```

Allowed severities:

```text
blocking
warning
note
```

## 13. Required Repair Templates

When blocking, the bookkeeper should give a minimal repair template.

For an inventory-only field:

```text
Add obligation row O-<n> for <field>.
Classify effect class.
Set authority_status to probe_required_pending_observation unless visible spec
or allowed observation locks the behavior.
Either:
  add primitive/de-lumping row,
  add axis row,
  add probe row,
  add D-ledger row,
or:
  explicitly defer/prove pass-through with evidence.
```

For a high-risk axis without probe:

```text
Add PR-<n> covering:
  positive state
  absence/default state
  wrong-type or malformed state
  interaction state, if applicable
```

For a missing CLI help/version bootstrap:

```text
Add HU/VE rows covering help aliases, version aliases, no-args process posture,
unknown flag behavior, help precedence, stdout/stderr destination, exit code,
usage header/program name, options ordering, and final newline.
Run bootstrap observations before using the flag inventory for implementation.
Obligationize every flag named by help output or explicitly defer it with
evidence.
```

For golden-fixture undercoverage:

```text
Add GF rows for realistic producer-output morphology families.
At minimum challenge pass, fail, mixed pass/fail/skip, nested/deep subtests,
no-test/empty, build failure, panic/stack, diagnostic/race, coverage, and
multi-package streams when applicable.
Cross each high-risk morphology with at least one renderer and one raw/process
surface.
```

For mode-interaction undercoverage:

```text
Add MI rows for every pair or triple of modes that share renderer, path,
follow/raw side-effect, order, denominator, or exit behavior.
Allocate probes for the interaction rather than relying on one-axis probes.
```

For missing upstream discriminator after branch-breaking repair:

```text
Add UD-<n> for the intertwined branch group.
Name the fixed branch, regressed branch, shared surface, and old flat rule.
Propose candidate parent discriminators.
Allocate counterfactual probes where the branches share all superficial
features except the proposed discriminator.
Run or require reference-first observation before implementation if authority is
not visible-spec direct.
Carry regression-retention probes for the branch that was previously green.
```

For authority over-promotion:

```text
Rewrite locked D-row into an observation-gated candidate D-row.
Preserve the field in the obligation/probe lattice.
Set authority_status to probe_required_pending_observation.
Remove mandatory implementation language until locked_by_visible_spec or
locked_by_observation applies.
```

For a grouped high-risk schema row:

```text
Split the grouped row into one row per behavior-bearing field.
Each child must receive its own terminal status.
```

## 14. Bookkeeper Prompt Skeleton

Use this shape for adversarial review workers:

```text
You are the adversarial bookkeeper, not the scaffold generator.

Your job is to find forgotten obligations and underbound probes.
Do not improve the scaffold silently.
Do not accept readiness by assertion.

Inputs:
  visible task packet
  generator phase artifacts
  generator-to-bookkeeper handoff

Tasks:
  1. Independently scan the visible task packet for named producers,
     structured formats, omitted field risks, runtime surfaces, and other
     candidate obligations the generator may have failed to extract.
  2. Build a shadow inventory from every field, primitive, omitted producer
     field, axis, interaction, probe, and D-row named anywhere.
  3. Enforce the producer-schema obligationization gate.
  4. Trace each high-risk item from first appearance to terminal state.
  5. Flag silent drops, inventory-only fields, grouped high-risk fields,
     probes without axes, and D-rows without probes.
  6. Flag visible-packet candidate obligations missing from the generator
     packet.
  7. If repair/eval deltas are present, scan for intertwined branch groups
     that need an upstream discriminator before more patching.
  8. Produce blocking objections with minimal generator repair templates.

Output:
  bookkeeper_shadow_inventory
  bookkeeper_obligation_continuity_audit
  bookkeeper_forgetting_objections
  bookkeeper_probe_adequacy_audit
  bookkeeper_upstream_discriminator_audit
  bookkeeper_readiness_decision
```

## 15. Success Criterion

The bookkeeper succeeds when it can answer:

```text
There is no behavior-bearing item discovered by the generator that has
silently disappeared.
No intertwined repair group is being handled by broad one-off patches without
an upstream discriminator row and branch-separating probes.
```

If that statement is not defensible from row references, the generator packet is blocked.
