# Program ODEU Gold Scaffold Meta-Program v1

Status: support note.

Authority layer: support only.

Scope: reusable meta-program for ProgramBench-style program reconstruction tasks where the target is a locked pre-implementation scaffold and probe contract.

For adversarial-checker runs, this combined note is superseded by the split v2 pair:

```text
docs/support/Program_ODEU_Gold_Scaffold_Generator_Meta_Program_v2.md
docs/support/Program_ODEU_Gold_Scaffold_Adversarial_Bookkeeper_v2.md
```

This version supersedes v0 for new reconstruction experiments. The main change is procedural:

```text
Do not start by naming expected edge-case families.
Start by deriving the task's own behavior primitives, then force disciplined
counterfactual decomposition until the branch ontology stops splitting.
```

The calibration lesson is that probe count by itself is weak. A 50-probe observation suite can still miss decisive behavior if the first-stage ontology allocated probe budget to the wrong axes. The goal of v1 is therefore not “more probes”; it is better axis discovery.

---

## 0. Core Claim

A gold scaffold is a control artifact for implementation, not a task summary.

The scaffold must establish:

```text
primitive ontology
counterfactual splits
branch axes
interaction/cross-product obligations
surface and authority ledger
probe contract
completion gate
```

No implementation should begin until this chain is explicit.

The central v1 rule:

```text
Every high-risk probe must trace back to a derived primitive, a counterfactual
split, and an interaction hypothesis.
```

If a probe cannot be traced back this way, it may still be useful, but it does not prove that the ontology is complete.

---

## 1. Anti-Priming Rule

The meta-program should avoid enumerating task-specific edge families in the controlling prompt.

Bad controlling style:

```text
Make sure to test cases A, B, C, D.
```

This primes the worker to satisfy salient named cases and stop searching.

Preferred controlling style:

```text
Extract the behavior primitives.
Run the canonical counterfactual battery against each primitive.
Split any primitive that can produce distinct observable outcomes.
Only then allocate probes to the derived axes and interactions.
```

Task-specific examples may appear only as illustrative, non-controlling examples after the procedural rule is established.

---

## 2. Phase 1: Primitive Extraction

Before writing probes, produce a primitive inventory.

Each primitive row should use this shape:

```text
primitive_id
primitive_name
primitive_kind
evidence_authority
input_surface
control_surface
output_surface
state_carried
default_or_absent_state
visibility_scope
downstream_consumers
observable_surfaces
initial_risk_posture
```

Allowed `primitive_kind` values:

```text
input_record
field_or_attribute
flag_or_option
mode_selector
filter_or_gate
renderer_or_formatter
state_transition
error_surface
exit_surface
filesystem_surface
environment_surface
dependency_or_runtime_surface
identity_or_metadata_surface
```

Primitive extraction must include both explicit and implicit primitives.

Explicit primitives are directly named by the visible spec.

Implicit primitives are required to make the explicit behavior possible:

```text
record identity
field absence
default values
ordering
membership
shadowing
selection
formatting width
stream termination
exit ordering
toolchain/runtime identity
```

Do not mark the primitive inventory complete until every visible behavior has at least one producing primitive and one observable surface.

### 2.1 Indication-Driven Question Generator

Some generic spec signals must automatically create question families. These
are not task-specific edge cases; they are structural obligations triggered by
the program class.

Each detected indication must produce both:

```text
generic_question_rows
required_artifact_rows
```

Use this mapping before naming any concrete edge case:

| generic indication | required generic questions | required artifact |
|---|---|---|
| structured records, JSON objects, config objects, CSV rows, AST nodes | Which fields affect lifecycle, validation, selection, display, exit, or side effects even if they are not rendered? Which fields must exist only to preserve decoder/type-error surfaces? | field-effect inventory |
| named external producer, standard command output, public structured format, language/tool API output | Is the visible example a complete schema or only a sample from a broader named producer format? What fields can that producer emit that are omitted from the example, and which omitted fields could affect lifecycle, subject selection, validation, filtering, rendering, aggregate exit, or error surfaces? | producer-schema expansion table |
| nested object, replacement object, alias, overlay, inherited/default object | Can the nested object become the selected semantic subject rather than merely add metadata? Which layer owns display truth, control truth, validation truth, and aggregate truth? | subject-selection table |
| optional, nullable, pointer-like, missing, empty, zero, default fields | What exact field-presence conjunction renders blank, defaults, validates false, errors, panics, or becomes unobservable? | field-presence lattice |
| filter, selector, mode, membership gate, include/exclude flag | At what stage is each row/state removed, and does it still reach validation, rendering, aggregate exits, or side effects? | lifecycle-stage table |
| aggregate decision, summary, CI mode, final exit, batch status | What is the denominator: decoded items, valid items, filtered items, rendered items, selected helper rows, or side-effect rows? Does aggregate action happen before or after output? | aggregate-denominator table |
| renderer, formatter, table, style, pretty printer, byte-exact output | What external renderer/library/width model is being imitated? Are bytes, runes, display cells, wrapping, alignment, and trailing newlines observable? | renderer-compatibility table |
| standard parser, flag package, logger, runtime panic, dependency/toolchain surface | Which runtime identity leaks into stdout, stderr, exit code, panic text, stack frames, usage text, or type names? | runtime-surface table |
| conflict between observations or evidence layers | Is this clean behavior, compatibility behavior, or unresolved contradiction? Is it generic or branch-specific? | conflict-isolation table |
| remand or focused postmortem probe set | Which previously discovered broad axes remain mandatory even if the remand probe set does not touch them? | regression-retention table |

The worker must treat these as generators, not suggestions. If the indication
is present, the artifact is required. If the worker believes an artifact is not
needed, it must record why the indication is absent or not externally
observable.

### 2.2 Program-Class Field Inventory

For structured input programs, the primitive inventory is incomplete until every
known or plausibly standard field is assigned an effect class.

Field effect classes:

```text
display_field
control_field
lifecycle_filter_field
validation_field
aggregate_field
identity_or_error_surface_field
pass_through_metadata_field
unknown_requires_probe
```

The key question is:

```text
Which fields are behavior-bearing even though a happy-path renderer would not
show them?
```

This protects against omitting fields that affect filtering, type errors,
ordering, exits, or panic paths.

### 2.3 Producer-Schema Expansion Table

If the visible spec names a producer, command, runtime, file format, API output,
or public structured format, the examples must not be treated as the complete
schema by default.

Required columns:

```text
producer_or_format_name
example_field_refs
plausible_omitted_field_refs
evidence_basis
possible_effect_class
why_behavior_bearing
probe_required
worker_visibility_posture
```

Mandatory question:

```text
What can this named producer emit that the visible example did not show?
```

Follow-up questions:

```text
Could an omitted field remove a row without being displayed?
Could an omitted field alter subject identity, replacement, aliasing, or
shadowing?
Could an omitted field affect validation, aggregate exit, or filtering?
Could an omitted field be observable only through decoder/type-error text?
Could an omitted nested object become the selected semantic subject?
```

The worker may use general programming knowledge about public formats and
standard tool outputs, but it must label the evidence basis:

```text
visible_spec_explicit
producer_name_inference
program_class_inference
requires_observation
```

If producer-schema expansion yields a plausible behavior-bearing omitted field,
the scaffold must either:

```text
add it to the field-effect inventory and probe plan
```

or:

```text
record why it is not externally observable for this task
```

### 2.4 High-Risk Producer Field De-Lumping

Producer-schema expansion rows must not remain as one broad "schema breadth"
obligation when they contain multiple behavior-bearing omitted fields.

Mandatory rule:

```text
Each plausible omitted field with a behavior-bearing effect class must become
its own primitive row, axis row, and probe obligation unless explicitly
classified as pass-through metadata with no observable surface.
```

Behavior-bearing effect classes include:

```text
lifecycle_filter_field
control_field
subject_selection_field
validation_field
aggregate_field
identity_or_error_surface_field
renderer_or_formatter
dependency_or_runtime_surface
```

Pass-through metadata may remain grouped only when all of the following are
true:

```text
no lifecycle effect
no subject-selection effect
no validation effect
no aggregate/exit effect
no renderer effect
no decoder/type-error surface beyond generic object acceptance
```

Effect-class expansion rules:

```text
lifecycle_filter_field:
  must create lifecycle row-class probes
  must include all-filtered and mixed-row cases
  must include wrong-type decoder/error probe when structured parser surfaces
  are observable

subject_selection_field:
  must create top-level-vs-nested disagreement probes
  must create separate display-truth, validation-truth, control-truth, and
  aggregate-truth rows
  must include conflict cases where top-level and replacement/alias values differ

validation_field:
  must create field-presence cross-products over the minimal comparison inputs
  must distinguish parser error, render false, render true, blank/default, and
  panic/crash when those surfaces are possible

aggregate_field:
  must name the denominator and include empty, filtered-empty, one-positive,
  and mixed-positive/negative cases

identity_or_error_surface_field:
  must include at least one wrong-type, missing, or conflicting-identity probe
  when standard parser/runtime errors are observable

renderer_or_formatter:
  if the width model is named or byte-exact rendering matters, must include
  a non-ASCII/display-width probe unless the format forbids non-ASCII input
```

The worker must produce a de-lumping table:

```text
producer_schema_row_ref
omitted_field_ref
effect_class
why_high_risk
own_primitive_ref
own_axis_ref
own_probe_refs
may_remain_grouped
grouping_justification
```

Completion gate:

```text
No implementation scaffold may lock while a high-risk omitted field is present
only inside a grouped producer-schema probe.
```

### 2.5 Effect-Class Type/Error Surface Expansion

When structured parser, runtime, decoder, flag, schema, or type-error surfaces
are observable, every de-lumped behavior-bearing field must receive type/error
surface analysis. Do not satisfy this with one generic malformed-input probe.

Mandatory rule:

```text
For every de-lumped structured field whose effect class is lifecycle_filter_field,
control_field, subject_selection_field, validation_field, aggregate_field, or
identity_or_error_surface_field, create type/error-surface probe obligations
unless the field's parser/runtime cannot expose field-specific errors.
```

The worker must produce a type/error expansion table:

```text
field_ref
effect_class
expected_shape
wrong_shape_cases
missing_case
null_case
empty_case
unparseable_case
field_specific_error_surface_possible
type_error_probe_refs
may_defer_type_surface
defer_reason
```

Effect-class-specific requirements:

```text
lifecycle_filter_field:
  include valid true/false or include/exclude states
  include wrong-type state
  include missing/default state
  include at least one all-filtered or mixed-row lifecycle probe

control_field:
  include enabled/disabled or present/absent states
  include wrong-type state
  include missing/default state
  include interaction with the downstream controlled surface

subject_selection_field:
  include absent state
  include valid nested/replacement object state
  include wrong-type nested object state
  include partial nested object state
  include top-level-vs-selected-subject disagreement

validation_field:
  include valid parse state
  include invalid/unparseable state
  include missing/null state
  include semantically valid and semantically invalid but parseable states
  include the minimal conjunction that changes true/false/blank/error/panic

aggregate_field:
  include valid aggregate trigger state
  include empty denominator
  include filtered-empty denominator
  include wrong-type or invalid aggregate input when parser-visible

identity_or_error_surface_field:
  include valid identity/error state
  include wrong-type state
  include missing state
  include conflicting identity/error state when possible
```

Completion gate:

```text
No high-risk field axis may be marked observation-ready if its type/error
surface is collapsed into a generic malformed-input probe while field-specific
parser/runtime errors are possible.
```

### 2.6 Monotonic Obligation Carry-Forward

Each later artifact may refine, split, supersede, or explicitly defer earlier
obligations. It may not silently drop a high-risk obligation discovered in an
earlier phase.

Mandatory rule:

```text
Once a field, primitive, axis, interaction, probe obligation, or D-ledger
candidate is classified as high-risk and behavior-bearing, every later phase
must carry it forward or record an explicit defer/supersede/drop reason.
```

The worker must produce an obligation-carry-forward ledger when any generated
artifact creates high-risk obligations.

Required columns:

```text
source_artifact_ref
obligation_ref
obligation_kind
risk_reason
phase2_status
phase3_status
phase4_status
phase5_status
final_status
if_dropped_reason
superseding_ref
```

Allowed statuses:

```text
carried_forward
split_into_children
superseded_by_ref
explicitly_deferred
dropped_with_reason
missing_error
```

Silent loss examples:

```text
field appears in producer-schema expansion but not in de-lumping
field appears in de-lumping but not in axes
axis appears in axis ledger but no probe obligation exists
probe obligation appears in phase 4 but is absent from the D-ledger without
defer/supersede reason
```

Completion gate:

```text
No scaffold may be marked observation-ready while any high-risk obligation has
status missing_error.
```

### 2.7 Subject-Selection Table

When a primitive can be replaced, wrapped, nested, defaulted, inherited, or
shadowed, produce a subject-selection table before probes.

Required columns:

```text
surface
top_level_value
nested_or_replacement_value
selected_value_hypothesis
control_truth_owner
display_truth_owner
validation_truth_owner
aggregate_truth_owner
conflict_case_required
probe_ref
```

Mandatory question:

```text
If top-level and nested values disagree, which one wins for each observable
surface?
```

Do not assume one answer applies to every surface. A top-level value may own
filter truth while a nested value owns display truth.

### 2.8 Field-Presence Lattice

For optional or pointer-like fields, produce a lattice rather than one missing
case.

Required dimensions:

```text
parent_absent
parent_null
parent_empty_object
parent_partial_object
child_absent
child_null
child_empty
child_valid
sibling_absent
sibling_present
selected_subject_top_level
selected_subject_nested
filtered_before_use
reaches_renderer_or_helper
```

Mandatory question:

```text
What is the minimal conjunction that changes the observable surface?
```

The implementation obligation must name the conjunction, not a broad rule like
"missing child field crashes" unless the lattice proves that broad rule.

### 2.9 Lifecycle Algebra

For stream, row, item, or record processors, produce a lifecycle algebra.

Required stages:

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

Mandatory question:

```text
For each row class, which downstream stages can still observe it?
```

Every filter or lifecycle gate must be tested against at least one row that
would fail or change behavior if it reached a later stage.

### 2.10 Regression Retention After Remand

Remand probes are additive. They do not replace the broad scaffold unless the
lock explicitly says the prior axis was superseded.

Before any implementation handoff after remand, produce:

```text
retained_axis_refs
remand_axis_refs
superseded_axis_refs
regression_probe_refs
implementation_packet_must_carry_refs
```

Mandatory question:

```text
Which broad obligations would a coder drop if the remand packet were the only
artifact they optimized against?
```

If the answer names a behavior-bearing field, lifecycle gate, subject-selection
rule, renderer surface, or conflict branch, the implementation packet is not
ready until that obligation is reasserted.

---

## 3. Phase 2: Counterfactual Battery

For each primitive, ask the same canonical questions.

The worker must record the answer as one of:

```text
splits_axis
does_not_split_axis
requires_probe
forbidden_by_spec
not_observable
unknown_requires_observation
```

Phase 2 has two sources of questions:

```text
canonical battery questions
indication-driven generated questions
```

Both must be answered. The canonical battery prevents shallow happy-path
reasoning; the indication-driven generator prevents broad program-class axes
from disappearing when they are not salient in the prompt.

### 3.1 Absence

```text
What if this primitive is absent?
What if it is null, empty, zero, defaulted, or implicit?
Does absence differ from explicit empty?
Does absence still leave a valid parent object?
Does absence suppress, default, error, panic, or render blank?
```

### 3.2 Multiplicity

```text
What if there are zero, one, many, duplicate, or conflicting instances?
Is order preserved, sorted, merged, deduped, or rejected?
Does a later instance override an earlier one?
```

### 3.3 Substitution

```text
Can this primitive be represented by a replacement, alias, wrapper, default,
environment value, derived value, or nested value?
If substitution exists, which layer owns display truth?
Which layer owns control truth?
Which layer owns validation truth?
```

### 3.4 Ordering

```text
What happens before this primitive is observed?
What happens after it is observed?
Can a parser error occur before filtering?
Can rendering occur before exit?
Can logging occur after partial success?
Can one valid object followed by an invalid object change output?
```

### 3.5 Filtering And Visibility

```text
Can this primitive be removed by a filter before another rule observes it?
Can invalid data be hidden by filtering, or does validation happen earlier?
Can a non-rendered item still affect exit code, summary, state, or side effects?
```

### 3.6 Shadowing And Precedence

```text
Can another primitive shadow this one?
Can a nested primitive override a top-level primitive?
Can a mode selector override default behavior?
Can an error state override normal rendering?
Can an explicit flag override environment/default behavior?
```

### 3.7 Authority Layer

```text
Is this primitive source truth, input truth, control truth, display truth,
validation truth, or compatibility truth?
Can those truths diverge?
Which truth is externally observable?
```

If truths can diverge, split the primitive.

### 3.8 Failure Layer

```text
What invalid forms should fail?
At what layer should they fail: parser, validator, renderer, runtime, process,
dependency, or environment?
What exact surface carries failure: stdout, stderr, exit code, panic, signal,
file output, or no output?
```

### 3.9 Conjunction

```text
Can this primitive combine with another valid primitive to create behavior not
visible from either primitive alone?
Can two filters interact?
Can a valid mode expose a latent invalid field?
Can a substitution interact with filtering, rendering, or exit code?
Can an error branch interact with partial output?
```

### 3.10 External Surface

```text
Where would a difference become observable?
stdout bytes?
stderr bytes?
exit code?
stream routing?
file output?
panic text?
stack frame?
dependency/toolchain metadata?
ordering?
absence of output?
```

If no observable surface is identified, the branch remains speculative and must not become an implementation obligation.

---

## 4. Primitive Splitting Rule

Split a primitive into separate axis rows when any counterfactual answer implies a different observable outcome.

Mandatory split triggers:

```text
absent and explicit-empty differ
top-level and nested value can diverge
display truth and control truth can diverge
validation before filter differs from validation after filter
render before exit differs from exit before render
generic error differs from special compatibility error
source/runtime identity appears in observable text
one mode changes parser, renderer, or exit behavior
```

Do not smooth these into prose. Each split becomes an axis candidate.

---

## 5. Axis Ledger

After primitive splitting, produce an axis ledger.

Each axis row:

```text
axis_id
source_primitive_refs
counterfactual_trigger
axis_statement
states
observable_surfaces
risk_reason
required_probe_posture
completion_gate
```

Allowed `required_probe_posture` values:

```text
must_probe_positive
must_probe_negative
must_probe_cross_product
must_byte_snapshot
must_process_snapshot
must_source_or_runtime_snapshot
probe_optional_low_risk
observation_only_no_implementation_obligation
```

The scaffold may not lock until every high-risk axis has at least one concrete probe or an explicit reason why it cannot be observed.

---

## 6. Interaction Matrix

The worker must not create a full Cartesian product blindly. Instead, create interaction rows where a pair or triple of axes can change behavior.

Interaction triggers:

```text
filter_before_validation
validation_before_filter
mode_changes_renderer
mode_changes_parser
mode_changes_exit
substitution_changes_display_truth
substitution_changes_control_truth
membership_changes_exit
error_after_partial_success
empty_after_filter
identity_leaks_to_error_text
runtime_or_dependency_controls_bytes
```

Each interaction row:

```text
interaction_id
axis_refs
why_interaction_can_change_behavior
expected_observable_surface
positive_probe_ref
negative_probe_ref
byte_or_process_snapshot_ref
status
```

Status values:

```text
required
observed
rejected_no_observable_difference
deferred_low_risk
conflict_requires_separate_rows
```

---

## 7. Probe Allocation

Probe allocation follows the ontology. It does not precede it.

Minimum rule for every high-risk axis:

```text
one ordinary positive probe
one absence/default/null/empty probe when applicable
one negative or malformed probe when applicable
one interaction probe when any interaction trigger exists
one exact external-surface snapshot when bytes/process behavior matters
```

Probe count is not a completion metric.

Completion depends on:

```text
axis coverage
interaction coverage
negative-path coverage
exact-surface coverage
implementation-shape coverage when observable
```

The worker must produce a coverage table:

```text
axis_id
covered_states
missing_states
probe_refs
uncovered_risk
lock_status
```

Allowed `lock_status` values:

```text
locked_by_probe
locked_by_visible_spec
locked_by_runtime_observation
open_requires_probe
open_requires_counterfactual_split
deferred_low_risk
conflict_isolated
```

---

## 8. Observation Phase

Observation may use an allowed reference executable only after Phase 1 and Phase 2 produce the primitive and axis ledgers.

Observation must not merely run probes. It must reconcile them back into the ontology:

```text
Did the observation confirm the axis?
Did it split the axis further?
Did it reveal a new primitive?
Did it show that two truths diverge?
Did it expose a byte/process/runtime surface?
Did it invalidate a visible-spec inference?
```

If observation reveals a new primitive or split, return to Phase 2 before locking the scaffold.

---

## 9. Conflict Handling

When two evidence sources disagree, isolate the disagreement as a conflict branch.

Conflict rows:

```text
conflict_id
clean_reference_behavior
alternate_observed_behavior
evidence_authority_for_each
affected_axes
affected_probes
compatibility_strategy
implementation_scope
non_laundering_note
```

Do not globalize conflict behavior.

Bad:

```text
All parse errors should return nonzero.
```

Better:

```text
Generic parse errors follow clean observation.
One evaluator-conflict fixture has a separate compatibility row.
```

---

## 10. D-Ledger Row Shape

The final scaffold must still produce D-ledger rows.

Each row:

```text
obligation_id
primitive_refs
axis_refs
interaction_refs
behavior_statement
primary_surface
secondary_surfaces
evidence_authority
counterfactual_basis
probe_refs
implementation_obligation
negative_path_posture
compatibility_bug_posture
D_depth
completion_gate
```

Rows without `primitive_refs` and `counterfactual_basis` are suspect. They may be useful notes, but they are not gold-scaffold obligations.

---

## 11. Implementation Readiness Gate

The scaffold may be handed to a coder only when all of the following are true:

```text
[ ] Visible behaviors are mapped to primitives.
[ ] Implicit primitives are listed, not assumed.
[ ] Every primitive received the canonical counterfactual battery.
[ ] Split triggers were converted into axis rows.
[ ] High-risk axes have positive, negative, and interaction probes as applicable.
[ ] Probe allocation is explained by axis coverage, not probe count.
[ ] Exact byte/process/runtime surfaces are separated from semantic surfaces.
[ ] Conflict branches are isolated and not generalized.
[ ] Every D-ledger row points to primitives, axes, evidence, and probes.
[ ] Remaining open risks are named before implementation begins.
```

Stop condition:

```text
If the scaffold has many probes but any high-risk axis is unprobed, the
scaffold is not implementation-ready.
```

---

## 12. Worker Prompt Skeleton

Use this shape for future reconstruction runs:

```text
You are deriving a gold scaffold, not implementing.

Do not begin with edge-case enumeration.

Phase 1:
  Extract behavior primitives from the visible spec.
  Include implicit primitives required by the explicit behavior.

Phase 2:
  Run the canonical counterfactual battery against every primitive.
  Split primitives into axes whenever an answer implies a distinct observable
  outcome.

Phase 3:
  Build the interaction matrix only for axis pairs/triples that can change
  behavior.

Phase 4:
  Allocate probes from axis and interaction coverage.
  Include positive, negative, absence/default, and exact-surface probes where
  required.

Phase 5:
  If reference observation is allowed, run probes and reconcile observations
  back into primitives and axes. If new axes appear, return to Phase 2.

Phase 6:
  Lock the pre-implementation scaffold with a D-ledger.
  Do not hand off to implementation while any high-risk axis is open.
```

---

## 13. Success Metric

The success metric is not:

```text
number of probes
length of scaffold
amount of detail
```

The success metric is:

```text
Can a competent coder agent implement the scaffold without needing to invent
unstated behavior?
```

A smaller probe suite with correct axes is better than a larger suite that densely samples already-obvious behavior.
