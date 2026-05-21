# Program ODEU Gold Scaffold Generator Meta-Program v2

Status: support note.

Authority layer: support only.

Scope: generator-side meta-program for ProgramBench-style reconstruction runs. This document tells the scaffold generator how to derive the pre-implementation scaffold. It does not self-certify completeness; completeness is checked by the separate adversarial bookkeeper program.

Companion document:

```text
docs/support/Program_ODEU_Gold_Scaffold_Adversarial_Bookkeeper_v2.md
```

## 0. Role Boundary

The generator is responsible for productive descent:

```text
visible spec
  -> primitive inventory
  -> indication-generated artifacts
  -> counterfactual splits
  -> axes
  -> interactions
  -> probe allocation
  -> observation reconciliation, if allowed
  -> D-ledger scaffold candidate
```

The generator is not responsible for declaring that nothing was forgotten. It must instead emit stable artifacts that a bookkeeper can audit.

The generator may write:

```text
candidate_ready_for_bookkeeper_review
```

It must not write:

```text
implementation_ready
```

unless the bookkeeper has passed the scaffold or all bookkeeper objections have been resolved in a later generator pass.

## 0.1 Candidate-Obligation Authority Ladder

The generator must distinguish discovery, tracking, probing, and implementation
truth.

Authority ladder:

```text
discovered_candidate
obligationized_for_tracking
probe_required_pending_observation
locked_by_visible_spec
locked_by_observation
explicitly_deferred_with_reason
```

Rules:

```text
discovered_candidate:
  A field, branch, or surface has been noticed but is not yet tracked.

obligationized_for_tracking:
  The item must not be forgotten. It needs axes/probes/deferral, but it is
  not yet implementation truth.

probe_required_pending_observation:
  The item is plausible and behavior-bearing enough to allocate probes, but
  the scaffold must phrase it as a question or candidate branch until
  observation or stronger visible evidence resolves it.

locked_by_visible_spec:
  The visible spec directly authorizes the behavior as implementation truth.

locked_by_observation:
  An allowed observation confirmed the behavior as implementation truth.

explicitly_deferred_with_reason:
  The item remains visible in the ledger but is not carried into current
  probes or implementation obligations, with a reason.
```

Bookkeeper objections can force:

```text
discovered_candidate -> obligationized_for_tracking
obligationized_for_tracking -> probe_required_pending_observation
```

Bookkeeper objections alone must not force:

```text
probe_required_pending_observation -> locked_by_visible_spec
probe_required_pending_observation -> locked_by_observation
```

Only direct visible-spec authority or allowed observation may lock an
implementation obligation.

## 1. Anti-Priming Rule

Do not begin with task-specific edge-case enumeration.

Start with the program's own behavior primitives and force counterfactual decomposition until the branch ontology stops splitting.

Bad controlling style:

```text
Make sure to test cases A, B, C, D.
```

Preferred controlling style:

```text
Extract behavior primitives.
Run the canonical counterfactual battery against each primitive.
Split any primitive that can produce distinct observable outcomes.
Allocate probes only after the axes and interactions are explicit.
```

## 2. Required Output Packet

The generator must produce these files or sections with stable IDs:

```text
phase1_primitives_and_indications
phase2_generated_question_artifacts
phase3_axis_and_interaction_ledger
phase4_probe_allocation_plan
phase5_pre_observation_scaffold_candidate
generator_to_bookkeeper_handoff
repair_discriminator_ledger, when prior repair/eval data exists
```

Every row that can be referenced later must have a stable ID.

Required ID families:

```text
P-   primitive rows
FE-  field-effect rows
PS-  producer-schema rows
DL-  de-lumped field rows
TE-  type/error rows
SS-  subject-selection rows
FL-  field-presence lattice rows
LC-  lifecycle-stage rows
AD-  aggregate-denominator rows
RC-  renderer-compatibility rows
RS-  runtime-surface rows
HU-  help/usage/control-plane rows
VE-  version/executable-identity rows
GF-  golden-fixture morphology rows
MI-  mode-interaction closure rows
UD-  upstream-discriminator repair rows
AX-  axis rows
IX-  interaction rows
PR-  probe rows
D-   D-ledger candidate rows
O-   obligation rows proposed by the generator
```

## 3. Phase 1: Primitive Extraction

Before writing probes, produce a primitive inventory.

Each primitive row must include:

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
bookkeeper_visibility
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

Primitive extraction must include explicit and implicit primitives.

Implicit primitives include:

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

## 4. Phase 1b: Indication-Driven Artifact Generation

Some generic spec signals automatically create artifact obligations. These are not task-specific edge cases; they are structural obligations triggered by the program class.

| Generic Indication | Required Questions | Required Artifact |
|---|---|---|
| structured records, JSON objects, config objects, CSV rows, AST nodes | Which fields affect lifecycle, validation, selection, display, exit, side effects, or parser/type-error surfaces even if not rendered? | field-effect inventory |
| named external producer, standard command output, public structured format, language/tool API output | Is the visible example complete or only a sample? What omitted fields can affect lifecycle, subject selection, validation, filtering, rendering, aggregate exit, or error surfaces? | producer-schema expansion table |
| nested object, replacement object, alias, overlay, inherited/default object | Can the nested object become selected semantic subject rather than metadata? Which layer owns display/control/validation/aggregate truth? | subject-selection table |
| optional, nullable, pointer-like, missing, empty, zero, default fields | What exact presence conjunction renders blank, defaults, validates false, errors, panics, or becomes unobservable? | field-presence lattice |
| filter, selector, mode, membership gate, include/exclude flag | At what stage is each row/state removed, and does it still reach validation, rendering, aggregate exits, or side effects? | lifecycle-stage table |
| aggregate decision, summary, CI mode, final exit, batch status | What is the denominator: decoded, valid, filtered, rendered, selected helper rows, or side-effect rows? Does aggregate action happen before or after output? | aggregate-denominator table |
| renderer, formatter, table, style, pretty printer, byte-exact output | What renderer/library/width model is being imitated? Are bytes, runes, display cells, wrapping, alignment, and trailing newlines observable? | renderer-compatibility table |
| standard parser, flag package, logger, runtime panic, dependency/toolchain surface | Which runtime identity leaks into stdout, stderr, exit code, panic text, stack frames, usage text, or type names? | runtime-surface table |
| CLI app with help, usage, version, or "run help for full usage" language | Is help a primary control-plane surface rather than incidental text? What flags, aliases, stdout/stderr destinations, program-name strings, final newlines, exit codes, and precedence rules are exposed? | help-usage/control-plane table |
| selected-option documentation or partial visible CLI option list | Is the visible list incomplete? Does help output reveal additional supported flags, aliases, legacy flags, or mode interactions? | help-derived flag inventory |
| version flag, executable identity, command name, or runtime-disclosed build metadata | Does version/help/no-args output expose an executable name, version string, build identity, or wrapper path? | version/executable-identity table |
| golden output examples, terminal tables, fixture names, "exact output", or renderer-heavy CLI output | What real-looking producer fixtures are needed beyond synthetic minimal rows, and which mode/renderer combinations must be byte-snapshotted? | golden-fixture morphology mesh |
| multiple behavior-changing modes such as format, color, follow, progress, trim/path, sort, slow, compare, no-tests, or smallscreen | Which pairs or triples can change behavior even when each mode is individually understood? | mode-interaction closure table |
| conflict between observations or evidence layers | Is this clean behavior, compatibility behavior, or unresolved contradiction? Is it generic or branch-specific? | conflict-isolation table |
| one repair fixes a branch but breaks another branch, or two failure groups appear to require opposite patches | What parent discriminator separates the two branches, and what counterfactual probe proves both branches can coexist? | upstream-discriminator repair ledger |
| remand or focused postmortem probe set | Which previously discovered broad axes remain mandatory even if the remand probe set does not touch them? | regression-retention table |

If an indication is present, the artifact is required. If the generator believes an artifact is unnecessary, it must add a `not_applicable` row with evidence.

## 4.1 CLI Help/Usage Bootstrapping Gate

For CLI programs, help and version behavior are control-plane behavior, not
documentation decoration.

If the visible packet includes any of:

```text
usage
help
run -h
run --help
full usage
version
options
flags
```

then the generator must allocate a bootstrap observation set before declaring
the main scaffold ready for implementation:

```text
-h
--help
-v
--version
no arguments / non-pipe stdin, if process context is observable
unknown flag
help combined with another valid flag
help combined with an invalid flag
```

The bootstrap output must be parsed into:

```text
HU rows:
  help_aliases
  help_stdout_stderr_posture
  help_exit_posture
  help_precedence_posture
  usage_header_program_name
  options_header_and_order
  final_newline_posture
  no_args_or_non_pipe_error_posture

VE rows:
  version_aliases
  version_stdout_stderr_posture
  version_exit_posture
  version_string_shape
  executable_or_wrapper_identity

help-derived flag inventory:
  flag_name
  aliases
  argument_shape
  default_or_absent_behavior
  interaction_targets
  authority_status
  probe_refs
```

Every flag named by observed help must become an obligation, an explicit
deferral, or a proven pass-through row. A selected visible option list is not
enough to prove the flag inventory complete.

Help-derived rows are normally:

```text
locked_by_observation
```

for the existence and text of the help/version surface, while behavior of each
listed flag remains:

```text
probe_required_pending_observation
```

until separately probed or directly specified.

## 4.2 Golden Fixture Morphology Mesh

For programs that summarize, transform, or render another program's structured
output, synthetic minimal rows are not enough.

The generator must build a golden-fixture morphology mesh before implementation
handoff. The mesh is a coverage artifact, not a full cartesian explosion.

Required morphology candidates, when applicable:

```text
single pass package
single failed test with detail output
skip-only or mixed pass/skip package
mixed pass/fail/skip package
nested subtests
deep subtests or long names
multi-package mixed outcomes
no-test or empty-test package
build or compile failure text
panic / stack-like output
race-detector or diagnostic transcript
coverage output
malformed or partial stream
previous/current comparison fixture
```

For renderer-heavy CLI tools, every major renderer mode must be byte-snapshotted
against at least one realistic fixture, and every high-risk morphology class
must be crossed with at least one renderer and one raw/follow/process surface.

The mesh must include:

```text
GF rows:
  fixture_family
  producer_morphology
  fixture_realism_basis
  modes_crossed
  renderer_refs
  raw_or_follow_refs
  expected_byte_snapshot_refs
  uncovered_morphology_risk
```

## 4.3 Mode-Interaction Closure Gate

Mode coverage is not complete just because each mode has one probe.

If two or more behavior-changing modes can alter the same subject selection,
renderer, raw side effect, path identity, order, denominator, or exit surface,
the generator must create `MI` rows.

High-risk mode interactions include:

```text
format x color x status mix
format x no-color/env x markdown/plain/basic
follow x follow-output x include-timestamp
follow x parser error after partial output
progress x follow x multi-package order
sort x slow x package grouping
sort x coverage x missing coverage
trimpath x compare x identity collision
trimpath x smallscreen x long path hierarchy
smallscreen x nested subtests x renderer bytes
notests x all/pass/skip x hidden-row denominator
legacy alias x format precedence
help x invalid flag x stdout/stderr/exit
```

Each `MI` row must include:

```text
mode_refs
shared_behavior_surface
why_pair_or_triple_can_change_behavior
positive_probe_refs
negative_or_precedence_probe_refs
byte_or_process_snapshot_refs
uncovered_interaction_risk
```

The generator may choose a bounded pairwise/triple set rather than a full
cartesian product, but it must explain why the chosen set closes the behavior
surface.

## 4.4 Upstream-Discriminator Repair Gate

When working after a failed implementation attempt, a failed local probe run, or
an official eval, the generator must treat branch-breaking repairs as theory
evidence.

If a candidate patch:

```text
fixes branch A but regresses branch B
requires one broad rule for A and the opposite broad rule for B
causes two failure groups to alternate between green and red
passes synthetic probes but fails realistic fixture morphology
```

then the generator must not continue with one-off code patches. It must create
an `UD` row and search for the missing parent discriminator.

Required `UD` row shape:

```text
ud_id
fixed_branch_refs
regressed_branch_refs
shared_surface
old_flat_rule
why_flat_rule_is_wrong
candidate_parent_discriminators
selected_parent_discriminator
branch_a_condition
branch_b_condition
counterfactual_probe_refs
reference_observation_refs
regression_retention_probe_refs
authority_status
implementation_patch_boundary
```

The repair question is:

```text
What distinction lets both observed branches be true at once?
```

The generator must explicitly test the discriminator by constructing probes
where the candidate conditions separate:

```text
branch A condition true / branch B condition false
branch A condition false / branch B condition true
both branches share all superficial features except the proposed discriminator
the final patch keeps already-green regression probes green
```

Only after the discriminator is observed or directly specified may the generator
promote the repair into implementation obligations.

Examples of discriminator classes:

```text
projection surface vs final report surface
completion stream order vs sorted summary order
substantive body present vs transcript would become empty
render-only failure vs process-failure denominator
display identity vs raw grouping identity
synthetic minimal fixture vs realistic producer morphology
generic parser behavior vs evaluator-compatibility exception
```

## 4.5 Grouped Divergence And Layer Attribution Gate

After any probe run or official eval, the generator must not convert failures
directly into patch instructions. It must first produce a grouped divergence
diagnosis.

Required diagnosis row:

```text
divergence_group_id
failed_row_refs
nearby_passed_row_refs
current_theory_node_refs
shared_surface_or_denominator
suspected_layer_transition
wrong_abstraction
candidate_discriminator_refs
new_probe_or_observation_needed
implementation_patch_allowed
evidence_authority
```

Allowed `suspected_layer_transition` values:

```text
L1_to_L2_missing_or_bad_conceptual_split
L2_to_L3_terminalization_or_probe_coverage_gap
L3_to_L4_implementation_transfer_error
L4_to_L5_official_compatibility_surface
authority_layer_conflict
```

Repair is blocked until the row states why the group failed relative to the
group that passed. The generator must especially avoid this pattern:

```text
failed row -> change expected output -> patch code
```

The required pattern is:

```text
theory branch -> predicted behavior -> observed pass/fail split
  -> grouped anomaly -> discriminator or layer repair
```

If the repair is at `L2_to_L3`, the next action is usually new reference-first
or counterfactual probes. If the repair is at `L3_to_L4`, the next action may be
implementation patching, but only with regression-retention probes for the
already-green sibling branches. If the repair is at `L4_to_L5`, the generator
must keep the row labeled as compatibility pressure or post-eval evidence unless
clean observation or visible-spec authority later promotes it.

## 4.6 Projection-Sharpening Closure Gate

When the remaining failures are narrow byte/process exactness rows, the
generator must not reopen the whole ontology. It should classify them as
projection-sharpening candidates and bind each to its parent projection node.

Examples:

```text
blank-line preservation inside a diagnostic transcript
ANSI color threshold on a summary cell
help/usage stream and program-name text
panic source file and line
stdout/stderr split after a correct behavior body
exit code after an otherwise-correct rendered report
```

Required closure row:

```text
projection_sharpening_id
parent_projection_node
exact_surface
byte_or_process_delta
why_broad_semantics_are_already_green
local_regression_gate_refs
official_or_reference_row_refs
authority_status
```

This gate prevents late exactness work from being mistaken for a broad semantic
theory failure.

## 5. Phase 1c: Producer-Schema Obligationization Gate

Producer-schema discovery must create obligations, not just notes.

For every plausible omitted producer-schema field, assign:

```text
effect_class
observable_surface_hypothesis
behavior_bearing_posture
obligationization_status
authority_status
obligation_ref
```

Allowed `effect_class` values:

```text
display_field
control_field
lifecycle_filter_field
validation_field
aggregate_field
subject_selection_field
identity_or_error_surface_field
pass_through_metadata_field
unknown_requires_probe
```

Allowed `obligationization_status` values:

```text
created_obligation
split_into_children
explicitly_deferred_with_reason
proven_pass_through_with_reason
unknown_requires_bookkeeper_challenge
```

Allowed `authority_status` values:

```text
discovered_candidate
obligationized_for_tracking
probe_required_pending_observation
locked_by_visible_spec
locked_by_observation
explicitly_deferred_with_reason
```

Mandatory rule:

```text
A plausible omitted field may not remain only in the producer-schema inventory.
It must become an obligation, split into obligations, or receive an explicit
deferral/pass-through reason.
```

However, obligationization is not implementation locking. Omitted producer
fields inferred from producer knowledge should normally start as:

```text
probe_required_pending_observation
```

unless the visible spec directly assigns them behavior.

Producer-native names implying membership, status, error, replacement, validity, filtering, deprecation, retraction, lifecycle role, or execution state require an obligation unless proven pass-through.

## 6. Phase 1d: High-Risk Producer Field De-Lumping

Do not keep a broad "schema breadth" row when it contains multiple behavior-bearing omitted fields.

Each behavior-bearing omitted field must receive:

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

Pass-through metadata may remain grouped only if all of these are true:

```text
no lifecycle effect
no subject-selection effect
no validation effect
no aggregate/exit effect
no renderer effect
no decoder/type-error surface beyond generic object acceptance
```

## 7. Phase 1e: Type/Error Surface Expansion

For every de-lumped behavior-bearing structured field, create a type/error-surface row unless field-specific parser/runtime errors are impossible.

Required columns:

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

One generic malformed-input probe does not satisfy this requirement for behavior-bearing fields.

## 8. Phase 2: Counterfactual Battery

For each primitive and obligationized field, answer the canonical battery.

Allowed answers:

```text
splits_axis
does_not_split_axis
requires_probe
forbidden_by_spec
not_observable
unknown_requires_observation
```

Canonical questions:

```text
Absence:
  What if it is absent, null, empty, zero, defaulted, or implicit?

Multiplicity:
  What if there are zero, one, many, duplicate, or conflicting instances?

Substitution:
  Can it be represented by a replacement, alias, wrapper, default,
  environment value, derived value, or nested value?

Ordering:
  What happens before and after this primitive is observed?
  Can parser error occur before filtering?
  Can rendering occur before exit?

Filtering and visibility:
  Can this primitive be removed before another rule observes it?
  Can a non-rendered item still affect exit, summary, state, or side effects?

Shadowing and precedence:
  Can a nested primitive override a top-level primitive?
  Can one mode override parser, renderer, or exit behavior?

Authority layer:
  Is this source truth, input truth, control truth, display truth,
  validation truth, or compatibility truth?
  Can those truths diverge?

Failure layer:
  What invalid forms should fail?
  At which layer: parser, validator, renderer, runtime, process,
  dependency, or environment?

Conjunction:
  Can this primitive combine with another valid primitive to create behavior
  not visible from either primitive alone?

External surface:
  Where would a difference become observable?
```

If truths can diverge, split the primitive.

## 9. Phase 3: Axis And Interaction Ledger

After primitive splitting, produce an axis ledger.

Axis rows:

```text
axis_id
source_primitive_refs
source_obligation_refs
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

Create interaction rows only where a pair or triple of axes can change behavior.

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

## 10. Phase 4: Probe Allocation

Probe allocation follows ontology. It does not precede it.

For every high-risk axis, allocate as applicable:

```text
one ordinary positive probe
one absence/default/null/empty probe
one negative or malformed probe
one interaction probe
one exact external-surface snapshot
one source/runtime identity snapshot when observable
```

For CLI control planes, allocate help/version/no-args probes before relying on
any flag inventory:

```text
one short-help probe
one long-help probe
one short-version probe, if version is plausible
one long-version probe, if version is plausible
one no-args / non-pipe process probe, if invocation context matters
one unknown-flag probe
one help-precedence probe
one final-newline / stdout-stderr snapshot
```

For renderer-heavy tools, allocate probes from the golden-fixture mesh. A
renderer byte matrix over synthetic fixtures does not satisfy this gate unless
the generator separately explains why synthetic fixtures are behavior-complete.

For multi-mode tools, allocate probes from the mode-interaction closure table.
One probe per mode is insufficient when mode pairs or triples share the same
observable surface.

Produce a coverage table:

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

## 11. Phase 5: Scaffold Candidate

The final generator artifact is a candidate, not a certified scaffold.

Each D-ledger candidate row:

```text
obligation_id
primitive_refs
axis_refs
interaction_refs
behavior_statement
primary_surface
secondary_surfaces
evidence_authority
obligation_authority_status
counterfactual_basis
probe_refs
implementation_obligation
negative_path_posture
compatibility_bug_posture
D_depth
completion_gate
bookkeeper_review_status
```

Rows without `primitive_refs`, `axis_refs`, and `counterfactual_basis` are not gold-scaffold obligations.

Rows with `obligation_authority_status` of `discovered_candidate`,
`obligationized_for_tracking`, or `probe_required_pending_observation` must not
be phrased as locked implementation truth. They must use candidate language:

```text
candidate branch to observe
tracking obligation
probe obligation pending observation
```

Only rows with:

```text
locked_by_visible_spec
locked_by_observation
```

may use mandatory implementation language such as "must implement" or "must
surface" without an observation caveat.

## 12. Generator-To-Bookkeeper Handoff

At the end of each generator pass, produce a handoff table:

```text
artifact_ref
row_id
row_kind
created_in_phase
risk_posture
behavior_bearing_posture
current_status
downstream_refs
drop_or_defer_reason
bookkeeper_question
```

The generator should include its own suspected weak points, but it must not resolve them by assertion.

Required final handoff sections:

```text
all_discovered_fields
all_obligationized_fields
all_deferred_or_pass_through_fields
all_axes_without_probe
all_probes_without_axis
all_D_rows_without_probe
all_open_observation_questions
all_open_upstream_discriminator_questions
```

## 13. Stop Conditions

Stop and return to an earlier phase if:

```text
a producer-schema field is inventory-only
a high-risk field has no obligation row
an obligation has no axis, probe, D-row, or explicit deferral
a probe lacks source axis or interaction refs
a D-row lacks a probe or evidence authority
observation reveals a new primitive or split
CLI help/version/no-args surfaces exist but no HU/VE rows exist
observed help output names flags that lack obligations or explicit deferrals
renderer-heavy output has no golden-fixture morphology mesh
behavior-changing modes share surfaces but lack MI interaction rows
realistic producer-output morphology is represented only by synthetic minimal rows
a repair fixes one branch by regressing another and no UD upstream-discriminator row exists
an implementation repair proceeds before UD counterfactual probes distinguish intertwined branches
the bookkeeper returns any blocking objection
```

The generator should then produce a revised packet, not a code implementation.
