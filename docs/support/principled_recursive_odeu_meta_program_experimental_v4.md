# Principled Recursive ODEU Meta-Program Experimental v4

## Purpose

This is a proposed refinement of the current ADEU / ODEU program-reconstruction scaffold. It turns the generator from an indication-and-checklist procedure into a recursive ontology descent procedure, then adds an explicit observation-to-obligation lock step before implementation.

v4 adds the lessons from the `tparse` Run H vs gold-baseline A/B:

```text
scoped-ready is not gold-ready;
green local probes over a scoped packet are not evidence of global parity;
implementation should target a gold-ready fixture ledger, not an open
discriminator ledger;
probe count should eventually be compressed by conceptual ownership, but only
after gold-required leaves are explicit.
```

The core idea is:

```text
visible program spec / README
  -> native semantic base ontology pass
  -> recursive application of a small operator calculus
  -> nested behavior branch tree
  -> intermediate terminalization and coverage adequacy audit
  -> per-leaf scoped-readiness / gold-readiness accounting
  -> promotion of scoped leaves to gold-ready leaves, or explicit deferral
  -> probe families grouped by tree structure
  -> optional probe ownership compression after raw gold coverage exists
  -> implementation coverage map grouped by the same tree
  -> local gold fixture green gate
  -> observation / eval feedback attached back to exact tree nodes
```

The task-specific details should not be named in the generic rules. The rules name only the primitive operations. Specifics such as `tparse` having raw follow output, package/test identity, panic-like output, race markers, markdown table byte geometry, trimpath display identity, or exit-denominator conflicts should arise from applying those operations to the base ontology inferred from the program spec and producer semantics.

## 1. Main correction to the current meta-program

The current v2 generator is already much better than a flat edge-case enumerator. Its weakness is that many required artifacts are still named as generic indications:

```text
field-effect table
producer-schema table
field-presence lattice
lifecycle table
aggregate-denominator table
renderer-compatibility table
mode-interaction table
...
```

Those artifacts are useful, but they should be derived views, not first-class primitive rules.

The more principled form is:

```text
Apply the same small set of conceptual operations to every semantic entity.
If an operation produces observably distinct children, recurse into those children.
When a branch reaches an observable leaf, allocate probes and implementation obligations.
```

So the generator no longer says:

```text
If this is a renderer-heavy CLI, remember golden fixtures.
```

It says:

```text
For every projection surface, apply projection grammar, external-surface, realism, and compatibility descent.
If the projection surface is byte-observable and depends on producer morphology, create fixture-morphology children until all distinct byte-producing branches are covered or explicitly deferred.
```

The existing special artifact names become labels for common subtrees produced by the recursive descent.

## 2. Four phases: semantic base pass, recursive descent, terminalization, gold promotion

### Phase A: native semantic base ontology pass

The generator first uses the model’s native semantic ability to answer: “What kind of machine is this program?”

This pass should not yet produce probes. It should produce an ontology graph with evidence labels.

For every program, extract these base node families when present:

```text
program class
external producer / input format
input sources
input records or requests
subjects / entities being acted on
state carried between inputs
operations / lifecycle transitions
control surfaces / modes / flags / config
selection / filtering / membership rules
aggregation / summary rules
projection / rendering / serialization surfaces
side-effect surfaces
error / failure / invalidity surfaces
process / runtime / dependency surfaces
identity / naming / path / metadata surfaces
evidence / authority boundaries
```

Each base node should include:

```text
node_id
semantic_name
program_class_role
source_phrase_or_inference
evidence_authority
known_consumers
known_observable_surfaces
initial_risk
open_questions
```

For `tparse`, the base pass should semantically identify it as approximately:

```text
CLI program consuming a line-oriented Go test JSON event stream,
accumulating package/test state,
and rendering summaries/details while optionally preserving raw output
and returning a process exit status.
```

That one sentence implies the base entities: stream, records, producer schema, package/test subjects, test lifecycle, output text, renderers, flags/modes, side effects, and process exit. The generic rules did not need to know about `panic`, `race`, `trimpath`, or `follow-output`; those emerge downstream from the ontology plus recursive operations.

### Phase B: recursive ontology descent

After the base ontology is present, the generator repeatedly applies the same conceptual operations to each node. The output is a nested branch tree.

A branch is meaningful when two possible child worlds can differ in:

```text
accepted input
internal state
selected subject
rendered output bytes
stderr
side-effect bytes/files
ordering/timing
exit code
runtime error text
future downstream behavior
```

A branch can stop only when all applicable operations are exhausted, the branch is proven pass-through, or it is explicitly deferred with a reason.

### Phase C: intermediate terminalization and coverage adequacy

After recursive descent and before executable probes are declared closed, the
generator must ask whether each behavior leaf is actually terminal.

A leaf is not terminal merely because one representative probe exists. It is
terminal only when no sibling branch can preserve the same high-level primitive
while changing:

```text
rendered bytes
stderr bytes
side-effect bytes or files
ordering
selected rows
aggregate denominator
exit code
runtime error text
downstream behavior
```

Terminalization requires the generator to bind one concrete combination of:

```text
observable state class
mode or composition context
fixture morphology / producer realism tier
projection dialect
side-effect posture
exit posture
evidence authority
```

Coverage adequacy then asks whether the terminal leaves are representative
enough for the behavior family. For any high-risk family with byte, producer,
side-effect, aggregate, or exit sensitivity, synthetic minimal fixtures are not
sufficient by themselves. The generator must either add realistic morphology
probes or mark the family as residual risk.

The key closure rule:

```text
probe_contract_closed requires:
  every high-risk primitive has terminal leaves;
  every terminal leaf has probe coverage, observation lock, or explicit deferral;
  every representative probe states which siblings it does not cover;
  synthetic-only coverage is not treated as full coverage for producer-shaped
    renderer or side-effect behavior.
```

### Phase D: scoped-to-gold readiness promotion

After terminal leaves exist, the generator must classify each leaf twice:

```text
scoped_readiness:
  Is this leaf ready for an implementation attempt bounded to the observed
  branch and its stated siblings-not-covered?

gold_readiness:
  Is this leaf ready to serve as part of the full local gold fixture contract
  for the task?
```

The two statuses must not be collapsed. A leaf can be correct and useful inside
one scoped discriminator table while still not being gold-ready for a full
implementation handoff.

Required promotion chain:

```text
ontology leaf
  -> scoped-ready leaf
  -> gold-ready leaf
  -> implementation obligation
  -> local gold fixture green
  -> official eval
```

The implementation loop is blocked until all gold-required leaves are either:

```text
gold_ready
explicitly_deferred_from_gold_with_expected_risk
```

If a run proceeds with only scoped-ready leaves, it must be labeled a scoped
implementation attempt, not a gold implementation attempt.

### Phase C hard gates

The generator may not declare the conceptual scaffold ready for executable
observation planning until these hard gates have been answered. These gates are
procedural and language-agnostic; they do not license task-specific facts.

#### Gate C1: help bootstrap required

Trigger:

```text
The visible spec mentions help, usage, full usage, version, command options,
or "run -h/--help".
```

Required output:

```text
help_bootstrap_required = true
help_bootstrap_status = blocking_until_observed | explicitly_deferred_with_risk
help_surface_candidates:
  - help aliases
  - version aliases
  - unknown flag behavior
  - invalid flag behavior
  - stdout/stderr destination
  - program-name / executable identity
  - option inventory discovered from help
  - precedence of help with valid and invalid flags
```

Rule:

```text
If help bootstrap is triggered, the visible option list is not a closed control
surface. Every hidden or help-derived option remains pending observation, but it
must be represented as an obligationized candidate rather than silently absent.
```

Required hidden-control role buckets:

```text
renderer_or_style_dialect_controls
ordering_sort_or_limit_controls
path_display_identity_controls
streaming_or_progress_controls
raw_output_side_effect_controls
timestamp_or_metadata_projection_controls
empty_or_no_subject_membership_controls
comparison_or_prior_run_controls
legacy_alias_or_compatibility_controls
runtime_identity_or_version_controls
```

Rule:

```text
If help bootstrap is required, the generator must create these buckets as
pending observation slots when the program class could plausibly expose them.
The bucket is not a claim that such a flag exists. It is an observation
classifier so discovered help flags are not interpreted as isolated options.
```

#### Gate C2: producer schema candidate obligation

Trigger:

```text
The program consumes a named external producer, standard command output,
structured event stream, public file format, language runtime output, or tool
API output.
```

Required output:

```text
producer_schema_candidate_table:
  candidate_field_or_record
  producer_role
  possible_consumers
  possible_value_lattice
  possible_lifecycle_effect
  possible_subject_or_denominator_effect
  possible_projection_effect
  possible_error_or_exit_effect
  authority = producer_inference | visible_spec | probe_required_pending_observation
  observation_needed
```

Rule:

```text
Unknown producer fields may remain pending, but they may not be collapsed into
one broad "schema deferred" row when their plausible roles differ. A field that
could affect lifecycle, selection, projection, aggregation, side effects, or
exit becomes an obligationized candidate.
```

For a test-output summarizer, this gate should force candidates for:

```text
event/action identity
subject identity
output payload
elapsed/time data
terminal package lines
diagnostic morphology
coverage-like output
no-test or empty-test morphology
build/runtime failure morphology
cached or prior-result morphology
```

The names are examples of producer roles, not facts about a specific task until
observed or directly specified.

#### Gate C2b: multi-consumer output second descent

Trigger:

```text
A producer field, payload, line, record body, or text blob is consumed by more
than one role, especially raw projection plus classification, aggregation, or
rendering.
```

Required output:

```text
multi_consumer_output_role_table:
  source_payload_ref
  raw_projection_role
  structural_marker_role
  diagnostic_body_role
  aggregate_signal_role
  package_or_subject_terminal_role
  metadata_or_metric_role
  pass_through_role
  false_positive_negative_control
  authority
  observation_needed
```

Role candidates for producer output include:

```text
raw bytes or raw lines
test/result marker lines
assertion or diagnostic body
panic or stack-like body
race or concurrency diagnostic body
package terminal or summary line
coverage or metric line
empty/no-subject marker
build/runtime failure line
generic pass-through output
```

Rule:

```text
The generator must not leave a multi-consumer payload as one broad "output"
node. Each role can have different lifecycle, aggregation, projection, and exit
effects, so each role needs either a probe leaf or an explicit deferral.
```

#### Gate C3: row-universe projection terminalization

Trigger:

```text
The program renders any table, list, report, progress stream, grouped summary,
or byte-exact projection over reduced records.
```

Required output for each projection:

```text
projection_row_universe:
  projection_surface
  row_universe
  row_membership_rule
  hidden_row_policy
  grouping_key
  raw_identity_vs_display_identity
  ordering_basis
  sort_key_candidates
  tie_policy_candidates
  denominator_for_counts
  denominator_for_exit
  byte_grammar_parts
  mode_interaction_refs
  morphology_refs
```

Rule:

```text
A projection leaf is not terminal until it says what rows enter the surface,
what rows are hidden but still counted, how row order is chosen, what identity
is displayed versus grouped, and what byte grammar parts can vary.
```

Byte grammar parts include:

```text
header
body
separator
blank lines
ANSI/color policy
cell width or wrapping
ordering
footer/final newline
stdout/stderr/file stream split
```

#### Gate C3b: projection byte-grammar child leaves

Trigger:

```text
A projection surface is byte-observable: stdout, stderr, a side-effect file, a
table, a markdown/plain/basic report, a progress line, usage text, or a raw
transcript.
```

Required output:

```text
projection_byte_grammar_child_leaves:
  projection_surface
  header_leaf
  body_leaf
  row_or_group_separator_leaf
  blank_line_leaf
  ansi_or_style_leaf
  cell_width_or_wrapping_leaf
  ordering_leaf
  footer_or_final_newline_leaf
  stdout_stderr_file_split_leaf
  process_exit_pairing_leaf
  negative_control_refs
```

Rule:

```text
Listing byte grammar parts in one row is not terminalization. Every
byte-sensitive projection must spawn child leaves for the grammar parts that
can independently change observable bytes or process behavior.
```

#### Gate C4: observed help control instantiation

Trigger:

```text
The help bootstrap has been observed, or any observed usage/error output
reveals flags, modes, aliases, environment assumptions, or invocation forms.
```

Required output:

```text
observed_help_control_instantiation_table:
  discovered_control_or_usage_form
  observed_spelling_or_aliases
  control_role_bucket
  affected_ontology_nodes
  affected_projection_surfaces
  affected_row_universe_or_denominator
  affected_side_effect_or_resource
  affected_error_or_exit_behavior
  positive_probe_refs
  negative_control_probe_refs
  authority = locked_by_reference_observation | conflict_isolated
  unresolved_discriminator_if_any
```

Rule:

```text
Help observation does not merely update an option list. Every discovered
control must be routed back through the ontology as a behavior operator:
selection, renderer, identity, ordering, streaming, side effect, metadata,
empty-subject membership, comparison, compatibility, runtime identity, error,
or exit. A discovered control is not terminal until it has positive probes and
negative controls for the behaviors it could affect.
```

The generator must not treat a visible help flag as self-explanatory. A flag
named like a display option can still affect row membership, error precedence,
side effects, stdout/stderr split, or exit status until observation proves
otherwise.

#### Gate C5: observed schema fixture synthesis

Trigger:

```text
The external producer schema, record examples, or producer-like output
morphology has been observed from reference behavior.
```

Required output:

```text
observed_schema_fixture_synthesis_table:
  schema_role_ref
  observed_field_or_payload_shape
  minimal_fixture_ref
  realistic_producer_shaped_fixture_ref
  false_positive_negative_fixture_ref
  malformed_or_wrong_type_fixture_ref
  mode_interaction_fixture_refs
  lifecycle_effect_locked
  projection_effect_locked
  denominator_or_exit_effect_locked
  authority
  unresolved_discriminator_if_any
```

Rule:

```text
A schema role is not locked by one minimal fixture. Each behavior-bearing role
needs a minimal fixture, a realistic producer-shaped fixture, a false-positive
negative fixture, and a mode-interaction fixture when the role affects
rendering, aggregation, side effects, or exit.
```

This prevents a clean but synthetic fixture from falsely closing branches whose
real producer morphology carries blank lines, marker-like text, package
terminal lines, metric lines, cached output, build/runtime diagnostics, or
multi-line failure bodies.

#### Gate C6: renderer dialect projection expansion

Trigger:

```text
Observation discovers any renderer, style, width, color, detail, progress,
raw-output, file-output, help, or report dialect.
```

Required output:

```text
renderer_dialect_projection_expansion_table:
  renderer_or_projection_mode
  row_universe_ref
  byte_grammar_child_leaf_refs
  control_cross_product_refs
  selection_interaction_refs
  color_or_style_interaction_refs
  width_or_identity_interaction_refs
  follow_or_streaming_interaction_refs
  error_or_exit_interaction_refs
  negative_control_probe_refs
  authority
```

Rule:

```text
Every discovered output mode gets its own row universe and byte grammar leaves
before implementation. The run may bound the cross product, but it must include
every control that can alter membership, ordering, identity, bytes, side
effects, stdout/stderr/file split, or process exit.
```

#### Gate C7: discriminator-locked probe rule

Trigger:

```text
Any probe is added after help, schema, renderer, or failure observation.
```

Required output field:

```text
locked_discriminator_ref
```

Rule:

```text
Every post-observation probe must name the unresolved discriminator it locks:
branch membership, byte grammar, field role, lifecycle order, side effect,
stdout/stderr split, row denominator, exit denominator, error precedence, or
compatibility conflict. Probe inflation without a named discriminator is
rejected.
```

If fixing one branch breaks another, the run must ascend to the nearest shared
parent discriminator, revise that parent, and then retain probes for both
sibling branches.

#### Gate C8: terminal leaf readiness contract

Trigger:

```text
Any terminal leaf is created, patched, observed, or carried forward into a
handoff packet.
```

Required output fields:

```text
leaf_id
ontology_path
primary_operator
scoped_readiness_status
scoped_ready_basis_refs
gold_readiness_status
gold_ready_basis_refs
gold_blocker_refs
missing_sibling_branches
missing_cross_products
fixture_realism_status
terminal_observation_status
probe_ownership_status
implementation_handoff_status
expected_score_risk_if_deferred
```

Allowed `scoped_readiness_status` values:

```text
scoped_ready
scoped_blocked_pending_observation
scoped_blocked_by_conflict
scoped_deferred_with_reason
not_applicable_to_current_scope
```

Allowed `gold_readiness_status` values:

```text
gold_ready
not_gold_ready_missing_sibling_branches
not_gold_ready_missing_cross_products
not_gold_ready_synthetic_only
not_gold_ready_unresolved_conflict
not_gold_ready_projection_exactness_open
not_gold_ready_fixture_realism_open
explicitly_deferred_from_gold_with_expected_risk
not_gold_required
```

Rule:

```text
locked_by_reference_observation does not imply gold_ready.
scoped_ready does not imply gold_ready.
gold_ready requires terminal observations or justified pass-through coverage for
the leaf's high-risk siblings, cross-products, fixture realism, and projection
surface.
```

For high-risk surfaces, a gold-ready leaf must also name:

```text
representative_fixture_refs
negative_control_refs
mode_interaction_refs
renderer_or_projection_refs
side_effect_refs
exit_denominator_refs
```

#### Gate C9: gold implementation handoff gate

Trigger:

```text
The run proposes to begin a full implementation attempt intended for official
submission, rather than a scoped implementation experiment.
```

Required output:

```text
gold_readiness_summary:
  total_terminal_leaves
  gold_required_leaves
  gold_ready_leaves
  gold_deferred_leaves
  scoped_only_leaves
  implementation_blockers
  expected_score_risks
```

Rule:

```text
Full implementation handoff is blocked unless every gold-required leaf is
gold_ready or explicitly_deferred_from_gold_with_expected_risk.
```

If any leaf is only scoped-ready, the handoff must say:

```text
handoff_type = scoped_implementation_attempt
not_gold_implementation_attempt
```

The local pre-official gate for a gold implementation is:

```text
all gold fixture probes green
all side-effect byte probes green
all regression-retention probes green
all deferred risks still explicitly deferred
```

Official eval should only follow that gate. If official eval is run before that
gate, classify it as an experiment, not as a gold closeout.

#### Gate C10: probe ownership compression phase

Trigger:

```text
The run has expanded enough raw probes to make gold-required leaves explicit,
and the user wants to reduce probe count or clarify probe ownership.
```

Required output:

```text
probe_ownership_compression_table:
  probe_id
  owned_leaf_refs
  strongest_owner_probe_ref
  compression_class
  retained_reason
  removable_if_refs
  hidden_source_risk_posture
```

Allowed `compression_class` values:

```text
owned_by_existing_probe
requires_new_probe_same_leaf
requires_new_probe_new_leaf
over_granular_but_hidden_source_risk_valid
redundant_and_removable
deferred_until_more_task_evidence
```

Rule:

```text
Probe compression happens after gold-required leaves are explicit, not before.
The goal is not fewer probes by default. The goal is the minimum probe set that
still proves every gold-required leaf, with retained over-granularity where
hidden-source reconstruction risk justifies it.
```

Compression is forbidden when it would collapse:

```text
distinct sibling branches
distinct output-role consumers
distinct side-effect destinations
distinct exit denominators
distinct renderer byte grammars
distinct fixture-realism tiers
distinct authority layers
```

## 3. The operator calculus

The operator set should be small and reusable. Existing row families such as `field-effect`, `producer-schema`, `lifecycle`, `renderer`, and `mode-interaction` are emitted when these operators are applied to particular node types.

### OP-B: Boundary / entity reification

Question:

```text
What is this thing, what counts as one instance of it, and what distinguishes it from neighboring things?
```

Typical child nodes:

```text
source identity
instance identity
raw identity vs display identity
parent vs child entity
record vs aggregate entity
control entity vs data entity
```

`tparse` example:

```text
Package raw identity and package display identity split because trimpath can change display without changing grouping truth.
```

### OP-D: Decomposition / part extraction

Question:

```text
What parts, fields, sub-objects, phases, attributes, or resources constitute this node?
```

Typical child nodes:

```text
fields of a structured record
subcommands / flags of a CLI
cells of a rendered table
columns of a summary
environment variables
resource paths
```

`tparse` example:

```text
A Go test JSON record decomposes into Action, Package, Test, Output, Elapsed, Time, FailedBuild, and omitted producer fields inferred from the named producer.
```

### OP-R: Role / consumer split

Question:

```text
Who consumes this node, and can different consumers require different truths?
```

Typical child nodes:

```text
parse truth
validation truth
control truth
state truth
selection truth
display truth
side-effect truth
exit truth
compatibility truth
```

`tparse` example:

```text
Output is not one field. It has raw-follow bytes, failure-detail body text, panic/build/race/no-test/coverage classifiers, and generic package/test output roles.
```

### OP-L: Lattice / value-state split

Question:

```text
What are the relevant states of presence, type, value, defaulting, emptiness, multiplicity, and conflict?
```

Typical child nodes:

```text
absent
null
empty
zero
defaulted
valid singleton
multiple
conflicting
wrong type
malformed
unknown value
```

`tparse` example:

```text
-trimpath is not boolean. The value lattice includes absent, bare flag, empty string, explicit prefix with slash, prefix without slash, auto, repeated value, boolean-looking string, and no-match prefix.
```

### OP-T: Temporal / lifecycle split

Question:

```text
When does this node appear, become valid, affect state, get filtered, get rendered, cause side effects, and cease to matter?
```

Typical child nodes:

```text
before decode
after decode before validation
after validation before filtering
after filtering before aggregation
after aggregation before rendering
during rendering
after side effect before error
finalization / EOF
post-render exit
```

`tparse` example:

```text
Raw follow bytes may be emitted before a later malformed JSON line causes process failure, so raw side effects and parser failure cannot be collapsed.
```

### OP-S: Subject / selection / aggregation split

Question:

```text
Which subject owns this fact, which rows are selected, and what denominator does an aggregate decision use?
```

Typical child nodes:

```text
package subject
test subject
subtest subject
helper/detail subject
hidden-but-aggregate subject
rendered denominator
valid-decoded denominator
selected denominator
exit denominator
side-effect denominator
```

`tparse` example:

```text
A test row hidden by the default renderer may still affect package fail counts and exit. Exit is not simply the rendered table status.
```

### OP-P: Projection / external surface split

Question:

```text
Where does this node become observable, and what grammar or byte convention controls that surface?
```

Typical child nodes:

```text
stdout
stderr
exit code
side-effect file
rendered table
markdown block
plain aligned rows
ANSI color
width / wrapping / final newline
filesystem path / resource mutation
```

`tparse` example:

```text
Failure details are not merely strings. They project through renderer-specific block geometry: identity header, body, blank lines, separator, package line, markdown fences, and final newlines.
```

### OP-F: Failure / negation / invalidity split

Question:

```text
What if this node is invalid, unavailable, contradictory, late, partial, or unsupported, and at which layer does failure surface?
```

Typical child nodes:

```text
parse error
validator error
flag parser error
runtime panic
dependency error
filesystem open/read/write error
unsupported mode
late error after partial success
error precedence branch
```

`tparse` example:

```text
Missing input file, directory input, malformed JSON, bad flag value, unknown flag, and follow-output open failure are not one error class; they differ in stderr, stdout, side effects, and exit.
```

### OP-C: Composition / interaction / non-commutation split

Question:

```text
When two branches are both active, do their operations commute? If not, which order or precedence wins?
```

Typical child nodes:

```text
mode x renderer
mode x side effect
filter x aggregate
selection x exit
identity projection x sort
path projection x smallscreen
error x partial side effect
runtime x renderer bytes
```

`tparse` example:

```text
trimpath x smallscreen x markdown is a real branch because path projection, wrapping, and markdown block geometry share the same output byte surface.
```

Required OP-C future-discriminator field:

```text
future_discriminator_if_conflict
```

For every high-risk interaction row, the generator must state what parent
condition it would test if sibling branches later conflict. Examples of
discriminator classes:

```text
raw stream surface vs final report surface
substantive body exists vs filtering would make body empty
completion order vs sorted summary order
rendered row universe vs exit denominator
raw identity vs display identity
synthetic minimal fixture vs realistic producer morphology
side-effect bytes written before late failure vs all-or-nothing failure
clean source-like behavior vs compatibility branch
```

This is not a prediction that the conflict will occur. It is repair readiness:
the run should know where it would ascend if a future patch fixes one sibling
and breaks another.

### OP-E: Evidence / authority split

Question:

```text
Why do we believe this branch exists, and is it implementation truth or only a candidate needing observation?
```

Typical child nodes:

```text
visible_spec_explicit
program_class_inference
producer_name_inference
probe_required_pending_observation
locked_by_reference_observation
post_eval_failure_pressure
implementation_repair_evidence
explicit_deferral
conflict_isolated
```

`tparse` example:

```text
Official failures around branch-sensitive exit must remain post-eval pressure until new reference-first probes distinguish the relevant morphology or invocation route.
```

## 4. Descent algorithm

The recursive generator should maintain a priority queue of open nodes.

```text
1. Create base ontology graph from the README/spec.
2. Run hard-gate discovery:
   help_bootstrap_required,
   producer_schema_candidate_obligation,
   multi_consumer_output_role_second_descent,
   row_universe_projection_terminalization,
   projection_byte_grammar_child_leaves.
3. If observations have been collected, run observation-lock gates:
   observed_help_control_instantiation,
   observed_schema_fixture_synthesis,
   renderer_dialect_projection_expansion,
   discriminator_locked_probe_rule.
4. For each node, apply OP-B, OP-D, OP-R, OP-L, OP-T, OP-S, OP-P, OP-F, OP-C, OP-E.
5. If an operation yields observably distinct children, attach them under the node.
6. Recurse into each child.
7. Create cross-node OP-C interaction candidates only when children share a surface, subject, lifecycle stage, resource, identity, or denominator.
8. Stop a branch only when every applicable operation is exhausted, explicitly deferred, or proven pass-through.
9. Run terminalization: split any leaf whose siblings could change bytes, files,
   ordering, denominator, or exit while preserving the same high-level primitive.
10. Run coverage adequacy: mark synthetic-only, representative-only, and
   fixture-morphology gaps before probe closure.
11. Assign scoped_readiness_status and gold_readiness_status to every terminal
    leaf.
12. Promote scoped-ready leaves to gold-ready only when sibling coverage,
    cross-products, fixture realism, projection exactness, side effects, and
    exit denominators are closed or explicitly deferred.
13. Emit probes from terminal branch obligations, not from an edge-case list;
    after observation, every probe must name `locked_discriminator_ref`.
14. If probe count is high after gold coverage exists, run probe ownership
    compression without collapsing distinct behavior leaves.
15. Attach every observation, official failure, and implementation repair back to the smallest responsible node.
```

A practical scheduling order:

```text
OP-B boundary first, so identities are clear.
OP-D decomposition second, so fields and parts exist.
OP-R role split before value lattices, so one field with multiple consumers is not lumped.
OP-L value/presence/type split next.
OP-T lifecycle and OP-S subject/denominator split next.
OP-P projection and OP-F failure split next.
OP-C interactions after local branches exist.
OP-E evidence status at every step.
```

This order is not a semantic law, but it prevents the common failure where one broad field row hides several roles and then receives only one happy-path probe.

## 5. Node schema

Every branch-tree node should have a stable record.

```yaml
node_id: N-...
parent_id: N-... | null
path: Program/Input/EventRecord/Output/Role/raw_follow/stdout
semantic_label: Raw Output bytes copied to stdout in follow mode
source_basis:
  evidence_authority: visible_spec | producer_inference | program_class_inference | observation | post_eval_pressure
  source_refs: []
operator_that_created_node: OP-R
applied_operators:
  OP-B: exhausted | produced_children | not_applicable | deferred
  OP-D: exhausted | produced_children | not_applicable | deferred
  OP-R: exhausted | produced_children | not_applicable | deferred
  OP-L: open | exhausted | produced_children | not_applicable | deferred
  OP-T: open | exhausted | produced_children | not_applicable | deferred
  OP-S: open | exhausted | produced_children | not_applicable | deferred
  OP-P: open | exhausted | produced_children | not_applicable | deferred
  OP-F: open | exhausted | produced_children | not_applicable | deferred
  OP-C: open | exhausted | produced_children | not_applicable | deferred
  OP-E: current_status
consumers:
  - parser
  - reducer
  - renderer
  - side_effect_writer
  - exit_resolver
observable_surfaces:
  - stdout
  - stderr
  - exit
  - side_effect_file
  - rendered_bytes
risk:
  byte_exact: true
  side_effect: true
  exit_sensitive: false
  producer_schema_sensitive: true
terminal_status: open | probe_required | locked | deferred | pass_through | conflict_isolated
scoped_readiness_status: scoped_ready | scoped_blocked_pending_observation | scoped_blocked_by_conflict | scoped_deferred_with_reason | not_applicable_to_current_scope
gold_readiness_status: gold_ready | not_gold_ready_missing_sibling_branches | not_gold_ready_missing_cross_products | not_gold_ready_synthetic_only | not_gold_ready_unresolved_conflict | not_gold_ready_projection_exactness_open | not_gold_ready_fixture_realism_open | explicitly_deferred_from_gold_with_expected_risk | not_gold_required
gold_blocker_refs: []
missing_sibling_branches: []
missing_cross_products: []
fixture_realism_status: realistic_enough | synthetic_only | mixed_but_incomplete | not_applicable
terminal_observation_status: reference_observed | visible_spec_locked | pass_through_proven | pending_observation | deferred
implementation_handoff_status: blocked | scoped_handoff_allowed | gold_handoff_allowed | not_applicable
probe_refs: []
implementation_owner: renderer | parser | reducer | side_effect | cli | exit | unknown
```

This schema is intentionally tree-first. Existing table rows are projections of this tree:

```text
field-effect inventory       = OP-R applied to structured fields
producer-schema expansion    = OP-D + OP-E applied to named external producer
field-presence lattice       = OP-L applied to field or option nodes
lifecycle-stage table        = OP-T applied to record/state/mode nodes
aggregate-denominator table  = OP-S applied to summary/exit/status nodes
renderer-compatibility table = OP-P applied to projection nodes
runtime-surface table        = OP-P + OP-F applied to runtime/dependency nodes
mode-interaction table       = OP-C applied to mode/control nodes
D-ledger rows                = terminal behavior leaves with evidence/probe status
```

## 6. Stop conditions and anti-explosion rules

The tree can expand without bound unless descent is disciplined. Use these stop rules.

A node may stop as `atomic_locked` when:

```text
all applicable operators have been applied or declared not applicable;
all behavior-bearing children are represented;
there is at most one consumer truth for the node;
its value/presence/type states are either probed, specified, or irrelevant;
its projection surfaces are byte/process/accounted for;
its failure branches are accounted for;
its interactions with other nodes are either probed, impossible, or deferred;
evidence authority is not over-promoted.
```

A node may stop as `pass_through` only when:

```text
it has no lifecycle effect;
it has no subject-selection effect;
it has no validation effect;
it has no aggregate/exit effect;
it has no renderer/side-effect effect;
it has no distinct parser/runtime error surface;
and it has no interaction with a higher-risk node.
```

A node may stop as `explicitly_deferred` only when the deferral says:

```text
what was deferred;
which operator would have split it;
which surface could be wrong;
why current budget/scope accepts the risk;
which future observation would unlock it.
```

A broad node must not stop when:

```text
it has multiple consumers;
it reaches both renderer and exit;
it reaches a side-effect surface;
it is byte-exact;
it belongs to a named external producer schema;
it affects filtering or aggregation;
it has late/partial failure ordering;
it is a mode/control surface that shares a renderer/resource/exit surface with another mode.
it is backed by a visible help/full-usage pointer and help bootstrap has not
  been observed or explicitly deferred;
it consumes a named external producer and lacks an obligationized producer
  candidate table;
it renders a table/list/report/progress stream and lacks row-universe,
  ordering, denominator, identity, and byte-grammar terminalization.
```

A probe family must not stop as `coverage_closed` when:

```text
it has only a representative probe for a multi-axis family;
it has byte-exact projection behavior but lacks byte snapshots;
it consumes a named external producer but uses only synthetic minimal fixtures;
it composes a mode with a renderer, side effect, or exit surface but lacks
  interaction rows;
it treats a state class such as panic, build error, no-test, race, cached, or
  skipped as incidental output instead of a terminal result state;
it does not say which sibling branches remain outside the current probe row.
it has a multi-consumer payload without role-specific leaves;
it lists projection byte grammar parts but does not create child leaves for
  independently variable byte/process parts;
it has a high-risk OP-C interaction without a future-discriminator plan.
it lacks per-leaf scoped_readiness_status and gold_readiness_status;
it marks a leaf scoped_ready while sibling branches or cross-products still
  block gold_readiness;
it treats a green local scoped probe packet as proof of gold readiness;
it has not classified probe ownership, or has compressed probes before
  gold-required leaves are explicit.
```

A scaffold must not stop as `gold_ready` when:

```text
any gold-required terminal leaf is only scoped_ready;
any high-density open discriminator is carried only as narrative risk;
any renderer, control-plane, side-effect, sort/order, identity, fixture
  morphology, or exit-denominator surface lacks terminal observations or
  explicit gold deferral;
the local gold fixture set has not been defined;
the implementation handoff does not say whether it is scoped or gold.
```

## 7. Probe grouping from the tree

A probe is a witness for a branch distinction. Probe grouping should mirror the tree.

Each probe row should name:

```text
probe_id
primary_node_path
operator_witnessed
sibling_branches_separated
minimal_fixture
realism_tier
observable_surface
expected_observation_kind
negative_control_or_baseline
interaction_partner_paths
future_discriminator_if_conflict
oracle_authority
implementation_owner
owned_leaf_refs
coverage_strength
compression_candidate_status
```

### Probe family types

```text
local discriminator probe
  Separates sibling branches created by one operator.

presence/type lattice probe
  Covers OP-L children such as absent/null/empty/wrong-type/default.

lifecycle-order probe
  Covers OP-T ordering such as side effect before late parser error.

subject/denominator probe
  Covers OP-S hidden-row, selected-row, aggregate, or exit denominators.

projection byte probe
  Covers OP-P renderer or serialization grammar.

failure-precedence probe
  Covers OP-F error ordering and process-surface priority.

interaction probe
  Covers OP-C non-commutation between two paths.

realistic morphology probe
  Covers a projection subtree over external producer-shaped fixtures rather than synthetic minimal rows.
```

The important rule:

```text
Probe families are grouped by nearest common ancestor in the ontology tree, not by superficial test file or by implementation module.
```

For example, a `tparse` probe for `-follow-output` plus late malformed input belongs under:

```text
Program
  / Side effects
  / Raw Output preservation
  / Lifecycle ordering
  / Late parser error after side effect
```

It should not be grouped merely as “malformed input” or “follow flag,” because its purpose is to witness non-commutation between raw side effects and parser failure.

## 8. Implementation coverage from the same tree

Code coverage should be semantic coverage over the branch tree.

Implementation starts only after the handoff type is explicit:

```text
scoped_implementation_attempt:
  allowed when scoped-ready leaves are locked for a bounded experiment and
  residual gold blockers are carried as expected score risk.

gold_implementation_attempt:
  allowed only when all gold-required terminal leaves are gold_ready or
  explicitly_deferred_from_gold_with_expected_risk, and the local gold fixture
  set is defined.
```

For a gold implementation attempt, the objective is not "implement the program
from the scaffold" in prose. The objective is:

```text
make the candidate executable pass the complete local gold fixture set,
including regression-retention probes, side-effect byte probes, and any
compatibility/projection sharpening probes that are gold-required.
```

Each terminal behavior leaf gets a coverage record:

```yaml
behavior_leaf: N-...
primary_operator: OP-P
implementation_owner: renderer.failure_details
fixtures: [PR-...]
asserted_surfaces: [stdout_sha256, stderr, exit]
state_invariant_refs: [N-...]
negative_controls: [PR-...]
known_conflicts: []
scoped_readiness_status: scoped_ready
gold_readiness_status: gold_ready
handoff_type: gold_implementation_attempt
probe_ownership_status: strongest_owner_probe | retained_overgranular_risk_probe | compressed_out
```

The implementation does not need one function per node. It needs explicit ownership by semantic layer:

```text
OP-D / OP-L / OP-F on input fields     -> parser and validator
OP-R on fields                         -> classifiers / role splitters
OP-T on records                        -> lifecycle reducer
OP-S on subjects and denominators      -> selector, aggregator, exit resolver
OP-P on external surfaces              -> renderers, serializers, side-effect writers
OP-C on modes                          -> mode orchestration and precedence rules
OP-E                                   -> probe/oracle/evidence ledger, not production behavior
```

This gives the repair loop a principled routing rule:

```text
If a failure maps to a leaf with OP-P as primary operator, repair renderer/projection first.
If it maps to OP-S, repair subject selection or denominator logic first.
If it maps to OP-T, repair reducer ordering/lifecycle first.
If it maps to OP-R, repair classification/de-lumping first.
If it maps to no existing leaf, the theory tree is missing a branch.
```

## 9. Worked `tparse` descent fragments

### 9.1 Base ontology root

```text
N0 Program: tparse
  Semantic class: CLI stream summarizer / renderer for Go test JSON events.
  Main external producer: go test -json / test2json-like stream.
  Core subjects: package, test, subtest, package-level diagnostic output.
  Core carried state: package/test lifecycle, output lines, elapsed, coverage, status.
  Core projections: basic table, plain table, markdown, failure details, raw follow bytes, progress lines, exit code.
  Core controls: source selection, filters, format/color, path trimming, slow/sort, follow/follow-output/timestamp, progress, compare.
```

### 9.2 Event `Output` descent

```text
N0 Program
└─ N1 Input event stream                         [OP-D]
   └─ N2 Event record                            [OP-D]
      └─ N3 Field: Output                        [OP-D]
         ├─ N4 Raw byte/string payload            [OP-R]
         │  ├─ N5 Follow stdout projection        [OP-P]
         │  ├─ N6 Follow-output file projection   [OP-P]
         │  └─ N7 Emitted before late parse error [OP-T + OP-F]
         ├─ N8 Test/package detail body           [OP-R]
         │  ├─ N9 Failure-detail renderer block   [OP-P]
         │  └─ N10 Markdown/plain/basic variants  [OP-P + OP-C]
         ├─ N11 Diagnostic classifier role        [OP-R]
         │  ├─ N12 Panic-like block               [OP-L + OP-P]
         │  ├─ N13 Build-failure-like block       [OP-L + OP-S]
         │  ├─ N14 Race-marker-like block         [OP-L + OP-S]
         │  ├─ N15 No-test-like block             [OP-L + OP-S]
         │  └─ N16 Coverage-line-like block       [OP-L + OP-S]
         └─ N17 Error surface for wrong shape      [OP-L + OP-F]
```

The generic rule never mentions `panic` or `race`. They arise because OP-R asks which consumers use `Output`, OP-L asks which value classes are semantically distinguished by the named Go-test producer and the visible renderer contract, and OP-S asks whether those classes alter aggregate or exit truth.

### 9.3 Package identity descent

```text
N0 Program
└─ N20 Subject: Package
   ├─ N21 Raw package identity                    [OP-B]
   │  ├─ N22 Grouping key                         [OP-S]
   │  └─ N23 Compare/current identity             [OP-S]
   ├─ N24 Display package identity                [OP-R]
   │  ├─ N25 trimpath projection                  [OP-L + OP-P]
   │  ├─ N26 smallscreen projection               [OP-P]
   │  └─ N27 markdown/plain/basic projection      [OP-P]
   └─ N28 Collision branch                         [OP-C]
      ├─ N29 raw packages distinct, display same  [OP-S + OP-P]
      └─ N30 sort/compare under collision         [OP-C]
```

This prevents the false rule “trimmed visible names are package identities.” The branch tree records that trimpath is display truth, while grouping and compare may use raw truth unless observed otherwise.

### 9.4 Action lifecycle descent

```text
N0 Program
└─ N40 Event record Action field
   ├─ N41 Recognized lifecycle action             [OP-L]
   │  ├─ N42 run/start/in-progress                [OP-T]
   │  ├─ N43 output-attaching action              [OP-T + OP-R]
   │  ├─ N44 pass/fail/skip finalizer             [OP-T + OP-S]
   │  └─ N45 bench/benchmark-like action          [OP-L + OP-S]
   ├─ N46 Missing or unknown action               [OP-L + OP-F]
   └─ N47 Incomplete lifecycle at EOF             [OP-T + OP-F]
```

`start` and `bench` are not hard-coded. They are expected candidates because OP-D and OP-E expand a named external producer schema, and OP-T asks which actions affect lifecycle finalization.

### 9.5 Follow/follow-output/timestamp descent

```text
N0 Program
└─ N60 Control mode: raw output preservation
   ├─ N61 follow stdout                           [OP-P]
   ├─ N62 follow-output file                      [OP-P]
   │  ├─ N63 file open before stream decode       [OP-T]
   │  ├─ N64 open failure precedence              [OP-F]
   │  └─ N65 suppress stdout when file present    [OP-C]
   ├─ N66 include timestamp                       [OP-P + OP-L]
   │  ├─ N67 valid event Time                     [OP-L]
   │  └─ N68 missing/null/default Time            [OP-L]
   └─ N69 late malformed stream after raw write   [OP-T + OP-F]
```

This branch group explains why probes should not be scattered across “follow,” “timestamp,” and “malformed input.” The actual behavior surface is raw-output side-effect ordering.

### 9.6 Exit/status denominator descent

```text
N0 Program
└─ N80 Process exit
   ├─ N81 Flag parser denominator                 [OP-F + OP-S]
   ├─ N82 Input-source denominator                [OP-F + OP-S]
   ├─ N83 Decoded valid event denominator         [OP-S]
   ├─ N84 Rendered selected rows denominator      [OP-S]
   ├─ N85 Package/test failure denominator        [OP-S]
   ├─ N86 Diagnostic classifier denominator       [OP-R + OP-S]
   ├─ N87 Side-effect failure denominator         [OP-F + OP-T]
   └─ N88 Conflict-isolated branch pressure       [OP-E]
```

This captures the key principle: rendered status, package summary, diagnostic classifier, parser failure, side-effect failure, and process exit are separate denominators that sometimes align and sometimes do not.

## 10. Bookkeeper v4 audit shape

The bookkeeper should audit operator continuity rather than only artifact continuity.

For each node, it asks:

```text
Did the generator apply every applicable operator?
If an operator was skipped, is there an explicit not-applicable or deferral reason?
If an operator produced children, did each child receive terminal status?
Does every high-risk child have a probe, observation lock, or explicit deferral?
Does every probe point back to the operator and sibling distinction it witnesses?
Do interaction probes exist for non-commuting branches sharing a surface?
Was any candidate branch over-promoted into implementation truth?
Does every terminal leaf distinguish scoped readiness from gold readiness?
Is any scoped-ready leaf being passed downstream as gold-ready without closing
or explicitly deferring its siblings, cross-products, fixture realism, and
projection/exit surfaces?
If probe compression occurred, did it preserve all distinct gold-required
behavior leaves?
```

Blocking bookkeeper failures become:

```text
operator_not_applied
operator_output_silent_drop
child_without_terminal_status
probe_without_operator_witness
behavior_leaf_without_probe_or_deferral
interaction_missing_for_shared_surface
candidate_overpromoted_to_locked_truth
post_eval_pressure_laundered_as_pre_observation_theory
scoped_ready_promoted_to_gold_ready
gold_handoff_with_open_required_leaf
green_scoped_probe_packet_treated_as_gold_gate
probe_compression_collapsed_distinct_leaf
```

The old shadow inventory is still useful, but the audit target is now the branch tree.

## 11. Observation and repair loop

Observations update the tree, not just expected outputs.

```text
reference observation confirms branch
  -> mark leaf locked_by_observation

reference observation contradicts branch
  -> either revise branch semantics or create conflict-isolated sibling

local probe green but official eval fails
  -> attach failure to nearest node
  -> if no node exists: missing ontology branch
  -> if node exists but no realistic morphology child: fixture morphology gap
  -> if child exists and local probe is too synthetic: probe under-realism
  -> if child exists and local probe matches but official differs: evidence conflict / branch-sensitive condition
  -> if exact bytes differ: projection compatibility gap

repair fixes one branch but regresses another
  -> do not keep patching the two leaves independently
  -> move upward to the smallest shared parent node or shared projection surface
  -> name the flat rule that made the branches conflict
  -> derive candidate upstream discriminators
  -> build counterfactual probes that differ only by the proposed discriminator
  -> keep regression-retention probes for the branch that was previously green
  -> patch only after the discriminator is observed or directly specified
```

This preserves evidence hygiene. Official failures are valuable pressure, but they do not become clean first-pass theory until reference-first observation or visible-spec authority locks the branch.

The repair loop therefore treats branch-breaking regressions as ontology
evidence. A regression is not merely a failed patch when it occurs on a sibling
branch sharing the same surface; it is usually proof that the current tree is
missing a parent discriminator. The expected repair artifact is an
upstream-discriminator row, not a stronger local patch.

### 11.1 Grouped divergence before repair

When local probes or official eval rows fail, the next artifact is not a patch
plan. It is a divergence diagnosis.

The generator must first compare failed rows against passed rows and ask:

```text
Which theory node predicted both sets?
Which sibling branch was missing, over-flattened, or assigned to the wrong
authority layer?
Did the failed rows share a projection surface, subject denominator, lifecycle
stage, value lattice, side effect, exit denominator, or fixture morphology?
Did the passed rows prove that part of the theory is already correct?
```

Only after this grouping step may the run proceed to probe repair or code
repair. The diagnosis row should classify the failure as one of:

```text
missing_conceptual_node
existing_node_badly_split
terminalization_gap
probe_under_realism
projection_exactness_gap
authority_layer_conflict
implementation_transfer_error
post_eval_compatibility_pressure
```

The important rule:

```text
failed probes are observations about the current theory,
not a to-do list of expected-output edits.
```

### 11.2 Layer-transition attribution

Every repair candidate must name the layer transition where the drift occurred.

Use the following default layer meanings:

```text
L0 visible prompt / public spec
L1 native base ontology
L2 recursive branch lattice
L3 executable probe contract / observation lock
L4 implementation transfer
L5 official eval compatibility surface
```

Typical attributions:

```text
L1 -> L2:
  The base ontology noticed a phenomenon but did not split it into the right
  semantic primitives.

L2 -> L3:
  The branch lattice existed, but probes did not terminalize it into executable
  observations with enough sibling coverage or realistic morphology.

L3 -> L4:
  The probe contract was correct, but implementation generalized it too far,
  applied it to the wrong sibling, or lost exact projection details.

L4 -> L5:
  Local theory and implementation are coherent, but the official branch exposes
  a compatibility dialect, public golden exactness surface, or post-eval-only
  conflict.
```

The repair schedule should move from the most local confirmed transfer errors
upward only when necessary. If a lower-layer repair breaks an already-green
group, stop and reclassify the shared parent before continuing.

### 11.3 Scientific repair cycle

A complete repair cycle has this shape:

```text
1. State the current theory node and expected behavior.
2. State the failed and passed evidence rows.
3. Diagnose the smallest wrong abstraction.
4. If needed, ascend to the smallest shared parent node.
5. Derive the missing discriminator.
6. Build counterfactual probes that isolate the discriminator.
7. Keep regression-retention probes for already-green siblings.
8. Patch the theory, then the probes, then the implementation.
9. Re-run local gates before official eval.
10. Record fixed rows, regressions, and remaining failures by layer.
```

The cycle is intentionally scientific:

```text
theory -> prediction -> observation -> grouped anomaly -> theory repair
```

It should not collapse into:

```text
official failure -> patch the nearest code branch
```

### 11.4 Green-gate discipline

Before submitting an implementation after any repair, require the strongest
available local green gate for that layer:

```text
original cleanroom probe contract
counterfactual sibling probes
new discriminator probes
realistic morphology probes
side-effect byte probes
regression-retention probes for previously green groups
```

For a gold implementation attempt, the local gate is stricter:

```text
1. every gold-required leaf has gold_readiness_status = gold_ready, or is
   explicitly_deferred_from_gold_with_expected_risk;
2. the local gold fixture set is defined from those leaves;
3. the candidate executable passes every local gold fixture;
4. every retained over-granular hidden-source-risk probe remains green;
5. every compressed probe is covered by a stronger owner probe.
```

The run must not submit to official eval on the basis of:

```text
scoped_ready leaf status
scoped local probe green
implementation prose conformance
uncompressed probe count alone
```

If official eval is used after a local green gate, classify its result as:

```text
confirmed_generalization
new_missing_branch
post_eval_compatibility_surface
official_conflict_pressure
```

Do not treat official success as retroactive proof that post-eval-only branches
were clean first-pass evidence. They remain labeled by their evidence source.

### 11.5 Final projection sharpening

Near convergence, remaining failures often stop being broad semantic gaps and
become projection-boundary gaps:

```text
internal blank-line preservation
ANSI coloring threshold
usage stream/program name
panic source line
table width and alignment
side-effect file bytes
process exit after otherwise-correct output
```

These are still ontology facts, but they sit at a narrow external-surface node.
The generator must keep them attached to their parent projection surface rather
than reopening the whole program theory. A 100-target repair at this stage
should be narrow, regression-gated, and explicitly labeled as projection
sharpening or compatibility sharpening.

## 12. How this changes the current v2 documents

The current v2 generator/bookkeeper can be refactored without discarding its useful content.

### Replace “required indication artifacts” with “operator-triggered derived views”

```text
Current artifact                         New source
field-effect inventory                   OP-R on structured fields
producer-schema expansion                OP-D + OP-E on named producer
high-risk field de-lumping               OP-R when a field has multiple consumers
field-presence lattice                   OP-L on any behavior-bearing node
lifecycle-stage table                    OP-T on records, actions, modes, effects
aggregate-denominator table              OP-S on summary/status/exit nodes
renderer-compatibility table             OP-P on projection nodes
runtime-surface table                    OP-F + OP-P on runtime/dependency nodes
help/control-plane table                 OP-D + OP-L + OP-F + OP-P on CLI controls
version/executable table                 OP-B + OP-P on identity/runtime surfaces
golden-fixture morphology mesh           OP-P + OP-D + OP-C on producer-shaped projection nodes
mode-interaction closure                 OP-C on control/mode nodes sharing surfaces
conflict-isolation table                 OP-E on contradictory observations
```

### Add a required branch-tree artifact

The generator should emit:

```text
recursive_ontology_tree
operator_application_ledger
terminal_leaf_ledger
terminal_leaf_readiness_ledger
probe_witness_map
probe_ownership_compression_table, when compression is requested
implementation_coverage_map
bookkeeper_operator_audit
```

The D-ledger should be a terminal-leaf readiness ledger, not a flat list of
obligations. It must be possible to pass the baton to a later phase with a
precise instruction:

```text
promote these scoped-ready leaves to gold-ready;
or accept these explicit gold deferrals with expected score risk.
```

## 13. Minimal generator prompt skeleton

```text
You are the recursive ontology generator.

Do not enumerate task-specific edge cases first.

First, read the visible README/spec and infer the program's base ontology:
program class, external producers, input entities, subjects, state, lifecycle,
controls, selection, aggregation, projections, side effects, errors, runtime,
identity, and evidence boundaries.

Before local descent closes, run the hard gates:
- if help/full usage/version/options are visible, emit help_bootstrap_required
  and a help/control inventory observation plan with typed hidden-control
  candidate buckets;
- if a named external producer or structured tool output is consumed, emit a
  producer_schema_candidate_table with obligationized pending fields and
  morphology candidates;
- if any producer payload is consumed by multiple roles, emit a
  multi_consumer_output_role_table and role-specific leaves;
- if any table/list/report/progress/grouped projection exists, emit
  projection_row_universe rows for membership, hidden rows, grouping,
  raw/display identity, order, sort/ties, denominators, byte grammar, modes,
  and morphology.
- if any projection is byte-observable, emit projection_byte_grammar_child_leaves
  for header/body/separator/blank-line/style/wrapping/order/footer/stream split.
- for high-risk OP-C rows, include future_discriminator_if_conflict.
- for every terminal leaf, emit both scoped_readiness_status and
  gold_readiness_status. Never treat scoped_ready as gold_ready by default.
- before implementation handoff, emit gold_readiness_summary and declare the
  handoff type: scoped_implementation_attempt or gold_implementation_attempt.
- only after gold-required leaves are explicit, optionally emit a probe
  ownership compression table. Do not compress probes that witness distinct
  sibling branches, output roles, side-effect destinations, exit denominators,
  renderer byte grammars, fixture-realism tiers, or authority layers.
- if observations have already been collected, convert them into locked
  obligations before adding implementation guidance:
  - help observations become observed_help_control_instantiation rows;
  - producer schema observations become observed_schema_fixture_synthesis rows;
  - discovered renderer/projection modes become
    renderer_dialect_projection_expansion rows;
  - every post-observation probe receives locked_discriminator_ref.

Then recursively apply the following operators to every ontology node:
OP-B boundary, OP-D decomposition, OP-R role/consumer, OP-L lattice,
OP-T lifecycle, OP-S subject/selection/aggregation, OP-P projection,
OP-F failure/negation, OP-C composition/interaction, OP-E evidence/authority.

For every operation:
- state why it applies or why it is not applicable;
- create children when observably distinct behavior can result;
- recurse into children;
- attach evidence authority;
- stop only with locked, probed, pass-through, deferred, or conflict-isolated status.

Finally emit:
1. recursive ontology tree;
2. operator application ledger;
3. terminal behavior leaves;
4. probe witness map;
5. terminal leaf readiness ledger with scoped and gold statuses;
6. implementation coverage map;
7. help bootstrap plan, if triggered;
8. producer schema candidate table, if triggered;
9. multi-consumer output role table, if triggered;
10. projection row-universe terminalization table, if triggered;
11. projection byte grammar child leaves, if triggered;
12. observed help control instantiation table, if observations exist;
13. observed schema fixture synthesis table, if observations exist;
14. renderer dialect projection expansion table, if observations exist;
15. discriminator-locked probe ledger, if observations exist;
16. gold readiness summary;
17. probe ownership compression table, only if compression is requested after
    gold-required leaves are explicit;
18. open risks and bookkeeper questions.
```

## 14. Minimal bookkeeper prompt skeleton

```text
You are the adversarial recursive ontology bookkeeper.

Audit the generator tree, not just the final obligations.

For every node:
- verify every applicable operator was applied, declared not applicable, or deferred;
- verify every operator-produced child has terminal status;
- verify every behavior-bearing leaf has a probe, observation lock, or explicit deferral;
- verify every probe witnesses a specific operator split and sibling distinction;
- verify every non-commuting shared-surface interaction has an OP-C row;
- reject candidate-to-truth overpromotion;
- reject post-eval pressure laundered into first-pass theory.
- reject scoped-ready leaves promoted to gold-ready without sufficient sibling,
  cross-product, fixture-realism, projection, side-effect, and exit closure;
- reject full implementation handoff unless all gold-required leaves are
  gold_ready or explicitly_deferred_from_gold_with_expected_risk;
- reject probe compression that collapses distinct gold-required leaves.

Return blocking objections with the smallest missing node/operator/probe repair.
```

## 15. Immediate application to the current `tparse` loop

For the current reconstruction target, the next meta-program pass should not simply add more V5 probes. It should first rebuild the loop-21 theory as a recursive tree, then place the remaining failures into that tree.

Expected mappings:

```text
follow/follow_mode failures
  -> N60 raw output preservation subtree
  -> likely missing OP-C / OP-T interactions among follow, follow-output, timestamp, progress, parser failure, and real fixture morphology

format/golden output failures
  -> OP-P projection grammar leaves
  -> renderer byte compatibility and fixture realism children

failure_details failures
  -> Output -> failure detail role -> renderer block geometry
  -> OP-P branch not deep enough

path/sort/smallscreen failures
  -> Package identity -> display identity -> trimpath -> smallscreen/sort interactions
  -> OP-C non-commutation children

panic/harvest/real_testdata failures
  -> Output diagnostic classifier -> panic/prescan morphology
  -> OP-L value-class depth plus OP-P fixture realism

branch-sensitive exit pressure
  -> Process exit denominator tree
  -> OP-E conflict-isolated until reference-first morphology probes split it

intertwined repair groups
  -> Sibling leaves under one shared parent surface
  -> do not choose between the two leaves by broad patching
  -> ascend to the parent discriminator, then descend again with probes
  -> examples from the current loop:
       follow noisy-line filtering needed the discriminator
       "substantive transcript exists vs filtering would empty transcript";
       progress ordering needed the discriminator
       "completion stream projection vs final summary projection"
```

The conceptual repair is therefore:

```text
1. Build the recursive tree.
2. Attach every existing PR/V3/V4/official row to tree nodes.
3. Mark uncovered behavior-bearing leaves.
4. Generate probes by missing operator witness, not by failing test-name mimicry.
5. For intertwined red/green repair groups, create an upstream-discriminator row
   before implementation patching.
6. Route code repair by each leaf's primary operator and implementation owner.
```

This is the path toward a general programming ontology meta-program: task specifics are extracted semantically at the base pass, then all downstream specificity is forced by stable conceptual operations.

## 16. v4 lesson from Run H vs gold baseline

The `tparse` Run H A/B against the eventual 100 baseline shows a distinct
readiness failure mode:

```text
local scoped probe packet green
  !=
gold scaffold ready
```

Run H correctly locked several scoped discriminator tables:

```text
schema field/shape posture
basic compare current-report-only behavior
raw malformed destination behavior
stdin plus -file precedence
```

But the official score density remained in other leaves:

```text
help / argparse / usage exactness
renderer / format / golden byte grammar
follow / follow-output / progress transcript
sort / slow projection
path / trimpath / display identity
failure detail / panic / build / race roles
harvest / real fixture morphology
```

The meta-program must therefore require a baton-passing artifact:

```text
terminal_leaf_readiness_ledger
```

Every leaf in that ledger must state:

```text
scoped readiness:
  what is ready for a bounded implementation attempt now;

gold readiness:
  what remains before this leaf can be part of the full local gold fixture
  contract for implementation and official-eval submission.
```

The next phase after a scoped run is not automatically implementation. It is:

```text
promote scoped-ready leaves to gold-ready
```

That phase should create the missing sibling observations, cross-products,
fixture realism, and projection/exit exactness probes needed for gold readiness.
Only after that promotion is complete should a full implementation loop begin.

### 16.1 Deferred probe-count optimization

Probe count should be optimized only after gold-required leaves are explicit.
The compression question is:

```text
Which probes prove the same behavior leaf, and which are witnessing genuinely
distinct lower-level hidden-source risk?
```

Use these compression classes:

```text
owned_by_existing_probe
requires_new_probe_same_leaf
requires_new_probe_new_leaf
over_granular_but_hidden_source_risk_valid
redundant_and_removable
deferred_until_more_task_evidence
```

This prevents two opposite mistakes:

```text
over-individualizing probes that are already owned by stronger fixtures;
compressing probes that are finer-grained because hidden source behavior can
fork below the current abstraction.
```

The first category is conceptual redundancy and can be compressed. The second
category is an innate reconstruction risk and must remain until more task
evidence proves it safe to compress.
