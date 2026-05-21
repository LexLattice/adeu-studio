# Principled Recursive ODEU Meta-Program Experimental v8

## Purpose

This is a proposed refinement of the current ADEU / ODEU program-reconstruction scaffold. It turns the generator from an indication-and-checklist procedure into a recursive ontology descent procedure, adds an explicit observation-to-obligation lock step before implementation, and adds an independent public-surface scout / granularity-fitness gate before any gold implementation handoff.

v5 carries forward the `tparse` Run H vs gold-baseline A/B lesson from v4:

```text
scoped-ready is not gold-ready;
green local probes over a scoped packet are not evidence of global parity;
implementation should target a gold-ready fixture ledger, not an open
discriminator ledger;
probe count should eventually be compressed by conceptual ownership, but only
after gold-required leaves are explicit.
```

v5 adds the lesson from the `scc` local-green / official-red failure:

```text
reference-observed fixture bytes are not enough;
public executable surfaces can reveal missing grammar depth;
conceptual reconstruction and executable scout evidence should be produced
blindly and then reconciled;
gold readiness requires generative rule evidence, not fixture/argv replay;
held-out sibling or metamorphic probes are required for high-risk public
grammar, renderer, selection, and side-effect surfaces;
probe compression remains a deferred future feature.
```

v5 also carries the later `scc` Phase31 -> Phase32 lesson:

```text
observed local leaves are not automatically entitled to all sibling projection
surfaces;
a leaf can be locally green and still lack projection rights;
implementation handoff must prove the parent discriminator across relevant
sibling projections, or carry an explicit projection gap.
```

v6 adds the `scc` Phase57 -> Phase59 generated-marker lesson:

```text
a positive transition through a configurable matcher is not enough to promote
the matcher branch to implementation truth;
matcher-bearing controls require a source / composition / scope / comparison /
consumer gate before gold promotion;
detection, denominator policy, display labeling, and projection consumers must
remain separate leaves unless observations prove they collapse.
```

v6 also incorporates the later `scc` Phase63 -> Phase64 value-shape lesson:

```text
when a matcher/remapper/configuration flag accepts a list-like value, the
argument grammar itself is a discriminator;
separate-value, equals-value, comma-list, comma-space normalization, and
repeated-flag composition must be probed independently;
repeated flags may union rather than replace, and a present-second / absent-first
probe does not distinguish those policies.
```

v6 additionally incorporates the `scc` Phase66 -> Phase68 diagnostic lesson:

```text
unknown-flag handling is not only an error state;
similar-suggestion diagnostics are a projection grammar with candidate source,
similarity threshold, max cardinality, ratio ordering, and tie ordering;
public-reference absence and official-eval presence must be labeled as a
post-eval compatibility branch rather than clean public-reference truth.
```

v6 also incorporates the `scc` Phase69 -> Phase70 remap/count-as lesson:

```text
remap and count-as are not a single feature branch;
they split into source subject scope, mapping target resolution, value-shape,
known-vs-unknown subject policy, search-window policy, and language-counting
consumer policy;
known-extension override evidence for one mapping form does not automatically
grant override authority for every source extension or every target kind.
```

v6 further incorporates the `scc` Phase72 -> Phase74 shared-extension lesson:

```text
extension classification can be a many-to-one public grammar, not a filename
lookup table;
shared extensions require content-discriminator probes, counting-consumer
probes, mixed-directory projection probes, and conflict labels when public
reference observations and official post-eval fixtures disagree on a consumer;
classification success does not imply counting, complexity, display, harvest,
or remap-consumer success.
```

v6 also incorporates the `scc` Phase75 -> Phase77 filtering identity lesson:

```text
filter failures can originate upstream in identity normalization rather than in
the predicate itself;
extension identity, shebang identity, default exclusion lists, custom override
semantics, and path normalization must be modeled as separate but interacting
surfaces;
custom list flags may replace defaults instead of unioning with them.
```

v6 also incorporates the `scc` Phase78 -> Phase82 core-counting lesson:

```text
counting fixes propagate widely through analysis, format, integration, error,
and special-output rows;
public language-list surfaces can define extension identity, but they do not
close language-specific comment, blank, complexity, generated/minified, or
renderer consumers;
shared classifiers must have precedence over flat language-map expansion.
```

v7 incorporates the `scc` Phase108 -> Phase109 source-postmortem lesson:

```text
after a run is local-green but official-red, continued blind fixture grinding can
measure only the current theory;
postmortem source inspection may be used as source-derived repair evidence to
identify missing meta-program operators, not to launder source facts into clean
first-attempt evidence;
large generated resource inventories, alternate entrypoints, cross-flag state
mutation graphs, event-stream grammars, output-router layering, estimator
formula subsystems, and toolchain/library contracts must become first-class
gold-readiness gates when the public surface suggests them.
```

v8 incorporates the GPTPro §4.3 review over the meta-ontology export:

```text
the current v7 direction is right, but the primitive operator vocabulary should
be factored into a smaller kernel algebra;
Warrant/evidence/readiness is a modal layer over every node, not an ordinary
behavior-splitting operator;
the missing primitive is Transform / semantic computation: the function that
maps input/state/substrate into computed truth before projection;
specialized gates such as matcher, resource, protocol, projection, formula,
fixture-realism, and source-postmortem should remain mandatory, but as derived
macros/views generated from the kernel rather than as peer primitives.
```

The core idea is:

```text
visible program spec / README
  -> native semantic base ontology pass
  -> recursive application of a kernel algebra
  -> mandatory macro gates triggered by program class and public surface
  -> nested behavior branch tree
  -> intermediate terminalization and coverage adequacy audit
  -> blind public-surface recon scout over the reference executable
  -> granularity fitness audit between scout surfaces and concept leaves
  -> repair missing depth axes before gold promotion
  -> per-leaf scoped-readiness / gold-readiness accounting
  -> matcher-policy gate for configurable matchers and marker-like classifiers
  -> value-shape gate for list-like matcher/remapper/configuration controls
  -> diagnostic suggestion grammar gate for close unknown public controls
  -> promotion of scoped leaves to gold-ready leaves, or explicit deferral
  -> probe families grouped by tree structure
  -> anti-replay generative-rule gate with held-out siblings / metamorphic probes
  -> probe ownership compression explicitly deferred unless later selected
  -> implementation coverage map grouped by the same tree
  -> local gold fixture green gate
  -> observation / eval feedback attached back to exact tree nodes
```

Probe ownership compression is not part of the v8 active run sequence. It stays
available as a future feature only after gold-required leaves, rule ownership,
and anti-replay coverage are explicit.

The task-specific details should not be named in the generic rules. The rules name only the primitive operations. Specifics such as `tparse` having raw follow output, package/test identity, panic-like output, race markers, markdown table byte geometry, trimpath display identity, or exit-denominator conflicts should arise from applying those operations to the base ontology inferred from the program spec and producer semantics.

## 1. Main correction to the earlier meta-program

The earlier v2 generator was already much better than a flat edge-case enumerator. Its weakness was that many required artifacts were still named as generic indications:

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

## 2. Core phases: semantic base pass, descent, scout, fitness, gold promotion

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

#### Phase D.1: leaf entitlement / projection rights audit

Before a scoped-ready leaf may become implementation-ready, the run must prove
that the leaf is entitled to the projection surfaces it will affect.

Required row shape:

```text
leaf_id
owning_parent_discriminator
observed_fixture_refs
public_projection_surfaces
sibling_projection_matrix
negative_control_refs
regression_retention_refs
cross_axis_composition_refs
projection_entitlement_status
projection_gap_refs
```

Allowed `projection_entitlement_status` values:

```text
observed_leaf_only
projection_entitled
projection_gap
explicitly_deferred_with_expected_risk
not_projection_sensitive
```

Rule:

```text
observed_leaf_only cannot become implementation-ready.
```

For every projection-sensitive leaf, promotion requires either:

```text
projection_entitled:
  the owning discriminator has been checked against relevant sibling
  projection surfaces, negative controls, and regression-retention probes.

explicitly_deferred_with_expected_risk:
  missing sibling projections are named and the run is not represented as a
  full gold implementation handoff.
```

If repairing one projected leaf breaks another already-green projected leaf,
the run must ascend to the smallest shared parent discriminator and repair that
parent before patching either leaf again.

### Phase E: blind public-surface recon scout

After the conceptual tree exists, run an independent scout over legitimate
public behavior exposed by the reference executable. The scout is intentionally
blind to the conceptual tree, probe contract, implementation attempts, and
official eval failures.

Allowed evidence:

```text
public CLI invocation behavior
help / usage / version / listing output
invalid flag and invalid value surfaces
missing value behavior
format and output route behavior
stdout / stderr / exit / file side effects
minimal fixtures created by the scout
```

Forbidden evidence:

```text
source inspection
decompilation
binary strings or symbol scraping
hidden/evaluator tests
official eval failures
prior conceptual artifacts
implementation artifacts
```

Required scout outputs:

```text
public_surface_command_log.jsonl
cli_grammar_harvest
invalid_value_and_precedence_matrix
output_mode_surface_ledger
fixture_behavior_surface_ledger
scout_gap_and_uncertainty_ledger
scout_to_granularity_fitness_handoff
```

The scout's purpose is not full reconstruction. Its purpose is to expose public
grammar and behavior axes that an otherwise plausible README/spec ontology might
have missed.

For CLI tasks, the scout must specifically attempt to harvest:

```text
top-level command shape
subcommands, if any
flag aliases
bool / string / strings / int / float / mapping-like value classes
terminal missing-value behavior
greedy next-token value binding behavior
unknown flag precedence
help/version/listing mode precedence
parse errors versus semantic invalid no-op/fallback
output route grammar
file side effects
renderer dialect names and minimal byte surfaces
cwd/path projection rules
```

### Phase F: granularity fitness audit

After the scout runs, a separate worker sees both sources:

```text
Source A: conceptual reconstruction tree and probe contract
Source B: blind public-surface scout ledger
```

The audit asks whether every scout-discovered public surface attaches cleanly to
a terminal concept leaf. The goal is not to patch probes. The goal is to decide
whether the conceptual tree has enough depth to generate correct behavior on
unseen siblings.

Required fitness outputs:

```text
scout_surface_to_concept_leaf_attachment_matrix
missing_depth_axis_ledger
anti_replay_gate_failure_analysis
gold_promotion_retrospective
meta_program_patch_recommendations
next_run_handoff
```

Allowed attachment statuses:

```text
attached_to_terminal_leaf
attached_to_parent_only_leaf_too_coarse
missing_leaf
contradicts_current_leaf
observed_example_only_no_generating_rule
public_surface_deferred_with_expected_risk
not_applicable_to_current_scope
```

Fitness rule:

```text
gold promotion is blocked for any high-risk public surface that is missing,
attached only to a coarse parent, contradicted by scout evidence, or observed
only as an example without a generating rule.
```

### Phase G: anti-replay generative-rule gate

Before implementation can be accepted as a gold attempt, each high-risk local
gold leaf must name the rule that generates its observed behavior.

Required rule evidence:

```text
rule_id
owned_leaf_refs
public_surface_refs
input_domain_or_value_class
parser_or_selection_or_projection_rule
expected_metamorphic_relations
reference_observation_examples
held_out_sibling_probe_refs
implementation_owner
replay_risk_posture
```

Anti-replay rule:

```text
byte equality over known fixtures is a regression gate, not a gold-readiness
gate. A leaf becomes anti_replay_ready only when a rule explains both observed
examples and held-out sibling or metamorphic probes.
```

Disallowed as sufficient implementation evidence:

```text
primary dispatch by exact probe id
primary dispatch by exact argv tuple
primary dispatch by exact fixture signature
embedding reference stdout/stderr/file bytes as the behavior source of truth
treating a generic fallback as sufficient while local probes hit replay cases
```

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
primary_kernel_operator
legacy_operator_alias
macro_gate_refs
scoped_readiness_status
scoped_ready_basis_refs
gold_readiness_status
gold_ready_basis_refs
gold_blocker_refs
missing_sibling_branches
missing_cross_products
fixture_realism_status
terminal_observation_status
public_surface_attachment_status
generative_rule_status
anti_replay_status
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
not_gold_ready_missing_public_surface_attachment
not_gold_ready_missing_generative_rule
not_gold_ready_replay_risk_open
explicitly_deferred_from_gold_with_expected_risk
not_gold_required
```

Rule:

```text
locked_by_reference_observation does not imply gold_ready.
scoped_ready does not imply gold_ready.
observed_example_only does not imply gold_ready.
gold_ready requires terminal observations or justified pass-through coverage for
the leaf's high-risk siblings, cross-products, fixture realism, projection
surface, public-surface attachment, generating rule, and anti-replay posture.
```

For high-risk surfaces, a gold-ready leaf must also name:

```text
representative_fixture_refs
negative_control_refs
mode_interaction_refs
renderer_or_projection_refs
side_effect_refs
exit_denominator_refs
public_surface_refs
generative_rule_refs
held_out_sibling_or_metamorphic_refs
```

#### Gate C9: configurable matcher-policy promotion gate

Trigger:

```text
Any control, schema field, file content pattern, route, selector, classifier,
filter, remapper, marker, regex-like value, string list, include/exclude value,
or user-supplied token can match a subject and then affect downstream behavior.
```

Required output:

```text
matcher_policy_ledger:
  matcher_node_ref
  matcher_kind
  default_matcher_sources
  custom_matcher_sources
  custom_source_posture
  matcher_composition_posture
  matcher_scope_posture
  matcher_comparison_posture
  matcher_value_shape_posture
  repeated_value_flag_posture
  match_window_or_field_scope
  parser_tokenization_rule
  negative_boundary_refs
  positive_transition_refs
  consumer_policy_refs
  projection_surface_refs
  unresolved_matcher_discriminators
  implementation_promotion_posture
```

Allowed `custom_source_posture` values:

```text
custom_replaces_defaults
custom_extends_defaults
custom_independent_mode
unknown_until_observed
not_applicable
```

Allowed `matcher_composition_posture` values:

```text
single_matcher
any_matcher_matches
all_matchers_required
ordered_first_match_wins
literal_full_value
unknown_until_observed
```

Allowed `matcher_scope_posture` values:

```text
whole_subject
bounded_prefix
selected_field
selected_line
selected_path_component
selected_metadata_field
unknown_until_observed
```

Allowed `matcher_comparison_posture` values:

```text
case_sensitive
case_insensitive
normalized_exact
regex_like
substring
unknown_until_observed
```

Allowed `matcher_value_shape_posture` values:

```text
separate_value_only
equals_value_supported
comma_list_supported
comma_list_with_space_normalized
repeated_flag_supported
quoted_or_escaped_value_required
unknown_until_observed
not_applicable
```

Allowed `repeated_value_flag_posture` values:

```text
repeated_flag_unions_values
repeated_flag_replaces_prior_values
repeated_flag_errors
unknown_until_observed
not_applicable
```

Rule:

```text
A positive matcher transition does not imply matcher grammar readiness.
```

Gold promotion is blocked unless the matcher ledger can answer:

```text
where matchers come from;
how default and custom matchers combine;
how multiple custom matchers compose;
which CLI/schema value shapes produce the matcher set;
what part of the subject is searched;
how matching compares text/values;
which downstream consumers receive the matched state.
```

Downstream consumers must be split when present:

```text
detection_truth
selection_or_denominator_truth
display_label_truth
structured_schema_truth
side_effect_route_truth
diagnostic_truth
exit_truth
```

Implementation handoff may include a matcher branch only at the level proven by
the ledger:

```text
basic_positive_transition_only:
  scoped handoff only; no broad matcher implementation claim.

matcher_policy_ready:
  implementation may encode the matcher source/composition/scope/comparison
  rule and named consumers.
```

If fixing one matcher consumer breaks another, the run must ascend to the
matcher policy parent before patching either consumer.

Examples of matcher-bearing surfaces include, without making task-specific
claims:

```text
generated markers
minified or generated detectors
include/exclude extension lists
regex path filters
remap/count-as rules
language shebang detectors
warning/error classifiers
route selectors
configuration keys
structured payload marker lines
```

#### Gate C10: diagnostic suggestion grammar gate

Trigger:

```text
A public control, flag, command, route, mode name, field name, or config key
can be misspelled or partially specified, and the program emits a corrective
suggestion rather than only an unknown-control error.
```

Required output:

```text
diagnostic_suggestion_ledger:
  diagnostic_node_ref
  unknown_token_source
  candidate_source_set
  candidate_namespace_posture
  similarity_metric_posture
  threshold_posture
  max_suggestion_count
  ratio_sort_posture
  tie_sort_posture
  short_vs_long_control_posture
  diagnostic_stream_posture
  diagnostic_authority_label
```

Allowed `diagnostic_authority_label` values:

```text
public_reference_observed
post_eval_compatibility_branch
conflict_public_reference_vs_official_eval
unknown_until_observed
```

Rule:

```text
Do not infer suggestion grammar from the existence of an unknown-control
error. Suggestions require their own projection grammar: source set, threshold,
cardinality, ratio ordering, tie ordering, and namespace boundary.
```

If the public reference does not suggest but official-eval rows require
suggestions, record that as a post-eval compatibility branch. Do not launder it
as public-reference behavior.

#### Gate C11: gold implementation handoff gate

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
all generative-rule ledgers complete for high-risk leaves
all held-out sibling / metamorphic anti-replay probes green
all side-effect byte probes green
all regression-retention probes green
all deferred risks still explicitly deferred
```

Official eval should only follow that gate. If official eval is run before that
gate, classify it as an experiment, not as a gold closeout.

#### Gate C12: probe ownership compression phase

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

For v6 program-reconstruction experiments, this gate is normally marked:

```text
probe_ownership_compression_status = deferred_future_feature
```

The active remedy for local-green / official-red mismatch is not compression.
It is public-surface scout, granularity fitness, and anti-replay rule evidence.

#### Gate C13: blind recon scout import

Trigger:

```text
The run has a conceptual reconstruction and a reference executable that may be
queried through legitimate public behavior.
```

Required output:

```text
blind_recon_scout_packet_ref
public_surface_command_log_ref
cli_grammar_harvest_ref
invalid_value_and_precedence_matrix_ref
output_mode_surface_ledger_ref
fixture_behavior_surface_ledger_ref
scout_gap_and_uncertainty_ledger_ref
scout_blindness_attestation
```

Rule:

```text
The scout must be produced independently from the conceptual tree. It must not
read prior reconstruction artifacts, implementation artifacts, source code,
hidden/evaluator tests, official eval failures, binary strings, symbols, or
decompiled material.
```

A gold promotion packet may not ignore scout-discovered public surfaces. Each
surface must be attached to a concept leaf, marked deferred with expected risk,
or recorded as a blocking missing depth axis.

#### Gate C14: granularity fitness attachment

Trigger:

```text
Both a conceptual reconstruction and a blind recon scout packet exist.
```

Required output:

```text
scout_surface_to_concept_leaf_attachment_matrix:
  scout_surface_ref
  public_behavior_axis
  attached_leaf_ref
  attachment_status
  missing_depth_axis_if_any
  gold_promotion_effect
  required_repair_action
```

Allowed `attachment_status` values:

```text
attached_to_terminal_leaf
attached_to_parent_only_leaf_too_coarse
missing_leaf
contradicts_current_leaf
observed_example_only_no_generating_rule
public_surface_deferred_with_expected_risk
not_applicable_to_current_scope
```

Rule:

```text
Gold promotion is blocked for high-risk surfaces whose status is
attached_to_parent_only_leaf_too_coarse, missing_leaf,
contradicts_current_leaf, or observed_example_only_no_generating_rule.
```

For CLI tasks, high-risk scout axes include at minimum:

```text
parser token-binding grammar
terminal missing-value grammar
unknown flag precedence
help/version/listing precedence
parse validation vs semantic invalid no-op/fallback
output route grammar
renderer dialect grammar
path projection grammar
classification / remap / filter denominator grammar
side-effect file behavior
exit denominator behavior
```

#### Gate C15: generative-rule readiness

Trigger:

```text
A terminal leaf is proposed for gold readiness and the leaf is parser,
selection, classification, aggregation, renderer, side-effect, error, or exit
sensitive.
```

Required output:

```text
generative_rule_ledger:
  rule_id
  owned_leaf_refs
  scout_surface_refs
  observed_probe_refs
  value_domain_or_fixture_family
  generating_rule_statement
  negative_or_boundary_controls
  sibling_variation_axes
  held_out_sibling_probe_refs
  metamorphic_relation_refs
  implementation_owner
  replay_risk_posture
```

Allowed `replay_risk_posture` values:

```text
anti_replay_ready
observed_example_only
fixture_signature_replay_risk
argv_replay_risk
byte_snapshot_only_risk
deferred_with_expected_risk
```

Rule:

```text
gold_ready requires replay_risk_posture = anti_replay_ready for high-risk
leaves, unless the leaf is explicitly_deferred_from_gold_with_expected_risk.
```

#### Gate C16: held-out sibling / metamorphic probe gate

Trigger:

```text
A gold implementation attempt is proposed after generative-rule readiness.
```

Required output:

```text
held_out_sibling_probe_manifest:
  probe_id
  hidden_from_implementation_construction
  owned_rule_ref
  sibling_axis
  metamorphic_relation
  expected_surface_from_rule
  comparison_surface
  authority
```

Rule:

```text
The implementation may see the rule and representative examples, but the gate
must retain at least one held-out sibling or metamorphic probe for each
high-risk rule family when feasible. Local gold byte probes remain regression
checks; held-out/metamorphic probes are the anti-replay check.
```

## 3. Kernel algebra and macro gates

The primitive operator set should be small and reusable. Existing row families
such as `field-effect`, `producer-schema`, `lifecycle`, `renderer`,
`matcher-policy`, `mode-interaction`, `resource-contract`, and
`source-postmortem` are derived views or mandatory macro gates emitted when the
kernel is applied to particular node types.

The v8 kernel is:

```text
K1 Factor
  Create entities, boundaries, parts, subresources, records, fields, controls.

K2 Partition
  Split by value, type, presence, grammar, validity, emptiness, conflict,
  negative state, and error state.

K3 Bind
  Split by role, consumer, subject owner, selected row, aggregate denominator,
  hidden denominator, side-effect owner, and exit denominator.

K4 Transform
  Split by semantic computation: reducers, counters, formula engines, lookup
  semantics, layout algorithms, classifier-to-metric transitions, estimator
  models, normalization, and state-to-truth functions.

K5 Sequence
  Split by lifecycle, initialization, mutation, ordering, timing, before/after
  state, late errors, and side-effect sequencing.

K6 Expose
  Split by observable surface: stdout, stderr, file, renderer dialect, byte
  grammar, stream, side effect, final newline, route, protocol response, and
  exit surface.

K7 Compose
  Split when two branches share a surface, state, resource, denominator,
  lifecycle stage, parser context, identity, or route and may not commute.

M0 Warrant
  Attach evidence authority, readiness, deferral, conflict, postmortem status,
  anti-replay posture, and promotion limits to every node, edge, probe,
  observation, and implementation claim.
```

`M0 Warrant` is not an ordinary behavior-splitting operator. It is a modal
annotation layer over the tree. A behavior can be deeply factored and still be
non-authoritative if its warrant is post-eval, source-postmortem, conflict-only,
or scoped rather than gold.

### Derived macro gates

The current specialized gates remain required. They are now classified as
macros generated from the kernel:

```text
MATCHER
  = K2 value grammar
  + K3 subject / scope / consumer
  + K7 default/custom/repeated/list composition
  + K6 diagnostic/display/schema/exit consumers
  + M0 evidence and promotion boundary

RESOURCE_CONTRACT
  = K1 resource inventory
  + K2 resource grammar and missing/malformed states
  + K4 resource lookup/use semantics
  + K6 resource-owned projection/error behavior
  + M0 cardinality and authority

PROTOCOL_GRAMMAR
  = K1 tokens/records/messages
  + K2 accepted/missing/invalid/wrong-type values
  + K5 parse/validate/reduce order
  + K6 parser errors and precedence

PROJECTION_GRAMMAR
  = K3 row universe and denominator
  + K6 headers/body/separators/style/wrapping/stream/file/exit
  + K7 mode and identity/order interactions

FORMULA_MODEL
  = K3 variables and presets
  + K4 formula/rounding/thresholds
  + K2 fallback/override/invalid states
  + K6 renderer-specific fields

INITIALIZATION_DEFAULTS
  = K1 startup inputs/config/env/resources
  + K5 initialization and overlay order
  + K7 env/config/argv/cwd/resource precedence
  + K6 help/version/no-args/error exposure

FIXTURE_REALISM
  = K1 producer-shaped fixture families
  + K2 realistic value morphology
  + K3 producer/consumer ownership
  + K7 synthetic-vs-real interaction risks
  + M0 anti-replay posture

SOURCE_POSTMORTEM_DISCOVERY
  = M0 postmortem_source_derived authority
  + K1/K4/K6/K7 missing operator discovery
  + next clean-run macro trigger
```

The older `OP-*` names remain below as compatibility labels for existing
artifacts. In v8 they are not the primary algebra.

```text
OP-B + OP-D          -> K1 Factor
OP-L + parts of OP-F -> K2 Partition
OP-R + OP-S          -> K3 Bind
new Transform rows   -> K4 Transform
OP-T                 -> K5 Sequence
OP-P                 -> K6 Expose
OP-C                 -> K7 Compose
OP-E                 -> M0 Warrant
OP-M                 -> MATCHER macro
```

### K4: Transform / semantic computation

Transform is the main new primitive in v8. It asks:

```text
What semantic function maps input, resource, control state, or substrate state
into computed truth before projection?
```

Required Transform questions:

```text
What is the reducer/counter/formula/layout/classifier function?

What are its input variables, hidden state, resource lookups, defaults,
fallbacks, and override controls?

Which outputs are semantic truth, and which are only later display labels?

Does the transform use integer division, float rounding, thresholds, locale,
width, time, or dependency-owned semantics?

Can two renderers expose the same transform differently?

Can a filter hide a row before a transform would otherwise panic, count, or
produce an estimate?
```

Examples from prior runs:

```text
FIGlet:
  glyph layout and smushing are K4 transforms, not renderer byte details.

go-mod-outdated:
  replacement-aware CurrentVersion/NewVersion/HasUpdate/InvalidTimestamp
  helpers are K4 transforms over module state.

tparse:
  event stream reducers, package/test status reducers, and exit-denominator
  reducers are K4 transforms before renderer exposure.

scc:
  language counting, complexity counting, generated/minified classification,
  COCOMO, and LOCOMO are K4 transforms.
```

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

### OP-M: Matcher / classifier policy split

v8 status: `OP-M` is retained as the `MATCHER` macro, not as a primitive
kernel operator. It is still mandatory for matcher-bearing controls because it
prevents a single positive matcher example from being over-promoted into a full
source/composition/scope/comparison/consumer contract.

Question:

```text
Does this node match subjects by user-supplied values, default values, content
markers, path patterns, schema markers, remap rules, filters, or classifier
tokens; and if so, what is the matcher source, composition, scope, comparison,
and downstream consumer policy?
```

Typical child nodes:

```text
default matcher source
custom matcher source
custom replaces defaults
custom extends defaults
single matcher
multiple matchers
any-match composition
literal full-value composition
separate-value form
equals-value form
comma-list form
comma-space normalization
repeated flag union
repeated flag replacement
bounded-prefix search
whole-subject search
selected-field search
case-sensitive comparison
case-insensitive comparison
detection truth
denominator truth
display label truth
schema projection truth
```

SCC-style example:

```text
A generated-marker control is not one boolean. It splits into default marker
set, custom marker set, default/custom replacement policy, multiple-marker
composition, first-N-byte scan scope, case-folding, generated detection,
--no-gen exclusion, and --gen display/projection consumers.
```

Required OP-M future-discriminator field:

```text
future_matcher_policy_discriminator_if_conflict
```

For every matcher-bearing branch, the generator must state which parent
matcher discriminator it would test if a later patch fixes one consumer and
breaks another. Typical discriminator classes:

```text
matcher_source_default_vs_custom
matcher_composition_single_vs_many
matcher_value_shape_separate_vs_equals
matcher_value_shape_comma_trimmed_vs_literal
repeated_flag_union_vs_replacement
matcher_scope_whole_vs_bounded
matcher_comparison_case_sensitive_vs_folded
detection_truth_vs_display_truth
denominator_truth_vs_projection_truth
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

v8 status: `OP-E` is retained as `M0 Warrant`, a modal annotation layer over
every node, edge, probe, observation, implementation claim, and postmortem
finding. It is not a peer behavior-splitting operator.

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
4. For each node, apply the v8 kernel:
   K1 Factor, K2 Partition, K3 Bind, K4 Transform, K5 Sequence,
   K6 Expose, K7 Compose, and M0 Warrant.
5. Trigger mandatory macros when node shape or public surface requires them:
   MATCHER, RESOURCE_CONTRACT, PROTOCOL_GRAMMAR, PROJECTION_GRAMMAR,
   FORMULA_MODEL, INITIALIZATION_DEFAULTS, FIXTURE_REALISM, and
   SOURCE_POSTMORTEM_DISCOVERY.
6. If an operation yields observably distinct children, attach them under the node.
7. Recurse into each child.
8. Create cross-node K7 interaction candidates only when children share a
   surface, subject, lifecycle stage, resource, identity, route, parser context,
   formula input, side-effect owner, or denominator.
9. Stop a branch only when every applicable operation is exhausted, explicitly deferred, or proven pass-through.
10. Run terminalization: split any leaf whose siblings could change bytes, files,
   ordering, denominator, or exit while preserving the same high-level primitive.
11. Run blind public-surface recon scout when a reference executable is
    available. The scout is independent from the conceptual tree.
12. Run granularity fitness: attach every scout-discovered public surface to a
    terminal leaf or mark the missing/coarse/contradictory depth axis.
13. Repair the concept tree and probe plan for any high-risk scout surface that
    lacks terminal attachment or generating-rule evidence.
14. Run coverage adequacy: mark synthetic-only, representative-only, and
   fixture-morphology gaps before probe closure.
15. Assign orthogonal readiness states to every terminal leaf:
    ontology_status, probe_status, scope_status, implementation_status, and
    gold_status.
16. Promote scoped-ready leaves to gold-ready only when sibling coverage,
    cross-products, fixture realism, projection exactness, public-surface
    attachment, generating-rule evidence, side effects, and exit denominators
    are closed or explicitly deferred.
17. Emit probes from terminal branch obligations, not from an edge-case list;
    after observation, every probe must name `locked_discriminator_ref`.
18. Before gold implementation, require generative-rule ledgers and held-out
    sibling or metamorphic anti-replay probes for high-risk behavior families.
19. If probe count is high after gold coverage exists and the user explicitly
    requests it, run probe ownership compression without collapsing distinct
    behavior leaves. Otherwise record compression as `deferred_future_feature`.
20. Attach every observation, official failure, and implementation repair back to the smallest responsible node.
```

A practical scheduling order:

```text
K1 Factor first, so identities and parts are clear.
K2 Partition next, so value/state/grammar alternatives are explicit.
K3 Bind before projection, so one field with multiple consumers is not lumped.
K4 Transform before projection, so semantic computation is not mistaken for
byte formatting.
K5 Sequence before interaction, so initialization, mutation, and lifecycle
ordering are explicit.
K6 Expose after the semantic substrate is known, so stdout/stderr/file/API/exit
surfaces are tied to their owners.
K7 Compose after local branches exist, so non-commutation is tested deliberately.
M0 Warrant at every step.

Derived macros can run as soon as their trigger appears, but must still emit
kernel-backed child rows rather than opaque checklist items.
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
kernel_operator_that_created_node: K3
legacy_operator_alias_that_created_node: OP-R
macro_gate_that_created_node: MATCHER | RESOURCE_CONTRACT | PROTOCOL_GRAMMAR | PROJECTION_GRAMMAR | FORMULA_MODEL | INITIALIZATION_DEFAULTS | FIXTURE_REALISM | SOURCE_POSTMORTEM_DISCOVERY | null
applied_kernel:
  K1_Factor: exhausted | produced_children | not_applicable | deferred
  K2_Partition: exhausted | produced_children | not_applicable | deferred
  K3_Bind: exhausted | produced_children | not_applicable | deferred
  K4_Transform: exhausted | produced_children | not_applicable | deferred
  K5_Sequence: exhausted | produced_children | not_applicable | deferred
  K6_Expose: exhausted | produced_children | not_applicable | deferred
  K7_Compose: open | exhausted | produced_children | not_applicable | deferred
  M0_Warrant: current_status
applied_legacy_operators:
  OP-B: exhausted | produced_children | not_applicable | deferred
  OP-D: exhausted | produced_children | not_applicable | deferred
  OP-R: exhausted | produced_children | not_applicable | deferred
  OP-L: open | exhausted | produced_children | not_applicable | deferred
  OP-M: open | exhausted | produced_children | not_applicable | deferred
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
gold_readiness_status: gold_ready | not_gold_ready_missing_sibling_branches | not_gold_ready_missing_cross_products | not_gold_ready_synthetic_only | not_gold_ready_unresolved_conflict | not_gold_ready_projection_exactness_open | not_gold_ready_fixture_realism_open | not_gold_ready_missing_public_surface_attachment | not_gold_ready_missing_generative_rule | not_gold_ready_replay_risk_open | explicitly_deferred_from_gold_with_expected_risk | not_gold_required
ontology_status: candidate | terminal_candidate | terminal_locked | pass_through | deferred | conflict_isolated
probe_status: no_probe_needed | probe_needed | probe_planned | probe_ready | observed_locked | probe_blocked | conflict_probe_needed
scope_status: not_scoped_ready | scoped_ready | scoped_blocked_pending_observation | scoped_blocked_by_conflict | scoped_deferred
implementation_status: not_ready | scoped_implementation_ready | gold_implementation_ready | blocked_by_projection_gap | blocked_by_replay_risk | blocked_by_conflict
gold_status: not_gold_required | not_gold_ready_missing_sibling | not_gold_ready_missing_cross_product | not_gold_ready_synthetic_only | not_gold_ready_projection_open | not_gold_ready_missing_public_surface | not_gold_ready_missing_generative_rule | not_gold_ready_replay_risk_open | gold_ready | explicitly_deferred_from_gold_with_expected_risk
gold_blocker_refs: []
missing_sibling_branches: []
missing_cross_products: []
fixture_realism_status: realistic_enough | synthetic_only | mixed_but_incomplete | not_applicable
terminal_observation_status: reference_observed | visible_spec_locked | pass_through_proven | pending_observation | deferred
public_surface_attachment_status: attached_to_terminal_leaf | attached_to_parent_only_leaf_too_coarse | missing_leaf | contradicts_current_leaf | observed_example_only_no_generating_rule | public_surface_deferred_with_expected_risk | not_applicable_to_current_scope
generative_rule_status: rule_ready | observed_example_only | missing_rule | contradicted_by_public_surface | deferred_with_expected_risk | not_applicable
anti_replay_status: anti_replay_ready | held_out_sibling_missing | metamorphic_relation_missing | fixture_signature_replay_risk | argv_replay_risk | byte_snapshot_only_risk | deferred_with_expected_risk | not_applicable
implementation_handoff_status: blocked | scoped_handoff_allowed | gold_handoff_allowed | not_applicable
matcher_policy_status: matcher_policy_ready | basic_positive_transition_only | unknown_until_observed | not_applicable
matcher_policy_refs: []
probe_refs: []
implementation_owner: renderer | parser | reducer | side_effect | cli | exit | unknown
```

This schema is intentionally tree-first. Existing table rows are projections of this tree:

```text
field-effect inventory       = K3 Bind applied to structured fields
producer-schema expansion    = PROTOCOL_GRAMMAR over K1/K2/K5/K6
field-presence lattice       = K2 Partition applied to field or option nodes
matcher-policy ledger        = MATCHER macro
lifecycle-stage table        = K5 Sequence applied to record/state/mode nodes
transform ledger             = K4 Transform over reducers/counters/formulas/layout
aggregate-denominator table  = K3 Bind applied to summary/exit/status nodes
renderer-compatibility table = PROJECTION_GRAMMAR over K3/K6/K7
runtime-surface table        = K6 Expose + M0 Warrant over runtime/dependency nodes
mode-interaction table       = K7 Compose applied to mode/control nodes
resource-contract table      = RESOURCE_CONTRACT macro
D-ledger rows                = terminal behavior leaves with warrant/probe status
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
it is matcher-bearing and lacks matcher source, composition, scope,
  comparison, and consumer policy.
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
it has public scout surfaces attached only to coarse parents;
it has reference-observed examples but no generating rule for a high-risk leaf;
it can be satisfied by exact fixture/argv replay;
it has no held-out sibling or metamorphic check for a high-risk parser,
  selection, renderer, side-effect, error, or exit rule.
it has a configurable matcher with only one positive transition and no
  opposite-boundary sibling.
it lets matcher detection, denominator policy, display label, and structured
  projection share one unsplit leaf.
```

A scaffold must not stop as `gold_ready` when:

```text
any gold-required terminal leaf is only scoped_ready;
any high-density open discriminator is carried only as narrative risk;
any renderer, control-plane, side-effect, sort/order, identity, fixture
  morphology, or exit-denominator surface lacks terminal observations or
  explicit gold deferral;
the local gold fixture set has not been defined;
the blind scout has not been run or explicitly deferred with expected risk;
the granularity fitness audit has unresolved high-risk missing depth axes;
any high-risk leaf lacks generative-rule evidence;
the anti-replay gate has not been satisfied;
the implementation handoff does not say whether it is scoped or gold.
```

## 7. Probe grouping from the tree

A probe is a witness for a branch distinction. Probe grouping should mirror the tree.

Each probe row should name:

```text
probe_id
primary_node_path
kernel_operator_witnessed
legacy_operator_alias
macro_gate_witnessed
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
public_surface_refs
generative_rule_ref
sibling_axis
metamorphic_relation_ref
hidden_from_implementation_construction
anti_replay_role
coverage_strength
compression_candidate_status
```

### Probe family types

```text
local discriminator probe
  Separates sibling branches created by one kernel operator or macro gate.

presence/type lattice probe
  Covers K2 Partition children such as absent/null/empty/wrong-type/default.

lifecycle-order probe
  Covers K5 Sequence ordering such as side effect before late parser error.

subject/denominator probe
  Covers K3 Bind hidden-row, selected-row, aggregate, or exit denominators.

projection byte probe
  Covers K6 Expose renderer or serialization grammar, often through the
  PROJECTION_GRAMMAR macro.

failure-precedence probe
  Covers K2 Partition plus K5 Sequence failure ordering and process-surface
  priority.

interaction probe
  Covers K7 Compose non-commutation between two paths.

matcher-policy probe
  Covers MATCHER macro source, composition, scope, comparison, or
  downstream-consumer distinctions for a matcher-bearing control or classifier.

realistic morphology probe
  Covers a projection subtree over external producer-shaped fixtures rather than synthetic minimal rows.

held-out sibling probe
  Covers a high-risk rule branch that implementation did not see as a fixed
  byte oracle during construction.

metamorphic relation probe
  Covers a rule invariant such as adding one code line, changing an extension,
  routing the same dialect to a file, or moving a flag value across argv
  positions.
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
make the held-out sibling and metamorphic anti-replay gate green for high-risk
generative rules.
```

The implementation handoff must also state:

```text
fixture_oracle_replay_forbidden_as_primary_strategy = true
exact_argv_dispatch_forbidden_as_primary_strategy = true
exact_fixture_signature_dispatch_forbidden_as_primary_strategy = true
reference_byte_embedding_forbidden_as_behavior_source = true
```

Reference bytes can remain test oracles. They cannot become the implementation's
primary behavior mechanism.

Each terminal behavior leaf gets a coverage record:

```yaml
behavior_leaf: N-...
primary_kernel_operator: K6
legacy_operator_alias: OP-P
macro_gate_refs: [PROJECTION_GRAMMAR]
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
generative_rule_refs: [GR-...]
anti_replay_probe_refs: [AR-...]
replay_risk_posture: anti_replay_ready
```

The implementation does not need one function per node. It needs explicit ownership by semantic layer:

```text
K1 Factor on input/record/resource parts          -> parser shape and data model
K2 Partition on value/error/state classes         -> parser and validator
K3 Bind on roles, subjects, consumers, denominators -> classifier, selector, aggregator, exit resolver
K4 Transform on semantic computation              -> reducers, counters, formula engines, normalizers
K5 Sequence on records/actions/mutations          -> lifecycle reducer and precedence handling
K6 Expose on external surfaces                    -> renderers, serializers, side-effect writers
K7 Compose on shared modes/resources/surfaces     -> mode orchestration and non-commutation handling
M0 Warrant                                        -> probe/oracle/evidence ledger, not production behavior
MATCHER macro                                    -> matcher source, composition, scope, comparison, and consumers
```

This gives the repair loop a principled routing rule:

```text
If a failure maps to a K6 leaf, repair renderer/projection/exposure first.
If it maps to K3, repair subject selection, role binding, or denominator logic first.
If it maps to K4, repair the semantic transform before touching projection.
If it maps to K5, repair reducer ordering/lifecycle first.
If it maps to K2, repair the value/error/state partition first.
If it maps to MATCHER, repair matcher policy before touching matcher consumers.
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

## 10. Bookkeeper v6 audit shape

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
Were blind scout surfaces attached to terminal leaves rather than coarse parent
nodes?
Does each high-risk gold leaf have a generating rule and anti-replay posture?
Do held-out sibling or metamorphic probes exist for high-risk rule families?
Is any scoped-ready leaf being passed downstream as gold-ready without closing
or explicitly deferring its siblings, cross-products, fixture realism, and
projection/exit surfaces?
If probe compression occurred, did it preserve all distinct gold-required
behavior leaves?
For matcher-bearing controls, did the generator split matcher source,
composition, scope, comparison, and downstream consumers before promotion?
Was any positive matcher transition promoted as broad matcher grammar?
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
blind_scout_missing_or_not_blind
scout_surface_unattached
scout_surface_attached_to_parent_only
observed_example_promoted_to_generating_rule
generative_rule_missing_for_high_risk_leaf
held_out_sibling_probe_missing
metamorphic_relation_missing
fixture_oracle_replay_not_blocked
probe_compression_collapsed_distinct_leaf
matcher_policy_missing
positive_matcher_transition_overpromoted
matcher_consumers_collapsed
matcher_boundary_sibling_missing
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
  -> if scout surface attaches only to a parent: granularity fitness failure
  -> if local probes were replayable: anti-replay gate failure
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

## 12. How this changes the earlier v2 documents

The earlier v2 generator/bookkeeper can be refactored without discarding its useful content.

### Replace “required indication artifacts” with “kernel-triggered derived views”

```text
Current artifact                         New source
field-effect inventory                   K3 Bind on structured fields
producer-schema expansion                PROTOCOL_GRAMMAR over K1/K2/K5/K6 plus M0
high-risk field de-lumping               K3 Bind when a field has multiple consumers
field-presence lattice                   K2 Partition on any behavior-bearing node
transform / formula ledger               K4 Transform on counters, reducers, formulas, layouts
lifecycle-stage table                    K5 Sequence on records, actions, modes, effects
aggregate-denominator table              K3 Bind on summary/status/exit nodes
renderer-compatibility table             PROJECTION_GRAMMAR over K3/K6/K7
runtime-surface table                    K2/K5/K6 plus M0 on runtime/dependency nodes
help/control-plane table                 PROTOCOL_GRAMMAR + PROJECTION_GRAMMAR on CLI controls
version/executable table                 K1 Factor + K6 Expose on identity/runtime surfaces
golden-fixture morphology mesh           FIXTURE_REALISM over K1/K2/K3/K7 plus M0
mode-interaction closure                 K7 Compose on control/mode nodes sharing surfaces
conflict-isolation table                 M0 Warrant on contradictory observations
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
- if any control, classifier, marker, remapper, filter, regex, path matcher,
  list value, schema marker, or user-supplied token matches subjects, emit a
  matcher_policy_ledger for source/composition/scope/comparison/consumer
  posture. A positive matcher transition is not sufficient for promotion.
- for high-risk K7 Compose rows, include future_discriminator_if_conflict.
- after conceptual reconstruction, run or import a blind public-surface recon
  scout packet, unless no reference executable is available or the scout is
  explicitly deferred with expected risk.
- run granularity fitness: attach scout surfaces to terminal leaves, and mark
  missing/coarse/contradictory surfaces as blockers.
- for high-risk leaves, emit generative_rule_ledger rows; observed fixture
  examples are not enough.
- before gold implementation, emit held-out sibling or metamorphic anti-replay
  probes for high-risk rule families where feasible.
- for every terminal leaf, emit both scoped_readiness_status and
  gold_readiness_status. Never treat scoped_ready as gold_ready by default.
- before implementation handoff, emit gold_readiness_summary and declare the
  handoff type: scoped_implementation_attempt or gold_implementation_attempt.
- only after gold-required leaves are explicit, optionally emit a probe
  ownership compression table if requested. In the default v6 run, mark probe
  compression as `deferred_future_feature`. Do not compress probes that witness
  distinct sibling branches, output roles, side-effect destinations, exit
  denominators, renderer byte grammars, fixture-realism tiers, or authority
  layers.
- if observations have already been collected, convert them into locked
  obligations before adding implementation guidance:
  - help observations become observed_help_control_instantiation rows;
  - producer schema observations become observed_schema_fixture_synthesis rows;
  - discovered renderer/projection modes become
    renderer_dialect_projection_expansion rows;
  - every post-observation probe receives locked_discriminator_ref.

Then recursively apply the v8 kernel algebra to every ontology node:
K1 Factor, K2 Partition, K3 Bind, K4 Transform, K5 Sequence, K6 Expose,
K7 Compose, with M0 Warrant at every step.

Legacy OP aliases may be recorded for continuity with earlier artifacts, but
they are not the active primitive calculus in v8. Use derived macro gates when
their triggers appear: MATCHER, RESOURCE_CONTRACT, PROTOCOL_GRAMMAR,
PROJECTION_GRAMMAR, FORMULA_MODEL, INITIALIZATION_DEFAULTS, FIXTURE_REALISM,
and SOURCE_POSTMORTEM_DISCOVERY.

For every operation:
- state why it applies or why it is not applicable;
- create children when observably distinct behavior can result;
- recurse into children;
- attach evidence authority;
- stop only with locked, probed, pass-through, deferred, or conflict-isolated status.

Finally emit:
1. recursive ontology tree;
2. kernel application ledger with legacy OP aliases where useful;
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
15. matcher policy ledger, if matcher-bearing surfaces exist;
16. discriminator-locked probe ledger, if observations exist;
17. blind recon scout packet refs and scout-surface attachment matrix;
18. missing depth axis ledger;
19. generative rule ledger;
20. held-out sibling / metamorphic anti-replay probe manifest;
21. gold readiness summary;
22. probe ownership compression table, only if compression is requested after
    gold-required leaves are explicit;
23. open risks and bookkeeper questions.
```

## 14. Minimal bookkeeper prompt skeleton

```text
You are the adversarial recursive ontology bookkeeper.

Audit the generator tree, not just the final obligations.

For every node:
- verify every applicable kernel operator and triggered macro gate was applied,
  declared not applicable, or deferred;
- verify every kernel/macro-produced child has terminal status;
- verify every behavior-bearing leaf has a probe, observation lock, or explicit deferral;
- verify every probe witnesses a specific kernel/macro split and sibling distinction;
- verify every non-commuting shared-surface interaction has a K7 Compose row;
- reject candidate-to-truth overpromotion;
- reject post-eval pressure laundered into first-pass theory.
- reject scoped-ready leaves promoted to gold-ready without sufficient sibling,
  cross-product, fixture-realism, projection, side-effect, and exit closure;
- reject gold-ready claims where a high-risk scout-discovered public surface is
  missing, attached only to a parent, contradicted, or observed only as an
  example without a generating rule;
- reject implementation handoff when high-risk leaves lack held-out sibling or
  metamorphic anti-replay probes;
- reject fixture/argv/byte replay as the primary implementation evidence;
- reject matcher-bearing branches promoted without source/composition/scope/
  comparison/consumer posture and negative-boundary siblings;
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

## 17. v5 lesson from `scc`: public scout and anti-replay gate

The `scc` experiment exposed a different failure mode from the `tparse` scoped
readiness problem:

```text
272 / 272 local reference probes green
  !=
general implementation of the program
```

The local gate was correct as a regression gate, but it was not an
anti-replay gate. A candidate can satisfy any finite fixture/argv byte contract
if it can identify the fixture and argv and replay the observed bytes.

The missing depth axes were:

```text
parser token-binding grammar
terminal missing-value grammar
unknown/help/version precedence
parse validation vs semantic invalid no-op/fallback
output route grammar
renderer dialect grammar
per-file path projection grammar
language classification / remap / filter denominator grammar
generated/minified/large threshold grammar
runtime values that alter semantic output
generative implementation evidence
```

The v5 process therefore adds:

```text
conceptual reconstruction
  -> blind public-surface scout
  -> granularity fitness audit
  -> missing depth-axis repair
  -> generative-rule ledger
  -> held-out sibling / metamorphic anti-replay gate
  -> implementation
  -> local byte regression gate
  -> official eval
```

The scout and conceptual tree must be independent until the fitness phase:

```text
conceptual worker:
  reads visible spec and builds the theory tree;

scout worker:
  reads only public executable behavior and logs exposed syntax, modes,
  errors, side effects, and minimal fixture behavior;

fitness worker:
  attaches scout surfaces to concept leaves and blocks gold promotion where
  the attachment is missing, too coarse, contradictory, or example-only.
```

## 18. v6 lesson from `scc`: matcher-policy gate

The Phase57 -> Phase59 SCC marker regression exposed a narrower failure mode:

```text
one positive matcher transition
  !=
matcher grammar known
```

The reconstructed SCC tree correctly discovered generated-file inclusion,
`--no-gen`, `--gen` display, and custom marker influence. The failure was
promotion depth: one custom-marker example was treated as enough to implement
custom marker behavior broadly.

The missing discriminator family was:

```text
matcher source:
  default marker set vs custom marker set

matcher composition:
  single marker vs many markers

matcher scope:
  whole file vs bounded prefix / selected field

matcher comparison:
  case-sensitive vs case-folded / normalized

matcher consumers:
  detection vs denominator exclusion vs display label vs structured projection
```

The v6 historical rule was:

```text
When a branch uses a configurable matcher, require OP-M before OP-S/OP-P
promotion. Do not let a matcher observation become an implementation
obligation until source, composition, scope, comparison, and consumers are
observed or explicitly deferred.
```

The v8 active form is:

```text
When a branch uses a configurable matcher, trigger the MATCHER macro before
K3 Bind, K4 Transform, or K6 Expose consumers are promoted. Do not let a
matcher observation become an implementation obligation until source,
composition, scope, comparison, and consumers are observed or explicitly
deferred.
```

Counterfactual probes must include both positive and opposite-boundary siblings:

```text
matching custom marker
nonmatching custom marker
multiple custom markers with one match
multiple custom markers with two positive matches
comma-list with and without spaces
equals-value marker form
repeated marker flags with two positive markers
default marker while custom marker is supplied
marker within scan scope
marker outside scan scope
case variant marker
same detection under exclusion and display/projection consumers
```

This rule generalizes beyond generated markers to include/exclude lists, regex
filters, remap rules, path matchers, shebang or language classifiers, route
selectors, diagnostic classifiers, schema marker lines, and configuration keys.

A public executable surface is not just a probe target. It is a grammar source.
For CLI programs, public help/error behavior can expose:

```text
whether list-like values can be supplied as --flag value or --flag=value;
whether comma-separated values trim spaces;
whether repeated flags union or replace previous values;
whether the same value-shape rule is shared by marker, remap, include/exclude,
or other matcher-bearing controls.
```

```text
flag value classes
aliases
enum hints
greedy value binding
terminal missing-value behavior
parse-time failure
semantic invalid fallback
stdout/stderr/exit precedence
output route syntax
side-effect file semantics
```

Gold promotion must not mark such surfaces as closed by byte snapshots alone.
It must ask:

```text
What rule generated this output?
What unseen sibling would distinguish rule implementation from replay?
What metamorphic relation should still hold if the fixture changes?
```

For example, a fixture-observed row:

```text
--sort name ./fixture
```

does not close parser behavior unless the tree also represents:

```text
--sort consumes the next token as a value;
`name` is not a positional path;
invalid sort values may fall back rather than fail;
unknown flags fail at parse time;
help/version/listing modes have their own precedence.
```

The same applies to renderers. A table snapshot is not a renderer grammar.
Gold readiness for byte projections requires a rule for:

```text
row membership
ordering
column set
cell value generation
alignment / width / truncation
footer presence
stdout/stderr/file destination
final newline
```

The new readiness distinction is:

```text
observed_example_only:
  reference bytes exist but no general rule is proven.

rule_ready:
  a generating rule is documented and attached to the tree.

anti_replay_ready:
  the rule passes held-out sibling or metamorphic probes.
```

Only `anti_replay_ready`, or explicit gold deferral with expected risk, can
support a gold implementation handoff for high-risk surfaces.

## 19. v6 lesson from `scc`: shared-extension classifier gate

The `scc` remap repair exposed a distinct classifier failure class:

```text
one extension
  -> multiple possible languages
  -> content discriminator
  -> per-language counting/comment/complexity consumer
  -> mixed-directory aggregation/projection consumer
```

The meta-program must not treat extension maps as flat dictionaries. For every
extension, filename, shebang, marker, or metadata field that can map to more
than one subject class, add a shared-surface classifier row:

```text
shared_classifier_ledger:
  classifier_node_ref
  shared_surface_kind
  shared_surface_token
  candidate_subject_classes
  content_discriminator_refs
  discriminator_search_scope
  fallback_subject_class
  per_subject_counting_consumer_refs
  per_subject_projection_consumer_refs
  mixed_subject_aggregation_probe_refs
  reference_observation_posture
  official_post_eval_conflict_posture
  unresolved_classifier_consumer_refs
```

Required discriminator probes:

```text
one fixture per candidate subject class
one mixed fixture containing all candidate classes
one negative fixture for a near-sibling grammar where feasible
one consumer probe per language-specific counting/comment/complexity rule
one projection probe for aggregate ordering and display names
```

Required promotion rule:

```text
classification_ready does not imply consumer_ready.
```

A branch can be:

```text
classifier_ready:
  the subject class is selected correctly.

consumer_ready:
  the selected subject class also has correct line, comment, complexity, cost,
  harvest, and projection behavior.

post_eval_compatibility_only:
  a public reference probe and official fixture disagree, so the row is carried
  as post-eval compatibility evidence rather than clean public-reference truth.
```

Counterfactual question to ask during reconstruction:

```text
If this identifier is normally a lookup key, can it instead be an ambiguous
surface whose true subject is selected by content, marker, shebang, path role,
or producer grammar?
```

This generalizes beyond file extensions to include:

```text
shared filenames
shared MIME-like markers
shebang plus remap conflicts
schema version markers
diagnostic prefixes
output route labels
language aliases
```

## 20. v6 lesson from `scc`: filter identity-normalization gate

Filtering should not be modeled as a final predicate over already-correct
subjects until the subject identity pipeline is locked. The `scc` filtering
repair showed this parent chain:

```text
raw path / file metadata / control value
  -> identity normalization
  -> default membership set
  -> custom override or union policy
  -> filter predicate
  -> aggregation denominator
```

For every filter, add an identity-normalization row before probe promotion:

```text
filter_identity_ledger:
  filter_node_ref
  subject_identity_source_refs
  extension_identity_posture
  shebang_identity_posture
  filename_identity_posture
  path_normalization_posture
  default_set_refs
  custom_set_value_shape_refs
  default_custom_composition_posture
  predicate_application_stage
  denominator_consumer_refs
  unresolved_identity_filter_refs
```

Allowed `default_custom_composition_posture` examples:

```text
custom_replaces_default
custom_unions_with_default
custom_intersects_default
custom_disabled_default_only
no_default_set
```

Required counterfactual questions:

```text
Does the filter act on extension identity, shebang identity, filename identity,
path identity, language identity, or rendered label?

Does a custom flag add to the default set, replace it, or disable it?

Are path controls normalized for trailing slashes, leading dots, casing,
relative roots, or symlink spelling before comparison?

Can two identity sources disagree, such as `.sh` extension vs bash shebang, and
which one wins for classification versus filtering?
```

Promotion rule:

```text
A filter is not gold-ready if its subject identity source is only assumed.
```

## 21. v6 lesson from `scc`: language-map and counting-consumer gate

Language classification has at least three layers:

```text
identity source:
  extension map / filename / shebang / public language list / content marker

classifier precedence:
  shared-extension content classifier vs flat extension lookup

counting consumer:
  comment grammar / blank grammar / code grammar / complexity grammar /
  generated-minified display grammar / renderer truncation grammar
```

A public language list is admissible evidence for extension identity, but not
for counting consumers. The meta-program must emit a separate ledger:

```text
language_counting_consumer_ledger:
  language_ref
  identity_source_refs
  classifier_precedence_refs
  comment_grammar_refs
  block_comment_state_refs
  blank_line_policy_ref
  code_line_policy_ref
  complexity_token_refs
  minified_consumer_refs
  generated_consumer_refs
  renderer_display_refs
  unresolved_consumer_refs
```

Required precedence rule:

```text
specific content classifiers and explicit remap/count-as rules run before
generic language-map fallback.
```

Required non-promotion rule:

```text
extension identity ready != counting consumer ready.
```

Counterfactual questions:

```text
Does this file extension name one language, or is it a shared surface?

If a public language list says an extension belongs to a language, is that a
fallback rule or does a more specific content/shebang/remap rule override it?

For each newly classified language, do we know how comments, blanks, code,
complexity, generated/minified markers, and display labels are counted?
```

## 22. v7 lesson from `scc`: source-postmortem operator discovery gate

When a run is locally green but remains materially official-red, do not keep
grinding the same probe universe indefinitely. At that point the local probes
may only be proving conformance to a deficient theory. The meta-program should
allow a labeled source-postmortem phase whose goal is not to patch the candidate,
but to discover which generic operators the reconstruction failed to instantiate.

Authority rule:

```text
source-postmortem findings are postmortem_source_derived;
they may repair the meta-program and classify ontology gaps;
they may not be laundered as clean first-attempt evidence.
```

Trigger:

```text
local probes are green or near-green
official evaluation remains materially red
remaining failures cluster by subsystem rather than by isolated row
additional local probes are likely to sample the same flawed ontology
```

Required source-postmortem ledgers:

```text
generated_resource_inventory_ledger:
  generated_tables
  embedded_databases
  bundled_fixture_directories
  schema_or_language_resources
  generated_source_files
  resource_cardinality_estimates
  consumer_surfaces
  promotion_blockers

entrypoint_stratification_ledger:
  entrypoint_ref
  parser_or_protocol_ref
  default_initialization_path
  shared_substrate_refs
  projection_schema_refs
  error_surface_refs
  cli_equivalence_posture

state_mutation_graph:
  control_ref
  control_kind
  mutated_state_refs
  implication_edges
  before_after_debug_snapshot_refs
  projection_consumer_refs

event_stream_grammar_ledger:
  event_level
  output_stream
  timestamp_grammar
  producer_refs
  dynamic_field_policy
  normal_output_interleaving_policy

router_renderer_layering_ledger:
  renderer_selector_refs
  output_router_refs
  target_grammar_refs
  final_output_wrapper_refs
  streaming_exception_refs
  side_effect_refs

estimator_formula_ledger:
  estimator_ref
  input_variables
  presets
  fallback_rules
  override_controls
  integer_float_conversion_rules
  threshold_projection_rules

toolchain_library_contract_ledger:
  declared_toolchain
  build_directives
  parser_framework
  formatter_libraries
  width_locale_libraries
  encoder_libraries
  library_owned_error_or_projection_surfaces
```

Promotion rule:

```text
If a source-postmortem reveals that a locally green leaf was actually backed by
a generated resource inventory, alternate entrypoint, state mutation graph,
event grammar, router layer, estimator formula, or toolchain/library contract,
that leaf is retroactively reclassified as scoped_ready_only.

The next clean run must instantiate the corresponding generic operator before
gold promotion.
```

Counterfactual questions for future clean runs:

```text
Does a broad public claim imply a generated resource denominator?

Does an API/server mode bypass the CLI parser and initialize state differently?

Does a flag mutate other flags or force hidden substrate calculation?

Does debug/trace/verbose output expose an event grammar rather than ad hoc text?

Does an output option select a renderer, route renderer output, or wrap final
process output?

Does a named estimator require formula, preset, fallback, override, and
threshold projection rows?

Does the real program depend on a toolchain, parser framework, formatter,
width/locale library, or encoder whose behavior must be treated as observable?
```

## 23. v8 lesson: kernel factoring, readiness product, and scout macros

The GPTPro §4.3 review over the meta-ontology export introduced the main v8
structural change: distinguish primitive operators from macro gates, artifact
views, and readiness states.

### Primitive vs macro vs artifact

Required vocabulary:

```text
primitive operator:
  small reusable conceptual move from the kernel algebra

mandatory macro gate:
  recurring compound pattern triggered by program class or public surface

artifact projection:
  table, ledger, report, or prompt emitted from the tree

readiness state:
  modal status of a leaf, branch, probe, scaffold, or handoff packet
```

This prevents the meta-program from treating `matcher_policy_ledger`,
`renderer_compatibility_table`, `source_postmortem_ledger`, or
`resource_contract_table` as primitive operators. They are generated artifacts
or macros.

### Orthogonal readiness product

Readiness must be a product of separate ledgers:

```yaml
ontology_status:
  candidate | terminal_candidate | terminal_locked | pass_through |
  deferred | conflict_isolated

probe_status:
  no_probe_needed | probe_needed | probe_planned | probe_ready |
  observed_locked | probe_blocked | conflict_probe_needed

scope_status:
  not_scoped_ready | scoped_ready | scoped_blocked_pending_observation |
  scoped_blocked_by_conflict | scoped_deferred

implementation_status:
  not_ready | scoped_implementation_ready | gold_implementation_ready |
  blocked_by_projection_gap | blocked_by_replay_risk | blocked_by_conflict

gold_status:
  not_gold_required | not_gold_ready_missing_sibling |
  not_gold_ready_missing_cross_product | not_gold_ready_synthetic_only |
  not_gold_ready_projection_open | not_gold_ready_missing_public_surface |
  not_gold_ready_missing_generative_rule | not_gold_ready_replay_risk_open |
  gold_ready | explicitly_deferred_from_gold_with_expected_risk
```

Non-promotion ladder:

```text
observed example != probe-ready
probe-ready != scoped-ready
scoped-ready != implementation-ready
scoped implementation-ready != gold implementation-ready
gold fixture green != clean evidence promotion for post-eval-only branches
```

### Mandatory scout probes by program class

The scout does not need task-specific edge names. It should use class-triggered
macro probes.

Universal CLI scout:

```text
no args
-h / --help / help aliases
--version / version aliases when plausible
unknown flag
invalid value for typed flag
missing value for value flag
greedy next-token binding
--flag=value versus --flag value
repeated flag behavior for list-like flags
help/version precedence with invalid flags
stdout/stderr/exit split
cwd and executable-name influence on usage text
stdin vs file source precedence when plausible
output route/file behavior when any output flag exists
```

Renderer / serializer / formatter scout:

```text
empty input
single row / multi-row
single line / multi-line body
special characters and trailing newlines
width/wrapping/smallscreen/terminal-width controls
color/ANSI/no-color controls
all declared formats
stdout vs file route
header/body/separator/footer/final-newline bytes
ordering/tie behavior
negative controls for hidden rows and no-row outputs
```

Structured stream parser / event aggregator scout:

```text
empty stream
blank lines
malformed record
wrong-shaped record
wrong-typed field
unknown field
missing required identity field
minimal valid record
realistic producer-shaped fixture
mixed valid + invalid stream
duplicate/conflicting terminal events
incomplete EOF lifecycle
output payload with multiple consumer roles
diagnostic morphology payload
aggregation denominator probe
exit denominator probe
raw-follow/side-effect ordering when raw output exists
late error after partial side effect
```

Filesystem counter / classifier / analyzer scout:

```text
single file by extension
filename-only identity
shebang identity
content-marker identity
shared extension with multiple possible languages
mixed directory with multiple subject classes
ignored/default-excluded path
custom include/exclude/remap/count-as value shape
default-vs-custom composition
binary/unreadable/empty file
nested directory and path normalization
large/generated/minified marker behavior
language/listing public surface if present
all output formats and output routing
debug/trace/verbose event grammar
formula/cost model overrides if present
```

Resource interpreter / resource-backed renderer scout:

```text
missing resource
resource search path / env / cwd precedence
malformed resource header
minimal resource
alternate resource packaging or extension
resource comments/metadata count
resource stack append/clear behavior
resource-controlled layout or transformation
resource-dependent error text and exit
```

Interactive TUI / workflow app scout:

```text
help/version/config-print surfaces
no-TTY startup
bad config file
config env vs CLI precedence
repo/worktree discovery
non-repo startup
terminal initialization failure or bounded TUI entry
external integration stubs when visible
safe timeout behavior
stdout/stderr/exit for noninteractive surfaces
```

Estimator / formula / metric program scout:

```text
default formula inputs
override controls
invalid numeric values
integer/float rounding
threshold text branches
empty/no-data behavior
format-specific projection fields
fallback/preset selection
```

API / server / MCP / programmatic entrypoint scout:

```text
method/schema listing
minimal valid request
unknown method
wrong-shaped request
CLI-equivalence or non-equivalence probe
alternate initialization path
projection schema shape
error status and stream behavior
```

### Over-priming control

The generator should receive operator-shaped counterfactuals, not named
task-specific edge lists.

Allowed prompt shapes:

```text
Does this payload have multiple consumers?
Can raw identity differ from display identity?
Can a route write side effects before a later parse error?
Can a selected-row denominator differ from an exit denominator?
Can the same semantic transform project differently through sibling renderers?
```

Disallowed as default generator prompts:

```text
Check panic/race/no-test.
Check trimpath.
Check scc generated marker exact branch.
Check go-mod-outdated missing Update.Time panic line.
```

Task-specific names can appear only after visible spec, program-class inference,
reference observation, official failure pressure, or source-postmortem warrant
has been attached.

### Probe compression rule

Probe compression remains a deferred optimization unless explicitly requested.
When used, it must compress by conceptual ownership, not by similar argv shape.

Safe compression requires:

```text
same terminal leaf
same authority layer
same observable surface
same realism tier
same generative rule
no unique sibling distinction
no unique side-effect/exit/consumer role
```

Never compress across:

```text
different consumers
different side-effect destinations
different exit denominators
different renderer byte grammars
different fixture-realism tiers
different authority layers
matcher consumers
synthetic fixture vs realistic producer morphology
```

### Source-postmortem escalation rule

Escalate to source-postmortem only when:

```text
local probes are green or near-green for the current scaffold
official evaluation remains materially red, or hidden-source risk remains large
failures cluster by subsystem rather than isolated byte rows
grouped divergence shows missing_conceptual_node, existing_node_badly_split,
  terminalization_gap, probe_under_realism, or coarse public-surface attachment
blind public-surface scout and granularity fitness have already run or were
  impossible and explicitly deferred
further blind probes are likely to sample the same flawed ontology rather than
  reveal the missing operator
```

Do not escalate when failures are isolated implementation transfer errors,
narrow projection sharpening with known parent nodes, regressions caused by a
broad patch, or branches still legitimately observable through public scout.
