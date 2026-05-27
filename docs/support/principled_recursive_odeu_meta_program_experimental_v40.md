# Principled Recursive ODEU Meta-Program Experimental v40

Authority layer: support / experimental meta-program revision.

This v40 patch extends:

```text
docs/support/principled_recursive_odeu_meta_program_experimental_v35.md
docs/support/principled_recursive_odeu_meta_program_experimental_v36.md
docs/support/principled_recursive_odeu_meta_program_experimental_v38.md
docs/support/general_program_ontology_derived_v1_5.md
```

Primary integration input:

```text
.codex/review-shell/chatgpt-downloads/xq_v35_counterfactual_review_v36.md
artifacts/manual_runs/programbench_xq_v35_adversarial_counterfactual_20260525T190000+0300/phase_outputs/v35_counterfactual_closeout.md
docs/support/xq_v36_descent_pass_review_v37.md
docs/support/xq_v38_consolidated_adversarial_pre_eval_schema.md
artifacts/manual_runs/programbench_xq_v35_adversarial_counterfactual_20260525T190000+0300/phase_outputs/v36_descent_counterfactual_closeout.md
docs/support/xq_v39_second_descent_result_integration_v40.md
artifacts/manual_runs/programbench_xq_v35_adversarial_counterfactual_20260525T190000+0300/phase_outputs/v39_pre_eval_descent_closeout.md
```

Core update:

```text
Adversarial pre-eval review is a two-stage circuit:

Stage A detects omitted salient axes.
Stage B detects under-descended active parents.

Stage C measures descent yield and decides whether to continue generic descent
or narrow into targeted microgrammar/source-tail closure.

No stage by itself proves gold readiness.
```

The `sibprogrammer__xq.b89f681` v35 counterfactual run is the evidence anchor.
It rebuilt from pre-official-eval artifacts only, reached local green on an
enhanced 176-probe public/reference manifest, and improved official eval from:

```text
v32 first pass:
  score: 67
  raw:   610 passed / 267 failed / 2 skipped / 879 total

v35 counterfactual first pass:
  score: 76
  raw:   684 passed / 193 failed / 2 skipped / 879 total
```

The transition had:

```text
old passed -> new passed:   610
old failed -> new passed:    74
old failed -> new failed:   193
old skipped -> new skipped:   2
old passed -> new failed:     0
```

The later v36 descent counterfactual continued from the v35 checkpoint and
improved official eval again:

```text
v36 descent counterfactual:
  score: 85
  raw:   760 passed / 117 failed / 2 skipped / 879 total
```

The v35 -> v36 transition had:

```text
old passed -> new passed:   684
old failed -> new passed:    76
old failed -> new failed:   117
old skipped -> new skipped:   2
old passed -> new failed:     0
```

This is a second clean positive method signal: after salience-breaking, a
separate blind descent-completeness pass found behavior-bearing closure
families that were already active but only represented by examples.

The consolidated method claim is:

```text
v35 proved pre-eval salience-breaking can recover omitted axes.
v36 proved pre-eval descent-completeness can recover under-terminalized active
parents.
```

The v39 second-descent pass continued from v36 and improved official eval again:

```text
v39 second descent:
  score: 88
  raw:   781 passed / 96 failed / 2 skipped / 879 total
```

The v36 -> v39 transition had:

```text
old passed -> new passed:   760
old failed -> new passed:    21
old failed -> new failed:    96
old skipped -> new skipped:   2
old passed -> new failed:     0
```

This validates a second Stage-B pass as useful, but the reduced marginal yield
creates a new method rule:

```text
After broad salience and descent-completeness gains, the orchestrator must
measure whether generic descent has saturated and whether the next move should
be targeted microgrammar/source-tail closure.
```

## 1. Readiness Label Correction

The v35 enhanced manifest status is:

```text
pre_eval_enhanced_scoped_gate_green
```

The v36 closure manifest status is:

```text
closure_matrix_green_for_first_batch
```

It is not:

```text
gold_ready_manifest
```

Reason:

```text
The manifest was reference-green and candidate-green, but official eval still
had a large tail in active sublanguage / formatter families.
```

For v36:

```text
The first closure batch was reference-green and candidate-green, but official
eval still had deeper XPath/XML/HTML tails inside the same macro-families.
```

Blocking rule:

```text
A pre-eval adversarial manifest may authorize a scoped first-pass official
attempt only if the posture is explicit. It may not authorize gold readiness
unless every active known sublanguage, renderer, route, diagnostic, and
resource topology family has its own closure matrix or a valid deferral proof.
```

## 2. Split Two Kinds of Probe Improvement

v36 separates:

```text
salience-breaking probes
  Find behavior-bearing axes that ordinary scout and ontology passes are likely
  to underweight because they are ambient, role-reversed, directional,
  mutating, convention-based, terminal-mediated, or hidden behind mixed-control
  precedence.

sublanguage closure probes
  Terminalize a known grammar, renderer, transform, selector, recovery, or
  routing family after the parent family is already activated.
```

Do not collapse these into one "more probes" bucket.

Method interpretation:

```text
Salience breakers improve first-pass theorem discovery.
Sublanguage closure matrices improve depth inside an already-known theorem
branch.
```

## 2A. `ADVERSARIAL_PRE_EVAL_TWO_STAGE_CIRCUIT`

Trigger:

```text
Any reconstruction task whose active ontology includes a parser, renderer,
selector/expression sublanguage, input/output dialect, mutation route, terminal
ecology, fatal-precedence lattice, or public scout surface that can hide sibling
behavior.
```

Required stages:

```text
Stage A: salience / omission adversary
  Find behavior-bearing siblings that were omitted because they were
  low-salience, ambient, convention-based, role-reversed, bidirectional, or
  side-effect-shaped.

Stage B: descent-completeness / closure-matrix adversary
  Find active parent branches that were named correctly but descended only
  through representative examples instead of terminal closure matrices.
```

Stage separation rule:

```text
Do not collapse Stage A and Stage B into a generic "find more edge cases" prompt.

Stage A asks:
  Which axes disappeared or were never promoted?

Stage B asks:
  Which activated parents are still only example-represented?
```

Blocking rule:

```text
A local-green manifest cannot become an official-ready candidate until both
salience gaps and descent-completeness gaps are closed, proved irrelevant, or
explicitly deferred with named risk.
```

Output statuses:

```text
salience_clean
salience_gaps_found
salience_gaps_deferred_with_risk
manifest_parity_green_with_descent_gaps
closure_matrix_required
closure_matrix_green
closure_matrix_green_with_witness_risk
official_ready_candidate
```

## 3. `PRE_EVAL_SALIENCE_BREAKER_GATE`

Trigger:

```text
After public scout and before implementation handoff.
```

Purpose:

```text
Search for low-salience behavior axes implied by the program class, public
schema, public scout observations, or utility promise before the local manifest
is locked as implementation-ready.
```

Required families when their trigger applies:

```text
ambient config convention
format role reversal
input/output directionality inversion
mutation side-effect route
multi-resource route edge
terminal/color/pager ecology
diagnostic precedence under mixed valid/invalid controls
selector/expression sublanguage sibling expansion
```

Blocking rule:

```text
A scout-observed program class must run the applicable salience-breaker probes
before local manifest lock. If a breaker is not run, it needs a typed
irrelevance, pass-through, or deferral proof.
```

## 4. `FORMAT_ROLE_REVERSAL_PROBE`

Trigger:

```text
A format appears anywhere as input, output, serializer, parser, renderer,
autodetect extension, pass-through medium, or conversion target.
```

Questions:

```text
Can the format be input as well as output?
Can the format be inferred from file extension?
Can it appear on stdin?
Can it pass through unchanged?
Can it be converted to and from each other public format?
Does its tree/value semantics differ by direction?
What are malformed-input diagnostics for that direction?
```

Required probe families:

```text
format as output
format as input
format by extension/autodetect
format through stdin
format under explicit flag
format as conversion source
format as conversion target
malformed input diagnostics
roundtrip / tree preservation
```

Closure rule:

```text
A format advertised in one role cannot be closed in that role alone unless the
opposite roles have been tested, proved unsupported, or explicitly deferred.
```

## 5. `AMBIENT_CONFIG_CONVENTION_PROBE`

Trigger:

```text
A CLI has config wording, defaults, debug/list modes, command-name identity,
formatting defaults, or a domain where dotfile conventions are common.
```

Questions:

```text
Is there a $HOME/.<cmd> config file?
Is XDG config used?
Does explicit config override ambient config?
What happens with malformed ambient config?
Which settings can ambient config alter?
Does in-place or mutating mode suppress some configured projection behavior?
```

Required probe families:

```text
$HOME/.<cmd>
$HOME/.config/<cmd>/config
XDG_CONFIG_HOME/<cmd>/config
cwd-local config if plausible
explicit config vs ambient config precedence
invalid ambient config diagnostics
ambient config ignored/proved-irrelevant negative control
mutation/in-place suppression of terminal-only configured effects
```

Closure rule:

```text
Config-like surfaces are not irrelevant merely because explicit config options
are absent or public scout did not make them salient. Ambient configuration
must be disproved, bounded, or deferred.
```

## 6. `SCOUT_OBSERVATION_PROMOTION_LEDGER`

Purpose:

```text
Prevent behavior-bearing public scout observations from disappearing when scout
data is compressed into a representative probe manifest.
```

Schema:

```yaml
scout_observation_promotion:
  observation_ref: string
  behavior_bearing: true | false | uncertain
  hob_node_ref: string | null
  promotion_action:
    promote_to_probe |
    merge_into_equivalence_class |
    defer_with_risk |
    prove_irrelevant |
    display_only_observation
  sibling_risk: low | medium | high
  manifest_status: included | merged | deferred | rejected
  warrant_ref: string | null
  notes: string
```

Rule:

```text
A behavior-bearing scout observation may not disappear between scout and probe
contract. If omitted, it needs a typed merge, deferral, pass-through, or
irrelevance proof.
```

## 7. `ROW_LEVEL_DELTA_ATTRIBUTION_LEDGER`

Purpose:

```text
After a method change moves official rows, attribute wins and regressions to
method gates, ontology nodes, implementation owners, and preservation
sentinels.
```

Schema:

```yaml
official_delta_ref:
  test_or_cluster: string
  old_status: passed | failed | skipped | not_run
  new_status: passed | failed | skipped | not_run
  primary_gate:
    scout_promotion |
    salience_breaker |
    format_role_reversal |
    ambient_config |
    sublanguage_representative |
    formatter_representative |
    mutation_side_effect |
    terminal_ecology |
    other
  ontology_node: string
  implementation_owner: string
  preservation_sentinels: []
  evidence_boundary:
    pre_eval_counterfactual |
    post_eval_pressure |
    source_tail |
    official_like_pressure
  notes: string
```

Rules:

```text
Separate wins caused by promoted public scout observations from wins caused by
new salience-breaker probes.

Do not treat score movement as semantic closure unless the relevant closure
matrix was already present or is created in a subsequent repair phase.
```

## 8. `SUBLANGUAGE_CLOSURE_ESCALATION_GATE`

Trigger:

```text
After salience breakers improve first-pass behavior but remaining failures
cluster in an active known sublanguage, formatter, transform, route, recovery,
or diagnostic family.
```

Purpose:

```text
Stop adding isolated representatives and compile the family into a closure
matrix.
```

Escalation examples:

```text
XPath selector/expression closure
SQL expression/function/aggregate closure
JSONPath/JQ-like selector closure
XML formatter/recovery closure
HTML formatter/recovery closure
CSV/TSV dialect closure
JSON input/output tree-preservation closure
TTY keymap and viewport state-machine closure
filesystem event/signal lifecycle closure
```

Rule:

```text
Do not keep adding representative salience breakers once the tail is a known
sublanguage or formatter. The next artifact must name the grammar axes,
cross-products, boundary cases, error laws, and renderer byte surfaces.
```

## 8A. `DESCENT_COMPLETENESS_CLOSURE_MATRIX_GATE`

Trigger:

```text
After scout-promotion and salience-breaker repair, before official-ready
posture, for every active parent that survived.
```

Question:

```text
Is this active parent terminalized into axes, or merely represented by examples?
```

Required row:

```yaml
descent_completeness_closure_matrix:
  parent_node_ref: string
  active_reason_refs: []
  existing_probe_refs: []
  current_status:
    example_represented |
    partial_matrix |
    closure_matrix_ready |
    proved_irrelevant |
    explicitly_deferred
  missing_axes:
    - grammar_axis
    - route_axis
    - projection_axis
    - value_domain_axis
    - lifecycle_axis
    - fatal_precedence_axis
    - side_effect_axis
    - substrate_axis
  high_yield_reference_probe_shapes: []
  deferral_risk: low | medium | high | blocker
  posture_effect: official_ready | scoped_green | block_ready
```

Blocking rule:

```text
Any active open-domain parser, renderer, selector, mutation, resource, or fatal
contract with current_status = example_represented blocks official-ready
posture.
```

Representative-overpromotion rule:

```text
A manifest family is not closed by representative probes unless each probe names
which sibling axes it covers and which sibling axes remain unprobed.
```

Allowed output claims:

```text
representative row green
manifest parity green
scoped local witness green
```

Forbidden unless matrix-backed:

```text
selector/expression sublanguage closed
formatter/recovery grammar closed
tree preservation closed
mutation lifecycle closed
fatal-precedence lattice closed
official-ready witness
```

## 8B. `DELTA_SCOUT_AFTER_SURPRISE_GATE`

Trigger:

```text
A public scout observes behavior that contradicts the naive ontology or broadens
a role: recovery instead of fatal behavior, input role instead of output-only
role, ambient convention, selector precedence, mutation behavior, or
channel/exit surprise.
```

Rule:

```text
Do not only promote the surprising row. Generate sibling probes around the
surprise and record which active parent needs re-descent.
```

Examples:

```text
malformed XML recovered -> harder malformed XML taxonomy
HTML accepted/recovered -> fragment/optional-tag/raw-text taxonomy
JSON input accepted -> JSON directionality/tree-preservation matrix
ambient config observed -> config search/precedence/error matrix
```

## 8C. `LOCAL_GREEN_POSTURE_CLASSIFIER`

Replace binary local-green posture with:

```text
manifest_parity_green
manifest_parity_green_with_salience_gaps
manifest_parity_green_with_descent_gaps
salience_breaker_green
closure_matrix_green
closure_matrix_green_with_witness_risk
official_ready_candidate
```

Rules:

```text
manifest_parity_green != official_ready
salience_breaker_green != sublanguage_closed
closure_matrix_green over one matrix != parent gold-closed
zero regressions over visible gates != hidden-tail exhausted
```

## 8D. `PRE_EVAL_DESCENT_YIELD_ACCOUNTING_GATE`

Purpose:

```text
Record whether additional pre-eval adversarial passes are finding new parents,
new child matrices, or only small terminal leaves.
```

Required row:

```yaml
pre_eval_descent_yield:
  pass_id: string
  previous_base: string
  added_probe_count: int
  parent_families_touched: []
  new_parent_count: int
  new_child_matrix_count: int
  terminal_leaf_count: int
  local_start_pass_rate: string
  local_final_pass_rate: string
  regression_gate_refs: []
  official_delta_if_measured:
    score_delta: int | null
    newly_passing_rows: int | null
    regressions: int | null
  posture:
    high_yield_parent_recovery |
    high_yield_child_matrix_recovery |
    low_yield_terminal_squeeze |
    saturated_generic_descent
```

Rules:

```text
Do not authorize another generic descent pass until the previous descent pass
has a yield-accounting row.

Score movement is not enough. The row must say whether the pass discovered new
parents, new child matrices, or only terminal microgrammar leaves.
```

## 8E. `DESCENT_SATURATION_AND_ESCALATION_GATE`

Rule:

```text
If a second or later generic descent pass produces mostly terminal microgrammar
leaves and substantially lower yield than the previous descent pass, stop broad
adversarial descent and switch to targeted microgrammar or source-tail closure.
```

Suggested trigger:

```text
new_parent_count = 0
remaining failures concentrate in three or fewer known parent families
latest measured gain < 50% of prior descent-pass gain
added probes are mostly formatter/parser/selector byte microgrammar variants
```

For the xq evidence sequence:

```text
v36 gain: +76 official rows
v39 gain: +21 official rows
remaining tail: XML / HTML / XPath dominant
classification: low_yield_terminal_squeeze
next posture: targeted_microgrammar_closure
```

Blocking rule:

```text
When the saturation trigger fires, a new generic "find more descent gaps" pass
is not authorized unless the orchestrator records a concrete novelty hypothesis
that differs from the already-saturated parent families.
```

## 8F. `TARGETED_MICROGRAMMAR_CLOSURE_GATE`

Trigger:

```text
Remaining pressure is concentrated under already-known sublanguages,
formatters, recovery grammars, or byte projections.
```

Required matrix:

```yaml
targeted_microgrammar_closure:
  parent_family: XML | HTML | XPath | JSON | CSS | route_config | other
  microgrammar_axes: []
  public_reference_probe_rows: []
  negative_sibling_rows: []
  byte_or_tree_or_exit_surfaces: []
  target_library_or_source_tail_needed: true | false
  preservation_gate_refs: []
  implementation_owner: string
  closure_status:
    matrix_needed |
    reference_locked |
    source_tail_needed |
    implementation_ready |
    deferred_with_risk
```

Target examples:

```text
XML recovery / error / encoding microgrammar
HTML formatter / raw-text / optional-tag byte grammar
XPath predicate / function / namespace / attribute semantics
JSON tree / malformed-input / indentation residuals
```

## 8G. `SOURCE_TAIL_ESCALATION_AFTER_PUBLIC_MICROGRAMMAR_GATE`

Rule:

```text
If a known formatter/parser/selector microgrammar remains red after two
public-reference microgrammar passes, source-tail or target-library equivalence
analysis becomes a justified next method, not a failure of blind ontology.
```

Evidence boundary:

```text
Source-tail analysis is not clean first-pass evidence.
It is a justified escalation after public-reference microgrammar descent has
saturated and must be labeled as source_tail or post_eval_pressure depending on
the inputs used.
```

## 9. Structured Document Transform CLI Profile

Strengthen:

```text
STRUCTURED_DOCUMENT_TRANSFORM_CLI
```

Trigger when a program:

```text
reads structured documents;
selects nodes, records, paths, or fields through a selector language;
formats, extracts, transforms, or converts markup/tree data;
mutates files in place;
routes multiple files/stdin/stdout;
prints to terminal/pager/color-sensitive surfaces;
exposes JSON/XML/HTML/YAML/TOML/CSV-like input or output formats.
```

Inherited obligations:

```text
CONTROL_TOKEN_GRAMMAR_AND_ALIASES
DOCUMENT_RESOURCE_ROUTE_TOPOLOGY
MUTATION_AND_IN_PLACE_LIFECYCLE
INPUT_FORMAT_DIALECTS_AND_ROLE_DIRECTIONALITY
SELECTOR_EXPRESSION_SUBLANGUAGE_CLOSURE
SELECTED_NODE_IDENTITY_AND_TREE_PRESERVATION
FORMATTER_RENDERER_BYTE_GRAMMAR
PARSE_RECOVERY_AND_DIAGNOSTIC_PRECEDENCE
TERMINAL_PAGER_COLOR_ECOLOGY
AMBIENT_CONFIG_TOPOLOGY
EVIDENCE_AND_CONFIG_CONVENTION_WARRANT
ADVERSARIAL_PRE_EVAL_AND_MANIFEST_RED_TEAM_GOVERNANCE
```

Important child nodes:

```text
FORMAT_DIRECTIONALITY_AND_TREE_PRESERVATION
AMBIENT_CONFIG_TOPOLOGY
SELECTOR_EXPRESSION_SUBLANGUAGE_CLOSURE
STRUCTURED_DOCUMENT_PARSE_RECOVERY_GRAMMAR
MARKUP_FORMATTER_BYTE_GRAMMAR
MUTATION_SIDE_EFFECT_LIFECYCLE
TERMINAL_PAGER_COLOR_ECOLOGY
```

Do not promote task-specific leaves such as `.xq`, XPath, HTML void elements,
or XML comments into universal obligations. Promote the generic owner and keep
the task-specific leaves in the task ontology.

## 10. Revised Phase Sequence

For structured-document transform CLI tasks:

```text
P1A  blind task-native ontology
P1B  GPO projection
P1C  intent / utility projection
P1D  reciprocal diff
P1E  merged activation / inherited obligations
P2   public scout
P2B  public scout observation promotion ledger
P2C  salience / omission adversarial gate
P3   locked manifest
P3B  representative-manifest red-team gate
P3C  descent-completeness closure-matrix gate
P3D  second descent squeeze only if novelty/yield posture supports it
P3E  descent saturation gate
P4   targeted microgrammar closure matrix or source-tail authorization
P5   bounded implementation handoff
P6   local green plus regression stack
P6B  local-green witness-shape audit
P6C  closure-matrix local gate
P7   official-readiness authorization
P8   official eval experiment
P9   post-eval pressure audit
```

The role split is:

```text
P2C asks:
  Did low-salience behavior axes disappear?

P3C asks:
  Are active parent branches terminalized deeply enough?

P3D/P3E ask:
  Is generic descent still discovering meaningful structure, or has it
  saturated into low-yield terminal variants?
```

For `xq` after v39, the next clean sequence is:

```text
Batch 0, no code:
  exact 96-row tail ownership;
  attach every remaining official row to XML, HTML, XPath, JSON, route/config,
  CSS, or other;
  split formatter byte failures from parser/recovery failures.

Batch 1:
  XML/HTML formatter and recovery microgrammar.

Batch 2:
  XPath predicate/function microgrammar.

Batch 3:
  JSON tree/indent, route/config precedence, CSS residual, and one-off other
  tail.
```

## 11. Transition Bookkeeper Rules

The bookkeeper must reject or downgrade a transition if any of these are true:

```text
scout observation is behavior-bearing and absent from the manifest without a
  typed promotion/merge/deferral/irrelevance row;
salience-breaker triggers apply but no probes or proofs are present;
probe manifest is called representative while active sibling families are
  unscoped;
active open-domain parser/renderer/selector/mutation/resource/fatal parent is
  example_represented after P3C;
descent-completeness matrix is absent for a triggered active parent without
  typed irrelevance, pass-through, or deferral proof;
second-or-later generic descent is requested without a
  PRE_EVAL_DESCENT_YIELD_ACCOUNTING row;
descent saturation triggers fire but the next plan still proposes broad
  adversarial descent instead of targeted microgrammar/source-tail closure;
pre-eval scoped green is promoted to gold readiness;
local green is used as official readiness while witness-shape audit flags a
  fixture-shaped implementation under an active open-domain family;
closure_matrix_green over one matrix is promoted to parent gold-closed while
  sibling matrices remain unowned;
remaining pressure clusters in a known sublanguage but the next plan adds only
  isolated representatives;
format is closed as output-only without directionality testing;
config-like surface is closed without ambient-convention disproof;
score movement is recorded without row/cluster-level delta attribution.
```

Allowed override requires:

```text
explicit scope downgrade;
expected risk statement;
owned HOB nodes;
deferred probe rows;
evidence boundary label;
posture label: scoped_experiment, manifest_parity_green_with_descent_gaps, or
  first_pass_attempt, not gold_attempt.
```

After saturation, allowed override additionally requires:

```text
new novelty hypothesis;
named parent family not already saturated;
expected yield/risk statement;
preservation sentinels for all touched implementation owners.
```

## 12. Worker Role Separation

The orchestrator must keep these worker prompts distinct:

```text
salience adversary:
  low-salience omitted siblings and manifest compression

descent adversary:
  representative-only active parents and missing closure matrices

implementation worker:
  bounded closure-matrix or targeted microgrammar implementation under existing
  regression gates

bookkeeper:
  status downgrade, inherited-obligation accounting, and phase-transition
  legality

yield accountant:
  compare consecutive pre-eval passes and classify whether the latest pass is
  parent recovery, child-matrix recovery, terminal squeeze, or saturated generic
  descent
```

Forbidden prompt collapse:

```text
find more edge cases before eval
```

Reason:

```text
That prompt hides the structural difference between omitted axes and
under-descended active parents.
```

After saturation, also forbidden:

```text
run another generic adversarial descent pass
```

unless the orchestrator records the novelty override described in the
`DESCENT_SATURATION_AND_ESCALATION_GATE`.
