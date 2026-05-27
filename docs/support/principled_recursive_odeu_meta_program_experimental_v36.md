# Principled Recursive ODEU Meta-Program Experimental v36

Authority layer: support / experimental meta-program revision.

This v36 patch extends:

```text
docs/support/principled_recursive_odeu_meta_program_experimental_v35.md
docs/support/general_program_ontology_derived_v1_5.md
```

Primary integration input:

```text
.codex/review-shell/chatgpt-downloads/xq_v35_counterfactual_review_v36.md
artifacts/manual_runs/programbench_xq_v35_adversarial_counterfactual_20260525T190000+0300/phase_outputs/v35_counterfactual_closeout.md
```

Core update:

```text
Adversarial pre-eval gates are validated as first-pass improvement and
omission-prevention gates, not as full coverage or gold-readiness gates.
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

This is a clean positive method signal: v35 found behavior axes that were
discoverable before official eval. It is not a closure proof for the whole
program.

## 1. Readiness Label Correction

The v35 enhanced manifest status is:

```text
pre_eval_enhanced_scoped_gate_green
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
P2C  pre-eval salience-breaker probes
P3   locked manifest
P3B  representative-manifest red-team gate
P4   bounded implementation handoff
P5   local candidate gate
P5B  local-green witness-shape audit
P6   official eval posture authorization
P7   delta attribution and sublanguage escalation decision
```

For `xq` after v35, the next clean sequence is:

```text
Batch 0, no code:
  row-level delta attribution for the 74 wins;
  row-level ownership for the 193 remaining failures;
  split salience-breaker vs scout-promotion contribution.

Batch 1:
  XPath selector/expression sublanguage matrix.

Batch 2:
  XML physical grammar / formatter / recovery matrix.

Batch 3:
  HTML formatter / recovery matrix.

Batch 4:
  JSON directionality / tree-preservation tail and IO route closure.
```

## 11. Transition Bookkeeper Rules

The bookkeeper must reject or downgrade a transition if any of these are true:

```text
scout observation is behavior-bearing and absent from the manifest without a
  typed promotion/merge/deferral/irrelevance row;
salience-breaker triggers apply but no probes or proofs are present;
probe manifest is called representative while active sibling families are
  unscoped;
pre-eval scoped green is promoted to gold readiness;
local green is used as official readiness while witness-shape audit flags a
  fixture-shaped implementation under an active open-domain family;
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
posture label: scoped_experiment or first_pass_attempt, not gold_attempt.
```
