# XQ v36 adversarial descent pass review / v37 schema integration

Authority layer: support / method-review synthesis.

Reviewed artifacts:

- `EXPERIMENT_PROTOCOL.md`
- `blind_descent_completeness_audit.md`
- `descent_pass_comparison_closeout.md`
- `phase7_v36_pre_eval_squeeze_attribution.md`

## 1. Verdict

The v36 adversarial pass is methodologically important and should be promoted into the meta-program.

The key result is not another implementation patch. It is a cleaner separation between two different pre-eval failure modes:

```text
v35 salience-breaker failure:
  low-salience sibling obligations were not inherited or promoted.

v36 descent-completeness failure:
  active parent branches were already named, but were represented by examples
  rather than terminal closure matrices.
```

The experiment protocol made this distinction explicit. It asked for a non-implementation, non-post-eval adversarial audit inserted after the v35 local-green base and before official eval, with official eval files, hidden tests, upstream source, and post-eval repair artifacts forbidden. It required separate review of transitions T1 through T4:

```text
T1: merged activation -> inherited obligation tree
T2: public scout observations -> locked/enhanced probe manifest
T3: locked/enhanced probe manifest -> implementation handoff
T4: local 176/176 green witness -> official-readiness posture
```

That is exactly the right structure. It asks whether each phase transition preserved the semantic circuit instead of treating local parity as enough.

## 2. What the artifacts prove

### 2.1 v35 proved salience-breaking value, not gold readiness

The v35 counterfactual improved the first-pass official result from:

```text
score 67, 610 passed / 267 failed / 2 skipped
```

to:

```text
score 76, 684 passed / 193 failed / 2 skipped
```

with 74 old failures becoming passes and zero old passes regressing.

The attribution is highly structured:

```text
34 wins: raw JSON input / FORMAT_ROLE_REVERSAL_PROBE
29 wins: ambient $HOME/.xq config / AMBIENT_CONFIG_CONVENTION_PROBE
 4 wins: promoted JSON scout rows
 4 wins: HTML formatter sibling scout rows
 3 wins: XPath representative scout rows
```

So v35 validated this method claim:

```text
Low-salience sibling and scout-promotion gates can squeeze real official points
before first official eval without official-eval hindsight.
```

But it did not validate gold readiness. It left a tail of active parent branches that were still example-represented.

### 2.2 v36 identified the remaining tail shape without official data

The v36 worker labeled the v35 state:

```text
manifest_parity_green_with_descent_gaps
```

and blocked official readiness. Its strongest named gaps were:

```text
XML parser/formatter/recovery closure
HTML parser/formatter/recovery closure
XPath selector/expression sublanguage closure
CSS invalid/no-match/projection closure
JSON tree preservation closure
in-place and filesystem mutation lifecycle
fatal-gate/channel precedence closure
terminal/pager ecology residuals
ambient config / raw JSON breadth residuals
```

It proposed eight matrices:

```text
M1 XML Reader/Writer Recovery
M2 HTML Recovery And Selector Binding
M3 XPath Sublanguage
M4 CSS Invalid/No-Match And Projection
M5 JSON Tree Preservation
M6 In-Place Destination Lifecycle
M7 Fatal-Gate And Channel Precedence
M8 Presentation And Ambient Ecology
```

The comparison closeout then checked this blind audit against the held-back official tail and found strong alignment:

```text
XPath sublanguage:          strong hit
XML formatter/recovery:     strong hit
HTML formatter/recovery:    strong hit
JSON tree/directionality:   strong hit
IO route/resource:          partial hit
config parser tail:         low-yield hit
other tail:                 mixed
```

This is the most important result: the worker recovered the dominant shape of the remaining official tail without seeing official failures.

## 3. Why this matters methodologically

Before v36, the pre-eval method could catch:

```text
scout rows dropped from the manifest
ambient conventions
format directionality / role reversal
obvious sibling omissions
```

After v36, the method can also catch:

```text
parent branches that are named but under-terminalized
sublanguages represented by literal examples
formatters represented by sample fixtures
parser recovery represented by two or three malformed sentinels
mutation lifecycle represented by one happy-path write
local green witnesses that are shape-narrow despite probe parity
```

This is a different class of failure. It is not a missing-label problem. It is a missing-depth problem.

The critical distinction:

```text
parent activated
  != inherited children terminalized

all scout observations promoted
  != sublanguage closure matrix complete

176/176 local green
  != official-ready witness
```

## 4. Layer-transition read

### T1: Merged activation -> inherited obligation tree

v35 activated the right broad parents, but many remained prose families. The v36 audit points to XML recovery, HTML recovery, XPath/CSS grammar, JSON preservation, mutation safety, and terminal ecology as parents that needed inherited child matrices.

Schema interpretation:

```text
T1 failure = parent activated but child inheritance was not strict enough.
```

Patch:

```text
Any active parent with a public sublanguage, parser, renderer, mutation route,
or diagnostic/fatal contract must produce a closure-matrix candidate unless
proved irrelevant or explicitly deferred.
```

### T2: Scout observations -> manifest

v35 fixed the earlier 99-probe compression by promoting 164 public scout observations and adding 12 salience probes. But v36 correctly says that this only made the manifest row-complete relative to the scout. It did not make the scout tail-complete.

Schema interpretation:

```text
T2 failure = promoted scout rows were still representative for active subtrees.
```

Patch:

```text
Surprising scout behavior must trigger a delta-scout pass. If a scout shows
recovery where fatal behavior was expected, or input-role reversal where only
output was expected, the orchestrator must ask what sibling space that surprise
opens.
```

### T3: Manifest -> implementation handoff

The v36 audit used implementation source only as a witness-shape audit. That is correct. It did not use source to derive product truth; it used source to ask whether local green could have been achieved through narrow mechanisms.

It found witness risks such as:

```text
literal XPath switch
forgiving XML scanner plus known replacements
selected HTML parser paths
sorted/collapsed JSON rendering
simple WriteFile in-place behavior
```

Schema interpretation:

```text
T3 failure = implementation handoff accepted representative fixture parity
without requiring generative ownership of active sublanguages.
```

Patch:

```text
Before official-ready posture, run witness-shape audit against every active
open-domain sublanguage/renderer/parser/mutation parent. If the implementation
is literal-switch-like or fixture-shaped under an active parent, require sealed,
metamorphic, or closure-matrix probes.
```

### T4: Local green -> official readiness

The v36 audit says local reference and candidate parity at 176/176 is strong evidence for manifest parity, but not official readiness.

Schema interpretation:

```text
T4 failure = readiness overpromotion.
```

Patch:

```text
A local-green manifest with open closure matrices must be labeled
manifest_parity_green_with_descent_gaps, not official_ready.
```

## 5. Proposed v37 meta-program additions

### 5.1 `DESCENT_COMPLETENESS_CLOSURE_MATRIX_GATE`

Trigger:

```text
After scout-promotion and salience-breaker repair, before implementation or
before official-ready posture, for every active parent that survived.
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
contract with current_status = example_represented blocks official-ready posture.
```

### 5.2 `REPRESENTATIVE_PARENT_OVERPROMOTION_CHECK`

Trigger:

```text
Any manifest family name contains a public sublanguage, dialect, selector,
formatter, parser recovery, mutation route, terminal ecology, or fatal lattice.
```

Rule:

```text
A manifest family is not closed by representative probes unless each probe names
which sibling axes it covers and which sibling axes remain unprobed.
```

Allowed output claims:

```text
XPath representative row green
XML malformed sentinel green
HTML comment preservation green
JSON raw role-reversal green
```

Forbidden unless matrix-backed:

```text
XPath closed
XML recovery closed
HTML formatter closed
JSON tree preservation closed
in-place lifecycle closed
```

### 5.3 `DELTA_SCOUT_AFTER_SURPRISE_GATE`

Trigger:

```text
A public scout observes behavior that contradicts the naive ontology or broadens
a role: recovery instead of fatal, input role instead of output-only role,
ambient convention, selector precedence, mutation behavior, or channel/exit
surprise.
```

Rule:

```text
Do not only promote the surprising row. Generate sibling probes around the
surprise.
```

For xq-like tasks:

```text
malformed XML recovered -> harder malformed XML taxonomy
HTML accepted/recovered -> fragment/optional-tag/raw-text taxonomy
JSON input accepted -> JSON directionality/tree-preservation matrix
ambient config observed -> config search/precedence/error matrix
```

### 5.4 `LOCAL_GREEN_POSTURE_CLASSIFIER`

Replace binary local-green posture with:

```text
manifest_parity_green
manifest_parity_green_with_salience_gaps
manifest_parity_green_with_descent_gaps
closure_matrix_green
closure_matrix_green_with_witness_risk
official_ready_candidate
```

Rule:

```text
Only closure_matrix_green without unresolved witness risk can become an
official-ready candidate.
```

### 5.5 `WITNESS_SHAPE_AUDIT_FOR_OPEN_DOMAIN_PARENTS`

Trigger:

```text
Local green exists for a manifest that includes active open-domain parents.
```

Audit allowed source use:

```text
implementation source may be inspected only to classify witness shape, not to
infer target reference behavior.
```

Risk signals:

```text
literal switch over observed expressions
hard-coded recovery replacements
fixture-specific serializer branches
global regex parser where grammar requires nested states
default empty success on unknown sublanguage forms
mutation write without lifecycle/atomicity/mode policy
```

Required result:

```text
If witness-shape risk is high, require sealed/metamorphic probes or closure
matrix probes before official-ready posture.
```

## 6. Program-class generalization

This lesson applies most strongly to tasks with any of these classes:

```text
structured document transformer
selector / query / expression sublanguage
markup parser / formatter / recovery behavior
input-output format role directionality
in-place mutation or filesystem side effects
terminal/pager/color ecology
fatal-gate/channel/exit precedence
```

A generic class should be added or strengthened:

```text
STRUCTURED_DOCUMENT_TRANSFORM_CLI
```

Inherited closure obligations:

```text
document parse and recovery grammar
selector/expression sublanguage
format directionality and tree preservation
formatter/serializer byte grammar
mutation destination lifecycle
fatal-gate/channel/exit precedence
ambient config topology
terminal/pager/color ecology
```

This should remain generic. Do not bake in `.xq`, XPath specifics, XML comment cases, or any single official fixture. The reusable idea is:

```text
A structured-document CLI often exposes several open-domain microgrammars. Once
one such parent is active, representative probes are not enough; the parent must
be compiled into a closure matrix.
```

## 7. Revised pre-eval sequence

The new pre-eval sequence should be:

```text
P1A  blind task-native ontology
P1B  GPO projection
P1C  reciprocal diff
P1D  merged activation / inherited obligations
P2   public scout
P2B  scout-to-manifest promotion audit
P2C  salience-breaker probe pass
P3   locked probe contract
P3B  representative-manifest red-team gate
P3C  descent-completeness closure-matrix gate
P4   implementation handoff
P5   local green
P5B  local-green witness-shape audit
P6   official eval posture authorization
```

The v36-specific addition is `P3C`. It is not the same as `P2C`.

```text
P2C asks: did we miss hidden siblings because they were low-salience?
P3C asks: are the active sibling subtrees terminalized deeply enough?
```

## 8. Next clean experiment for xq

Do not patch from official failures.

Use the v36 matrices M1-M8 to generate a bounded public/reference closure manifest:

```text
M1 XML reader/writer recovery
M2 HTML recovery and selector binding
M3 XPath sublanguage
M4 CSS invalid/no-match and projection
M5 JSON tree preservation
M6 in-place destination lifecycle
M7 fatal-gate and channel precedence
M8 presentation and ambient ecology
```

Then:

```text
1. Run reference parity for the v36 closure manifest.
2. Remove or mark unstable rows that cannot be reference-locked cleanly.
3. Patch candidate against v35 + v36 local gates only.
4. Run witness-shape audit again.
5. Only then run official eval.
6. Attribute gains by matrix.
```

Expected gain shape:

```text
mostly XPath / XML / HTML / JSON closure rows,
not ambient config or raw JSON directionality rows.
```

## 9. Integration bottom line

v35 proved:

```text
pre-eval salience-breaking works.
```

v36 proves:

```text
pre-eval descent-completeness auditing can identify the dominant remaining
closure families before official eval.
```

Still not yet proven:

```text
that implementing from the v36 closure matrices recovers the remaining official
points without official-tail repair.
```

The safe schema integration is therefore:

```text
Promote v36 as a mandatory readiness blocker / closure-matrix compiler,
not yet as a guaranteed score-gain mechanism.
```
