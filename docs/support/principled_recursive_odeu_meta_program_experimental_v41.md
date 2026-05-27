# Principled Recursive ODEU Meta-Program Experimental v41

Authority layer: support / experimental meta-program revision.

This v41 patch extends:

```text
docs/support/principled_recursive_odeu_meta_program_experimental_v40.md
docs/support/general_program_ontology_derived_v1_5.md
artifacts/manual_runs/programbench_xq_v35_adversarial_counterfactual_20260525T190000+0300/phase_outputs/v40_remaining_failure_findability_audit.md
.codex/review-shell/chatgpt-downloads/xq_v40_findability_review_v41.md
```

Core update:

```text
When active parents are stable and repeated descent passes have low official
yield despite local-green reference probes, stop generic descent. Compile the
remaining tail by findability source before generating more probes or patches.
```

The `sibprogrammer__xq.b89f681` v40 pass is the evidence anchor:

```text
v40 targeted microgrammar pass:
  added probes: 40
  local v40 gate: 40 / 40
  prior gates preserved: v35 176 / 176, v36 32 / 32, v39 33 / 33
  official result: score 88, 782 passed / 95 failed / 2 skipped
  official delta from v39: +1 row, 0 regressions
```

Interpretation:

```text
parent activated
  -> representative probes generated
  -> local gates green
  -> terminal official leaves still open
```

This is not a missing-parent failure. It is a tail findability and evidence
source mismatch.

## 1. `TAIL_FINDABILITY_AND_EVIDENCE_SOURCE_GATE`

Trigger:

```text
score is high or parent families are stable;
multiple salience/descent passes have already been run;
a targeted pass gains little despite local green;
remaining failures cluster under already-active parents.
```

Required row:

```yaml
tail_findability:
  tail_bucket: string
  row_count: int
  active_parent_node_refs: []
  current_probe_status:
    representative_green |
    matrix_green |
    not_green
  missed_terminal_kind:
    corpus_parity |
    sublanguage_inventory |
    serializer_dialect_atom |
    fatality_minimal_pair |
    projection_renderer_split |
    resource_topology_tail |
    reader_writer_pair |
    host_library_equivalence |
    official_tail_exactness
  findability_mode:
    blind_conceptual |
    public_scout |
    reference_minimal_pair |
    fixture_corpus_harvest |
    source_tail |
    library_equivalence |
    official_tail_repair
  expected_blind_yield: high | medium | low
  recommended_next_path:
    methodology_experiment |
    source_compatible_tail_closure
  evidence_boundary:
    pre_eval_clean |
    public_reference |
    post_eval_pressure |
    source_tail
  closure_posture:
    blocked |
    probe_ready |
    implementation_ready |
    source_tail_ready
```

Blocking rule:

```text
No further generic descent pass is allowed after saturation unless the remaining
bucket is classified as blind-findable by a new discriminator.
```

## 2. `CANONICAL_SUBLANGUAGE_INVENTORY_GATE`

Trigger:

```text
The program embeds a selector language, query language, matcher grammar,
expression surface, filter language, or mini-language over a resource.
```

Required inventory axes:

```text
lexical token classes
path/navigation axes
operators
predicates / filters
function families
literal and value types
coercion rules
namespace / scope / environment rules
no-match behavior
malformed behavior
projection consumer split
```

For XPath-like surfaces, the inherited inventory is:

```text
path axes
attribute axis
parent axis
predicates
numeric comparisons
text node selection
string/number/node-set coercions
function families
namespace/prefix behavior
no-match and malformed forms
projection byte grammar
```

Rule:

```text
Sampling selector examples is not sublanguage closure. A sublanguage closes only
through inventory coverage, proved irrelevance, or explicit source-tail deferral.
```

## 3. `FIXTURE_CORPUS_PARITY_GATE`

Trigger:

```text
Official/public pressure compares against named golden fixtures, corpus-derived
inputs, or source-derived formatter fixtures; isolated syntax-atom probes are
green but corpus rows remain red.
```

Required split:

```text
atomic syntax coverage
  !=
whole-fixture morphology parity
```

Required row:

```yaml
fixture_corpus_parity:
  corpus_ref: string | null
  fixture_family: XML | HTML | JSON | text | other
  morphology_axes:
    - encoding
    - declaration_or_doctype
    - processing_instruction
    - namespace
    - comment_shape
    - raw_text_island
    - mixed_text_child_wrapping
    - self_closing_policy
    - optional_tag_policy
    - whitespace_policy
  evidence_source:
    public_reference_generated |
    public_fixture_harvest |
    source_tail_fixture |
    official_tail_only
  closure_status:
    not_started |
    corpus_matrix_ready |
    source_tail_ready |
    closed
```

Rule:

```text
If whole-fixture parity is the obligation, atom probes cannot be promoted to
gold closure.
```

## 4. `HOST_LIBRARY_EQUIVALENCE_GATE`

Trigger:

```text
Behavior depends on parser, serializer, formatter, selector engine, codec,
terminal library, SQL engine, YAML/JSON/XML/HTML library, regex engine, or
runtime-specific diagnostic surface.
```

Required outputs:

```text
target library or reference stack candidate
observed public behavior subset
known divergences from current implementation substrate
fallback or emulation strategy
scope of equivalence claim
source-tail/post-eval evidence label if used
```

Rule:

```text
When a tail is library-compatible behavior, blind probes may only bound the
surface. Exact closure requires library-equivalence proof, fixture-corpus
parity, or explicit source-tail repair.
```

## 5. `PROJECTION_RENDERER_SEPARATION_GATE`

Required separation:

```text
selector evaluation:
  selected node-set / value-set

projection rendering:
  text projection
  node projection
  attribute projection
  separator policy
  indentation policy
  color/style policy
  final newline policy
  empty/no-match policy
```

Rule:

```text
A probe that proves a selector can find a node does not prove the node/text/attr
projection byte grammar.
```

## 6. `MINIMAL_PAIR_FATALITY_MATRIX_GATE`

Trigger:

```text
Malformed/recovery behavior remains after representative malformed probes passed.
```

Required dimensions:

```text
syntax class
minimal mutation from valid input
route: stdin / file / multi-file / in-place
mode: default / format-specific / selector / JSON / HTML / XML / mutation
expected channel
expected exit
partial output policy
```

Rule:

```text
One malformed input shape does not transfer to another syntax class, route, or
output mode without a minimal-pair proof.
```

## 7. `DESCENT_SATURATION_DETECTOR`

Required row:

```yaml
descent_saturation:
  previous_pass_delta: int
  current_pass_delta: int
  probes_added: int
  local_gate_green: true | false
  regression_count: int
  active_parent_stability: stable | changing
  saturation_status:
    not_saturated |
    likely_saturated |
    saturated
  next_method_allowed:
    - canonical_inventory
    - minimal_pair_matrix
    - fixture_corpus_harvest
    - source_tail
    - official_tail_repair
```

Rule:

```text
If probes added are high, local gates are green, active parents are stable, and
official delta is near zero, stop generic descent.
```

## 8. Path Choice Contract

The orchestrator must choose a posture before the next pass:

```text
methodology_experiment:
  optimize for learning what remains blind-findable.
  Do not claim this is the highest-yield solving path.

source_compatible_tail_closure:
  optimize for solving the task.
  Use fixture corpus, source-tail, or library equivalence with evidence labels.
```

For `xq`, v41 authorizes:

```text
Path A:
  canonical XPath inventory
  minimal-pair fatality matrix
  projection-renderer split matrix
  no source-tail or official-tail repair during derivation

Path B:
  source-compatible XML/HTML fixture-corpus parity and library-equivalence repair
```

Do not generalize task-specific leaves such as `unformatted*.xml` names or
specific fixture labels. Do generalize the gate structure:

```text
fixture-corpus parity is distinct from syntax-atom coverage
embedded language closure requires inventory traversal
selector success is not projection byte closure
malformed behavior requires minimal-pair fatality matrices
library-compatible tails require evidence-source escalation
repeated low-yield descent triggers saturation and method-choice gates
```
