# Principled Recursive ODEU Meta-Program Experimental v44

Authority layer: support / experimental meta-program revision.

This v44 patch extends:

```text
docs/support/principled_recursive_odeu_meta_program_experimental_v40.md
docs/support/principled_recursive_odeu_meta_program_experimental_v41.md
docs/support/principled_recursive_odeu_meta_program_experimental_v43.md
docs/support/general_program_ontology_derived_v1_5.md
artifacts/manual_runs/programbench_xq_v35_adversarial_counterfactual_20260525T190000+0300/phase_outputs/v40_remaining_failure_findability_audit.md
.codex/review-shell/chatgpt-downloads/xq_v40_findability_review_v41.md
docs/support/xq_v42_source_tail_100_review_v43.md
```

Core update:

```text
When active parents are stable and repeated descent passes have low official
yield despite local-green reference probes, stop generic descent. Compile the
remaining tail by findability source before generating more probes or patches.

When the residual tail is localized to host-library, source-root fixture,
golden-corpus, or target-substrate compatibility, source-tail escalation may be
authorized only as a labeled evidence-posture change, with witness separation,
prior-gate preservation, and non-laundering.

Low-yield closing passes are not waste. They are explicit saturation probes.
They measure whether the current evidence layer still has productive descent
remaining, and they authorize official eval or evidence-layer switching when
active owners remain stable and marginal yield collapses.
```

The `sibprogrammer__xq.b89f681` v40-v42 sequence is the evidence anchor:

```text
v40 targeted microgrammar pass:
  added probes: 40
  local v40 gate: 40 / 40
  prior gates preserved: v35 176 / 176, v36 32 / 32, v39 33 / 33
  official result: score 88, 782 passed / 95 failed / 2 skipped
  official delta from v39: +1 row, 0 regressions

v41 blind-findability Path A:
  local v41 gate: 49 / 49
  prior gates preserved: v35 176 / 176, v36 32 / 32, v39 33 / 33, v40 40 / 40
  official result: score 89, 784 passed / 93 failed / 2 skipped

v42 source-tail Path B:
  evidence posture: source_tail + fixture_corpus_tail + host_library_equivalence
  prior gates preserved: v35 176 / 176, v36 32 / 32, v39 33 / 33, v40 40 / 40, v41 49 / 49
  official result: solved, 876 passed / 0 failed / 3 skipped / 879 total
```

Interpretation:

```text
parent activated
  -> representative probes generated
  -> local gates green
  -> terminal official leaves still open

then:
  -> evidence-source classification authorizes source-tail only for localized
     host-library / fixture-corpus / target-substrate tails
  -> source-tail witness preserves prior blind/public gates
  -> official tail closes without relabeling source-derived facts as blind
     evidence
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

## 7B. `LOW_YIELD_CLOSING_PASS_AS_SATURATION_PROBE`

Trigger:

```text
The reconstruction has already produced a high-confidence ontology and one or
more large-gain implementation/probe loops, but uncertainty remains about
whether the current evidence layer still contains blind/publicly findable
leaves.
```

Purpose:

```text
Run a bounded closing pass precisely to measure marginal yield, not because the
orchestrator expects a large solve jump.
```

Required row:

```yaml
low_yield_closing_pass:
  base_run_ref: string
  pass_ref: string
  pass_kind:
    salience_adversary |
    descent_completeness |
    targeted_microgrammar |
    public_reference_matrix |
    other
  active_owner_nodes_before: []
  active_owner_nodes_after: []
  probes_added: int
  local_gate_green: true | false
  official_or_reference_delta:
    passed_delta: int
    failed_delta: int
    regression_count: int
  marginal_yield_status:
    productive |
    low_yield |
    saturated |
    inconclusive
  authorized_next_step:
    continue_same_layer |
    official_eval |
    evidence_layer_switch |
    theory_upgrade_audit
  rationale: string
```

Rules:

```text
A low-yield closing pass is valid evidence about method saturation only if it
preserves prior gates or records regressions explicitly.

If active owner nodes remain stable, local gates are green, regressions are zero
or explained, and marginal official/reference yield is low across one or two
closing passes, the orchestrator should stop repeating the same pass type.

The next step after saturation is either official eval or an explicitly
authorized evidence-layer switch. It is not unbounded probe inflation.
```

Post-eval use:

```text
If post-eval failures remain after a saturation-triggered eval, classify them
by derivability:

derivable_by_better_GPO:
  promote general ontology gap.

derivable_by_better_meta_program:
  promote transition/gate/procedure gap.

derivable_by_better_public_probe_design:
  promote probe-construction rule.

source_or_corpus_identity_tail:
  label as source_tail / fixture_corpus_tail / host_library_equivalence.

substrate_or_evaluator_tail:
  label as target_substrate / observation_ecology / evaluator_artifact.
```

Non-laundering rule:

```text
The closing pass establishes saturation posture. It does not make later
source-tail or post-eval facts retroactively blind/pre-eval evidence.
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

## 9. `SOURCE_TAIL_ESCALATION_AUTHORIZATION_GATE`

Trigger:

```text
high-score tail remains after salience, descent, targeted microgrammar, and
findability gates;
remaining owners are known;
public/reference probes have saturated or have demonstrably low marginal yield;
residual rows require host-library, source-root fixture, official-corpus, or
target-substrate parity.
```

Required row:

```yaml
source_tail_escalation:
  triggering_run_ref: string
  prior_blind_gates_green: []
  remaining_tail_count: int
  known_owner_nodes: []
  public_findability_status:
    saturated | still_blind_findable | mixed
  requested_evidence_source:
    - source_tail
    - fixture_corpus_tail
    - host_library_equivalence
    - target_substrate_dependency
  non_laundering_statement: string
  allowed_scope: []
  forbidden_use: []
  posture:
    blocked | authorized_source_tail | authorized_fixture_corpus | mixed
```

Blocking rule:

```text
Source-tail access is not authorized merely because official score is below
100. It is authorized only when the residual tail has been localized and
blind/public methods are saturated or explicitly lower-yield for the owner.
```

## 10. `HOST_LIBRARY_EQUIVALENCE_WITNESS_EXTENSION`

Trigger:

```text
behavior depends on parser, selector, renderer, serializer, query engine,
codec, formatter, terminal library, database driver, shell, OS library, or
other target dependency.
```

This extends section 4 with a witness row for the tail stage.

Required row:

```yaml
host_library_equivalence:
  behavior_owner: string
  target_library_or_dependency: string
  public_probe_coverage: []
  source_tail_evidence: []
  target_substrate_build_evidence: []
  divergence_from_local_heuristic: []
  equivalence_status:
    public_approximation | source_tail_required | equivalent | incompatible | deferred
```

Rule:

```text
At tail stage, replacing a host library with heuristic reimplementation is not
closed unless the heuristic is proved equivalent on the active corpus and
microgrammar axes.
```

## 11. `FIXTURE_CORPUS_PARITY_TAIL_EXTENSION`

Trigger:

```text
remaining rows compare against golden files, corpus fixtures, branch test/data,
source-root examples, or realistic morphology distributions not reproduced by
synthetic atoms.
```

This extends section 3 with a tail-stage corpus row.

Required row:

```yaml
fixture_corpus_parity:
  corpus_ref: string
  owner_nodes: []
  corpus_morphology_axes: []
  synthetic_probe_gap: string
  source_or_branch_fixture_refs: []
  parity_status:
    not_started | partial | green | skipped_rows_documented
```

Rule:

```text
Formatter, serializer, parser-recovery, and route tails cannot be declared
gold-closed from atom probes if the official corpus includes morphology
combinations not represented by those atoms.
```

## 12. `SOURCE_TAIL_WITNESS_SEPARATION_GATE`

Trigger:

```text
source-tail implementation diverges from a prior blind or public-only
candidate.
```

Required row:

```yaml
source_tail_witness_separation:
  blind_witness_ref: string
  source_tail_witness_ref: string
  shared_probe_gates_preserved: []
  changed_authority_layer: true
  allowed_backport_to_blind_schema:
    - method_gate
    - owner_mapping
    - findability_rule
    - evidence_source_rule
  forbidden_backport_to_blind_schema:
    - source-derived expected bytes
    - source-derived hidden fixture facts
    - direct implementation-specific shortcuts
```

Rule:

```text
A source-tail witness can solve the task and improve future method, but its
source-derived facts must not be relabeled as blind reconstruction evidence.
```

## 13. `BUILD_FLOOR_ADAPTATION_GATE`

Trigger:

```text
upstream/source-tail witness requires dependency, language, module, package,
runtime, or ABI-floor changes to compile in the target cleanroom.
```

Required row:

```yaml
build_floor_adaptation:
  upstream_witness_ref: string
  target_substrate_ref: string
  changed_files_or_manifest: []
  semantic_change_claim:
    none | bounded | behavior_affecting
  compile_proof: string
  smoke_proof: string
  dependency_vendor_or_pin_status: string
```

Rule:

```text
Build-floor adaptation is allowed only if separated from product-semantic
repair and proven in the target substrate.
```

## 14. Readiness Vocabulary Update

Add or strengthen these statuses:

```text
blind_path_saturated:
  remaining tail has known owners and repeated blind/public probes have low
  marginal yield.

source_tail_authorized:
  source-tail access is methodologically allowed for specific owners.

fixture_corpus_tail:
  exact behavior is tied to source/branch fixture morphology or golden files.

host_library_equivalence_tail:
  exact behavior is determined by target library semantics rather than by a
  compact task-native heuristic.

source_tail_solved:
  source-tail witness solves the task while preserving prior locked gates.

not_blind_evidence:
  fact may update future gates but cannot be reported as clean first-pass
  reconstruction truth.
```

## 15. Structured Document Transform CLI Tail Obligations

Keep the existing structured-document obligations:

```text
control token grammar and aliases
document resource route topology
input format role directionality
selector/expression sublanguage
selected-node identity and tree preservation
in-place mutation lifecycle
formatter / renderer byte grammar
parse-recovery and diagnostic precedence
terminal/color/pager ecology
ambient config topology
adversarial pre-eval governance
```

Add tail-stage obligations:

```text
host-library selector equivalence
host-library parser/recovery equivalence
formatter corpus parity
source-root fixture topology
golden-file morphology distribution
library-vs-heuristic replacement proof
build-floor adaptation
source-tail witness separation
```

## 16. Generalized Phase Ladder Update

The finalized xq ladder should be available for future structured-document
tasks:

```text
P1A  blind task-native ontology
P1B  GPO projection
P1C  utility / intent projection
P1D  reciprocal ontology diff
P1E  merged activation and inherited obligations

P2   public scout
P2B  scout observation audit
P2C  salience / omission adversarial gate

P3   locked probe contract
P3B  representative manifest red-team gate
P3C  descent-completeness closure-matrix gate
P3D  optional second descent squeeze if yield remains high
P3E  bounded closing pass as saturation probe

P4   implementation handoff
P5   local green
P5B  witness-shape audit
P5C  closure-matrix local gate

P6   official-readiness authorization
P7   official eval experiment
P8   post-eval pressure audit
P9   tail findability and evidence-source gate

Path A:
  further blind/public microgrammar if still findable

Path B:
  source-tail / fixture-corpus / host-library equivalence if blind path saturated

P10  source-tail witness separation and prior-gate preservation
P11  target-substrate build-floor adaptation proof
P12  official source-tail eval
P13  non-laundering closeout and schema update
```

## 17. Evidence-Layer Selection Rule

Not every remaining failure is findable at the same evidence layer:

```text
omission tail:
  salience adversary

under-descended parent:
  closure matrix descent

microgrammar tail:
  targeted public/reference matrix

corpus/library tail:
  source-tail / fixture-corpus / library equivalence

substrate tail:
  target dependency/build-floor proof
```

The mature orchestrator should select the evidence source appropriate to the
tail instead of repeating the previous pass type after marginal yield saturates.
