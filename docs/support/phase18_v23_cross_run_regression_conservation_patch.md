# Phase 18 Audit Review: Why Axis Wins Regress Other Axis Wins

Authority layer: post-eval pressure synthesis and meta-program patch proposal.

This note reviews the current run-vs-history comparison and diagnoses why recent
runs improve on some semantic axes while losing earlier wins on other axes. It
then proposes a v23 meta-program patch focused on cross-run semantic
preservation, orthogonal-pool triangulation, and regression-conserving
implementation handoff.

## 1. Immediate read of the comparison

The current run is best interpreted as a valid **methodology repair** but not as
a product-compatibility closeout:

```text
current run: trdsql_v20_guard_replay_high_iter3
posture:     method_test
score:       66
raw rows:    956 passed / 446 failed / 1 skipped / 1403 total
```

The current run is explicitly not gold-ready: its visible-regression gate was
only `35 / 53`, the sealed sibling gate was `9 / 10`, and it was authorized as a
method test, not as a gold handoff.

The comparison shows three different phenomena that must not be collapsed:

1. **v20 guard vs v20 replay-collapse**

   ```text
   won: 895
   lost: 6
   net: +889
   ```

   This proves the anti-replay / orchestration guard worked. The official suite
   now sees a broad generative program rather than a finite manifest replay
   witness.

2. **v20 guarded vs v19 phase11**

   ```text
   won: 370
   lost: 64
   net: +306
   ```

   This proves the guarded v20 mechanism generalizes better across query,
   renderer, input, wildcard, and extended reader surfaces. But it loses analyze
   and CLI exactness.

3. **v20 guarded vs best HOB phase21**

   ```text
   won: 41
   lost: 133
   net: -92
   ```

   This proves the iterative HOB chain still owns many exactness leaves better:
   analyze/report mode, CLI/argparse, config/db topology, diagnostics, TBLN/YAML,
   renderer byte grammar, and output option edge cases.

The current run therefore moved the witness class in the right direction but did
not preserve all previous product-compatibility owners.

## 2. Root cause

The root cause is **not** simply that one model/run was better or worse.

The root cause is:

```text
semantic discovery axes were treated as alternative implementation programs,
not as partial leaf owners in one persistent obligation tree.
```

Different tracks discovered and repaired different parts of the program:

```text
HOB iterative chain:
  stronger on exact compatibility and regression conservation.

Intent / utility branch:
  stronger on user-job discovery and affordance-level behavior families.

v20 guarded branch:
  stronger on anti-replay, broad generative behavior, and query/resource/input
  generalization.
```

But the orchestrator did not force a **cross-run semantic merge** before the
next implementation handoff. As a result, the worker received a bounded target
that improved new axes but was not required to preserve the best-known leaves
from older axes.

### More precise causal chain

```text
post-hoc audit identifies a parent discriminator
  -> worker operationalizes a bounded implementation slice
  -> slice improves that axis
  -> shared code paths also affect neighboring axes
  -> old green leaves are not imported as hard preservation obligations
  -> regressions appear in analyze / CLI / config / renderer exactness
```

This is not accidental. In `trdsql`, most axes share implementation surfaces:

```text
CLI parse / mode dispatch
  affects help, analyze, config, ordinary query, error precedence.

source router / reader registry
  affects SQL binding, analyze, input dialects, resource routes, wildcard,
  compression, diagnostics.

value normalizer
  affects JSON/YAML/TBLN, SQL aggregates, raw output, JSON output, null policy.

renderer registry
  affects query output, analyze output, golden output formats, output-file
  guessing, diagnostics.

config/db substrate
  affects ordinary query, debug, analyze examples, driver quoting, db list,
  persistent state, error behavior.
```

So the semantic pools are orthogonal as **discovery lenses**, but not orthogonal
as **implementation effects**.

## 3. What the comparison specifically proves

### 3.1 The replay failure was real and is now largely repaired

The original v20 high run had a locally green gate but collapsed to score `2`;
the official summary classified the dominant class as `1268` failures returning
`rc 127` for unlisted argv shapes, with only visible manifest-like cases passing.
That was a probe-replay witness, not a program witness.

The guarded run moving to score `66` proves that anti-replay/orchestration
changed the witness type. This is a method win.

### 3.2 The current run does not preserve exactness ownership

The current failure topology is now mostly:

```text
analyze/report modes
CLI/argparse edge behavior
extended reader/writer surfaces
config/db topology
renderer exactness
diagnostic exactness
```

Against HOB phase9, the current run wins on wildcard/advanced/ext-reader
surfaces but loses on analyze/CLI/config/TBLN exactness. Against HOB phase21, the
same losses dominate, and the current run is `-94` passed rows behind the best
comparable HOB result.

This means the current run improved **breadth of mechanism** while losing
**compatibility exactness overlays**.

### 3.3 HOB was better at preserving prior leaves

The Phase 15 HOB comparison improved from score `67` to `72` with only `2`
regressions:

```text
fixed tests: 82
persistent failures: 367
new regressions: 2
net failure delta: -80
```

That is the signature of a regression-conserving loop. It did not solve all
families, but it preserved more of what it already owned.

### 3.4 The second track was useful but not safe alone

The intent/utility lane generated real wins: 52 Phase9 failures became passes,
concentrated in user-job semantics such as CLI discovery, input shaping,
structured JSON/JQ, SQL over resource-bound files, path/resource utility, and
raw downstream output. But the same audit recorded 361 regressions over Phase9
passes.

That is exactly the signature of a discovery pool that is useful for finding
new discriminators but unsafe when used as a direct implementation axis without
merge and preservation gates.

## 4. Deeper abstraction: discovery orthogonality is not implementation orthogonality

The current meta-program uses orthogonal semantic pools:

```text
P = program mechanism
U = user utility
S = public schema
R = resource topology
D = data dialect/value grammar
T = transform/embedded language
O = output/downstream consumer
N = negative utility/failure precedence
E = methodological equivalence
H = historical delta/regression conservation
```

This is good for discovery. But the implementation must know when two pools
share a code owner.

The missing distinction is:

```text
semantic-pool independence
  !=
implementation-effect independence
```

A pool is independent if it can propose obligations without reading another
pool. A patch is independent only if its implementation impact cone does not
alter another pool's owned leaves, or if all affected leaves are regression
checked.

This is the central v23 patch.

## 5. Proposed v23 meta-program additions

### V23.1 Cross-run semantic delta ledger

Before any implementation handoff, the orchestrator must compile a run-to-run
semantic delta ledger:

```yaml
cross_run_delta_row:
  eval_row_id: string
  test_namespace: string
  previous_run_status: pass | fail | skip | unknown
  current_run_status: pass | fail | skip | unknown
  delta_class: persistent_pass | new_win | regression | persistent_failure
  previous_owner_run: string | null
  current_owner_run: string | null
  hob_node_ref: string | null
  semantic_pool_refs: []
  implementation_owner_refs: []
  evidence_authority: post_eval_pressure | local_locked | reference_locked
```

The key product is not just score delta. It is:

```text
which semantic leaves each run appears to own.
```

### V23.2 Win-owner registry

Every previously solved leaf gets a preservation owner:

```yaml
win_owner_row:
  leaf_ref: string
  best_known_owner_run: string
  best_known_evidence_refs: []
  owned_surface:
    stdout | stderr | exit | file | resource | mode | renderer | diagnostic
  semantic_family: string
  implementation_owner: string
  preservation_status:
    must_preserve | may_defer_scoped | conflict_isolated | obsolete_by_better_rule
  sentinel_probe_refs: []
```

No new implementation batch may proceed until every `must_preserve` leaf in the
patch impact cone has a sentinel.

### V23.3 Implementation impact cone gate

Every planned patch must declare what it can affect:

```yaml
patch_impact_cone:
  patch_batch_ref: string
  touched_code_owners:
    - cli_parser
    - mode_dispatch
    - source_router
    - input_importer_registry
    - sql_binder
    - sqlite_executor
    - value_normalizer
    - renderer_registry
    - analyze_renderer
    - config_db_topology
    - diagnostic_emitter
  affected_hob_nodes: []
  affected_semantic_pools: []
  preserved_leaf_sentinels: []
  non_commutation_risks: []
  status: clear | requires_more_sentinels | blocked
```

If a patch touches `source_router`, it must regression-check analyze, ordinary
query, wildcard, compression, path identity, and diagnostics. If it touches
`renderer_registry`, it must regression-check query renderers, analyze renderers,
raw/TBLN/YAML/Markdown/ASCII/vertical surfaces, and output-file routing.

### V23.4 Discovery-pool vs implementation-pool separation

Semantic pools should remain independent for discovery, but implementation must
run through shared owner analysis:

```text
pool output
  -> HOB node mapping
  -> implementation owner mapping
  -> impact cone
  -> preservation sentinels
  -> patch
```

The forbidden shortcut is:

```text
pool output
  -> patch
```

### V23.5 Regression conservation as a transition precondition

The current run already exposed this issue: visible-regression gate `35 / 53`
was enough for a method test but not enough for product readiness.

v23 should make the distinction hard:

```text
method_test_authorization:
  allowed with incomplete visible-regression gate, but result cannot be compared
  as product progress without regression accounting.

product_repair_authorization:
  blocked unless visible-regression gate is green for every must-preserve leaf
  in the patch impact cone.

gold_attempt_authorization:
  blocked unless all visible, sealed, metamorphic, and historical preservation
  sentinels are green or explicitly deferred with expected risk.
```

### V23.6 Non-commutative axis gate

Every pair of axes that share an implementation owner must be treated as
potentially non-commuting:

```yaml
axis_commutation_row:
  axis_a: SQL_RESOURCE_BINDER
  axis_b: ANALYZE_REPORT_MODE
  shared_owner: source_router | input_importer_registry | value_normalizer
  predicted_commutes: true | false | unknown
  required_sentinel_refs: []
  observed_result: commuted | regressed_a | regressed_b | conflict
```

This prevents the model from assuming that a better SQL/resource route patch
will automatically preserve analyze/report output.

### V23.7 Compatibility overlay model

The implementation architecture should be forced to separate:

```text
mechanism core:
  resource routing, input decoding, SQL execution, value normalization.

compatibility overlays:
  Go flag wording, help text, analyze examples, tablewriter spacing,
  renderer byte grammars, config/db diagnostics, exact stderr/stdout split.
```

Many current losses look like compatibility overlays were overwritten or never
imported when the mechanism core was generalized.

v23 should require an explicit row:

```yaml
compatibility_overlay_row:
  overlay_ref: string
  base_mechanism_ref: string
  surface: help | analyze | renderer | config | diagnostic | output_option
  exactness_contract_refs: []
  can_be_approximated: false
  sentinel_refs: []
```

### V23.8 Cross-run merge handoff

Before implementation, the orchestrator should construct a merged target:

```text
Target Ω* for next run =
  current best generative mechanism leaves
  + best HOB exactness leaves
  + second-track utility-discovered leaves
  + explicit deferrals/conflicts
```

The worker should not be asked to implement “v20” or “HOB” or “intent track”. It
should be asked to implement a numbered merge target with preservation
sentinels.

## 6. Root-cause taxonomy for the observed regressions

### A. New core mechanism overwrote exact mode behavior

Likely affects:

```text
analyze/report mode
CLI/argparse
config/db diagnostics
TBLN/YAML/renderers
output option exactness
```

Pattern:

```text
generalized parser/router/renderer
  -> branch reaches broader query/input behavior
  -> mode-specific exact bytes or diagnostic precedence lost
```

### B. Old exactness leaves were not imported into the new local gate

Pattern:

```text
best prior run owned leaf X
new run did not include X as a must-preserve sentinel
worker patched another family
X regressed silently until official eval
```

### C. Semantic pool insight became implementation pressure without owner merge

Pattern:

```text
utility or mechanism pool finds new user-job family
patch implements new affordance
shared implementation owner changes old family
no commutation proof / no regression sentinel
```

### D. Representative patches were mistaken for macro closure

Pattern:

```text
fix one gzip route, one wildcard route, one raw output route
claim resource/output family improved
unprobed siblings still open or regress
```

### E. Method-test evidence was compared like product-readiness evidence

The current run is explicitly a method test. It should be credited for fixing the
replay witness class, but product comparisons must account for the incomplete
visible-regression gate.

## 7. Recommended next sequence

Do not start with code repair. Start with cross-run semantic merge.

### Batch 0: differential merge board

Inputs:

```text
current guarded v20 run
best HOB phase21 run
HOB phase9 baseline
v19/v20 second-track wins
Phase16/HOB regression sentinel list
```

Outputs:

```text
cross_run_delta_ledger
win_owner_registry
implementation_owner_map
compatibility_overlay_map
must_preserve_sentinel_manifest
open_conflict_ledger
```

### Batch 1: preserve exactness overlays

Target only:

```text
analyze/report mode exactness
CLI/argparse edge behavior
config/db diagnostic topology
TBLN/YAML/renderer exactness
output option edge cases
```

But patch them as overlays on top of the current generative core, not by
reverting the core.

### Batch 2: re-run guard lattice

Required local gates:

```text
visible-regression gate: must be 53 / 53 for must-preserve leaves
sealed sibling gate: must be green for active macro families
historical HOB sentinels: green for imported exactness leaves
new current wins: green for resource/query/input leaves
anti-replay: still green
```

### Batch 3: official eval posture

If any preservation sentinel is red:

```text
posture = method_test_or_scoped_repair
```

Only if preservation and generative gates are green:

```text
posture = product_repair_attempt / gold_attempt depending on open deferrals
```

## 8. v23 one-line invariant

```text
A new semantic axis may not be optimized until the orchestrator has proven which
previously green leaves share its implementation owners and has imported those
leaves as preservation obligations.
```

## 9. Bottom line

The system is improving because each method discovers real axes. The system is
regressing because those axes are not yet merged into a persistent, numbered,
owner-aware obligation tree before implementation.

The fix is not to abandon semantic pools or return to one HOB track. The fix is:

```text
orthogonal discovery
  + deterministic HOB inheritance
  + cross-run win-owner registry
  + implementation impact cones
  + non-commutation sentinels
  + compatibility overlays
  + regression conservation as a transition gate
```

That turns run-to-run variation from a destructive competition between partial
witnesses into a constructive merge of partial leaf owners.
