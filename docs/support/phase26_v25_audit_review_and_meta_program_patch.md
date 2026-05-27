# Phase 26 Audit Review + v25 Meta-Program Patch

Authority layer: `audit_of_post_eval_pressure_synthesis`.

Input under review: `phase26_remaining_failure_and_regression_audit.md`.

## 1. Verdict

The Phase 26 audit is directionally correct and stronger than the previous audit style. It does three things well:

1. It proves the v24 Batch 1 resource-pipeline repair was a real method gain rather than a local reshuffle.
2. It identifies the six regressions as shared owner-impact failures, not random losses.
3. It removes the previous unclassified residual by manually assigning the remaining failures to concrete method families.

The score movement is meaningful:

```text
previous: 1031 passed / 371 failed / 1 skipped / 1403 total, score 72
current:  1120 passed / 282 failed / 1 skipped / 1403 total, score 79
delta:    +95 newly passing rows, -6 regressions, +89 net passed rows
```

The important interpretation is:

```text
v24 Batch 1 worked because it repaired the upstream resource-to-language pipeline.
The remaining pressure has shifted away from resource-pipeline closure and toward
sublanguage terminalization, row-shape semantics, and mode-as-program topology.
```

So this is not a failed run. It is the first clean example in this sequence where the method both improves broad behavior and leaves a relatively crisp next frontier.

## 2. Main correction to the audit

The audit says the next largest gain is dialect/sublanguage descent. That is true, but too broad for a worker handoff.

The actual next frontier should be split into four enforceable layers:

```text
A. conservation repair for the six regressions
B. target-substrate dependency equivalence for codecs
C. clean sublanguage closure, starting with TBLN
D. cross-cutting row/value-domain lattice across JSON/YAML/JQ/delimited readers
```

`DIALECT_SUBLANGUAGE_TERMINALIZATION_MATRIX = 169` is not a worker task. It is a compilation target. It must be lowered into separate numbered subtrees before implementation.

## 3. Regression diagnosis

The six regressions are all caused by patches that widened an implementation owner without proving sibling contexts.

### R1. SQL relation-token overreach

The relation-binding patch solved comma joins, but it treated any comma-adjacent token as a possible resource token. That imported relation-list behavior into projection-list and quoted-identifier contexts.

The missing discriminator is:

```text
relation-list resource token
  != projection-list expression token
  != quoted identifier token
  != quoted resource literal
  != arithmetic expression token
```

This is not just a SQL bug. It is a meta-program miss:

```text
binder expansion was accepted without contextual tokenizer confinement.
```

### R2. Empty-query fatal gate regression

Multi-statement execution made the empty query case look like a valid zero-statement execution. The missing discriminator is:

```text
empty query as fatal input
  != statement list with zero result rows
  != multi-statement execution whose last statement has no rows
```

This belongs to the fatal gate lattice and mode dispatch, not renderer logic.

### R3. Blank row vs empty field regression

Blank-row filtering erased a meaningful one-column empty field under `-inull ""`. The missing discriminator is:

```text
blank physical line
  != empty record
  != one-column empty field
  != missing cell after delimiter
  != null-token-converted value
```

This should not be a one-off sentinel. It should become a global row-universe lattice applied to every reader that can produce rows.

## 4. v25 meta-program additions

### 4.1 `CONTEXTUAL_TOKENIZER_SCOPE_GATE`

Trigger:

```text
Any patch broadens a tokenizer, parser, binder, selector, SQL rewriter,
resource matcher, CLI token binder, or embedded-language recognizer.
```

Required row:

```yaml
contextual_tokenizer_scope:
  tokenizer_or_binder_ref: string
  broadened_token_or_pattern: string
  allowed_contexts: []
  forbidden_contexts: []
  quote_escape_comment_states: []
  nesting_states: []
  adjacent_operator_states: []
  positive_sentinel_refs: []
  negative_context_sentinel_refs: []
  owner_impact_cone_refs: []
  closure_status: blocked | scoped_ready | gold_ready
```

Rule:

```text
A widened tokenizer/binder patch cannot be accepted until every adjacent grammar
context sharing the widened token has either a negative sentinel or an explicit
irrelevance proof.
```

For `trdsql`, this means any SQL resource-binder patch touching commas must prove at least:

```text
FROM/JOIN relation-list comma            -> resource-binding allowed
SELECT projection-list comma             -> resource-binding forbidden
function argument comma                  -> resource-binding forbidden unless relation grammar says otherwise
quoted identifier containing keyword     -> resource-binding forbidden
quoted resource path in relation context -> resource-binding allowed
arithmetic expression around comma       -> expression semantics preserved
```

### 4.2 `PATCH_IMPACT_CONE_SENTINEL_COMPILER`

Trigger:

```text
A patch touches a shared owner such as sql_resource_binder, source_router,
reader_registry, value_normalizer, renderer_registry, mode_dispatch,
or diagnostic_emitter.
```

Required output:

```yaml
patch_impact_cone:
  touched_owner: string
  changed_rule: string
  upstream_nodes: []
  downstream_consumers: []
  old_green_leaf_refs: []
  new_target_leaf_refs: []
  sibling_context_refs: []
  required_preservation_sentinels: []
  local_gate_status: blocked | green | scoped_green
```

Rule:

```text
The orchestrator must synthesize preservation sentinels from shared owner impact,
not only from the parent failure bucket being repaired.
```

This would have imported arithmetic SELECT, quoted identifiers, empty query, and `-inull ""` before the Batch 1 patch was accepted.

### 4.3 `TARGET_DEPENDENCY_EQUIVALENCE_GATE`

Trigger:

```text
Any behavior passes through an optional Python module, external binary,
codec helper, shell tool, OS facility, locale, DB driver, or runtime extension.
```

Required row:

```yaml
target_dependency_equivalence:
  dependency_ref: string
  dependency_kind: python_module | external_binary | codec_helper | db_driver | os_facility | shell_tool
  local_probe_status: pass | fail | not_run
  target_substrate_probe_status: pass | fail | not_run
  fallback_available: true | false
  bundled_or_pinned: true | false
  official_posture: proven_equivalent | scoped_local_only | blocked | deferred_with_risk
```

Rule:

```text
Local green is not official posture for optional dependencies.
The dependency must be proven inside the target evaluator substrate or replaced
with a portable/bundled fallback.
```

For this run, zstd is not primarily a product ontology failure. It is an equivalence failure until the target substrate confirms `zstandard`, a `zstd` helper, or a portable fallback.

### 4.4 `SUBLANGUAGE_CLOSURE_COMPILER`

Trigger:

```text
A public format, selector, renderer, mini-language, query dialect, or structured
format has its own syntax/value/error rules.
```

Required row:

```yaml
sublanguage_closure:
  sublanguage_ref: TBLN | jq | JSON | YAML | LTSV | width | raw | markdown | other
  grammar_axis_refs: []
  value_domain_axis_refs: []
  identity_binding_axis_refs: []
  transform_axis_refs: []
  error_axis_refs: []
  input_to_sql_axis_refs: []
  output_byte_axis_refs: []
  reference_probe_matrix_ref: string | null
  source_postmortem_needed: true | false
  implementation_ready: true | false
```

Rule:

```text
A sublanguage name is not an implementation target. It must be compiled into a
closure matrix first.
```

This gate should treat TBLN and jq differently:

```text
TBLN:
  most likely needs empirical reference capture and/or source postmortem because
  the exact metadata/type/header/data-row grammar is not semantically obvious.

jq:
  ontology and utility descent can force it as an embedded transform language,
  but exact grammar breadth needs reference or source evidence.
```

### 4.5 `ROW_UNIVERSE_VALUE_SHAPE_LATTICE`

Trigger:

```text
Any reader can emit rows and any option can skip, limit, number, null-map,
header-map, blank-filter, or infer row shape.
```

Required lattice:

```text
physical line states:
  absent file
  empty file
  blank line
  whitespace line
  delimiter-only line
  trailing delimiter
  leading delimiter
  one-column empty field
  missing cell
  extra cell
  sparse record
  header-only file
  data-only file
  header + zero data rows

semantic value states:
  empty string
  missing value
  null token
  null after -inull
  null before output -onull
  numeric-looking string
  boolean-looking string
  binary/non-UTF8 value
  nested array/object value
```

Rule:

```text
Reader repairs must preserve this lattice across all active formats. A patch may
not collapse blank-line filtering, null conversion, empty-field semantics, and
row skipping into one rule.
```

## 5. Review of remaining buckets

### TBLN: next clean high-yield target

The audit is right that TBLN is the largest clean subtree. It has 53 remaining rows and splits into input grammar, output grammar, column identity binding, and invalid grammar diagnostic. This should be the next conceptual batch after conservation and dependency gates.

Required pre-patch probes:

```text
metadata rows
type rows
header rows
data rows
sparse rows
null/empty cells
column identity and quoting
input-to-SQL table binding
TBLN output byte grammar
invalid TBLN diagnostic/exit/channel
```

Do not patch TBLN from official rows alone. Run reference capture first. If reference capture still leaves ambiguity, escalate to source-postmortem as `source_derived_operator_discovery` rather than laundering source details into first-pass evidence.

### JSON/YAML/JQ: linked but not one batch

These are related by value-domain and projection, but they should not be one implementation batch.

Split into:

```text
JSON/YAML value-domain matrix:
  scalar / object / array / nested / mixed / null / binary / unicode / malformed

jq embedded transform matrix:
  array iteration / object construction / indices / recursive descent /
  multiple filters / rename transforms / error semantics

JSON/YAML output byte matrix:
  escaping / unicode / null / binary / nested rehydration / final newline
```

The same owners are shared across all three:

```text
reader_registry
value_normalizer
jq_transformer
sqlite_importer
renderer_registry
```

So each sub-batch must import preservation sentinels for the others.

### Config/DB mode topology

The audit is right to defer this until after dialect pressure stabilizes. Config/DB touches too many shared owners:

```text
mode_dispatch
config_loader
db_connection_manager
sqlite_executor
diagnostic_emitter
renderer_registry
```

It should be treated as `MODE_AS_PROGRAM`, not as a few passive flags.

## 6. Methods that would have discovered each issue earlier

| Issue | Earliest discoverable layer | Best triangulation axis | Method that would have caught it |
|---|---:|---|---|
| SELECT-list comma regression | L7 -> L8 implementation transfer | implementation owner + grammar context | `CONTEXTUAL_TOKENIZER_SCOPE_GATE` with negative context sentinels |
| Empty-query regression | L7 -> L8 implementation transfer | fatal precedence + mode dispatch | `PATCH_IMPACT_CONE_SENTINEL_COMPILER` + empty-query sentinel |
| `-inull ""` regression | L7 -> L8 implementation transfer | row universe + value normalization | `ROW_UNIVERSE_VALUE_SHAPE_LATTICE` preservation sentinel |
| zstd failures | E3/E4/E5 methodology equivalence | target substrate / dependency ecology | `TARGET_DEPENDENCY_EQUIVALENCE_GATE` |
| TBLN residual | L4 -> L2, then L2 -> L3 | public schema + empirical reference + possible source-postmortem | `SUBLANGUAGE_CLOSURE_COMPILER` / `TBLN_AS_SUBLANGUAGE_GATE` |
| jq residual | L1 -> L2, L4 -> L2, L2 -> L3 | ontology + utility + empirical reference | `JQ_AS_EMBEDDED_TRANSFORM_SUBLANGUAGE` |
| input row-shape residual | L2 -> L3 | ontology + dialect empirical + negative utility | `ROW_UNIVERSE_VALUE_SHAPE_LATTICE` |
| config/db residual | L4 -> L2 | public schema + mode-as-program + negative utility | `MODE_AS_PROGRAM_MATRIX` |
| analyze residual | L4 -> L2 | utility + public schema + byte observation | analyze as independent report program |
| output renderer residual | L2 -> L3 / L3 -> L4 | output/downstream projection + reference byte grammar | renderer byte matrix |

## 7. v25 orchestration sequence

### Batch 0: conservation repair only

Purpose:

```text
restore six regressions without opening new conceptual surfaces.
```

Required sentinels:

```text
SQL context:
  SELECT c1, c2
  SELECT c1*2
  SELECT "c2"
  SELECT "FROM"
  FROM a, b
  JOIN resource
  quoted resource path in FROM/JOIN

Fatal gate:
  empty query
  whitespace-only query
  semicolon-only query
  multi-statement with last SELECT

Row universe:
  blank physical line
  trailing blank line
  one-column empty field
  delimiter-only row
  -inull "" conversion
```

No official eval from this alone unless all Batch 1 resource-pipeline sentinels remain green.

### Batch 1: target-substrate codec equivalence

Purpose:

```text
turn codec support from local capability into target-substrate proof.
```

Required target-image probes:

```text
gzip input/output
bzip2 input/output
xz input/output
lz4 input/output
zstd input/output
explicit -oz overrides extension
extension guessing vs -out-without-guess
mixed compressed/uncompressed wildcard, if still in scope
```

Allowed implementation outcomes:

```text
portable implementation
bundled dependency
proven helper path
explicit deferral with expected official risk
```

### Batch 2: TBLN sublanguage

Purpose:

```text
close the largest clean conceptual subtree.
```

Do this only after a reference-capture matrix exists.

### Batch 3: JSON/YAML value domains + jq transform

Purpose:

```text
separate value-domain terminalization from transform-language terminalization.
```

Do not hand this as one giant dialect task. Split into JSON/YAML value rows, jq transform rows, and output byte rows.

### Batch 4: config/db/analyze mode-as-program

Purpose:

```text
model configuration, DB drivers, db list, debug, persistent DB, and analyze as
mode/resource/report programs.
```

This comes after row/dialect stabilization because it shares the reader, value, SQL, renderer, and diagnostic owners.

## 8. v25 bookkeeper rejections

Reject a worker report if it says any of the following without the required gate evidence:

```text
fixed SQL resource binder
fixed dialect matrix
fixed TBLN
fixed jq
fixed compression
fixed row-shape semantics
fixed config/db
```

Require narrowed claims:

```text
closed 5.2.4 relation-list resource binding under FROM/JOIN contexts;
projection-list comma and quoted-identifier sentinels remain green.

closed TBLN metadata/header/data sparse-row input grammar;
TBLN output byte grammar remains scoped.

closed zstd via bundled fallback in target substrate;
local-only zstandard support no longer counts as evidence.
```

## 9. Bottom line

Phase 26 is a real success: score 72 -> 79 with only six regressions. The next meta-program improvement is not another broad repair rule. It is stricter enforcement of context-local tokenization, target-dependency equivalence, and sublanguage closure before implementation.

The v25 one-line rule:

```text
A repair that broadens a shared owner must prove its grammar context, dependency
substrate, and sibling preservation before it is allowed to count as a parent
closure.
```
