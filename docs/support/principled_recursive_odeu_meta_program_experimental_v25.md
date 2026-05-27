# Principled Recursive ODEU Meta-Program Experimental v25

## Contextual Closure, Dependency Equivalence, And Sublanguage Compilation

Authority layer: support / experimental meta-program revision.

This v25 patch extends the v20 orthogonal semantic-pool method and the v23/v24
failure-coverage compiler lessons. It is based on the `trdsql` Phase 26 audit,
where the v24 Batch 1 resource-pipeline repair improved official score from
`72` to `79`, but introduced six regressions through shared-owner overreach.

Evidence boundary:

```text
This patch is post-eval-pressure-derived.
It may define future gates, worker contracts, and audit requirements.
It must not launder official-eval failures into clean first-pass evidence.
```

## 1. v25 Core Invariant

```text
A repair that broadens a shared owner must prove its grammar context,
dependency substrate, and sibling preservation before it is allowed to count as
parent closure.
```

Short form:

```text
broadened mechanism != closed behavior
local green != target-substrate proof
sublanguage name != implementation-ready task
```

## 2. Why v25 Exists

The Phase 26 `trdsql` audit showed three distinct failure classes after a
successful resource-pipeline repair:

```text
1. Contextual tokenizer overreach:
   a comma resource-binder fix for FROM/JOIN relation lists also matched SELECT
   projection-list commas and quoted column identifiers.

2. Target-substrate dependency mismatch:
   zstd probes passed locally because the local Python environment had
   zstandard, but evaluator Python 3.10 did not.

3. Sublanguage under-compilation:
   remaining failures clustered in TBLN, JSON/YAML, jq, row-shape semantics,
   config/db topology, and analyze/report mode.
```

The method error was not lack of effort. It was accepting parent closure before
the repair proved:

```text
where the widened token is legal,
what sibling contexts it must not affect,
which dependencies exist in the target substrate,
and whether a named dialect/format is actually a closed sublanguage matrix.
```

## 3. New Gates

### 3.1 `CONTEXTUAL_TOKENIZER_SCOPE_GATE`

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
A widened tokenizer/binder patch cannot be accepted until every adjacent
grammar context sharing the widened token has either a negative sentinel or an
explicit irrelevance proof.
```

For SQL resource binders, comma handling must distinguish at least:

```text
FROM/JOIN relation-list comma            -> resource binding allowed
SELECT projection-list comma             -> resource binding forbidden
function argument comma                  -> resource binding forbidden unless relation grammar says otherwise
quoted identifier containing keyword     -> resource binding forbidden
quoted resource path in relation context -> resource binding allowed
arithmetic expression around comma       -> expression semantics preserved
```

### 3.2 `PATCH_IMPACT_CONE_SENTINEL_COMPILER`

Trigger:

```text
A patch touches a shared owner such as sql_resource_binder, source_router,
reader_registry, value_normalizer, renderer_registry, mode_dispatch,
diagnostic_emitter, config_loader, db_connection_manager, or codec_router.
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
The orchestrator must synthesize preservation sentinels from shared-owner
impact, not only from the parent failure bucket being repaired.
```

This gate blocks a patch if it improves a target leaf while leaving sibling
contexts untested.

### 3.3 `TARGET_DEPENDENCY_EQUIVALENCE_GATE`

Trigger:

```text
Any behavior passes through an optional Python module, external binary,
codec helper, shell tool, OS facility, locale, DB driver, runtime extension,
filesystem feature, or environment-provided executable.
```

Required row:

```yaml
target_dependency_equivalence:
  dependency_ref: string
  dependency_kind:
    python_module | external_binary | codec_helper | db_driver |
    os_facility | shell_tool | runtime_extension | filesystem_feature
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

### 3.4 `SUBLANGUAGE_CLOSURE_COMPILER`

Trigger:

```text
A public format, selector, renderer, mini-language, query dialect, or structured
format has its own syntax, value, transform, identity, byte, or error rules.
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
  blocked_reason: string | null
```

Rule:

```text
A sublanguage name is not an implementation target. It must be compiled into a
closure matrix first.
```

Worker-handoff hard gate:

```text
Do not assign "fix TBLN", "fix jq", "fix YAML", or "fix dialect matrix".
Assign only bounded subtrees whose grammar/value/error/output axes are named
and whose reference/source warrants are explicit.
```

### 3.5 `ROW_UNIVERSE_VALUE_SHAPE_LATTICE`

Trigger:

```text
Any reader can emit rows and any option can skip, limit, number, null-map,
header-map, blank-filter, infer row shape, or widen/narrow cells.
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
Reader repairs must preserve this lattice across all active formats.
A patch may not collapse blank-line filtering, null conversion, empty-field
semantics, and row skipping into one rule.
```

## 4. v25 Orchestration Sequence

### Batch 0: Conservation Repair

Purpose:

```text
Restore regressions caused by a previous patch without opening new conceptual
surfaces.
```

Required sentinel families:

```text
contextual tokenizer:
  positive context probes for the repaired grammar location;
  negative context probes for adjacent grammar locations sharing the widened token.

fatal gate:
  empty input / empty query / whitespace-only query / semicolon-only query.

row universe:
  blank physical line / trailing blank line / one-column empty field /
  delimiter-only row / null-token conversion.
```

No official eval from Batch 0 alone unless:

```text
target batch sentinels remain green,
old preservation sentinels remain green,
and new negative-context sentinels are green.
```

### Batch 1: Target-Substrate Dependency Equivalence

Purpose:

```text
Turn local capability into target-substrate proof.
```

Required for codecs and helpers:

```text
input route in local substrate
input route in target substrate
output route in local substrate
output route in target substrate
extension guessing
explicit override
fallback/bundle proof when dependency is absent
```

Allowed outcomes:

```text
portable implementation
bundled dependency
proven helper path
explicit deferral with expected official risk
```

### Batch 2: Sublanguage Closure

Purpose:

```text
Compile a named format/selector/renderer into a bounded subtree before
implementation.
```

Start with the highest-yield clean subtree, but do not treat the subtree name as
the task. For a TBLN-like branch, compile:

```text
metadata rows
type rows
header rows
data rows
sparse rows
null/empty cells
column identity and quoting
input-to-SQL table binding
output byte grammar
invalid grammar diagnostic/channel/exit
```

### Batch 3: Value Domain And Transform Split

Purpose:

```text
Separate value-domain terminalization from transform-language terminalization.
```

For JSON/YAML/jq-like branches:

```text
JSON/YAML value-domain matrix:
  scalar / object / array / nested / mixed / null / binary / unicode / malformed

jq embedded transform matrix:
  array iteration / object construction / indices / recursive descent /
  multiple filters / rename transforms / error semantics

JSON/YAML output byte matrix:
  escaping / unicode / null / binary / nested rehydration / final newline
```

## 5. Bookkeeper Rejections

Reject worker reports that claim broad closure without gate evidence:

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
closed relation-list resource binding under FROM/JOIN contexts;
projection-list comma and quoted-identifier sentinels remain green.

closed TBLN metadata/header/data sparse-row input grammar;
TBLN output byte grammar remains scoped.

closed zstd via bundled fallback in target substrate;
local-only zstandard support no longer counts as evidence.
```

## 6. Method Selection Table

| Issue class | Earliest discoverable layer | Required v25 method |
| --- | --- | --- |
| tokenizer/binder context regression | `L7 -> L8` implementation transfer | `CONTEXTUAL_TOKENIZER_SCOPE_GATE` |
| shared-owner regression | `L7 -> L8` owner-impact transfer | `PATCH_IMPACT_CONE_SENTINEL_COMPILER` |
| optional dependency mismatch | `E3/E4/E5` equivalence transfer | `TARGET_DEPENDENCY_EQUIVALENCE_GATE` |
| named format/mini-language residual | `L4 -> L2`, then `L2 -> L3` | `SUBLANGUAGE_CLOSURE_COMPILER` |
| blank/null/row-shape residual | `L2 -> L3` | `ROW_UNIVERSE_VALUE_SHAPE_LATTICE` |
| config/db/debug/list mode residual | `L4 -> L2` | `MODE_AS_PROGRAM_MATRIX` plus dependency/resource lifecycle rows |

## 7. Handoff Posture

For future ProgramBench reconstruction runs, v25 must be applied before an
implementation handoff whenever:

```text
the patch touches a shared implementation owner;
the patch broadens token recognition;
the behavior depends on local tools or optional libraries;
the remaining branch is a named sublanguage;
the branch includes row/value shape policy.
```

If any required v25 row is missing, the handoff posture is:

```text
blocked_for_context_dependency_or_sublanguage_compilation
```
