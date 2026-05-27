# Principled Recursive ODEU Meta-Program Experimental v26

## Sublanguage Closure, Bucket Sanity, And Schema-Bearing Formats

Authority layer: support / experimental meta-program revision.

This v26 patch extends v25. It keeps the contextual-tokenizer,
target-substrate, and sublanguage-compilation gates, and adds the Phase 31
lesson: post-eval buckets can be good pressure synthesis while still being
unsafe as worker batons until each row passes bucket sanity.

This revision is based on the `trdsql` Phase 31 audit and the GPTPro
`phase31_v26_audit_review_sublanguage_closure_patch.md` review. Phase 30
reached a clean conservation baseline:

```text
current: 1127 passed / 275 failed / 1 skipped / 1403 total, score 79
vs phase25: +7 newly passing rows, -0 regressions
vs phase28: +1 newly passing row, -0 regressions
```

The remaining failure surface is dominated by public format and transform
sublanguages. The next risk is not choosing TBLN as the next subtree; that is
reasonable. The risk is handing a worker a bucket that contains stray
control-plane rows, then allowing a format repair to patch CLI/help behavior or
shared diagnostics by accident.

Evidence boundary:

```text
This patch is post-eval-pressure-derived.
It may define future gates, worker contracts, and audit requirements.
It must not launder official-eval failures into clean first-pass evidence.
```

## 1. v26 Core Invariant

```text
A repair that broadens a shared owner must prove its grammar context,
dependency substrate, and sibling preservation before it is allowed to count as
parent closure.

A post-eval bucket is not an implementation baton until its rows have passed
namespace, failure-surface, and owner sanity or been explicitly reclassified.

A public format name is not a closed behavior claim until its input grammar,
output grammar, value domain, schema binding, diagnostics, and option overlays
are terminalized or explicitly deferred.
```

Short form:

```text
broadened mechanism != closed behavior
local green != target-substrate proof
sublanguage name != implementation-ready task
classified pressure != worker-ready baton
format parser success != reader/writer/schema closure
```

## 2. Inherited v25 Basis

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

## 4. Inherited v25 Orchestration Sequence

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

| Issue class | Earliest discoverable layer | Required v26 method |
| --- | --- | --- |
| tokenizer/binder context regression | `L7 -> L8` implementation transfer | `CONTEXTUAL_TOKENIZER_SCOPE_GATE` |
| shared-owner regression | `L7 -> L8` owner-impact transfer | `PATCH_IMPACT_CONE_SENTINEL_COMPILER` |
| optional dependency mismatch | `E3/E4/E5` equivalence transfer | `TARGET_DEPENDENCY_EQUIVALENCE_GATE` |
| named format/mini-language residual | `L4 -> L2`, then `L2 -> L3` | `SUBLANGUAGE_CLOSURE_COMPILER` |
| blank/null/row-shape residual | `L2 -> L3` | `ROW_UNIVERSE_VALUE_SHAPE_LATTICE` |
| config/db/debug/list mode residual | `L4 -> L2` | `MODE_AS_PROGRAM_MATRIX` plus dependency/resource lifecycle rows |

## 7. Handoff Posture

For future ProgramBench reconstruction runs, v26 must be applied before an
implementation handoff whenever:

```text
the patch touches a shared implementation owner;
the patch broadens token recognition;
the behavior depends on local tools or optional libraries;
the remaining branch is a named sublanguage;
the branch includes row/value shape policy.
```

If any required v26 row is missing, the handoff posture is:

```text
blocked_for_context_dependency_or_sublanguage_compilation
```

## 8. v26 Additions

### 8.1 `POST_AUDIT_BUCKET_SANITY_GATE`

Purpose:

```text
Prevent post-eval classification buckets from becoming implementation batons
when their row attachments are inconsistent with namespace, failure surface, or
implementation owner.
```

Trigger:

```text
Any post-eval audit is used to form a worker task or implementation handoff.
```

Required row:

```yaml
post_audit_bucket_sanity_row:
  failure_row_ref: string
  assigned_bucket: string
  assigned_subbucket: string
  test_namespace: string
  first_failure_surface: string
  declared_owner_set: []
  expected_layer: string
  namespace_bucket_consistent: true | false
  failure_text_bucket_consistent: true | false
  owner_bucket_consistent: true | false
  corrected_bucket: string | null
  corrected_subbucket: string | null
  handoff_status:
    accepted_for_batch |
    bucket_suspect_blocked |
    reclassified_before_batch |
    deferred_manual_review
```

Blocking rule:

```text
No worker handoff may include a bucket whose rows have not passed bucket sanity
or been explicitly reclassified.
```

Control-plane residual extraction is mandatory. Rows about help, CLI aliases,
argparse, boolean flag forms, negative integer parsing, missing values,
unknown flags, or stdout/stderr/exit usage contracts must not remain hidden
under dialect, codec, TBLN, renderer, or row-shape buckets.

### 8.2 `FORMAT_SUBLANGUAGE_CLOSURE_GATE`

Purpose:

```text
A public format name cannot remain a label. When public behavior exposes the
format as input, output, SQL binding, value conversion, diagnostics, or option
overlay, each surface must descend as a child obligation.
```

Required child obligations:

```text
lexical grammar
record/row grammar
metadata/header grammar
value-domain conversion
null/empty policy
schema/column identity
SQL/resource binding
renderer byte grammar
roundtrip behavior
diagnostic/fatal grammar
option-overlay interactions
```

Closure rule:

```text
A format subtree is not closed by parser examples alone.
It closes only when input, output, binding, diagnostics, and option overlays are
covered or explicitly deferred.
```

### 8.3 `SCHEMA_BEARING_TABULAR_FORMAT_GATE`

Purpose:

```text
Handle formats where the file itself can declare names, types, or metadata that
must become SQL table schema rather than data rows.
```

Required branches:

```text
name header present
name header absent
type header present
type header absent
metadata rows
no headers
empty/sparse cells
mismatched column count
unknown type / default text type
type conversion into SQLite-compatible values
schema identity exposed through SQL
output type/name row byte grammar
roundtrip parse -> SQL -> render
```

For the current `trdsql` task, TBLN is the triggering instance.

### 8.4 `READER_WRITER_PAIR_CLOSURE_GATE`

Purpose:

```text
If a dialect exists as both input and output format, parser success and writer
success must be paired through roundtrip and byte-grammar probes.
```

Required matrix:

```text
input only
output only
input -> raw output
input -> same dialect output
input -> JSON/YAML output
same dialect output -> re-import if supported
null/value/type preservation across route
newline/final-newline/escaping preservation
```

### 8.5 `SHARED_OWNER_INTERFACE_BOUNDARY_GATE`

Purpose:

```text
Prevent format-specific repairs from globally perturbing reader_registry,
value_normalizer, renderer_registry, source_router, sql_resource_binder,
diagnostic_emitter, or mode_dispatch.
```

Required row:

```yaml
shared_owner_touch_row:
  owner: reader_registry | value_normalizer | renderer_registry | source_router | sql_resource_binder | diagnostic_emitter | mode_dispatch
  patch_reason: string
  affected_format_or_mode: string
  local_adapter_boundary: string
  imported_preservation_sentinels: []
  forbidden_global_behavior_changes: []
  sibling_contexts_proven_unchanged: []
```

Rule:

```text
A TBLN repair should primarily modify tbln_reader_writer. If it touches shared
normalization, rendering, source routing, or diagnostics, it must import
sentinels for already-green sibling families.
```

### 8.6 `CONTROL_PLANE_RESIDUAL_DE_LUMPING_GATE`

Purpose:

```text
Ensure CLI/help/argparse rows do not remain hidden under dialect, codec,
renderer, or format buckets.
```

Required residual extraction:

```text
-h / --help aliases
help stdout/stderr/exit
unknown flag grammar
bool explicit value grammar
negative integer flag grammar
-- separator
missing value precedence
flag before/after query precedence
```

## 9. v26 TBLN Handoff Rule

The worker baton must not say:

```text
Fix TBLN failures.
```

It must say:

```text
Close SCHEMA_BEARING_TABULAR_FORMAT_GATE for TBLN within bounded scope.
```

Worker-visible obligation tree:

```text
TBLN
  1. lexical / line grammar
  2. metadata row grammar
  3. name header grammar
  4. type header grammar
  5. absent-header default schema
  6. value conversion and null policy
  7. sparse / mismatched / EOF diagnostics
  8. SQL schema binding and column identity
  9. output writer byte grammar
  10. input-output roundtrip
  11. option overlays: -inull, -onull, preread, skip/limit where applicable
  12. analyze / diagnostic compatibility where TBLN is the input
```

## 10. v26 Orchestrator Sequence

```text
P0 no-code audit sanitation:
  run POST_AUDIT_BUCKET_SANITY_GATE;
  reclassify control-plane residuals;
  produce corrected per-bucket row lists;
  attach rows to numbered HOB children.

P1 no-code TBLN reference matrix:
  generate probes from SCHEMA_BEARING_TABULAR_FORMAT_GATE;
  lock reference stdout/stderr/exit/files;
  mark unknowns/deferred siblings explicitly.

P2 implementation handoff:
  bound first patch to tbln_reader_writer;
  touch shared owners only through declared adapter boundaries;
  import preservation sentinels before patch.

P3 local candidate gate:
  TBLN matrix green;
  preservation sentinels green;
  no new control-plane, SQL-tokenizer, CSV/null, or resource-pipeline regressions.

P4 official method run:
  classify official delta by numbered TBLN nodes;
  do not use official rows as clean first-pass truth.
```
