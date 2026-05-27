# Principled Recursive ODEU Meta-Program Experimental v30

## Reactive Scheduler Program-Class Bundle

Authority layer: support / experimental meta-program revision.

This v30 patch extends v29. It keeps the contextual-tokenizer,
target-substrate, sublanguage-compilation, bucket-sanity, intermediate-work,
single-subtree closure, official-tail re-entry, and tail-dialect schema
integration gates. It adds the `entr` lesson: watcher/scheduler/supervisor
programs need a class-specific reactive bundle that treats event-channel
topology, process ecology, resource mutation, interactive control, and
liveness/exit law as inherited child obligations.

This revision is based on:

```text
docs/support/entr_progression_generalization_v30.md
artifacts/manual_runs/programbench_entr_v1_1_prep_20260523T041503/final_entr_reconstruction_causal_mapping.md
docs/support/general_program_ontology_derived_v1_2.md
```

The inherited v28/v29 basis remains below. The newest v30 additions begin at
section 26.

The earlier v28 revision was based on the `trdsql` Phase 56 audit and the
GPTPro `phase56_v28_schema_integration_review.md` review. Phase 55 reached a
strong method gain:

```text
Phase55 official:
  score: 91
  rows:  1283 passed / 119 failed / 1 skipped / 1403 total

Comparable Phase30:
  score: 79
  rows:  1127 passed / 275 failed / 1 skipped / 1403 total

Delta:
  +175 newly passing rows
  -19 regressions
  +156 net passed rows
```

The remaining failure surface is no longer dominated by broad resource-route
topology. It is a tail-closure surface split across target-substrate dependency
tails, public sublanguage tails, value-domain/error tails, compatibility
overlays, mode-state exactness tails, and scoped-green-but-not-gold sibling
tails.

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

## 11. v27 Intermediate Work Triage Gate

Triggered whenever an implementation candidate is tested against an
intermediate local matrix before official eval.

Purpose:

```text
Prevent a broad local matrix from becoming broad patch authorization.
```

Required triage row:

```yaml
intermediate_work_triage_row:
  candidate_witness_type:
    one_of:
      - replay_table
      - mechanism_scaffold
      - scoped_subtree_witness
      - gold_attempt
  matrix_scope:
    active_phase_count: int
    active_owner_count: int
    broadness_status: bounded | overloaded
  phase_pass_rates:
    - phase_ref: string
      passed: int
      failed: int
      total: int
      pass_rate: number
  failed_branch_rank:
    - branch_ref: string
      failed_count: int
  earliest_failed_transition_by_phase:
    - phase_ref: string
      transition_ref: string
      reason: string
  implementation_transfer_errors:
    - subtree_ref: string
      explanation: string
  theory_terminalization_gaps:
    - subtree_ref: string
      missing_terminal_children: [string]
  orchestrator_transition_errors:
    - error_ref: string
      explanation: string
  allowed_next_handoff_type:
    one_of:
      - no_code_audit
      - conservation_only
      - single_subtree_closure
      - broad_integration
      - official_eval
```

Blocking rule:

```text
If active_phase_count > 2 and combined pass rate < 70%, the next step cannot
be another broad implementation patch. It must be no-code audit sanitation or
a single-subtree closure batch.
```

The Phase 40 trdsql local matrix is the seed example:

```text
active_phase_count: 6
combined pass rate: 64 / 179 = 35.8%
allowed_next_handoff_type: single_subtree_closure
forbidden_next_handoff_type: broad_integration, official_eval
```

## 12. v27 Single-Subtree Closure Contract

A worker baton for implementation after an overloaded intermediate matrix must
name exactly one primary subtree.

Required baton shape:

```yaml
single_subtree_closure_contract:
  primary_subtree_ref: string
  source_matrix_refs: [string]
  target_closure_threshold:
    type: exact_green | bounded_partial | diagnostic_only
    pass_target: string
  allowed_owners:
    - owner_ref: string
      allowed_touch_reason: string
      adapter_boundary: string
  forbidden_owners:
    - owner_ref: string
      forbidden_reason: string
  imported_preservation_sentinels:
    - sentinel_ref: string
      source_phase_ref: string
      reason: string
  sibling_contexts_to_hold_constant:
    - subtree_ref: string
  completion_gate:
    local_matrix_requirement: string
    preservation_requirement: string
    regression_budget: string
```

The baton must not say:

```text
Improve the remaining matrices.
```

It must say:

```text
Close this numbered subtree to this threshold, through these owners, while
preserving these sentinels.
```

## 13. v27 Broad-Matrix Interpretation Rule

A broad matrix is authorized for triage and pressure localization only.

Allowed uses:

```text
rank failed branches
rank shared owners
identify overloaded handoffs
choose a next subtree
surface non-commuting owners
separate implementation-transfer errors from theory terminalization gaps
```

Forbidden uses:

```text
authorize a broad code patch
declare official readiness
merge sibling subtrees into one worker baton
count representative examples as subtree closure
launder post-eval pressure into clean reference evidence
```

## 14. v27 trdsql Phase 40 Application

Phase 40 produced:

```text
combined local matrix: 64 passed / 115 failed / 179 total
phase33 TBLN:          16 / 40
phase34 dialects:      17 / 38
phase35 row lifecycle: 19 / 29
phase36 jq selectors:   5 / 22
phase37 modes:          2 / 24
phase38 resources:      5 / 26
```

Classification:

```text
candidate_witness_type: mechanism_scaffold
macro_closure: absent
handoff_broadness: overloaded
official_eval_authorized: false
```

Allowed next handoff:

```text
single_subtree_closure
```

Recommended candidates:

```text
Option A:
  primary_subtree_ref: TBLN_SCHEMA_BEARING_SUBLANGUAGE
  reason: largest original official remaining subtree
  target: phase33 >= 36 / 40 without preservation regression

Option B:
  primary_subtree_ref: CONFIG_DB_ANALYZE_MODE_AS_PROGRAM
  reason: weakest intermediate transfer, highest methodology value
  target: phase37 >= 18 / 24 without CLI/config/analyze preservation regression
```

Default selection rule:

```text
If the goal is official score movement, choose Option A.
If the goal is method stability and weak-layer repair, choose Option B.
```

## 15. v28 Official Tail Re-Entry Rule

Triggered whenever an official eval follows a scoped repair, method-test patch,
or high-score method gain and the remaining failures cluster by public family or
implementation owner.

Purpose:

```text
Prevent official-tail clusters from becoming flat worker buckets.
Route each cluster first through schema re-entry so the orchestrator can decide
whether the issue is a missing parent, missing sibling, compatibility overlay,
target-substrate equivalence failure, or implementation transfer bug.
```

Required row:

```yaml
official_tail_reentry_row:
  cluster_id: string
  failure_count: int
  primary_owner: string
  shared_owner_with_recent_patch: true | false
  prior_local_matrix_status:
    one_of:
      - absent
      - red
      - scoped_green
      - gold_green
      - unknown
  official_tail_relation:
    one_of:
      - new_parent_missing
      - missing_sibling_under_existing_parent
      - compatibility_overlay_conflict
      - target_substrate_equivalence
      - implementation_transfer_bug
      - post_eval_only_unknown
  earliest_discoverable_layer: string
  required_triangular_axes: []
  required_preservation_sentinels: []
  next_gate: string
  handoff_posture:
    one_of:
      - blocked_until_schema_split
      - probe_ready
      - implementation_ready
      - scoped_deferred
```

Blocking rule:

```text
A remaining official cluster cannot be handed directly to a worker until this
row is filled and its next gate is named.
```

Tail relation meanings:

```text
new_parent_missing:
  The current ontology has no adequate parent concept for the failures.

missing_sibling_under_existing_parent:
  A parent exists, but the local matrix covered only representative children.

compatibility_overlay_conflict:
  Two public or official branches disagree by stream, exit, precedence, spelling,
  diagnostic prefix, or branch-local behavior.

target_substrate_equivalence:
  Local behavior depends on a dependency, binary, interpreter feature, codec,
  OS facility, locale, path topology, or packaging fact not proved in the target.

implementation_transfer_bug:
  The theory and probes are adequate, but the candidate witness failed to
  implement or preserve the locked behavior.
```

## 16. Scoped-Green Official Sibling Tail Gate

Triggered when a local matrix for macro `M` is green or near-green, but the
official tail still contains failures owned by `M` or by `M`'s implementation
owner.

Required row:

```yaml
scoped_green_official_sibling_tail:
  macro_ref: string
  local_green_matrix_refs: []
  official_tail_rows: []
  owner_refs: []
  sibling_axes_missing:
    - grammar
    - value_domain
    - diagnostic
    - renderer
    - target_substrate
    - row_lifecycle
    - mode_overlay
    - method_equivalence
  scoped_to_gold_expansion_required: true
  forbidden_claim: parent_closed
  allowed_claim: scoped_green_with_official_sibling_tail
```

Readiness addition:

```text
scoped_green_with_official_sibling_tail
```

Meaning:

```text
The local matrix remains valuable and regression-worthy, but it cannot be used
as gold closure because official pressure still names unclosed siblings under
the same parent or owner.
```

Rule:

```text
local green + official sibling tail => not_gold_ready_missing_sibling_tail.
```

This is the general form of the Phase 55 TBLN and codec-resource lesson:

```text
TBLN local-green did not close type aliases, timestamptz, whitespace, long
string, punctuation, negative/zero numeric, or unsupported-line siblings.

Codec-resource local-green did not close zstd target-substrate availability or
stdout/file byte equivalence.
```

## 17. Compatibility Overlay Conflict Gate

Triggered when a public surface has branch-specific stdout, stderr, exit,
usage, diagnostic, or precedence behavior and a global implementation rule
would satisfy one branch while breaking another.

Required row:

```yaml
compatibility_overlay_conflict:
  surface_ref: string
  branch_dimensions:
    - spelling_or_alias
    - invalid_arg_context
    - stream_destination
    - exit_code
    - diagnostic_prefix
    - precedence_order
  public_reference_rows: []
  official_pressure_rows: []
  conflict_status:
    one_of:
      - branch_discriminator_known
      - branch_discriminator_missing
      - public_official_conflict_isolated
  implementation_rule_scope:
    one_of:
      - branch_local
      - global_forbidden
```

Applied immediately to CLI/help/argparse branches:

```text
--help
-help
-h
invalid arg + help
help before invalid arg
help after invalid arg
stdout vs stderr
rc0 vs rc2
```

Forbidden shortcut:

```text
Do not globally rewrite help behavior to satisfy one branch.
```

Required closure:

```text
Every help branch must have a stream, exit, usage-header, diagnostic, and
precedence warrant before implementation.
```

## 18. Target-Stable Dependency Contract

Triggered when behavior depends on an optional library, external binary, codec
helper, shell tool, interpreter feature, locale, platform resource, DB driver,
or filesystem feature.

This gate specializes v26 `TARGET_DEPENDENCY_EQUIVALENCE_GATE` for official
tail closure.

Required row:

```yaml
target_stable_dependency_contract:
  dependency_ref: string
  behavior_surfaces:
    - input_decode
    - output_encode
    - extension_guessing
    - explicit_flag_override
    - stdout_bytes
    - file_bytes
  local_availability:
    one_of: [present, absent, unknown]
  packaged_eval_availability:
    one_of: [present, absent, unknown]
  fallback_strategy:
    one_of:
      - pure_in_bundle
      - vendored_dependency
      - proven_external_helper
      - branch_deferred
  target_substrate_probe_refs: []
  packaging_refs: []
  preservation_sentinels: []
```

Applied immediately to zstd:

```text
zstd output and input behavior must work in the packaged evaluator substrate,
not only in the local Python environment.
```

Required preservation sentinels:

```text
gzip input/output
bz2 input/output
xz input/output
lz4 input/output
extension guessing
explicit -oz override
stdout compressed bytes
output-file compressed bytes
unsupported helper diagnostic
```

## 19. Public Sublanguage Closure Gate

Triggered when a public format, selector, renderer, query fragment, mode, or
named option has syntax and semantics richer than a single flag label.

Required row:

```yaml
public_sublanguage_closure:
  sublanguage_ref: string
  lexical_grammar_refs: []
  parse_tree_refs: []
  semantic_transform_refs: []
  value_domain_refs: []
  diagnostic_refs: []
  renderer_or_output_refs: []
  row_binding_refs: []
  negative_boundary_refs: []
  preservation_sentinels: []
  readiness:
    one_of:
      - label_only
      - scoped_examples
      - matrix_locked
      - scoped_green
      - gold_ready
      - scoped_green_with_official_tail
```

Applied immediately to:

```text
jq
TBLN
JSON / JSONL
YAML
fixed-width / ps / dpkg
```

Bookkeeper rejection rules:

```text
Reject "fixed jq" unless 5.4 child matrix is closed or explicitly scoped.
Reject "fixed JSON/YAML" unless parse, value, output, and diagnostic branches
are separated.
Reject "fixed zstd" unless target-substrate proof exists.
Reject global help changes unless branch discriminators are locked.
Reject TBLN gold closure while official sibling tail remains.
```

## 20. v28 Child Node Additions

The top-level HOB schema remains stable:

```text
1  Control plane / invocation grammar
2  Public schema and mode family
3  Input resource and route topology
4  Input dialect and value-domain grammar
5  Embedded language / transform substrate
6  Subject, identity, binding, and aggregation
7  State, lifecycle, and mutation
8  Output router, renderer, and byte grammar
9  Diagnostics, fatal gates, and channel contracts
10 Runtime substrate and observation ecology
11 Methodological equivalence and warrant
12 Probe, readiness, and implementation handoff
```

Add these child nodes for tail closure:

```text
4.2 JSON / JSONL grammar
  4.2.1 top-level object / array / scalar / empty
  4.2.2 array-of-arrays to row mapping
  4.2.3 nested object/array stringification vs flattening
  4.2.4 JSONL stream parse lifecycle
  4.2.5 mid-stream error timing
  4.2.6 Go-like parse error wording
  4.2.7 binary / invalid UTF-8 value handling

4.3 YAML grammar
  4.3.1 scalar / mapping / sequence / null
  4.3.2 anchors and merge keys
  4.3.3 duplicate key behavior
  4.3.4 embedded JSON/YAML value unpacking
  4.3.5 malformed syntax diagnostics
  4.3.6 typed scalar conversion

4.6 fixed-width / ps / dpkg reader
  4.6.1 width specification grammar
  4.6.2 column boundary discovery
  4.6.3 dpkg header skipping
  4.6.4 ps command tail preservation
  4.6.5 numeric thousands separators
  4.6.6 unicode column names
  4.6.7 analyze hints for width-like files

4.7 TBLN schema-bearing grammar
  4.7.1 metadata/header/type rows
  4.7.2 absent type rows defaulting
  4.7.3 type aliases: postgres, timestamp, timestamptz
  4.7.4 numeric negative/zero conversion
  4.7.5 long string / punctuation preservation
  4.7.6 leading/trailing whitespace preservation
  4.7.7 unsupported-line diagnostics
  4.7.8 output type row preservation

5.4 jq selector / transform sublanguage
  5.4.1 dotted path selector
  5.4.2 array iteration []
  5.4.3 array index [n]
  5.4.4 pipe composition
  5.4.5 select(predicate)
  5.4.6 object construction / key rename
  5.4.7 multiple extraction paths
  5.4.8 recursive descent
  5.4.9 type mismatch diagnostics
  5.4.10 resource suffix binding: file.json::.path
  5.4.11 row compiler from selector result

8.4 JSON/YAML renderer value preservation
  8.4.1 numeric type preservation
  8.4.2 null rendering and -onull
  8.4.3 nested JSON-looking string rehydration
  8.4.4 binary/non-UTF8 escape policy
  8.4.5 special-character escaping

8.7 compression output route
  8.7.1 extension guess
  8.7.2 explicit -oz override
  8.7.3 stdout compression bytes
  8.7.4 output-file compression bytes
  8.7.5 unsupported codec diagnostic
  8.7.6 target-stable codec availability

8.10 renderer priority and conflict overlay
  8.10.1 multiple output format flags
  8.10.2 -out extension vs explicit output flag
  8.10.3 -out-without-guess
  8.10.4 special-character priority interactions

11.4 target dependency equivalence
  11.4.1 optional Python module availability
  11.4.2 external helper binary availability
  11.4.3 vendored fallback coverage
  11.4.4 target-image replay proof
  11.4.5 packaged artifact proof

11.9 official sibling tail re-entry
  11.9.1 scoped-green official tail detection
  11.9.2 owner-tail mapping
  11.9.3 sibling-axis expansion
  11.9.4 tail-to-worker handoff blocker
```

## 21. v28 trdsql Phase 56 Cluster Mapping

| Cluster | Count | Schema node(s) | v28 gate |
| --- | ---: | --- | --- |
| `JSON_YAML_VALUE_AND_ERROR_DOMAIN` | 31 | `4.2`, `4.3`, `4.9`, `8.4`, `9.4` | `PUBLIC_SUBLANGUAGE_CLOSURE_GATE` plus value/error grammar |
| `JQ_SELECTOR_SUBLANGUAGE` | 18 | `5.4`, `3.5`, `4.2`, `9.4` | `PUBLIC_SUBLANGUAGE_CLOSURE_GATE` |
| `CODEC_ZSTD_AND_COMPRESSION_ECOLOGY` | 12 | `3.7`, `8.7`, `10.4`, `11.4` | `TARGET_STABLE_DEPENDENCY_CONTRACT` |
| `WIDTH_FIXED_TABLE_READER` | 11 | `4.6`, `6.2`, `7.2`, `2.4` | `PUBLIC_SUBLANGUAGE_CLOSURE_GATE` |
| `CLI_HELP_ARGPARSE_CONFLICT` | 10 | `1.1`, `1.5`, `9.1`, `11.8` | `COMPATIBILITY_OVERLAY_CONFLICT_GATE` |
| `TBLN_SCHEMA_TYPE_GRAMMAR` | 10 | `4.7`, `6.2`, `8.6`, `9.4` | `SCOPED_GREEN_OFFICIAL_SIBLING_TAIL_GATE` |
| `CONFIG_DB_STATE_TOPOLOGY` | 9 | `2.7`, `3.10`, `7.4`, `9.5` | mode-state topology gate |
| `ROW_UNIVERSE_AND_INPUT_ROW_SHAPE` | 6 | `6.1`, `7.1`, `4.x` | row universe ordering lattice |
| `RESOURCE_PATH_DIAGNOSTIC_AND_MUTATION` | 5 | `3.2`, `5.2`, `7.5`, `9.3` | resource mutation diagnostic overlay |
| `ANALYZE_MODE_EXACTNESS` | 3 | `2.4`, `8.8`, `6.2` | analyze exactness overlay |
| `SQL_NUMERIC_TYPE_RENDERING` | 2 | `5.2`, `8.4`, `6.4` | SQL numeric rendering gate |
| `OUTPUT_ROUTER_RENDERER_PRIORITY` | 2 | `8.1`, `8.7`, `1.x` | output priority compatibility overlay |

## 22. v28 Next Sequence

### Batch 0: Tail Schema Compilation

No code.

```text
1. Import Phase30 regressions as preservation sentinels.
2. Fill official_tail_reentry_row for every remaining cluster.
3. Mark each cluster as missing sibling, overlay conflict, target-substrate
   equivalence, implementation transfer bug, or new parent.
4. Attach every row to numbered HOB child nodes.
5. Emit a worker baton only after the relevant gate is probe-ready.
```

### Batch 1: zstd Target-Stable Codec Contract

Reason:

```text
12 rows, narrow owner surface, clear E4 target-substrate miss, low semantic
interaction if gzip/bz2/xz/lz4/output-route sentinels are imported.
```

Acceptance:

```text
zstd works in the packaged evaluator substrate, not only local Python.
```

### Batch 2: CLI Help Compatibility Overlay

Reason:

```text
10 rows, including 9 Phase30 regressions.
```

Acceptance:

```text
Every help branch has explicit stream, exit, and precedence warrant.
```

### Batch 3: jq Selector Sublanguage

Reason:

```text
18 rows plus 4 regressions. Treat jq as an embedded selector/transform
language, not as a bag of string patterns.
```

### Batch 4: JSON/YAML Value Domain And Error Grammar

Split into:

```text
4A JSON/JSONL parse and stream lifecycle
4B YAML anchors/merge/duplicate/malformed grammar
4C structured scalar/value normalization and output rendering
4D diagnostic wording/timing
```

### Batch 5: Fixed-Width / ps / dpkg Dialect Family

Treat fixed-width as its own schema-bearing dialect family.

### Batch 6: TBLN Scoped-to-Gold Promotion

Use `SCOPED_GREEN_OFFICIAL_SIBLING_TAIL_GATE`; do not claim parent closure from
the existing local-green matrix.

### Batch 7: Smaller Overlays By Shared Owner

Group remaining rows by implementation owner:

```text
config_loader / db topology
row_lifecycle / value_normalizer
resource_binder / sqlite executor
renderer / output_router
analyze_renderer
```

## 23. v28 Worker Baton Tail Closure Template

Every worker baton after Phase 56 must include:

```yaml
v28_worker_baton:
  handoff_type:
    one_of:
      - scoped_subtree_closure
      - compatibility_overlay
      - target_dependency_equivalence
  target_cluster: string
  target_hob_nodes: []
  primary_gate: string
  allowed_implementation_owners: []
  forbidden_implementation_owners: []
  required_pre_patch_probes: []
  required_reference_observations: []
  required_target_substrate_observations: []
  required_preservation_sentinels: []
  official_tail_rows_used_as_pressure_only: []
  local_matrix_closure_target: string
  post_patch_report_must_include:
    - rows closed by numbered node
    - regressions by preservation sentinel
    - remaining sibling tail
    - whether parent is gold_ready or scoped_green_with_official_tail
```

## 24. v28 Bottom Line

```text
After a high-score method gain, the orchestrator must not continue broad
patching. It must compile the official tail into schema-level sibling
expansion, compatibility overlays, and target-substrate equivalence rows.

parent macro closure must survive official sibling-tail pressure.
```

---

## 25. v29 Tail-Dialect Schema Integration

Authority layer: `post_eval_pressure_review`.

v29 integrates the Phase77 tail-dialect review:

```text
docs/support/phase77_v29_tail_dialect_schema_integration.md
```

The v29 correction applies once the reconstruction is globally mechanistic and
official-compatible, but a small tail remains concentrated in public dialect
or byte-surface siblings.

### 25.1 New Readiness State

```text
gold_tail_not_closed
```

Meaning:

```text
The program theorem is globally stable, but specific gold-tail public dialect
or byte-surface sibling leaves remain open.
```

This is stronger than `scoped_green_with_official_sibling_tail`: the remaining
rows are no longer broad scoped risk. They are explicit gold-tail obligations
that must be owned row-by-row.

### 25.2 Tail Row Ownership Exactness Gate

Trigger:

```text
official failure tail <= roughly 5 percent of total rows
or score >= 95
```

Required row:

```yaml
remaining_tail_row:
  test_name: string
  branch: string
  primary_hob_node: string
  secondary_hob_nodes: []
  failure_class: string
  first_failure_surface: string
  implementation_owner: string
  required_method:
    one_of:
      - ontology
      - public_reference
      - source_postmortem
      - substrate_equivalence
      - preservation
  preservation_sentinels: []
  patch_class_allowed: true|false
  patch_class_forbidden_reason: string|null
```

Rule:

```text
At gold-tail stage, approximate buckets are not worker handoffs. Every
remaining row must have exactly one primary node, optional secondary nodes, an
implementation owner, a method posture, and preservation sentinels.
```

### 25.3 Tail Dialect Microgrammar Closure Gate

Trigger:

```text
a public input format, output format, reader mode, or syntax-bearing option
remains in the failure tail.
```

Required closure fields:

```yaml
dialect_ref: string
input_physical_grammar: present|not_applicable|open
schema_binding_grammar: present|not_applicable|open
value_domain_grammar: present|not_applicable|open
row_lifecycle_rules: present|not_applicable|open
renderer_byte_grammar: present|not_applicable|open
diagnostic_grammar: present|not_applicable|open
source_or_target_substrate_equivalence: proven|needs_translation|open
preservation_sentinels_imported: true|false
```

Rule:

```text
A public format name cannot close as a label. It closes only when its remaining
microgrammar surfaces are implemented, proved irrelevant, or explicitly
deferred with expected risk.
```

### 25.4 Host Library Surface Translation Gate

Trigger:

```text
the reconstruction uses a host parser, renderer, or diagnostic library whose
surface is not the target program's library surface.
```

Required decision:

```yaml
host_library: string
target_surface: string
surfaces_affected:
  - diagnostic wording
  - stream shape
  - line_column_numbering
  - duplicate_key_policy
  - scalar_normalization
  - map_ordering
strategy:
  one_of:
    - translate_surface
    - emulate_target
    - replace_library
    - source_postmortem_needed
    - defer_with_risk
```

Rule:

```text
Host-library behavior is not an oracle. If the target exposes a different
parser, renderer, or diagnostic surface, the implementation must translate,
emulate, replace, or explicitly defer that difference.
```

### 25.5 Type Provenance Authority Gate

Trigger:

```text
renderer output depends on source type, declared schema, reader-inferred type,
or runtime substrate type.
```

Required row:

```yaml
value_ref: string
source_declared_type: string|null
reader_inferred_type: string|null
sqlite_runtime_type: string|null
renderer_claimed_type: string|null
provenance_sidecar_available: true|false
allowed_renderer_inference:
  one_of:
    - none
    - from_declared_schema
    - from_reader_type
    - from_sqlite_type
    - explicitly_reference_locked
```

Rule:

```text
A renderer may not invent type provenance from string shape when prior
negative evidence shows that broad string-pattern inference regresses sibling
leaves.
```

### 25.6 Reader-Local Row Lifecycle Gate

Trigger:

```text
skip, limit, header, preread, row-number, blank, sparse, wildcard, binary, or
extension-guess behavior differs by reader family.
```

Required axes:

```text
CSV skip/header/limit order
inum generated-column placement and collision naming
LTSV union-of-fields and missing-field cells
LTSV malformed diagnostics
PSV extension delimiter guess
wildcard multi-file schema union
binary/non-UTF8 value representation by output format
```

Rule:

```text
Row controls are not globally post-import by default. Each reader may own a
local lifecycle order.
```

### 25.7 Analyze Advice Coupling Gate

Trigger:

```text
an analyze/report mode gives format or query advice based on reader morphology.
```

Rule:

```text
Analyze advice is not a free renderer string. It is coupled to reader family,
header inference, sampled morphology, driver quoting, and dialect detection.
```

### 25.8 Patch-Class Negative History Gate

Trigger:

```text
a prior patch class produced zero wins, regressions, or both in the same
subtree.
```

Rule:

```text
A rejected patch class becomes forbidden until the orchestrator provides a
node-level proof explaining why the same class will not recur.
```

Example:

```text
If broad TBLN renderer-only string-pattern type inference regressed sibling
rows, future TBLN work must proceed through schema-bearing grammar and type
provenance, not another renderer-string heuristic.
```

### 25.9 Output Format Precedence Overlay Gate

Trigger:

```text
multiple output-format flags, output-file extension guessing, or explicit
output format controls collide.
```

Required axes:

```text
first-wins vs last-wins
explicit flag vs output-extension guess
-out-without-guess
format aliases
stdout vs file route
```

Rule:

```text
Output format precedence is a control-plane overlay over renderer choice, not
a renderer implementation detail.
```

### 25.10 Gold Tail Batch Authorization Gate

No gold-tail implementation batch may start unless:

```text
1. TAIL_ROW_OWNERSHIP_EXACTNESS_GATE is satisfied.
2. Each row in the batch has one primary HOB node.
3. All batch rows share either one implementation owner or an explicit coupled
   owner set.
4. Preservation sentinels are imported from every previously accepted phase
   that shares the owner.
5. Any negative-history patch class is explicitly forbidden in the baton.
6. Host-library translation obligations are either in scope or excluded with
   expected risk.
```

### 25.11 v29 Bottom Line

```text
At gold-tail stage, do not patch symptoms or broad shared owners. Patch only a
numbered microgrammar leaf with row ownership, preservation sentinels, and a
proof that the chosen patch class is allowed.
```

## 26. v30 Reactive Scheduler Program-Class Bundle

### 26.1 Trigger

Activate `REACTIVE_SCHEDULER_PROGRAM_CLASS` when the target program:

```text
watches files/resources;
runs commands after events;
listens for keyboard, signal, timer, child-state, filesystem, socket, or other
  runtime events;
restarts or supervises child processes;
keeps a loop alive after work;
or generates/invokes helper scripts or status filters as part of runtime
  behavior.
```

The trigger is class-specific. It must not be imposed on ordinary batch CLI
programs, renderer-only tools, or pure data converters unless one of the above
runtime/control/liveness traits applies.

### 26.2 Core Invariant

```text
For reactive programs, the hidden ontology is often not in data formats or
renderers. It is in event-channel topology, scheduler lifecycle, command
boundary, resource mutation, process supervision, and liveness/exit law.
```

Short form:

```text
feature label != closed behavior
event != filesystem change only
stdin != runtime control stream
child launch != child supervision
directory/resource watch != one boolean switch
live timeout != harness noise by default
```

### 26.3 `EVENT_CHANNEL_TOPOLOGY_GATE`

Trigger:

```text
Any reactive program-class activation.
```

Required row:

```yaml
event_channel_topology:
  configuration_streams: []
  runtime_event_streams: []
  control_streams: []
  child_state_streams: []
  signal_streams: []
  timer_streams: []
  network_streams: []
  filesystem_streams: []
  startup_events: []
  external_events: []
  synthetic_events: []
  observer_horizon: string
  blocking_nonblocking_posture: string
  liveness_expectation_after_event: string
  evidence_refs: []
  closure_status: blocked | scoped_ready | gold_ready
```

Rule:

```text
Do not infer keyboard/control behavior from stdin shape.
Do not infer filesystem watcher behavior from static file-open behavior.
Do not infer child-process behavior from parent exit alone.
```

### 26.4 `CONFIG_STREAM_VS_CONTROL_STREAM_GATE`

Trigger:

```text
The program reads configuration from stdin or a config stream and also exposes
interactive/runtime controls.
```

Required axes:

```text
stdin-as-configuration
stdin-as-control
/dev/tty or control terminal
PTY/tmux observer profile
signal controls
control stream absent
control stream present while configuration stream is piped
composition with ordinary modes
```

Rule:

```text
Interactive does not mean stdin is TTY. Interactive means a runtime control
resource exists and has its own event grammar.
```

### 26.5 `RESOURCE_WATCH_REGISTRATION_GATE`

Trigger:

```text
The program watches, polls, registers, subscribes to, tails, reloads, or
otherwise tracks external resources over time.
```

Required axes:

```yaml
resource_watch_registration:
  opened_resources: []
  registered_watch_identities: []
  displayed_identities: []
  mutation_tracked_identities: []
  parent_identities: []
  child_identities: []
  symlink_path_policy: string
  symlink_target_policy: string
  hidden_entry_policy: string
  deletion_policy: string
  replacement_policy: string
  child_metadata_policy: string
  recursion_or_depth_policy: string
  closure_status: blocked | scoped_ready | gold_ready
```

Rule:

```text
The file path read at startup is not automatically the watch identity.
Resource identity can move through parent directories, symlink policy,
hidden-entry policy, and mutation lifecycle.
```

### 26.6 `SCHEDULER_STARTUP_EVENT_LIVENESS_GATE`

Trigger:

```text
The program reacts to startup, runtime events, child completion, or repeated
events while remaining alive.
```

Required axes:

```text
startup run
postponed startup
first event run
debounce/consolidation
restart old child before new run
exit-after-run
remain-live-after-run
fatal event after run
parent exit from child status
parent exit from event/resource condition
observer timeout as success/failure surface
```

Critical cross-product:

```text
mode x resource topology x command class x event type
```

Rule:

```text
A scheduler law cannot close from one representative event. It must declare
startup, event, liveness, and exit behavior for the active resource and command
classes or defer siblings with expected risk.
```

### 26.7 `COMMAND_BOUNDARY_AND_ARGUMENT_BINDING_GATE`

Trigger:

```text
The reactive program invokes user-supplied commands, scripts, filters, shells,
or callbacks.
```

Required axes:

```text
direct argv execution
shell string execution
placeholder or selected-resource substitution
selected-resource binding
shell argv0/$0 binding
cwd and environment defaults
quoting and spaces in resource paths
command not found / exec failure
command-class-specific scheduler/exit behavior
```

Rule:

```text
Command binding is a language boundary. It must be modeled as its own
sublanguage, not as string concatenation.
```

### 26.8 `CHILD_PROCESS_SUPERVISION_GATE`

Trigger:

```text
The parent launches, restarts, signals, waits on, kills, or reaps child
processes.
```

Required axes:

```text
direct child vs process group
restart policy
old-child termination
termination signal choice
HUP/TERM/INT/QUIT forwarding
already-exited child cleanup
zombie prevention
terminal-close cleanup
child stdout/stderr ownership
parent exit derived from child exit/signal
```

Rule:

```text
If the program supervises children, process ecology is product behavior, not
harness noise.
```

### 26.9 `STATUS_FILTER_SUBPROGRAM_GATE`

Trigger:

```text
The program generates, invokes, reads, preserves, or routes through a helper
script/filter/template that transforms runtime status into user-visible
reports.
```

Required axes:

```text
generated template shape
custom helper preservation
helper path/environment override
creation timing relative to blocking reads/events
permissions/executable state
input record grammar
exit/signal record grammar
stdout/stderr/status projection
failure of helper itself
```

Rule:

```text
A status helper is a subprogram. Treat it like a sublanguage plus resource
lifecycle, not as a string formatter.
```

### 26.10 `INTERACTIVE_CONTROL_TERMINAL_GATE`

Trigger:

```text
Runtime keyboard controls, PTY/tmux behavior, curses/terminal control, or
/dev/tty behavior appears in visible schema, scout observations, failures, or
program intent.
```

Required axes:

```text
control terminal exists / absent
watch-list or config stdin separate from control terminal
TTY vs pipe vs PTY vs tmux
startup behavior under interactive mode
trigger key grammar
quit key grammar
non-quit uppercase or variant keys
ignored keys
composition with restart, clear, shell, postpone, resource-watch modes
observer horizon / timeout / nonblocking read
```

Rule:

```text
PTY/interactive behavior may be product control-plane semantics, not merely
resource ecology or harness artifact.
```

### 26.11 `DIRECT_CONTAINER_CONFLICT_LATTICE`

Trigger:

```text
A resource kind can be both direct subject and parent/container of other
watched or processed subjects.
```

Required axes:

```text
direct resource route
derived parent route
startup behavior
child-entry mutation behavior
hidden-entry policy
count-change fatal behavior
command-class-specific behavior
interactive composition
exit/liveness consequence
```

Rule:

```text
If one resource can be both watched object and container of watched objects,
create a conflict lattice before patching event behavior.
```

### 26.12 `REACTIVE_REJECTED_PATCH_CLASS_GATE`

Trigger:

```text
A reactive repair solves one tail and regresses sibling rows under the same
event, resource, command, scheduler, process, or diagnostic owner.
```

Required row:

```yaml
rejected_patch_class:
  patch_ref: string
  solved_leaf_refs: []
  regressed_leaf_refs: []
  shared_owner: string
  collapsed_discriminator: string
  forbidden_future_strategy: string
  required_parent_ascent: string
  preservation_sentinel_refs: []
  closure_status: blocked | scoped_ready | gold_ready
```

Rule:

```text
A rejected patch defines a forbidden patch class and a required parent ascent.
Future work under that owner must name the missing discriminator before patching.
```

### 26.13 Reactive Worker Handoff Template

Before source patching, the orchestrator should require:

```yaml
reactive_program_handoff:
  active_class: REACTIVE_SCHEDULER_PROGRAM_CLASS
  event_channels:
    configuration_streams: []
    runtime_event_streams: []
    control_streams: []
    child_state_streams: []
  resource_topology:
    watched_subjects: []
    registered_identities: []
    parent_identities: []
    mutation_cases: []
  scheduler_laws:
    startup: []
    event: []
    restart: []
    exit_after: []
    remain_live: []
  command_boundary:
    direct_argv: blocked | scoped_ready | gold_ready | not_applicable
    shell_string: blocked | scoped_ready | gold_ready | not_applicable
    selected_resource_binding: blocked | scoped_ready | gold_ready | not_applicable
    env_cwd_defaults: blocked | scoped_ready | gold_ready | not_applicable
  process_supervision:
    process_group: blocked | scoped_ready | gold_ready | not_applicable
    signal_forwarding: blocked | scoped_ready | gold_ready | not_applicable
    zombie_prevention: blocked | scoped_ready | gold_ready | not_applicable
  interactive_control:
    control_terminal: blocked | scoped_ready | gold_ready | not_applicable
    keyboard_grammar: blocked | scoped_ready | gold_ready | not_applicable
    observer_horizon: blocked | scoped_ready | gold_ready | not_applicable
  status_subprogram:
    generated_template: blocked | scoped_ready | gold_ready | not_applicable
    custom_override: blocked | scoped_ready | gold_ready | not_applicable
    path_env_overlay: blocked | scoped_ready | gold_ready | not_applicable
  diagnostic_exit_liveness:
    stdout_stderr_split: blocked | scoped_ready | gold_ready
    parent_exit_law: blocked | scoped_ready | gold_ready
    live_timeout_success: blocked | scoped_ready | gold_ready
  preservation_sentinels: []
  rejected_patch_classes: []
  handoff_status: blocked | scoped_ready | implementation_ready | gold_ready
```

### 26.14 v30 Bottom Line

```text
For reactive tools, route watcher/scheduler/supervisor behavior into the
reactive bundle early. Once the class applies, all event, resource, command,
process, interactive, status, diagnostic, and liveness children are inherited
obligations unless explicitly proved irrelevant or deferred with expected risk.
```
