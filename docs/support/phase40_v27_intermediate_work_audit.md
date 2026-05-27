# Phase 40 / v27 Intermediate Work Audit

Authority layer: `support / local-matrix pressure audit`.

Scope: audit of the uploaded `trdsql_candidate.py` and `phase40_local_matrix_after_single_pass_summary.md`. This is not an official-eval attribution and should not be promoted as gold behavior evidence.

## 1. Executive verdict

The intermediate work is a **generative scaffold**, not a replay-table collapse. The candidate is organized around argv parsing, resource opening, input importers, SQLite resource binding, renderers, output routing, config loading, analyze mode, and execution. That is the right witness *type* for this task.

However, the Phase 40 matrix shows that the single implementation pass is not close to closure:

```text
combined local matrix: 64 passed / 115 failed / 179 total
pass rate:             35.8%
```

By phase:

```text
phase33 TBLN schema-bearing matrix:        16 / 40  = 40.0%
phase34 dialect/value/renderer matrix:     17 / 38  = 44.7%
phase35 row-universe/lifecycle matrix:     19 / 29  = 65.5%
phase36 jq selector sublanguage matrix:     5 / 22  = 22.7%
phase37 config/db/analyze mode matrix:      2 / 24  =  8.3%
phase38 codec/resource ecology matrix:      5 / 26  = 19.2%
```

So this pass should be classified as:

```text
mechanistic_witness_scaffold_present
macro_closure_not_achieved
implementation_ready_for_next_narrow_batch: no
useful_for_diagnosis: yes
```

The work does not justify moving to official eval. It justifies a narrower next handoff.

## 2. Main layer-transition diagnosis

### 2.1 The implementation handoff was too broad

The current pass attempted to touch all of these active matrices at once:

```text
TBLN schema-bearing format
JSON/YAML/LTSV/value-domain/renderers
row universe and lifecycle
jq selector/transform sublanguage
config/db/analyze mode
codec/resource ecology
```

That violates the main v23-v26 lesson: shared owners need preservation sentinels and bounded impact cones before broadening. The result is predictable: the candidate has broad mechanism-shaped code, but every high-risk surface is still partially open.

The correct reading is not:

```text
candidate failed; patch more rows
```

It is:

```text
orchestrator allowed a multi-subtree patch before one subtree was closed
```

### 2.2 The largest immediate failure is mode-as-program, not TBLN

The previous official remaining-failure audit correctly identified TBLN as the largest official subtree, but this local matrix tells us something different about the intermediate patch quality:

```text
phase37 config/db/analyze: 2 / 24
phase38 codec/resource:   5 / 26
phase36 jq:               5 / 22
```

Those phases are worse than TBLN by pass rate. So the patch did not merely under-close TBLN. It also failed to transfer the **mode-as-program** and **runtime/resource ecology** layers.

That matters because analyze/config/db/codecs are not isolated side features. They share owners with readers, diagnostics, renderers, source routing, and output routing. Patching TBLN next without protecting these owners can cause another axis-shuffle.

### 2.3 The candidate is mechanism-shaped but still label-driven inside sublanguages

The code is modular, but many modules encode shallow approximations:

- TBLN has a parser and writer, but the writer emits a fixed `; name` / `; type` pair and treats output types as `text`; it is not yet a schema-bearing tabular sublanguage with preserved type/value/null/escape identity.
- jq has regex-based support for a handful of patterns; it is not yet a transform-language boundary with a declared supported grammar and reference-locked error semantics.
- YAML/JSON readers normalize broad shapes, but the value-domain lattice is still too flat for scalar/object/array/null/malformed/multi-doc/mixed-shape branches.
- analyze mode renders a generic table report; it is not yet a separate discovery/advice program with driver quoting, dialect hints, jq advice, empty/header-only policy, and byte/prose contract.
- config/db topology loads JSON config and renders simple db list, but does not yet close default path, driver/DSN precedence, invalid resource precedence, debug, persistent DB, or external-driver diagnostic topology.
- codec handling is present, but target-substrate dependency equivalence is not proven for all codecs and output routes.

The common pattern is:

```text
public feature label
  -> plausible mechanism
  -> representative examples pass
  -> sibling grammar remains open
```

That is the exact failure v17-v26 were designed to prevent.

## 3. Phase-by-phase audit

### 3.1 Phase33: TBLN schema-bearing matrix — 16 / 40

Status:

```text
TBLN scaffold exists, but sublanguage closure is not achieved.
```

Likely missing child obligations:

```text
TBLN physical line grammar
metadata row grammar
name row grammar
type row grammar
default schema when name/type absent
column identity preservation
empty vs null cells
sparse rows
newline escaping
input typed conversion
output type annotation policy
custom null output
invalid grammar diagnostics
roundtrip input -> SQL -> output
```

The current writer likely over-normalizes by emitting fixed type metadata and treating every output column as text. The next TBLN pass should not patch failures individually; it should implement a `TBLN_SCHEMA_OBJECT` with explicit fields:

```text
names
inferred/default names
types
inferred/default types
metadata rows
data rows
cell raw text
cell semantic value
cell output spelling
invalid-line classifier
```

### 3.2 Phase34: dialect/value/renderer matrix — 17 / 38

Status:

```text
Reader and renderer registries exist, but dialect value domains are still under-terminalized.
```

Remaining branches show pressure in:

```text
yaml_input_value_domain
json_input_diagnostics
yaml_input_diagnostics
yaml_renderer_byte_grammar
json_input_control_overlay
json_renderer_byte_grammar
value_type_grammar
input_grammar
output_grammar
roundtrip
```

The next correction should split this into two different owners:

```text
reader value-domain semantics
renderer byte grammar
```

Do not let a renderer patch change reader normalization unless the numbered node explicitly imports that interaction.

### 3.3 Phase35: row-universe/lifecycle matrix — 19 / 29

Status:

```text
Best transferred phase, but still not closed.
```

The failures are concentrated around:

```text
skip_option_order: 6
row_number_overlay: 2
limit_preread_order: 1
state_lifecycle_mutation: 1
```

The code applies `skip_rows`, then `limit_rows`, then `row_number`. That is a real policy, but the matrix says the reference policy is not fully captured across headers, preread, `-is`, `-ir`, `-ilr`, `-inum`, empty/blank rows, and format-specific readers. The missing parent is not just an option-order bug; it is:

```text
ROW_WINDOW_PIPELINE = physical rows -> header/preread -> skip -> limit -> schema -> rownum -> SQL visibility
```

The next row-universe pass should produce a single pipeline object, not per-reader ad hoc row slicing.

### 3.4 Phase36: jq selector sublanguage — 5 / 22

Status:

```text
jq is still treated as pattern matching, not as an embedded transform boundary.
```

Failures include:

```text
jq_error_semantics: 7
jq_projection_semantics: 5
resource_suffix_selector_binding: 4
jq_transform_semantics: 1
```

The current approach is a set of regex branches. That is acceptable as a scoped compatibility shim only if the supported jq grammar is declared and exhaustively probed. It is not acceptable as a claim that the jq sublanguage is closed.

Minimum next grammar split:

```text
path selection: .foo, .foo.bar, .items[]
array projection: .[], .[n]
pipe composition: lhs | rhs
select predicate: select(.k), select(.k == "v")
object construction: {out:.path}
recursive descent: .. | select/has-like forms
resource suffix binding: file.json::.path vs -ijq path
error semantics: syntax, type mismatch, missing names, empty selection
```

### 3.5 Phase37: config/db/analyze mode — 2 / 24

Status:

```text
Mode-as-program transfer mostly failed.
```

This is the most important intermediate-work warning. The code has `load_config`, `render_dblist`, and `analyze`, but local matrix performance says these are only skeletons.

Required split:

```text
AnalyzeMode
  file import and schema discovery
  data sample table
  type inference table
  dialect advice
  JSON/JQ advice
  LTSV/delimiter advice
  driver-specific quote advice
  header-only/no-data policy
  -a vs -A output difference
  exact stdout/stderr/exit byte contract

ConfigDBMode
  default config path
  explicit config path
  JSON parse failures
  db selection and missing db
  dblist projection
  driver/DSN overlay
  debug projection
  sqlite vs non-sqlite behavior
  persistent DB lifecycle
```

This phase should not be patched in the same batch as TBLN. It is its own mode-program batch.

### 3.6 Phase38: codec/resource ecology — 5 / 26

Status:

```text
Codec and resource ecology remain target-substrate sensitive.
```

The code has compression handlers and some fallbacks. But the matrix still shows `compressed_output_route`, `compressed_input_route`, `resource_path_topology`, stdin aliases, and suffix selector binding failures. This means the resource topology is not just codec import/export; it is:

```text
resource route grammar
  + format guessing after codec suffix stripping
  + stdin alias binding
  + suffix selector `::` binding
  + output extension inference
  + target-substrate dependency parity
  + error precedence
```

The next codec work must prove dependency equivalence before counting local green rows as transfer-ready.

## 4. Implementation-transfer errors vs theory gaps

### Implementation-transfer errors

These are places where the theory is already clear and the candidate likely just has an incomplete implementation:

```text
some compressed route handling
some output route inference
some stdin aliases
some delimiter/quote handling
some row-number/header output details
some JSON/YAML renderer exactness
```

But even these need sentinel protection because they touch shared owners.

### Theory or terminalization gaps

These are not safe to patch as isolated rows:

```text
TBLN schema-bearing sublanguage
jq transform/error sublanguage
AnalyzeMode as separate discovery/advice program
ConfigDBMode as separate resource-topology program
ROW_WINDOW_PIPELINE across header/skip/preread/limit/rownum
DIAGNOSTIC_PRECEDENCE across reader/resource/SQL/output failures
TARGET_CODEC_SUBSTRATE_EQUIVALENCE
```

### Orchestrator failure

The strongest process-level finding:

```text
The orchestrator allowed one implementation pass to span six active matrices.
```

This is the same old gap in a new form: the meta-program can identify the right subtree, but if the handoff is too broad, the worker produces a shallow global approximation rather than subtree closure.

## 5. Proposed v27 meta-program patch

Add the following gate:

```text
INTERMEDIATE_WORK_TRIAGE_GATE
```

Triggered whenever a candidate patch is tested against an intermediate local matrix before official eval.

Required outputs:

```yaml
candidate_witness_type:
  replay_table | mechanism_scaffold | scoped_subtree_witness | gold_attempt
matrix_scope:
  active_phase_count: int
  active_owner_count: int
  broadness_status: bounded | overloaded
phase_pass_rates: []
failed_branch_rank: []
earliest_failed_transition_by_phase: []
implementation_transfer_errors: []
theory_terminalization_gaps: []
orchestrator_transition_errors: []
allowed_next_handoff_type:
  no_code_audit | conservation_only | single_subtree_closure | broad_integration | official_eval
```

Blocking rule:

```text
If active_phase_count > 2 and combined pass rate < 70%, the next step cannot be
another broad implementation patch. It must be no-code audit sanitation or a
single-subtree closure batch.
```

Add a second gate:

```text
SINGLE_SUBTREE_CLOSURE_CONTRACT
```

A worker baton must name exactly one primary subtree, imported preservation sentinels, allowed owners, forbidden owners, and closure criteria.

For this run, the allowed next handoff should be:

```text
single_subtree_closure
```

not:

```text
broad_integration
```

and definitely not:

```text
official_eval
```

## 6. Recommended next sequence

### Batch 0: no-code matrix sanitation

Before any patch:

```text
1. Attach each of the 115 local failures to numbered HOB children.
2. Mark which ones are TBLN, jq, mode-program, codec, row-window, or diagnostic.
3. Identify shared implementation owners touched by each child.
4. Import preservation sentinels from Phase 31 official green leaves.
5. Choose exactly one subtree for the next implementation batch.
```

### Batch 1: choose one of two viable paths

Option A, if optimizing official remaining failure count:

```text
TBLN_SCHEMA_BEARING_SUBLANGUAGE only
owners: tbln_reader_writer, value_normalizer adapter, renderer adapter
forbidden: jq_selector, config_db_topology, analyze_renderer, sql_resource_binder, global source_router
closure target: phase33 >= 36/40 with no preservation regressions
```

Option B, if optimizing local matrix weak-phase risk:

```text
CONFIG_DB_ANALYZE_MODE_AS_PROGRAM only
owners: analyze_renderer, config_db_topology, mode_dispatch, diagnostic_emitter
forbidden: tbln_reader_writer, jq_selector, codec_router except fixtures required by analyze
closure target: phase37 >= 18/24 with no CLI/config/analyze preservation regressions
```

I would choose **Option A** if the goal is official score movement, because Phase 31 still shows TBLN as the largest official remaining subtree. I would choose **Option B** if the goal is methodological stability, because Phase 40 shows the mode-program layer is the weakest transfer.

### Batch 2 and later

```text
Batch 2: ROW_WINDOW_PIPELINE
Batch 3: JQ_SUBLANGUAGE_BOUNDARY
Batch 4: TARGET_CODEC_SUBSTRATE_EQUIVALENCE
Batch 5: CONFIG_DB_ANALYZE_MODE_AS_PROGRAM, if not chosen earlier
Batch 6: output renderer byte exactness
```

## 7. Bottom line

The intermediate work is valuable, but not because it is close to green. It is valuable because it tells us the next failure is not discovery. It is **closure discipline**.

Current state:

```text
mechanism architecture:      present
anti-replay posture:         acceptable
subtree closure:             absent
mode-as-program transfer:    very weak
jq transfer:                 weak
codec/resource transfer:     weak
TBLN transfer:               partial
row-window transfer:         partial but promising
```

Next invariant:

```text
A broad local matrix is for triage, not for patch authorization.
Patch authorization must happen at one numbered subtree at a time.
```
