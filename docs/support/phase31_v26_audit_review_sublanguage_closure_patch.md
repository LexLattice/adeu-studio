# Phase 31 Audit Review and v26 Sublanguage-Closure Patch

Authority layer: `post_eval_pressure_synthesis`.

Scope: review of `phase31_remaining_failure_audit_after_contextual_star.md`, `phase31_bucket_samples.md`, `phase31_remaining_failure_summary.json`, and `phase31_failure_rows.jsonl`.

## 1. Verdict

The Phase 31 audit is directionally correct and methodologically valuable.

The current run is not a broad new product-theory gain; it is a clean conservation repair:

```text
current: 1127 passed / 275 failed / 1 skipped / 1403 total, score 79
phase25: 1120 passed / 282 failed / 1 skipped / 1403 total, score 79
phase28: 1126 passed / 276 failed / 1 skipped / 1403 total, score 79
```

Delta:

```text
vs phase25: +7 newly passing rows, -0 regressions
vs phase28: +1 newly passing row, -0 regressions
```

Interpretation:

```text
Phase 30 fixed the contextual-star / compact SELECT*FROM regression
without rebreaking wildcard, glob, quoted identifiers, arithmetic, empty-query,
or blank-row sentinel branches.
```

This matters because Phase 26 showed the previous six regressions were caused by a shared-owner/context overreach: a broad SQL comma/resource-binding patch leaked relation-list logic into projection-list, quoted-identifier, arithmetic, empty-query, and blank-field contexts. Phase 31 confirms that contextual repair can be made conservation-safe.

## 2. Main agreement with the audit

The audit's central diagnosis is right:

```text
The next large gap is not another resource-router pass.
The dominant remaining miss is public format / transform sublanguage terminalization.
```

The remaining failure surface is:

```text
tbln_grammar:                 53
input_format_dialect:         45
input_row_shape_semantics:    37
jq_json_projection:           34
config_db_topology:           22
analyze_report_mode:          21
diagnostic_precedence:        14
output_renderer_byte_grammar: 14
compression_io:               13
stdin_resource_binding:       13
resource_path_topology:        4
sql_semantics:                 4
state_lifecycle_mutation:      1
```

The method pressure is similarly clear:

```text
DIALECT_SUBLANGUAGE_TERMINALIZATION_MATRIX       169
MODE_AS_PROGRAM_MATRIX                            43
RESOURCE_TO_LANGUAGE_PIPELINE_MATRIX              30
NEGATIVE_UTILITY_FATAL_PRECEDENCE_LATTICE         14
OUTPUT_ROUTE_AND_DOWNSTREAM_CONSUMER_MATRIX       14
SQL_SUBSTRATE_BREADTH_GATE                         5
```

So the right next frontier is not:

```text
more generic source routing
more broad SQL-resource binder work
more renderer surface guessing
```

It is:

```text
format names -> grammar-bearing sublanguages
jq flag/path suffix -> embedded transform language
row options -> row-universe lifecycle lattice
analyze/config/db -> mode-as-program re-entry
compression -> target-substrate dependency equivalence
```

## 3. Main correction: the audit is classification-good, but not yet fully worker-ready

The statement:

```text
No current failures were unmapped by the Phase 26 taxonomy.
```

is useful but too weak. The taxonomy has no unmapped rows, but it still has a few **misattached** rows.

Examples found in the Phase 31 row file:

```text
eval.tests.test_help_output.test_dash_h_help_text_matches_dash_help_ignoring_stream
  bucketed as: tbln_grammar::tbln_input_grammar
  actual layer: CLI help alias / control-plane grammar

eval.tests.test_help_output.test_dash_h_prints_help_to_stderr_and_exit_zero
  bucketed as: compression_io::compressed_output_route
  actual layer: CLI help alias / stdout-stderr-exit contract

eval.tests.test_argparse_validation.test_integer_flags_accept_negative_and_zero_parsewise[args0]
eval.tests.test_argparse_validation.test_integer_flags_accept_negative_and_zero_parsewise[args1]
eval.tests.test_argparse_validation.test_integer_flags_accept_negative_and_zero_parsewise[args2]
  bucketed as: tbln_grammar::tbln_input_grammar
  actual layer: CLI integer flag parse grammar
```

This does not overturn the audit. TBLN remains the largest clean bounded subtree even after removing these stray control-plane rows. But it means the audit should not be handed directly to a worker as a patch contract.

### v26 patch: `POST_AUDIT_BUCKET_SANITY_GATE`

Before implementation handoff, every post-eval bucket must pass a sanity check:

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
  handoff_status:
    accepted_for_batch |
    bucket_suspect_blocked |
    reclassified_before_batch |
    deferred_manual_review
```

Blocking rule:

```text
No worker handoff may include a bucket whose rows have not passed
bucket sanity or been explicitly reclassified.
```

This prevents the worker from patching `tbln_reader_writer` to fix `-h`, or patching codecs to fix help stream behavior.

## 4. Refined reading of the remaining frontier

The remaining 275 failures are best understood as five frontiers, not thirteen independent patch queues.

### Frontier A: schema-bearing tabular sublanguages

Primary bucket:

```text
tbln_grammar: 53
```

TBLN is not just an input format. It is a schema-bearing tabular sublanguage:

```text
physical line grammar
metadata/header rows
optional name header
optional type header
default column identity when headers are absent
typed value conversion
null / empty / sparse cell policy
SQL schema binding
output writer byte grammar
roundtrip behavior
diagnostic/fatal error grammar
```

The audit's recommendation to make TBLN the next batch is right, but the batch must be framed as `SCHEMA_BEARING_TABULAR_FORMAT_GATE`, not merely `TBLN_AS_SUBLANGUAGE_GATE`.

### Frontier B: value-domain dialects

Buckets:

```text
input_format_dialect: 45
output_renderer_byte_grammar: 14
```

This family covers JSON, YAML, LTSV, delimited readers, invalid syntax, scalar/object/array/null values, duplicate columns, non-UTF8 bytes, YAML output byte grammar, and JSON renderer exactness.

The missing parent is:

```text
DIALECT_VALUE_DOMAIN_AND_RENDERER_PAIR
```

not just:

```text
input format parser
```

### Frontier C: row-universe lifecycle overlays

Bucket:

```text
input_row_shape_semantics: 37
```

This remains too flat. The row universe must distinguish:

```text
physical blank line
empty record
delimiter-only record
short row
sparse row
one-column empty field
missing cell after delimiter
skip before header
header before skip
preread before limit
limit before import
row-number column identity
row-number after filtering
row-number before SQL
```

The right gate is:

```text
ROW_UNIVERSE_LIFECYCLE_LATTICE
```

### Frontier D: embedded transform sublanguages

Bucket:

```text
jq_json_projection: 34
```

jq must be promoted from dotted selector to embedded transform sublanguage:

```text
array indexing
array iteration
recursive descent
multiple filters
object construction
key rename
type mismatch errors
syntax errors
file.json::.suffix binding
YAML/JSON interop
analyze-mode advice interaction
```

The right gate is:

```text
JQ_AS_EMBEDDED_TRANSFORM_SUBLANGUAGE
```

### Frontier E: mode-as-program and target-substrate equivalence

Buckets:

```text
config_db_topology: 22
analyze_report_mode: 21
diagnostic_precedence: 14
compression_io: 13
```

These should not be mixed with ordinary query-output leaves.

Mode families need:

```text
MODE_AS_PROGRAM_MATRIX
```

Compression needs:

```text
TARGET_CODEC_SUBSTRATE_GATE
```

because zstd/lz4 behavior can pass locally and still fail in the evaluator substrate if optional dependencies or helpers are absent.

## 5. v26 meta-program additions

### 5.1 `POST_AUDIT_BUCKET_SANITY_GATE`

Purpose:

```text
Prevent post-eval classification buckets from becoming implementation batons
when their row attachments are inconsistent with namespace, failure surface,
or implementation owner.
```

Trigger:

```text
Any post-eval audit is used to form a worker task.
```

Rule:

```text
Every failure row must pass bucket sanity or be reclassified before worker handoff.
```

### 5.2 `FORMAT_SUBLANGUAGE_CLOSURE_GATE`

Purpose:

```text
A public format name cannot remain a label. It must descend into an input
language, output language, value-domain language, schema-binding language, and
error language when those surfaces are public.
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
A format subtree is not closed by fixing parser examples alone.
It closes only when input, output, binding, diagnostics, and option overlays are
covered or explicitly deferred.
```

### 5.3 `SCHEMA_BEARING_TABULAR_FORMAT_GATE`

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

For the current task, TBLN is the triggering instance.

### 5.4 `READER_WRITER_PAIR_CLOSURE_GATE`

Purpose:

```text
If a dialect exists as both an input and output format, parser success and
writer success must be paired through roundtrip and byte grammar probes.
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

### 5.5 `SHARED_OWNER_INTERFACE_BOUNDARY_GATE`

Purpose:

```text
Prevent format-specific repairs from globally perturbing reader_registry,
value_normalizer, renderer_registry, source_router, sql_resource_binder, or
diagnostic_emitter.
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

### 5.6 `CONTROL_PLANE_RESIDUAL_DE_LUMPING_GATE`

Purpose:

```text
Ensure CLI/help/argparse rows do not remain hidden under dialect or codec
buckets.
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

## 6. Review of the recommended next batch

The audit recommends:

```text
TBLN_AS_SUBLANGUAGE_GATE
```

I agree, with two hardening changes.

### 6.1 Run bucket sanity first

Before any source patch:

```text
Batch 0: audit-bucket sanity
  reclassify stray -h / argparse rows out of TBLN/compression
  produce corrected TBLN row list
  produce corrected compression row list
  attach every remaining row to a numbered HOB child
```

This should be a no-code batch.

### 6.2 Make TBLN a schema-bearing tabular format batch

The implementation baton should not say:

```text
Fix tbln_grammar failures.
```

It should say:

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

## 7. Required pre-patch TBLN probe matrix

### 7.1 Input grammar probes

```text
TBLN-I01 name header present
TBLN-I02 type header present
TBLN-I03 name + type headers present
TBLN-I04 no name header
TBLN-I05 no type header
TBLN-I06 no headers
TBLN-I07 metadata rows before schema rows
TBLN-I08 sparse row with missing trailing cells
TBLN-I09 delimiter-only / empty fields
TBLN-I10 mismatched too many cells
TBLN-I11 empty file EOF
TBLN-I12 single-row EOF during preread
TBLN-I13 newline inside value / escaped newline
TBLN-I14 special characters / unicode
```

### 7.2 Value and type probes

```text
TBLN-V01 int conversion
TBLN-V02 float conversion
TBLN-V03 bool conversion
TBLN-V04 timestamp/text fallback
TBLN-V05 unknown type defaults to text or errors, reference-locked
TBLN-V06 empty field default policy
TBLN-V07 custom -inull replacement
TBLN-V08 literal null not replaced by default unless reference says so
```

### 7.3 SQL binding probes

```text
TBLN-S01 SELECT named columns from TBLN
TBLN-S02 SELECT auto columns when names absent
TBLN-S03 WHERE on typed numeric column
TBLN-S04 ORDER BY typed numeric column
TBLN-S05 aggregate over typed numeric column
TBLN-S06 JOIN TBLN with CSV or second TBLN
TBLN-S07 column identity with reserved words / special names
```

### 7.4 Output grammar probes

```text
TBLN-O01 basic output byte grammar
TBLN-O02 name row output grammar
TBLN-O03 type row output grammar
TBLN-O04 newline escaping
TBLN-O05 custom -onull output
TBLN-O06 empty result set output
TBLN-O07 final newline
TBLN-O08 raw/table-to-TBLN route interaction
```

### 7.5 Roundtrip probes

```text
TBLN-R01 TBLN input -> TBLN output preserves names/types where expected
TBLN-R02 TBLN input -> JSON output preserves typed values
TBLN-R03 TBLN input -> YAML output preserves null/value domains if renderer touched
TBLN-R04 TBLN output -> TBLN re-import if supported by scope
```

### 7.6 Diagnostic probes

```text
TBLN-D01 invalid grammar during query
TBLN-D02 invalid grammar during analyze
TBLN-D03 mismatched column count message
TBLN-D04 EOF / empty file message
TBLN-D05 invalid type annotation message
TBLN-D06 stderr/stdout/exit split
```

### 7.7 Preservation sentinels

Import at minimum:

```text
SQL tokenizer/contextual-star sentinels
resource pipeline sentinels
CSV blank / delimiter-only / -inull sentinels
JSON/YAML output sentinels if renderer_registry or value_normalizer is touched
help/argparse sentinels if cli_parser is touched
config/analyze sentinels if diagnostic_emitter or mode_dispatch is touched
```

## 8. Alternative small batch: codec substrate

The audit's alternative small batch is also valid:

```text
TARGET_CODEC_SUBSTRATE_GATE for zstd/lz4
```

This is less conceptually central than TBLN, but it is a clean test of the methodological equivalence doctrine:

```text
local codec success
  != target-substrate codec success
```

Required sequence:

```text
1. Probe evaluator-like target image for zstd/lz4 import/helper availability.
2. Decide portable fallback vs bundled dependency vs explicit unsupported behavior.
3. Lock input and output codec bytes separately.
4. Run extension guessing and explicit -oz override probes.
5. Import resource-pipeline and output-router preservation sentinels.
```

This can be a low-risk score increment, but it should not preempt the larger sublanguage-closure repair unless the orchestrator wants a substrate-equivalence micro-test.

## 9. Orchestrator sequence for next run

Recommended sequence:

```text
P0 no-code audit sanitation
  - run POST_AUDIT_BUCKET_SANITY_GATE
  - reclassify control-plane residuals
  - produce corrected per-bucket row lists
  - attach rows to numbered HOB children

P1 no-code TBLN reference matrix
  - generate TBLN probes from schema-bearing tabular format tree
  - lock reference stdout/stderr/exit/files
  - mark unknowns/deferred siblings explicitly

P2 implementation handoff
  - bounded to tbln_reader_writer first
  - shared owners touched only through declared adapter boundaries
  - preservation sentinels imported before patch

P3 local candidate gate
  - TBLN matrix green
  - preservation sentinels green
  - no new control-plane or SQL-tokenizer regressions

P4 official method run
  - classify official delta by numbered TBLN nodes
  - do not use official rows as clean first-pass truth
```

Optional branch:

```text
P1b TARGET_CODEC_SUBSTRATE_GATE
  - run only if a small substrate-equivalence batch is desired before TBLN
```

## 10. Expected failure modes if the next worker is underconstrained

If the worker receives only:

```text
Fix TBLN failures.
```

likely bad outcomes:

```text
special-cases visible test strings
implements whitespace splitting rather than TBLN schema grammar
fixes input but not output
fixes output but not SQL schema binding
changes value_normalizer globally and regresses JSON/YAML/CSV/null behavior
changes diagnostic_emitter globally and regresses help/config/analyze errors
uses local codec/dependency behavior as target truth
```

If the worker receives the v26 baton:

```text
Close SCHEMA_BEARING_TABULAR_FORMAT_GATE for TBLN,
with bucket sanity, reference matrix, shared-owner boundaries,
and preservation sentinels.
```

then the run becomes a clean method test of sublanguage closure.

## 11. Bottom line

Phase 31 confirms that the contextual-tokenizer fix was successful and conservation-safe. It also sharpens the remaining frontier: the score is now blocked mainly by dialect/format/transform sublanguages that were recognized as names but never terminalized as grammars.

The audit is good enough as pressure synthesis, but not yet good enough as a worker baton. The next meta-program revision should insert a bucket-sanity gate and then require schema-bearing sublanguage closure, starting with TBLN.
