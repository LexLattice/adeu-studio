# Phase 22 Optimal Failure-Coverage Methods and Discovery-Layer Attribution

Authority layer: methodological / post-eval pressure synthesis.

This note answers a specific question: for the remaining `trdsql` failures, which methods would have covered them earlier, at which layer they should have been uncovered, and which triangulation axis should have carried the signal.

It is not a patch list. It is a coverage-method selection matrix for the next meta-program revision.

---

## 0. Current state

Latest usable run:

```text
score: 72
raw rows: 1031 passed / 371 failed / 1 skipped / 1403 total
```

Delta from the guarded score-66 predecessor:

```text
+75 passed rows
-75 failed rows
```

Phase 22 remaining buckets:

```text
input_format_dialect:        59
tbln_grammar:                50
unclassified:                46
diagnostic_precedence:       34
jq_json_projection:          34
compression_io:              31
input_row_shape_semantics:   31
config_db_topology:          30
analyze_report_mode:         22
stdin_resource_binding:      19
sql_semantics:                9
output_routing_guessing:      5
resource_path_topology:       2
```

The Phase 20 preservation pass was effective because it imported prior green leaves as explicit preservation obligations. It closed `509 / 509` mapped preservation leaves and repaired CLI/config diagnostics, analyze/report prose, renderer byte grammar, TBLN metadata rows, YAML null/quote behavior, JSON object rehydration, and gzip side-effect bytes. The remaining failures are therefore not merely “forgot earlier wins.” They are mostly unclosed sibling families outside the preservation scope.

---

## 1. Main conclusion

The optimal next method is not another single-track audit or another raw official-failure patch. The right method is a **triangulated branch-matrix compiler**:

```text
remaining failure bucket
  -> earliest upstream discriminator
  -> active semantic pools
  -> numbered HOB child subtree
  -> reference/scout/source observation requirement
  -> preservation owner import
  -> pre-patch probe matrix
  -> bounded implementation owner
```

The remaining failures are best explained by five upstream discriminators:

```text
D1  Resource-to-reader-to-SQL binding pipeline
D2  Input dialect and value-domain terminalization
D3  TBLN / jq / JSON projection sublanguages
D4  Mode/resource topology and fatal precedence
D5  Output routing / downstream byte contract
```

These should not be patched independently. They are connected by shared implementation owners:

```text
source_router
codec_router
reader_registry
value_normalizer
jq_selector
sql_resource_binder
mode_dispatcher
renderer_registry
output_router
diagnostic_emitter
config_db_topology
```

The key v24 invariant:

```text
A remaining failure bucket is not implementation-ready until the orchestrator
has identified the earliest layer that could have found it and has compiled the
corresponding triangulation axes into a branch matrix with preservation sentinels.
```

---

## 2. Layer vocabulary used here

```text
L0  Visible README / task statement / product intention.
L1  Native base ontology: what kind of program is this?
L2  Deterministic HOB activation and inherited child obligation fill.
L3  Orthogonal semantic pool triangulation: mechanism, utility, resource, dialect,
    transform, output, negative, equivalence, historical preservation.
L4  Public empirical scout: help, no-args, public reference behavior, controlled fixtures.
L5  Reference observation lock: split stdout/stderr/exit/files, byte and side-effect truth.
L6  Source-postmortem operator discovery, labeled as source-derived, not clean first-pass truth.
L7  Implementation handoff and owner map.
L8  Local candidate / sealed / metamorphic validation.
L9  Official eval pressure.
```

Earliest layer means the first layer where the program should have become suspicious enough to force a branch, not necessarily the layer that can provide exact byte truth.

---

## 3. Triangulation axes

```text
P  Program-mechanism ontology
   What machinery does the program imply: resource routes, readers, SQL substrate,
   renderers, modes, diagnostics?

U  Intent / utility
   What user job would break if this branch is absent: query files, shape input,
   convert output, inspect unknown data, diagnose malformed resources?

S  Public schema
   What help/usage/options/modes reveal: formats, compression flags, config/db flags,
   analyze modes, jq flags, output guessing flags?

E  Empirical public scout / reference observation
   What exact public behavior happens under small fixtures: stdout/stderr/exit/files,
   bytes, precedence, side effects?

R  Resource ecology / route topology
   How resources are named, opened, decoded, expanded, routed, and cleaned:
   stdin/stdout, files, globs, compressed files, output files, config/db files.

D  Dialect/value-domain grammar
   How input formats turn bytes into rows and values: CSV/LTSV/YAML/TBLN/JSON/JQ,
   empty/scalar/object/array/null/malformed rows.

T  Transform / embedded language substrate
   How SQL/jq/analyze transforms map resource-bound data to results.

O  Output/downstream projection
   How results become bytes/files/compression/table formats and how downstream users
   consume those bytes.

N  Negative utility / fatal precedence
   What false success is dangerous; which error should win; which channel/exit owns it?

H  Historical preservation / cross-run owner map
   Which old wins share implementation owners and must be imported as sentinels.

M  Methodological equivalence / witness bundle
   Whether local/reference/official artifacts, substrates, and observation channels are equivalent.
```

---

## 4. Bucket-by-bucket optimal discovery matrix

### 4.1 `input_format_dialect` — 59 rows

**Earliest layer:** `L2 -> L3`.

The dialect names were public and ontologically obvious, but the branch was under-terminalized. The missed step was not “discover CSV/YAML/JSON/TBLN exists”; it was “compile every public input dialect into a value-domain grammar and error contract.”

**Best triangulation axes:** `S + D + U + E`, with `H` sentinels.

**Optimal method:** `DIALECT_VALUE_DOMAIN_MATRIX`.

Required child axes:

```text
format = csv | tsv | psv | ltsv | json | jsonl | yaml | tbln | text | width
shape = empty | header_only | one_row | trailing_blank | scalar | object | array |
        nested | mixed | null | binary/non_utf8 | malformed
options = header | no_header | skip | limit | delimiter | null_value | row_number |
          explicit_no_guess | jq/selector where applicable
surface = SQL import | analyze | output renderer | diagnostic
```

**Probe form before patch:** reference and candidate matrix rows for each dialect family, with at least one happy path, one malformed path, one empty/header-only path, and one option-composition path. Do not ask the worker to patch “input formats” until it has a numbered matrix.

**Why this would have covered failures:** most remaining input-format failures are sibling leaves of known public formats. A HOB inherited-child fill would have kept them open until dialect grammar, value conversion, and error surface were accounted for.

---

### 4.2 `tbln_grammar` — 50 rows

**Earliest layer:** `L4 -> L2 re-entry`, then `L2 -> L3`.

TBLN was a named public format, but it was treated as a format label rather than its own row language with metadata, headers, nulls, sparse rows, comments/blank lines, and output grammar.

**Best triangulation axes:** `S + D + O + E`, source-postmortem if public scouts cannot infer grammar.

**Optimal method:** `TBLN_AS_SUBLANGUAGE_GATE`.

Required child axes:

```text
TBLN input grammar:
  metadata rows
  table name rows
  header rows
  data rows
  blank/comment rows
  null / empty / missing cell policy
  sparse or irregular row policy
  malformed grammar and fatal precedence

TBLN output grammar:
  metadata ordering
  field ordering
  escaping / quoting
  final newline
  stdout vs file route
  null policy
```

**Probe form before patch:** one public-reference micro-fixture per TBLN grammar primitive, plus one workflow probe that imports TBLN and exports TBLN. A failed TBLN preservation probe with zero covered leaves should not be ignored; it should create a new subtree rather than stay informational.

**Why this would have covered failures:** TBLN has enough internal grammar that a single renderer/input example cannot generalize. The correct method is sublanguage terminalization, not renderer tweaking.

---

### 4.3 `unclassified` — 46 rows

**Earliest layer:** `L9 -> L2 audit re-entry`, but only because prior layers failed to classify them.

Unclassified is not a true parent. It is a bookkeeping failure.

**Best triangulation axes:** `H + P + E + N`.

**Optimal method:** `UNCLASSIFIED_ZERO_TOLERANCE_GATE`.

Required split candidates:

```text
- input row shape/value conversion
- resource route/name binding
- output byte exactness
- diagnostic precedence
- config/db topology
- SQL state/mutation
- implementation transfer bug
- methodological equivalence failure
```

**Probe form before patch:** classification probes only, not product patches. Each row must receive an ontology path, owner, earliest transition, and at least one nearest-sibling pass/fail contrast.

**Why this would have covered failures:** unclassified rows often hide the highest-leverage parent discriminator. Patching them raw reintroduces the exact failure mode v16/v17 were designed to prevent.

---

### 4.4 `diagnostic_precedence` — 34 rows

**Earliest layer:** `L3 -> L4`, with a public scout requirement at `L4`.

Negative utility would have discovered the family, but exact precedence and wording require reference observation.

**Best triangulation axes:** `N + E + S + R`, with source-postmortem if two public observations conflict.

**Optimal method:** `FATAL_PRECEDENCE_LATTICE`.

Required child axes:

```text
flag parse error
missing value error
resource open error
codec decode error
reader grammar error
jq/selector error
SQL execution error
output file open/write error
config/db/driver error
which stdout/stderr/exit wins
whether partial side effect occurred before failure
```

**Probe form before patch:** collision probes where two possible errors are present at once. Example pattern:

```text
malformed input + bad output route
bad config + bad SQL
bad compression flag + unreadable file
bad jq + malformed JSON
```

**Why this would have covered failures:** diagnostics are not independent strings; they are first-fatal gate order plus channel/exit projection. A patch to string text without precedence probes will oscillate.

---

### 4.5 `jq_json_projection` — 34 rows

**Earliest layer:** `L1 -> L2` for “jq is a transform sublanguage,” then `L4 -> L2` if help exposed selector controls.

**Best triangulation axes:** `T + D + U + E`.

**Optimal method:** `JQ_JSON_PROJECTION_SUBLANGUAGE_GATE`.

Required child axes:

```text
selector syntax = absent | dotted path | nested path | array index | invalid syntax
input shape = object | array | nested array/object | scalar | null | malformed
result shape = scalar | object | array | empty | missing path
consumer = SQL import | analyze | output JSON/YAML/raw | diagnostic
suffix/source syntax = flag jq | resource suffix path | explicit JSON/YAML interop
```

**Probe form before patch:** paired reference/candidate probes over the same nested fixture, varying only selector and result shape. Add negative probes where invalid selector must not silently degrade to unfiltered input.

**Why this would have covered failures:** utility can discover “users project nested JSON,” but exact jq semantics need empirical observation or source-postmortem. The optimal method is a sublanguage matrix, not ad hoc JSON parsing.

---

### 4.6 `compression_io` — 31 rows

**Earliest layer:** `L2`, because compressed files are resource routes, not row parsing details. Public help/output flags then force `L4 -> L2` re-entry.

**Best triangulation axes:** `R + S + E + M`, possibly source-postmortem for unsupported dependency parity.

**Optimal method:** `CODEC_ROUTE_MATRIX`.

Required child axes:

```text
codec = gzip | bzip2 | xz | zstd | lz4
route = input file | wildcard input | stdin | output file | stdout
selection = magic autodetect | extension inference | explicit -oz override | no-guess
format interaction = compressed extension stripped before format inference
error = missing dependency | invalid compressed bytes | wrong codec flag | unsupported codec
byte witness = magic/header/trailer where applicable
```

**Probe form before patch:** route-level probes, not reader-level probes. For every codec supported or emulated, test both “decode then parse dialect” and “render then encode route.” Include one explicit override case where extension and flag disagree.

**Why this would have covered failures:** compression touches routing, format inference, output side effects, and dependency equivalence. Treating it as `open_text()` decoration misses most official pressure.

---

### 4.7 `input_row_shape_semantics` — 31 rows

**Earliest layer:** `L2 -> L3`.

This is the row-universe sibling of input dialect grammar. It is not about file format alone; it is about how rows are created, skipped, limited, numbered, named, and rejected.

**Best triangulation axes:** `P + D + U + E`.

**Optimal method:** `ROW_UNIVERSE_AND_OPTION_OVERLAY_MATRIX`.

Required child axes:

```text
row source = header row | data row | blank row | trailing row | malformed row
options = -ih | -is | -ilr | -ir | -inum | -inull | explicit format | no-guess
naming = header names | default c1/c2 | row-number column | collision with existing name
policy = skip before/after header | limit before/after skip | blank included/excluded
consumer = SQL | analyze | renderer | diagnostics
```

**Probe form before patch:** small CSV/LTSV/TBLN/JSONL fixtures where only one row-shape variable changes. Add metamorphic probes: increasing limit by one should add exactly one row after the same skip/header policy.

**Why this would have covered failures:** this branch sits between input decoding and SQL binding. Without row-universe probes, patches will fix one dialect while regressing header/skip/limit/numbering behavior.

---

### 4.8 `config_db_topology` — 30 rows

**Earliest layer:** `L4 -> L2` from public help/schema; also discoverable by utility if “query configured databases” is treated as a real user job.

**Best triangulation axes:** `S + R + U + N + E`.

**Optimal method:** `MODE_AS_PROGRAM_AND_DB_RESOURCE_TOPOLOGY`.

Required child axes:

```text
config path = absent | default | explicit valid | explicit missing | explicit malformed
DB = temp SQLite | persistent DB file | configured DB | invalid DSN | invalid driver
modes = query | analyze | dblist | debug | help/version
side effect = DB file creation | table persistence | config read diagnostics
channel = stdout/stderr/debug lines/exit
```

**Probe form before patch:** separate mode probes for `-config`, `-db`, `-dblist`, `-driver`, `-dsn`, and `-debug`, plus one workflow probe where config changes ordinary query behavior. Include preservation sentinels for CLI control-plane and diagnostics before touching parser/mode dispatcher.

**Why this would have covered failures:** config/db is a resource substrate and mode family, not passive CLI metadata. It must be modeled before ordinary query behavior is considered closed.

---

### 4.9 `analyze_report_mode` — 22 rows

**Earliest layer:** `L4 -> L2` public schema re-entry, with `U` as a strong independent signal.

**Best triangulation axes:** `U + S + O + E + H`.

**Optimal method:** `ANALYZE_AS_DISCOVERY_PROGRAM_GATE`.

Required child axes:

```text
input dialect advice = CSV-looking JSON | LTSV-looking CSV | delimiter advice | jq advice
file shape = header_only | no_data | mixed types | nested JSON | SQL-only mode
renderer = prose header | data types table | data samples table | examples block
DB/driver = quote characters | reserved words | configured driver
channel/exit = stdout/stderr/fatal cases
```

**Probe form before patch:** golden-ish byte probes for analyze report sections, but grouped by section owner. Add workflow probes: “user inspects unknown file, receives advice, then runs suggested query.”

**Why this would have covered failures:** analyze is not a diagnostic side path. It is a user-facing mode with its own renderer and transform. The utility lane should have promoted it early; public scout gives exact mode entry.

---

### 4.10 `stdin_resource_binding` — 19 rows

**Earliest layer:** `L1 -> L2` from the program class “SQL over resources,” then `L2 -> L3` for path/name binding.

**Best triangulation axes:** `R + T + U + E`.

**Optimal method:** `STDIN_AS_NAMED_RESOURCE_GATE`.

Required child axes:

```text
stdin role = data stream | query file | absent source | literal table name token
format = explicit flag | guessed from context | no-guess
binding = table name stdin | default table name | alias | resource suffix selector
composition = join stdin with file | query stdin only | output to stdout/file
```

**Probe form before patch:** pair equivalent file and stdin inputs, then vary only binding syntax. Add a join probe involving stdin and a file resource.

**Why this would have covered failures:** stdin is not only an input stream; in this program class it becomes a resource that must be imported, named, and bound into SQL.

---

### 4.11 `sql_semantics` — 9 rows

**Earliest layer:** `L1 -> L2`.

The core discriminator is still:

```text
SQL as embedded computation substrate
  != handcrafted file-query subset
```

**Best triangulation axes:** `T + U + E`, source-postmortem if exact rewrite rules remain ambiguous.

**Optimal method:** `SQL_SUBSTRATE_BREADTH_GATE`.

Required child axes:

```text
expression-only SELECT
resource-backed SELECT
joins / aliases / comma joins
subqueries
multiple semicolon statements
mutation / persistent state
functions / aggregates / order / case / casts / nulls
resource token rewrite vs DB-native token semantics
```

**Probe form before patch:** metamorphic SQL probes where semantics should be delegated to the DB once resources are bound. Add negative probes for resource-looking tokens in invalid contexts.

**Why this would have covered failures:** a broad SQL engine cannot be validated by a few SELECT-over-file examples. The proof obligation is that the candidate has a real embedded-language substrate with resource binding at its boundary.

---

### 4.12 `output_routing_guessing` — 5 rows

**Earliest layer:** `L4 -> L2` from public options and output route behavior.

**Best triangulation axes:** `O + R + S + E`.

**Optimal method:** `OUTPUT_ROUTE_INFERENCE_MATRIX`.

Required child axes:

```text
route = stdout | output file
format source = explicit output flag | output extension | no-guess | conflicting flags
codec source = explicit -oz | output extension | no-guess | conflicting extension/flag
side effect = file created | file bytes compressed | stdout empty/non-empty | error on bad path
priority = multiple output flags | last wins? first wins? fixed priority?
```

**Probe form before patch:** output route probes must assert stdout, stderr, exit, file existence, file bytes, and codec magic separately.

**Why this would have covered failures:** output guessing is a route+renderer+codec precedence problem, not renderer formatting.

---

### 4.13 `resource_path_topology` — 2 rows

**Earliest layer:** `L2`, with utility and resource ecology triggers.

**Best triangulation axes:** `R + U + E + H`.

**Optimal method:** `PATH_IDENTITY_AND_ROUTE_NORMALIZATION_GATE`.

Required child axes:

```text
spaces
quotes
tilde expansion
glob no-match
glob multi-match
relative/absolute path
SQL token quoting
path-to-table display identity vs internal table name
```

**Probe form before patch:** a small path morphology matrix and a preservation sentinel for any source-router changes.

**Why this would have covered failures:** path handling has high shared-owner risk; even two failures can regress many previously solved resource-binding rows.

---

## 5. Which axis should have found what?

### Ontology-first discoveries

These should have appeared from native semantic descent over “SQL over files / tabular conversion” before public scouting:

```text
resource-to-SQL binding
stdin as resource
SQL as embedded language
row universe / header / skip / limit semantics
output as downstream-consumer byte contract
negative utility around malformed data and false success
```

They are not exact-byte truths, but they are strong enough to create HOB inherited obligations.

### Public-schema / empirical scout discoveries

These require observing help or public reference behavior:

```text
exact list of input/output formats
presence of jq controls
compression controls
analyze modes
config/db/driver controls
multiple output flag priority
stdout/stderr/exit split
fatal precedence and diagnostic wording
output file guessing and compression side effects
```

The scout should not merely record these. It should trigger `L4 -> L2` re-entry and create numbered children.

### Utility/intent discoveries

Utility should have forced these even before exact observations:

```text
users query ad hoc files as resources
users join heterogeneous resources
users inspect unknown files before querying
users project nested JSON/YAML values
users export output to downstream tools
users expect compressed files to behave like files
users expect malformed data to fail visibly, not silently succeed
```

Utility cannot close byte grammar or exact error precedence, but it should generate workflow and negative-utility probes.

### Source-postmortem discoveries

Source-postmortem is optimal only after ontology/public/utility leave ambiguity. It is especially useful for:

```text
TBLN exact grammar
zstd/lz4 dependency behavior
Go tablewriter alignment and renderer priority
Go JSON escaping behavior
driver-specific quote characters
SQL token rewrite rules
analyze report section construction
```

Source-derived facts should patch the meta-program as operator triggers, not be laundered into first-pass evidence.

### Historical preservation discoveries

The cross-run owner map should cover:

```text
CLI/parser exactness
analyze/report text already won
config/db diagnostics already won
renderer byte grammar already won
wildcard/resource wins
raw/YAML/TBLN partial wins
```

Whenever source_router, reader_registry, renderer_registry, mode_dispatcher, or diagnostic_emitter is touched, the relevant previous wins become must-preserve sentinels.

---

## 6. Optimal method stack by expected coverage

### Method A: `RESOURCE_TO_LANGUAGE_PIPELINE_MATRIX`

Covers most of:

```text
stdin_resource_binding
resource_path_topology
sql_semantics
part of input_row_shape_semantics
part of compression_io
part of config_db_topology
```

Layer discovery:

```text
L1/L2 ontology + L3 resource/transform pool + L4 public scout
```

Triangulation:

```text
P + R + T + U + E + H
```

Core matrix:

```text
resource route
  x decoder/codec
  x dialect reader
  x table identity/binding
  x SQL context
  x output consumer
  x diagnostic/fatal gate
```

### Method B: `DIALECT_SUBLANGUAGE_TERMINALIZATION_MATRIX`

Covers most of:

```text
input_format_dialect
tbln_grammar
jq_json_projection
input_row_shape_semantics
```

Layer discovery:

```text
L2/L3 HOB inherited children + L4 empirical scout + L5 observation lock
```

Triangulation:

```text
D + T + U + S + E
```

Core matrix:

```text
public dialect
  x byte grammar
  x value-domain shape
  x row-universe policy
  x selector/sublanguage if any
  x error branch
  x renderer/output branch
```

### Method C: `NEGATIVE_UTILITY_FATAL_PRECEDENCE_LATTICE`

Covers most of:

```text
diagnostic_precedence
part of input_format_dialect
part of compression_io
part of config_db_topology
part of output_routing_guessing
```

Layer discovery:

```text
L3 negative utility + L4/L5 empirical reference observation
```

Triangulation:

```text
N + E + R + D + O
```

Core matrix:

```text
first fatal owner
  x resource layer
  x decode layer
  x dialect grammar layer
  x transform layer
  x output side-effect layer
  x channel/exit projection
```

### Method D: `MODE_AS_PROGRAM_MATRIX`

Covers most of:

```text
analyze_report_mode
config_db_topology
some diagnostic_precedence
some output byte compatibility
```

Layer discovery:

```text
L4 public schema re-entry + L3 utility + L5 reference bytes
```

Triangulation:

```text
S + U + P + E + H
```

Core matrix:

```text
mode
  x resources consumed
  x transform performed
  x renderer sections
  x diagnostic branch
  x side effects
  x config/db substrate
```

### Method E: `OUTPUT_ROUTE_AND_DOWNSTREAM_CONSUMER_MATRIX`

Covers most of:

```text
output_routing_guessing
renderer residuals
some compression_io
some diagnostic_precedence
```

Layer discovery:

```text
L2/L3 output ontology + L4 public output flags + L5 byte observation
```

Triangulation:

```text
O + R + S + E + H
```

Core matrix:

```text
semantic rows
  x renderer family
  x output route
  x option overlay
  x codec overlay
  x stdout/stderr/file split
  x byte grammar
```

---

## 7. What should have been discovered by which method?

| Failure family | Optimal earliest method | Earliest layer | Primary axis | Exactness axis | Source-postmortem needed? |
|---|---|---:|---|---|---|
| input_format_dialect | HOB inherited dialect/value matrix | L2/L3 | ontology + dialect | public reference | only for obscure byte/error details |
| tbln_grammar | public schema re-entry into TBLN sublanguage | L4 -> L2 | public schema + dialect | reference/source | likely yes for full grammar |
| diagnostic_precedence | negative utility fatal-gate lattice | L3/L4 | negative utility | reference observation | sometimes |
| jq_json_projection | transform sublanguage matrix | L1/L2 + L4 | transform + utility | reference/source | likely for jq quirks |
| compression_io | resource route/codec matrix | L2 + L4 | resource ecology | reference/dependency | yes for codec/dependency parity |
| input_row_shape_semantics | row-universe option overlay matrix | L2/L3 | ontology + dialect | reference | rarely |
| config_db_topology | mode-as-program + DB resource topology | L4 -> L2 | public schema + utility | reference/source | yes for driver/config specifics |
| analyze_report_mode | analyze-as-discovery-program | L4 -> L2 | utility + public schema | reference bytes | maybe for section construction |
| stdin_resource_binding | stdin-as-named-resource | L1/L2 | resource + transform | reference | no, unless naming exactness unclear |
| sql_semantics | embedded SQL substrate breadth | L1/L2 | transform | reference/source | sometimes |
| output_routing_guessing | output route inference matrix | L4/L5 | output + resource | reference bytes | no for common cases |
| resource_path_topology | path identity/route normalization | L2 | resource + utility | reference | no for common cases |
| unclassified | zero-tolerance de-lumping | L9 -> L2 | historical + ontology | nearest-sibling probes | depends after split |

---

## 8. The strongest counterfactual sequence

The remaining 371 rows would have been most robustly covered by this sequence:

```text
1. Run public schema re-entry again, but only for the remaining failure families.
2. Activate HOB parents for:
   3 Resource topology
   4 Dialect/value grammar
   5 Embedded language / SQL / jq transform
   8 Output route / renderer
   9 Diagnostics / fatal gates
   2 Mode families / analyze / config
3. Import inherited children by default.
4. Run orthogonal semantic pools P/U/S/R/D/T/O/N/H over the active parents.
5. Build a triangulation board:
   node -> supporting axes -> missing axes -> required probe type.
6. Generate reference probes before source patches:
   mechanism + workflow + negative utility + byte/side-effect.
7. Import v23 preservation sentinels for every touched owner.
8. Dispatch one bounded implementation batch.
9. Run local candidate probes plus sealed/metamorphic siblings.
10. Attribute deltas by numbered node, not by raw test module.
```

The key difference from previous loops is that each failure family must be forced through at least two independent axes:

```text
ontology says this branch should exist;
public scout or reference observation says how it surfaces;
utility says why a workflow needs it;
historical preservation says what must not regress;
source-postmortem supplies exact internal grammar only when public methods stall.
```

---

## 9. Recommended next batch order

### Batch 0 — attribution compiler, no code

```text
- De-lump `unclassified` to zero.
- Map all 371 failures to numbered HOB children.
- For each child, name earliest discoverable layer and active triangulation axes.
- Build preservation import list by implementation owner.
```

### Batch 1 — resource-to-language pipeline

```text
Primary buckets:
  stdin_resource_binding
  sql_semantics
  resource_path_topology
  compression_io subset
  input_row_shape subset

Owners:
  source_router
  codec_router
  sql_resource_binder
  value_normalizer
```

### Batch 2 — dialect sublanguages

```text
Primary buckets:
  input_format_dialect
  tbln_grammar
  jq_json_projection
  input_row_shape_semantics

Owners:
  reader_registry
  tbln_reader_writer
  jq_selector
  value_normalizer
```

### Batch 3 — mode and diagnostics

```text
Primary buckets:
  diagnostic_precedence
  config_db_topology
  analyze_report_mode

Owners:
  mode_dispatcher
  config_db_topology
  diagnostic_emitter
  analyze_renderer
```

### Batch 4 — output route and byte exactness

```text
Primary buckets:
  output_routing_guessing
  remaining renderer exactness
  compression output side effects

Owners:
  renderer_registry
  output_router
  codec_router
```

---

## 10. v24 meta-program patch proposal

Add the following gate:

```text
REMAINING_FAILURE_OPTIMAL_COVERAGE_COMPILER
```

Required output row:

```yaml
failure_bucket: string
count: int
earliest_discovery_layer: L0|L1|L2|L3|L4|L5|L6|L7|L8|L9
upstream_discriminator: string
primary_triangulation_axes: [P,U,S,E,R,D,T,O,N,H,M]
required_pre_patch_methods:
  - ontology_descent
  - public_schema_reentry
  - empirical_reference_probe
  - utility_workflow_probe
  - negative_utility_probe
  - source_postmortem_operator_discovery
  - preservation_sentinel_import
  - methodological_equivalence_check
numbered_hob_nodes: []
implementation_owners: []
preservation_sentinels_required: []
sealed_or_metamorphic_probe_required: true|false
source_postmortem_allowed_after: string
handoff_status: blocked_until_matrix | probe_ready | implementation_ready | deferred
```

Blocking rule:

```text
A remaining failure bucket cannot be handed to an implementation worker until
this row is complete and at least two independent triangulation axes support the
selected upstream discriminator, unless the bucket is explicitly labeled as a
single implementation-transfer bug.
```

The second new rule:

```text
Exact byte/source-postmortem evidence may close leaves, but it may not be the
first and only reason a parent exists. Parent existence should come from
ontology, public schema, utility, or resource/transform semantics whenever
possible.
```

---

## 11. Bottom line

The remaining failures would not have been best covered by more raw probes. They needed different discovery methods at different layers:

```text
Ontology/HOB should have forced:
  resource binding, SQL substrate, row universe, stdin-as-resource, output contracts.

Utility should have forced:
  inspect unknown data, nested projection, compressed files as data files,
  downstream output usability, negative false-success cases.

Public empirical scout should have forced:
  exact format/mode/control inventory, output guessing, jq/config/analyze controls,
  stdout/stderr/exit/file splits.

Reference observation should have forced:
  byte grammars, fatal precedence, codec magic, exact section/report shapes.

Source postmortem should have supplied:
  TBLN grammar, codec dependency parity, Go renderer quirks, SQL rewrite details,
  driver-specific quoting, when public probes could not infer them efficiently.

Historical preservation should have forced:
  prior green analyze/CLI/config/diagnostic/renderer leaves to survive every
  patch touching shared owners.
```

The v24 improvement is to require each remaining bucket to name the optimal triangulation mix before code begins.
