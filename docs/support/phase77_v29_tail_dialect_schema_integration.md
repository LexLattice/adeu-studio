# Phase77 Audit Review and v29 Tail-Dialect Schema Integration

Authority layer: `post_eval_pressure_review`

Inputs reviewed:

- `phase77_remaining_failure_audit.md`
- current accepted baseline as reported in the audit:

```text
phase: Phase76
run: trdsql_v39_csv_update_writeback
score: 96
raw rows: 1345 passed / 57 failed / 1 skipped / 1403 total
```

The audit’s evidence posture is correct: this is post-eval pressure, not clean first-pass evidence and not a source-compatible gold claim.

## 1. Core verdict

The Phase77 audit is directionally strong. It correctly recognizes that the remaining 57 rows are not a collapse of the reconstructed `trdsql` ontology. At score 96, the high-level program theorem is now mostly stable:

```text
resource-backed SQL substrate
  + public input dialects
  + row/import controls
  + renderers/output router
  + analyze/config modes
  + diagnostics
  + codec/resource ecology
```

The remaining tail is instead concentrated in terminal dialect closure and target-surface equivalence:

```text
width table grammar
TBLN grammar and type provenance
JSON/JSONL Go-compatible diagnostics and stream shape
YAML value/parser/renderer dialect
row-universe source-specific lifecycle rules
one output-format precedence row
```

The most important meta-program update is:

```text
At high score / low residual count, parent ontology repair must switch into
TAIL DIALECT CLOSURE mode: each remaining public dialect must be treated as a
micro-language with grammar, value domain, provenance, diagnostics, renderer,
and preservation sentinels.
```

## 2. Audit-of-audit correction

The audit’s buckets are useful, but they are still partly approximate. The reconstructed counts are:

```text
Width/analyze:       ~9
JSON/JSONL:          ~12
YAML:                ~15
TBLN:                ~9
Row universe/import: ~10
Output priority:     ~1
```

These sum to 56, while the accepted baseline says 57 failures. This is not a major conceptual problem, but it matters at a score-96 tail. v29 should require exact row ownership before implementation:

```text
No approximate bucket count may become a worker handoff at score-tail stage.
Every remaining row must have exactly one primary node, optional secondary
nodes, implementation owner, and preservation sentinel set.
```

This becomes `TAIL_ROW_OWNERSHIP_EXACTNESS_GATE` below.

## 3. Main schema integration

### 3.1 New readiness state

Add:

```text
gold_tail_not_closed
```

Meaning:

```text
The program is globally mechanistic and broadly official-compatible, but a
small set of public dialect or byte-surface sibling leaves remain open.
```

This is distinct from:

```text
scoped_green_with_official_sibling_tail
```

because Phase76 is now beyond local scoped-green pressure. The remaining rows are small enough and concrete enough that the orchestrator should manage them as explicit gold-tail leaves.

### 3.2 New v29 gates

Add these gates to the meta-program:

```text
TAIL_ROW_OWNERSHIP_EXACTNESS_GATE
TAIL_DIALECT_MICROGRAMMAR_CLOSURE_GATE
HOST_LIBRARY_SURFACE_TRANSLATION_GATE
TYPE_PROVENANCE_AUTHORITY_GATE
READER_LOCAL_ROW_LIFECYCLE_GATE
ANALYZE_ADVICE_COUPLING_GATE
PATCH_CLASS_NEGATIVE_HISTORY_GATE
OUTPUT_FORMAT_PRECEDENCE_OVERLAY_GATE
GOLD_TAIL_BATCH_AUTHORIZATION_GATE
```

The core v29 invariant:

```text
At gold-tail stage, no patch may target a symptom string or a broad shared
owner. It must target a numbered microgrammar leaf with preservation sentinels
and a proof that the chosen patch class is allowed.
```

## 4. Gate definitions

### 4.1 `TAIL_ROW_OWNERSHIP_EXACTNESS_GATE`

Trigger:

```text
official failure tail <= roughly 5 percent of total rows, or score >= 95
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
  required_method: ontology | public_reference | source_postmortem | substrate_equivalence | preservation
  preservation_sentinels: []
  patch_class_allowed: true|false
  patch_class_forbidden_reason: string|null
```

Rule:

```text
The orchestrator may not hand a tail batch to a worker while any row is
unowned, multiply-owned without a primary node, or assigned only to an
approximate bucket.
```

### 4.2 `TAIL_DIALECT_MICROGRAMMAR_CLOSURE_GATE`

Trigger:

```text
a public input/output format, reader mode, or syntax-bearing option remains in
the failure tail.
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
microgrammar surfaces are either implemented, proved irrelevant, or explicitly
deferred with expected risk.
```

### 4.3 `HOST_LIBRARY_SURFACE_TRANSLATION_GATE`

Trigger:

```text
the implementation uses a host library whose parse/render/diagnostic surface is
not the target program’s library surface.
```

Examples in Phase77:

```text
Python json.JSONDecodeError != Go encoding/json diagnostics
PyYAML parse/order/anchor/duplicate-key behavior != target YAML behavior
```

Required decision:

```yaml
host_library: string
target_surface: string
surfaces_affected:
  - diagnostic wording
  - stream shape
  - line_column numbering
  - duplicate key policy
  - scalar normalization
  - map ordering
strategy: translate_surface | emulate_target | replace_library | source_postmortem_needed | defer
```

Rule:

```text
Host-library behavior is not an oracle. If the target is known or reference-
observed to expose a different parser surface, the implementation must either
translate, emulate, replace, or explicitly defer.
```

### 4.4 `TYPE_PROVENANCE_AUTHORITY_GATE`

Trigger:

```text
renderer output depends on source type, declared schema, or reader provenance.
```

Phase77 example:

```text
TBLN output type lines require source type provenance, not broad output-string
classification.
```

Required row:

```yaml
value_ref: string
source_declared_type: string|null
reader_inferred_type: string|null
sqlite_runtime_type: string|null
renderer_claimed_type: string|null
provenance_sidecar_available: true|false
allowed_renderer_inference: none | from_declared_schema | from_reader_type | from_sqlite_type | explicitly_reference_locked
```

Rule:

```text
A renderer may not invent type provenance from string shape when prior negative
evidence shows that broad string-pattern inference regresses sibling leaves.
```

### 4.5 `PATCH_CLASS_NEGATIVE_HISTORY_GATE`

Trigger:

```text
a prior patch class produced zero wins or regressions in the same subtree.
```

Phase77 example:

```text
Phase73 broad TBLN renderer type inference produced 0 wins and 6 regressions.
```

Rule:

```text
A rejected patch class becomes forbidden until the orchestrator provides a new
node-level proof explaining why the same class will not recur.
```

This is not merely preservation. It is method memory.

### 4.6 `READER_LOCAL_ROW_LIFECYCLE_GATE`

Trigger:

```text
skip, limit, header, preread, row-number, blank, sparse, wildcard, or binary
normalization differs by reader family.
```

Rule:

```text
Row controls are not globally post-import by default. Each reader may own a
local lifecycle order.
```

Required axes:

```text
CSV skip/header/limit order
inum collision naming and column order
LTSV union-of-fields and missing-field cells
LTSV malformed diagnostics
PSV extension delimiter guess
wildcard multi-file schema union
binary decode policy per output format
```

### 4.7 `ANALYZE_ADVICE_COUPLING_GATE`

Trigger:

```text
an analyze/report mode gives format or query advice based on reader morphology.
```

Rule:

```text
Analyze advice is not a free renderer string. It is coupled to reader family,
header inference, sampled morphology, driver quoting, and dialect detection.
```

This matters because the width cluster includes two analyze rows. They should not be silently folded into width parsing; they are a coupled mode-program surface.

### 4.8 `OUTPUT_FORMAT_PRECEDENCE_OVERLAY_GATE`

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
Output format precedence is a control-plane overlay over renderer choice, not a
renderer implementation detail.
```

## 5. Reclassification of Phase77 clusters

### A. Width fixed-table reader and analyze advice

Audit classification: correct, but split into two linked nodes.

Recommended schema nodes:

```text
4.11 FIXED_WIDTH_FAMILY_GRAMMAR
4.11.1 ps-style header boundary discovery
4.11.2 ps COMMAND/tail-field absorption
4.11.3 ps numeric cells with spacing/thousands groups
4.11.4 dpkg status/name/version/arch/description morphology
4.11.5 Unicode header identity binding
2.4.7 Analyze advice coupled to fixed-width / JSON-like / LTSV-like samples
```

Best discovery method:

```text
ontology descent: format family != whitespace split
public/reference empirical: exact column boundaries and analyze strings
source-postmortem: optional if boundary rules remain ambiguous
```

Implementation owner:

```text
width_reader + analyze_advice, not sqlite_executor and not renderer_registry
```

### B. JSON and JSONL decoder/error domain

Audit classification: correct, but split target stream shape from diagnostic translation.

Recommended schema nodes:

```text
4.12 JSON_STREAM_DECODER_AND_ROW_SHAPE
4.12.1 top-level object stream
4.12.2 top-level array stream
4.12.3 JSONL line stream
4.12.4 array followed by extra document tokens
4.12.5 nested public fixture row shape
9.6.1 Go-compatible JSON diagnostic translation
9.6.2 query path vs analyze path diagnostic prefix
```

Best discovery method:

```text
conceptual descent: JSON document vs stream vs line-stream distinction
public/reference empirical: exact invalid/truncated wording and row-number overlay
source-postmortem: high value for Go encoding/json wording if public probes are noisy
```

Implementation owner:

```text
json_reader + diagnostic_emitter; renderer only for already-proven JSON output sentinels
```

### C. YAML value, parse, renderer, and structure domain

Audit classification: directionally correct, but too broad for one handoff.

Recommended schema nodes:

```text
4.13 YAML_TARGET_DIALECT
4.13.1 null propagation by source route
4.13.2 numeric/scalar formatting by source provenance
4.13.3 embedded JSON string unpacking
4.13.4 embedded YAML string rendering
4.13.5 anchors, aliases, and merge keys
4.13.6 duplicate-key diagnostic
4.13.7 mapslice/order preservation
4.13.8 malformed bracket/quote diagnostic
4.13.9 multiline/tab/escape normalization
8.13 YAML renderer byte contract
```

Best discovery method:

```text
ontology descent: YAML is not one parser call; it is parse features + scalar domain + order + renderer
public/reference empirical: exact byte/error rows
source-postmortem: likely optimal for mapslice/order, duplicate keys, and Go/yaml diagnostic details
```

Implementation owner:

```text
yaml_reader + value_normalizer + yaml_renderer + diagnostic_emitter
```

But v29 must forbid a single broad PyYAML loader swap unless all preservation rows are active.

### D. TBLN grammar and type provenance

Audit classification: strong. This is the most important method-memory case.

Recommended schema nodes:

```text
4.14 TBLN_SCHEMA_BEARING_GRAMMAR
4.14.1 ; name schema row grammar
4.14.2 ; type schema row grammar
4.14.3 no-type default text rows
4.14.4 input type aliases and postgres aliases
4.14.5 timestamptz/date/string distinctions
4.14.6 whitespace-preserving cells
4.14.7 long punctuation-containing strings
4.14.8 newline escaping
4.14.9 null / -onull behavior
4.14.10 unsupported line vs column-count diagnostics
8.14 TBLN renderer byte grammar with provenance sidecar
```

Best discovery method:

```text
ontology descent: schema-bearing tabular format, not pipe-delimited table
public/reference empirical: exact unsupported-line and conversion behavior
source-postmortem: high value for type aliases and provenance retention rules
negative historical evidence: Phase73 forbids renderer-only broad string inference
```

Implementation owner:

```text
tbln_reader_writer + value/type provenance sidecar
```

### E. Row universe, import controls, and delimited formats

Audit classification: correct, but should become reader-local lifecycle rather than a mixed bucket.

Recommended schema nodes:

```text
6.5 READER_LOCAL_ROW_LIFECYCLE
6.5.1 CSV skip/header/limit order
6.5.2 inum generated-column placement and collision naming
6.5.3 LTSV union-of-fields and missing-cell policy
6.5.4 LTSV malformed diagnostic prefix
6.5.5 PSV extension delimiter guessing
6.5.6 wildcard multi-file schema union
6.5.7 binary/non-UTF8 value representation by output format
```

Best discovery method:

```text
conceptual descent: controls compose with reader-local lifecycle
public/reference empirical: exact order and byte surfaces
preservation: CSV update/writeback, wildcard, JSON renderer, YAML scalar, Phase72 escapes
```

Implementation owner:

```text
reader_registry + row_lifecycle + value_normalizer
```

### F. Output router priority

Audit classification: correct. This is a tiny compatibility overlay.

Recommended schema node:

```text
8.2.8 Output format precedence under mixed flags
```

Best discovery method:

```text
public scout could have discovered it with mixed-format flag probes
```

Implementation owner:

```text
cli_parser/output_router, not renderer_registry
```

## 6. Which failures should have been discovered where

| Failure family | Best early discovery layer | Best triangulation axis | Why |
|---|---|---|---|
| Width ps/dpkg | L2 -> L3 | ontology + empirical | `-iwidth` is a separate family-specific table grammar, not generic whitespace. |
| Width analyze hints | L4 -> L2 re-entry | public schema + empirical | Analyze is its own mode-program and advice depends on sampled morphology. |
| JSON stream/error | L3 -> L4 | empirical + substrate equivalence | Exact Go-like error wording and stream behavior require reference/source-compatible surfaces. |
| YAML parser/value/order | L2 -> L3 and L3 -> L4 | ontology + source-postmortem + empirical | Host YAML behavior differs and exact mapslice/order/diagnostics are hard to infer. |
| TBLN type provenance | L2 -> L3 | ontology + source-postmortem + negative history | Type output must be derived from schema/provenance, not output string shape. |
| Row lifecycle | L3 -> L4 | ontology + empirical | Reader controls are source-specific lifecycle rules, not global post-import rules. |
| Output priority | L3 -> L4 | public scout | Mixed flag order is a control-plane precedence leaf. |

## 7. Recommended next orchestrator sequence

### Batch 0: no code

```text
1. Produce exact row ownership for all 57 rows.
2. Split width-reader rows from analyze-advice rows.
3. Split JSON stream-shape rows from Go-diagnostic translation rows.
4. Split YAML parser-feature rows from renderer/value-provenance rows.
5. Mark Phase73 TBLN renderer-string inference as a forbidden patch class.
6. Import Phase76 and Phase73 preservation sentinels.
```

### Batch 1: width fixed-table reader

Reason: compact, low blast radius, likely useful official gain.

Closure condition:

```text
ps/dpkg matrix green
analyze advice sentinels green
no regression in generic text, CSV, LTSV, SQL cast/order/group-by, or analyze table output
```

### Batch 2: TBLN grammar/type-provenance

Reason: high value but high regression risk.

Closure condition:

```text
TBLN input grammar matrix green
TBLN output provenance matrix green
Phase73 regression sentinels green
no broad string-inference patch path used
```

### Batch 3: JSON/JSONL target diagnostics and stream shape

Reason: many rows are target parser/stream exactness.

Closure condition:

```text
JSON/JSONL stream matrix green
Go-compatible diagnostic translation matrix green
Phase72 JSON renderer and JSONL escaping sentinels green
```

### Batch 4: YAML target dialect

Reason: largest broad surface but high substrate risk.

Closure condition:

```text
YAML parser-feature matrix green
YAML scalar/null/provenance matrix green
YAML renderer matrix green
already-green YAML suffix, negative scalar, and output rows preserved
```

### Batch 5: reader-local row lifecycle + output priority

Reason: cross-reader risk; should follow width/TBLN to avoid duplicate row-union patches.

Closure condition:

```text
CSV skip/header/limit
inum collision
LTSV union/malformed
PSV extension guessing
wildcard schema union
binary output policy
mixed output format precedence
```

## 8. Worker baton template for the next batch

```yaml
worker_baton:
  handoff_type: gold_tail_subtree_closure
  target_batch: WIDTH_FIXED_TABLE_READER
  active_v29_gates:
    - TAIL_ROW_OWNERSHIP_EXACTNESS_GATE
    - TAIL_DIALECT_MICROGRAMMAR_CLOSURE_GATE
    - ANALYZE_ADVICE_COUPLING_GATE
  primary_hob_nodes:
    - 4.11 FIXED_WIDTH_FAMILY_GRAMMAR
    - 2.4.7 ANALYZE_ADVICE_COUPLED_TO_READER_MORPHOLOGY
  allowed_owners:
    - width_reader
    - analyze_advice
    - schema_inferencer
  forbidden_owners:
    - sqlite_executor
    - renderer_registry_global
    - json_yaml_value_normalizer
  required_pre_patch_artifacts:
    - width_reference_matrix
    - analyze_advice_reference_matrix
    - preservation_sentinel_manifest
  closure_condition:
    - all width/analyze batch probes green
    - imported sentinels green
    - no owner-wide regressions
  deferral_policy:
    - rows outside 4.11/2.4.7 remain untouched unless preserving sentinels require repair
```

## 9. v29 patch summary

Add to the meta-program:

```text
At high-score tail, switch from parent-discriminator repair to exact dialect
microgrammar closure.

Each remaining row must have exact ownership.
Each dialect must close as grammar + value domain + provenance + diagnostics +
renderer + preservation, not as a feature label.
Host-library parser/renderer surfaces require target-surface translation or
explicit deferral.
Prior rejected patch classes become forbidden until a new proof reauthorizes
them.
```

Bottom line:

```text
Phase77 shows the reconstruction has crossed from broad ontology repair into
compatibility-theorem finishing. The next gains should come from mini-matrices
for exact target dialects, not from broad mechanism patches.
```
