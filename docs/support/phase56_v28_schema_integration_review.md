# Phase56 / v28 Schema Integration Review

Authority layer: `post_eval_pressure_synthesis`.

Task: `noborus__trdsql.d8c5ff6`.

Inputs reviewed:

- `phase56_remaining_failure_audit.md`
- `official_eval_summary.md` for Phase55

This note reviews Codex's remaining-failure audit after the Phase54/55 codec-resource patch and integrates the result into the ADEU / ODEU program-reconstruction schema.

---

## 1. Core verdict

The Phase55 result is a real method gain.

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

The Phase54/55 patch did not merely fix a few byte edges. It repaired a broad `CODEC_RESOURCE_ECOLOGY` transition: resource token topology, compressed/resource value ecology, output-path behavior, zstd/lz4 frame shape, multi-file glob/header handling, no-match glob semantics, tilde handling in SQL relation tokens, and output-path diagnostics.

The remaining 119 failures therefore have a different character from the earlier 275-failure surface. They are no longer dominated by resource-route topology. They split into:

```text
1. target-substrate dependency tail
2. public sublanguage tails
3. value-domain / diagnostic tails
4. compatibility-overlay conflicts
5. mode-state exactness tails
6. scoped-green-but-not-gold sibling tails
```

The audit's most important meta-program lesson is correct:

```text
A scoped-green subtree is not gold-ready when the official failure tail still
contains sibling dialects under the same owner.
```

This should become an explicit v28 schema rule, not just a narrative lesson.

---

## 2. Review of Codex audit

### 2.1 What the audit gets right

The audit correctly identifies that Phase55 leaves a compact but semantically deep tail:

| Cluster | Count | Correct high-level reading |
| --- | ---: | --- |
| `JSON_YAML_VALUE_AND_ERROR_DOMAIN` | 31 | Structured value-domain grammar remains under-terminalized. |
| `JQ_SELECTOR_SUBLANGUAGE` | 18 | jq is still an embedded selector/transform language, not a pattern bag. |
| `CODEC_ZSTD_AND_COMPRESSION_ECOLOGY` | 12 | zstd remains target-substrate / dependency-equivalence pressure. |
| `WIDTH_FIXED_TABLE_READER` | 11 | fixed-width is a separate dialect family, not a text-reader variant. |
| `CLI_HELP_ARGPARSE_CONFLICT` | 10 | help behavior is a compatibility overlay conflict, not a parser rewrite. |
| `TBLN_SCHEMA_TYPE_GRAMMAR` | 10 | TBLN local-green was scoped-ready, not gold-ready. |
| `CONFIG_DB_STATE_TOPOLOGY` | 9 | config/db/debug/default state topology remains partial. |
| `ROW_UNIVERSE_AND_INPUT_ROW_SHAPE` | 6 | row lifecycle ordering remains incomplete. |
| `RESOURCE_PATH_DIAGNOSTIC_AND_MUTATION` | 5 | route repair exposed diagnostic/mutation overlays. |
| `ANALYZE_MODE_EXACTNESS` | 3 | analyze is mostly closed but still has exactness leaves. |
| `SQL_NUMERIC_TYPE_RENDERING` | 2 | SQL type coercion and output type rendering remain partial. |
| `OUTPUT_ROUTER_RENDERER_PRIORITY` | 2 | small output-priority/escaping overlay remains. |

The audit also correctly identifies that 19 regressions versus Phase30 must be imported as preservation sentinels before the next batch:

```text
CLI/help:                       9
jq selector:                    4
resource diagnostics:           2
row universe / inum collisions: 2
YAML anchors:                   1
config default invalid JSON:    1
```

### 2.2 Main correction

The recommended repair order is plausible, but the schema integration should not treat the remaining clusters as flat implementation buckets.

At score 91, each cluster should be routed through one of three schema mechanisms:

```text
A. tail sibling expansion
   local/scoped matrix green, but official tail still hits same owner.

B. compatibility overlay conflict
   two or more public/official branches disagree on stream/exit/precedence.

C. target-substrate dependency equivalence
   local behavior depends on optional module/binary/helper availability.
```

This means v28 should not merely add more macros. It should add a **tail re-entry protocol** that decides whether a remaining bucket is:

```text
new ontology missing parent
existing parent with missing child sibling
compatibility overlay conflict
methodological equivalence failure
implementation transfer bug
```

Only then should a worker receive a patch baton.

---

## 3. v28 schema additions

### 3.1 `OFFICIAL_TAIL_REENTRY_GATE`

Trigger:

```text
official eval after a scoped or method-test patch reaches high score,
and remaining failures cluster by owner or public schema family.
```

Required row:

```yaml
official_tail_reentry_row:
  cluster_id: string
  failure_count: int
  primary_owner: string
  shared_owner_with_recent_patch: true|false
  prior_local_matrix_status:
    absent | red | scoped_green | gold_green | unknown
  official_tail_relation:
    new_parent_missing |
    missing_sibling_under_existing_parent |
    compatibility_overlay_conflict |
    target_substrate_equivalence |
    implementation_transfer_bug |
    post_eval_only_unknown
  earliest_discoverable_layer: string
  required_triangular_axes: []
  required_preservation_sentinels: []
  next_gate: string
  handoff_posture:
    blocked_until_schema_split |
    probe_ready |
    implementation_ready |
    scoped_deferred
```

Blocking rule:

```text
A remaining official cluster cannot be handed directly to a worker until this
row is filled.
```

### 3.2 `SCOPED_GREEN_OFFICIAL_SIBLING_TAIL_GATE`

Trigger:

```text
local matrix for macro M is green or near-green,
but official tail still contains failures owned by M or M's implementation owner.
```

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
  allowed_claim: scoped_green_with_tail
```

Rule:

```text
local green + official sibling tail => not_gold_ready_missing_sibling_tail.
```

This is the direct generalization of the TBLN and codec-resource lessons.

### 3.3 `COMPATIBILITY_OVERLAY_CONFLICT_GATE`

Trigger:

```text
a public surface has branch-specific stdout/stderr/exit/usage behavior,
and one global implementation rule would satisfy one branch but break another.
```

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
    branch_discriminator_known |
    branch_discriminator_missing |
    public_official_conflict_isolated
  implementation_rule_scope: branch_local | global_forbidden
```

Applied immediately to `CLI_HELP_ARGPARSE_CONFLICT`.

### 3.4 `TARGET_STABLE_DEPENDENCY_CONTRACT`

Trigger:

```text
behavior depends on optional library, external binary, codec helper, shell tool,
interpreter feature, locale, or platform-provided resource.
```

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
  local_availability: present|absent|unknown
  packaged_eval_availability: present|absent|unknown
  fallback_strategy:
    pure_in_bundle |
    vendored_dependency |
    proven_external_helper |
    branch_deferred
  target_substrate_probe_refs: []
  packaging_refs: []
  preservation_sentinels: []
```

Applied immediately to zstd.

### 3.5 `PUBLIC_SUBLANGUAGE_CLOSURE_GATE`

Trigger:

```text
a named public format, selector, renderer, query fragment, or mode has syntax
and semantics richer than a single flag label.
```

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
    label_only |
    scoped_examples |
    matrix_locked |
    scoped_green |
    gold_ready |
    scoped_green_with_official_tail
```

Applied to `jq`, `TBLN`, `YAML`, `JSON/JSONL`, and fixed-width.

---

## 4. Integration into the numbered HOB schema

The existing top-level schema can stay stable:

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

v28 adds deeper child nodes and tail statuses.

### 4.1 Cluster-to-schema mapping

| Cluster | Count | Schema node(s) | v28 gate | Main triangulation axes |
| --- | ---: | --- | --- | --- |
| `JSON_YAML_VALUE_AND_ERROR_DOMAIN` | 31 | `4.2 JSON`, `4.3 YAML`, `4.9 value-domain`, `8.4 JSON/YAML renderers`, `9.4 reader diagnostics` | `STRUCTURED_VALUE_DOMAIN_AND_ERROR_GRAMMAR` | ontology + public schema + empirical reference + source-postmortem if exact wording stalls |
| `JQ_SELECTOR_SUBLANGUAGE` | 18 | `5.4 jq selector/transform`, `3.5 resource suffix binding`, `4.2 JSON/YAML row compiler`, `9.4 jq diagnostics` | `JQ_AS_EMBEDDED_SELECTOR_LANGUAGE` | transform ontology + public schema + empirical reference + preservation history |
| `CODEC_ZSTD_AND_COMPRESSION_ECOLOGY` | 12 | `3.7 codec routes`, `8.7 output compression`, `10.4 dependency substrate`, `11.4 package equivalence` | `TARGET_STABLE_DEPENDENCY_CONTRACT` | methodological equivalence + resource ecology + target-substrate probe |
| `WIDTH_FIXED_TABLE_READER` | 11 | `4.6 fixed-width`, `6.2 column identity`, `7.2 row lifecycle`, `2.4 analyze advice` | `FIXED_WIDTH_AS_DIALECT_FAMILY` | dialect ontology + empirical reference + mode/analyze sentinels |
| `CLI_HELP_ARGPARSE_CONFLICT` | 10 | `1.1 help aliases`, `1.5 invalid arg grammar`, `9.1 channel/exit`, `11.8 conflict warrant` | `COMPATIBILITY_OVERLAY_CONFLICT_GATE` | public observation + official pressure + branch discriminator |
| `TBLN_SCHEMA_TYPE_GRAMMAR` | 10 | `4.7 TBLN`, `6.2 column/type identity`, `8.6 TBLN renderer`, `9.4 invalid grammar diagnostics` | `SCOPED_GREEN_OFFICIAL_SIBLING_TAIL_GATE` | existing local matrix + official tail + source-postmortem for grammar if needed |
| `CONFIG_DB_STATE_TOPOLOGY` | 9 | `2.7 config/db modes`, `3.10 config resource`, `7.4 DB state`, `9.5 debug/config diagnostics` | `CONFIG_DB_STATE_MACHINE_GATE` | public schema + resource topology + negative utility |
| `ROW_UNIVERSE_AND_INPUT_ROW_SHAPE` | 6 | `6.1 row universe`, `7.1 read lifecycle`, `4.x dialect-specific row shape` | `ROW_UNIVERSE_ORDERING_LATTICE` | lifecycle ontology + empirical reference + preservation sentinels |
| `RESOURCE_PATH_DIAGNOSTIC_AND_MUTATION` | 5 | `3.2 path identity`, `5.2 SQL mutation`, `7.5 persistent effects`, `9.3 route diagnostics` | `RESOURCE_MUTATION_DIAGNOSTIC_OVERLAY` | resource topology + SQL transform + negative/fatal precedence |
| `ANALYZE_MODE_EXACTNESS` | 3 | `2.4 analyze mode`, `8.8 analyze renderer`, `6.2 table-name identity` | `ANALYZE_MODE_EXACTNESS_OVERLAY` | public schema + reference byte lock |
| `SQL_NUMERIC_TYPE_RENDERING` | 2 | `5.2 SQL semantics`, `8.4 JSON/YAML renderers`, `6.4 aggregate type` | `SQL_NUMERIC_VALUE_RENDERING_GATE` | transform + renderer empirical |
| `OUTPUT_ROUTER_RENDERER_PRIORITY` | 2 | `8.1 renderer choice`, `8.7 output route`, `1.x flag precedence` | `OUTPUT_PRIORITY_COMPATIBILITY_OVERLAY` | output route + byte reference + flag precedence |

---

## 5. New child nodes to add

### 5.1 Under `4 Input dialect and value-domain grammar`

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
```

### 5.2 Under `5 Embedded language / transform substrate`

```text
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
```

### 5.3 Under `8 Output router, renderer, and byte grammar`

```text
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
```

### 5.4 Under `11 Methodological equivalence and warrant`

```text
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

---

## 6. Best next sequence

### Batch 0: no code — tail schema compilation

```text
1. Import the 19 Phase30 regressions as preservation sentinels.
2. Fill `official_tail_reentry_row` for all 12 clusters.
3. Mark each cluster as:
   - missing sibling under existing parent
   - compatibility overlay conflict
   - target-substrate equivalence
   - implementation transfer bug
4. Attach every row to numbered HOB child nodes.
5. Produce one worker baton only after the relevant gate is probe-ready.
```

### Batch 1: zstd / target-stable codec contract

Why first:

```text
- 12 rows
- narrow owner surface
- clear E4/target-substrate miss
- low semantic interaction risk if guarded
```

Required sentinels:

```text
gzip, bz2, xz, lz4 input/output
out-without-guess
explicit -oz override
stdout compressed bytes
output file compressed bytes
unsupported helper diagnostic
```

Acceptance:

```text
zstd works in the packaged evaluator substrate, not only local Python.
```

### Batch 2: CLI help / argparse compatibility overlay

Why second:

```text
- 10 rows
- 9 of 19 regressions
- small if treated as branch-local overlay
```

Do not globally rewrite help. Build a branch matrix over:

```text
--help
-help
-h
invalid arg + help
help before/after invalid flags
stdout vs stderr
rc0 vs rc2
```

Acceptance:

```text
Every help branch has explicit stream/exit warrant.
```

### Batch 3: jq selector sublanguage

Why third:

```text
- 18 rows
- 4 regressions
- unlocks JSON/YAML workflow branches
```

Close `5.4 jq selector / transform sublanguage` as a sublanguage, not as pattern additions.

Required scope:

```text
.items[]
.data.records[]
.items[1]
.users[] | select(...)
recursive descent
multiple extraction paths
object construction / rename
YAML/JSON interop
resource suffix selector binding
error/type mismatch diagnostics
```

### Batch 4: JSON/YAML value-domain and error grammar

This is the largest cluster, but it should be split internally:

```text
4A JSON/JSONL parse and stream lifecycle
4B YAML anchors/merge/duplicate/malformed grammar
4C structured scalar/value normalization and output rendering
4D diagnostic wording/timing
```

Do not make this one broad worker patch unless Batch 3 jq sentinels are imported.

### Batch 5: fixed-width / ps / dpkg dialect family

Treat fixed-width as a separate schema-bearing dialect family. Do not patch the CSV/text reader directly unless the fixed-width adapter boundary is declared.

### Batch 6: TBLN scoped-to-gold promotion

TBLN is not absent; it is scoped-green with official sibling tail. Use the new gate:

```text
SCOPED_GREEN_OFFICIAL_SIBLING_TAIL_GATE
```

Focus on:

```text
type aliases
numeric negative/zero
timestamptz
whitespace preservation
long strings and punctuation
unsupported-line diagnostic
```

### Batch 7: small overlays by shared owner

Group the smaller clusters by implementation owner:

```text
config loader / db topology:
  CONFIG_DB_STATE_TOPOLOGY

row lifecycle / value normalizer:
  ROW_UNIVERSE_AND_INPUT_ROW_SHAPE
  SQL_NUMERIC_TYPE_RENDERING

resource binder / sqlite executor:
  RESOURCE_PATH_DIAGNOSTIC_AND_MUTATION

renderer/output router:
  ANALYZE_MODE_EXACTNESS
  OUTPUT_ROUTER_RENDERER_PRIORITY
```

Do not patch these as isolated row fixes. Import preservation sentinels from the owning subsystem.

---

## 7. Worker-baton template for v28

Every next worker baton should include this block:

```yaml
v28_worker_baton:
  handoff_type: scoped_subtree_closure | compatibility_overlay | target_dependency_equivalence
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
    - whether parent is gold_ready or scoped_green_with_tail
```

Bookkeeper rejection rules:

```text
Reject if worker says "fixed jq" without closing 5.4 child matrix.
Reject if worker says "fixed JSON/YAML" without separating parse, value, output, and diagnostics.
Reject if worker says "fixed zstd" without target-substrate proof.
Reject if worker changes global help behavior without branch discriminator.
Reject if local-green TBLN is promoted to gold while official sibling tail remains.
```

---

## 8. General meta-program patch

Add to v28:

```text
TAIL-1 OFFICIAL_TAIL_REENTRY_GATE
TAIL-2 SCOPED_GREEN_OFFICIAL_SIBLING_TAIL_GATE
TAIL-3 COMPATIBILITY_OVERLAY_CONFLICT_GATE
TAIL-4 TARGET_STABLE_DEPENDENCY_CONTRACT
TAIL-5 PUBLIC_SUBLANGUAGE_CLOSURE_GATE
TAIL-6 VALUE_DOMAIN_AND_ERROR_GRAMMAR_GATE
TAIL-7 FIXED_WIDTH_AS_DIALECT_FAMILY_GATE
TAIL-8 WORKER_BATON_TAIL_CLOSURE_TEMPLATE
```

The new readiness state:

```text
scoped_green_with_official_sibling_tail
```

Meaning:

```text
A local matrix can remain valuable and regression-worthy, but it cannot be used
as gold closure because official pressure still names unclosed siblings under
the same owner.
```

The new orchestration rule:

```text
After a high-score method gain, the orchestrator must not continue broad patching.
It must compile the official tail into schema-level sibling expansion,
compatibility overlays, and target-substrate equivalence rows.
```

---

## 9. Bottom line

Phase55 confirms that the resource-ecology and preservation approach is working. The remaining 119 failures are now concentrated enough that they should be treated as a **tail-closure problem**, not a broad reconstruction problem.

The next schema improvement is:

```text
parent macro closure must survive official sibling-tail pressure.
```

The next implementation improvement is:

```text
zstd target-stable dependency first,
then CLI help compatibility overlay,
then jq as a real sublanguage,
then JSON/YAML value-domain closure.
```

The next orchestration improvement is:

```text
Every remaining cluster gets an official-tail re-entry row before any worker patch.
```
