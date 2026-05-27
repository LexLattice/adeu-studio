# Phase 16 Audit-of-Audit and v18 Meta-Program Patch

Authority layer: support / post-eval pressure interpretation.

Claim scope: this audits the Phase 16 remaining-failure audit itself. It does not treat official failures as clean first-pass reconstruction evidence. It evaluates whether the audit is strong enough to drive the next worker under the deterministic hierarchical obligation-tree discipline introduced in v17.

---

## 1. Verdict

The Phase 16 audit is directionally correct and materially useful, but it is not yet operationally deterministic enough for the next worker.

It correctly reports the score movement:

```text
Phase 9:   score 67, 953 passed / 449 failed / 1 skipped
Phase 15:  score 72, 1033 passed / 369 failed / 1 skipped

fixed tests:        82
persistent failures: 367
new regressions:     2
net failure delta: -80
```

It also correctly preserves the evidence boundary:

```text
official failures = post-eval pressure attribution
not clean first-pass evidence
```

The main weakness is that several buckets are still too high-level. In particular:

```text
input_dialect_value_and_error_grammar: 194 rows
analyze_config_and_control_plane_schema: 65 rows
misc_exactness_or_unclassified: 31 rows
```

These cannot be passed to a worker as repair targets. Under v17, a parent class imports child obligations. Therefore these buckets must be compiled into numbered child obligations, irrelevance proofs, probe rows, and regression sentinels before implementation.

The strongest correction is:

```text
The audit should not only classify remaining failures.
It must also prove that each broad failure class has been lowered into a
closed or explicitly deferred inherited subtree.
```

---

## 2. What the audit gets right

### 2.1 The score delta is real progress

The jump to score 72 is not a random improvement. The fixed-pressure table shows improvements across wildcard/resource handling, advanced features, external queries/readers/writers, database drivers, stdin/stdout, row numbering, output guessing, raw output, glob patterns, and jq error paths.

This supports the v16/v17 diagnosis:

```text
parent-rule repairs help,
but only for the child branches actually operationalized.
```

### 2.2 The largest remaining pressure is no longer packaging or ABI

The earlier catastrophic witness/substrate failure is gone. The current surface is product-behavior pressure, mainly terminalization and sibling-coverage gaps.

Dominant remaining zones:

```text
input dialect/value/error grammar
analyze/config/control-plane mode grammars
codec route/dependency behavior
renderer byte grammar
SQL identity/resource binding
type/value-domain semantics
```

### 2.3 The audit correctly identifies regressions as integration-risk pressure

The two regressions are important:

```text
test_limit_read_with_skip_and_header
test_tilde_expansion_in_path
```

These are not small accidents. They show that prior repairs still lack sibling-retention enforcement. A next batch that ignores them may improve new rows while damaging already-green branches.

---

## 3. Main audit-of-audit correction

The audit currently has two roles mixed together:

```text
1. descriptive classification of remaining failures;
2. operational repair plan for the next worker.
```

It succeeds at role 1. It is only partially ready for role 2.

Under v17, the next worker needs a numbered obligation tree, not broad labels. A label like:

```text
input_dialect_value_and_error_grammar
```

must be compiled into child branches such as:

```text
4.1 CSV delimiter/header/skip/limit row-window grammar
4.2 fixed-width column segmentation grammar
4.3 JSON/JSONL root-shape and invalid syntax grammar
4.4 YAML scalar/array/map/sparse/binary/null grammar
4.5 TBLN row and separator grammar
4.6 LTSV key/value row grammar
4.7 jq selector grammar and error precedence
4.8 empty/blank/malformed resource error grammar
4.9 null/binary/unicode value-domain conversion
4.10 option conflict and flag override precedence
```

Every child branch then needs one of:

```text
covered_terminalized
covered_by_probe_matrix
proved_pass_through
proved_irrelevant
conflict_isolated
scoped_deferred_with_expected_risk
blocked_pending_reference_observation
blocked_pending_methodological_equivalence
```

Without that lowering, the next worker will again patch representative children and leave the parent open.

---

## 4. Re-bucketing the Phase 16 buckets

### 4.1 `input_dialect_value_and_error_grammar` is not one parent

The audit calls this the largest class at 194 rows. That is accurate as a surface count, but it is too broad as a causal parent.

It should split into at least six parent discriminators:

#### A. Reader option overlay and row-window semantics

Examples:

```text
skip + header + limit
header/no-header column naming
blank line handling
row numbering interaction
explicit no-guess / input format flags
```

This branch likely owns the regression:

```text
test_limit_read_with_skip_and_header
```

Layer:

```text
K5 Sequence + K3 Bind + K7 Compose
```

Interpretation:

```text
Row windows are not just parser options.
They determine which physical rows become schema, data rows, hidden rows, and
SQL-visible rows.
```

#### B. Dialect decoder grammar

Examples:

```text
CSV delimiter syntax
fixed-width specs
TBLN parsing
LTSV parsing
YAML structures
JSON/JSONL root shapes
multi-document inputs
```

Layer:

```text
K2 Partition + PROTOCOL_GRAMMAR + K6 Expose error surfaces
```

#### C. Value-domain conversion

Examples:

```text
null conversion
binary bytes
invalid UTF-8
unicode escaping
YAML binary tags
numeric/string preservation
```

Layer:

```text
K4 Transform + K2 Partition + K6 renderer exposure
```

This branch crosses input and output. It should not live only under input dialect.

#### D. Error/fatal-gate grammar

Examples:

```text
empty files should fail nonzero
malformed JSON error text
invalid delimiter error text
skip beyond length fail/succeed policy
incompatible format diagnostics
```

Layer:

```text
COMPETING_FATAL_GATE_PRECEDENCE + K6 stderr/exit grammar
```

#### E. Selector and jq sublanguage

Examples:

```text
file.json::.data
invalid jq expression
selector concatenation in analyze mode
JSON/YAML jq interop
```

Layer:

```text
POSITIONAL_DSL_AST + EMBEDDED_LANGUAGE_SUBSTRATE
```

This is not merely input format. It is a selector language over resource content.

#### F. Source-to-SQL schema binding

Examples:

```text
c1/c2 fallback vs header names
column count mismatch
column aliases
header-only file behavior
```

Layer:

```text
RESOURCE_TO_LANGUAGE_BINDER + K3 Bind
```

This is the bridge between reader grammar and SQL identity.

### 4.2 `analyze_config_and_control_plane_schema` should split

The audit groups 65 rows under analyze/config/control-plane. That is useful but still too coarse.

Suggested split:

```text
2.2 help/usage/control-surface exactness
2.7 mode family precedence and flag routing
3.10 config resource topology
3.11 database/driver/DSN topology
8.A analyze renderer grammar
8.B analyze example-query generator
8.C analyze detection/advice heuristics
8.D driver-dependent quoting in analyze output
9.1 stdout/stderr/exit diagnostic channel contract
9.5 config/db error grammar
```

Key correction:

```text
Analyze mode is not only a diagnostic mode.
It is a renderer plus schema detector plus example-query generator plus
format-advice heuristic.
```

The sample analyze failures show at least four separate obligations:

```text
header detection / data-type table names
JSON/LTSV-looking CSV advice
jq path reflected in table identity
MySQL driver quote character for keywords
```

These should not be patched through one analyze-output template.

### 4.3 `misc_exactness_or_unclassified` should not survive as a repair bucket

The audit marks 31 rows as unclassified. That is acceptable for an audit draft, but not for worker handoff.

Immediate de-lumping:

```text
1. flag grammar and compatibility
   - -ig=false
   - -inum + -oh naming: n vs num

2. output-route error projection
   - invalid output path should emit product-style open error, not traceback

3. config / DSN / persistent DB topology
   - invalid DSN nonzero
   - persistent database file creation

4. JSON escape / Unicode / binary output policy
   - \u escaping vs literal Unicode
   - HTML escaping such as & -> \u0026
   - YAML binary vs plain byte/string expectation

5. incompatible-format fatal grammar
   - malformed JSON/incompatible format should be product diagnostic, not Python traceback

6. value-domain renderer exactness
   - row-number column name
   - binary, null, unicode, special characters
```

Rule:

```text
No implementation batch may target `misc_exactness_or_unclassified`.
Rows must first be assigned to numbered HOB nodes or explicitly blocked.
```

### 4.4 `compression_and_external_reader_writer_codecs` is correctly identified but under-split

The audit correctly notes that compression is a codec family, not a gzip/bz2/xz neighborhood. But the child branches should be explicit:

```text
3.7.1 extension auto-detection
3.7.2 explicit -iz/-oz override precedence
3.7.3 input decoder magic/extension agreement
3.7.4 output writer magic bytes and flush/close
3.7.5 unsupported dependency parity: lz4/zstd availability
3.7.6 compressed wildcard expansion
3.7.7 double-extension format guessing
3.7.8 stdout compressed bytes vs text capture
3.7.9 output file compressed bytes vs renderer payload
```

The key equivalence issue:

```text
If the reference has lz4/zstd support but the reconstruction substrate lacks
the dependency, the branch is not just implementation-missing.
It is a target-substrate/methodological-equivalence obligation.
```

### 4.5 `renderer_exact_byte_grammar` is valid but must separate semantic renderers from library dialects

The audit correctly says renderer families were present but not byte-terminalized.

However, the next tree should split:

```text
8.1 raw / delimiter / final newline / all-selected-columns
8.2 CSV quoting / headers / CRLF
8.3 JSON / JSONL value-domain escape policy
8.4 YAML scalar/binary/null/array byte grammar
8.5 markdown table alignment and separator grammar
8.6 ASCII tablewriter dialect
8.7 vertical format record grammar
8.8 TBLN output grammar
8.9 LTSV output grammar
8.10 output format flag precedence
8.11 output-file extension guessing
8.12 stdout/file route split
8.13 compression writer interaction
```

The next worker should not patch `render_table()` generically. It should patch one numbered renderer subtree at a time with byte probes.

### 4.6 `sql_identity_binding_and_resource_rewrite` is high leverage, but not necessarily the first implementation patch

The audit recommends SQL identity and resource rewrite first. That is plausible because it is an upstream discriminator for joins, aliases, subqueries, quoted paths, stdin aliasing, and table-name/query-file composition.

But the audit should qualify the recommendation:

```text
SQL binder is high-leverage but currently only 23 visible remaining rows.
The 194-row input dialect bucket is larger because it still contains multiple
unlowered parents.
```

Recommended revised order:

```text
B0 regression sentinels and de-lumping gate
B1 SQL resource-token closure if bounded to path/alias/subquery/comma-join grammar
B2 row-window + reader-option overlay, because it owns an actual regression
B3 input dialect/error grammar matrix
B4 analyze/config mode renderer and topology
B5 renderer exact byte grammar
B6 codec/dependency parity and compressed writer closure
```

This prevents a premature broad SQL patch that breaks row-window/resource-route branches again.

### 4.7 `type_numeric_and_sql_function_semantics` partially misattributes its own examples

Some rows in this bucket are genuinely numeric/value-domain leaves:

```text
AVG 15.0 vs 15
SUM/COUNT integer rendering
JSON numeric representation
```

But the function examples with trailing `,
` suggest row-universe/blank-row leakage, not only SQL function semantics:

```text
function_length/lower/upper output has an extra blank row
```

So the split should be:

```text
5.5 numeric result type and display normalization
5.6 host SQL function availability
4.x input blank-row / row-universe import semantics
8.x renderer final row/newline grammar
```

This matters because patching SQL functions will not fix an extra imported blank row.

---

## 5. What the audit is missing as an audit artifact

### 5.1 Delta attribution by numbered node

The audit lists fixed modules, but not fixed rows by HOB node.

Needed table:

```text
HOB node | fixed rows | persistent rows | regressed rows | new rows | interpretation
```

Without this, we cannot tell whether the Phase 15 patch generalized a parent rule or merely fixed representative examples.

### 5.2 Regression-retention obligations

The audit notes two regressions, but the next handoff must create hard blockers:

```text
REGRESSION_SENTINEL_GATE:
  every previously green row that regressed becomes a required local sentinel
  before any new batch is accepted.
```

For this run:

```text
R1 = limit + skip + header row-window sentinel
R2 = tilde path expansion sentinel
```

These should be run before and after every next patch.

### 5.3 Child-obligation closure states

The audit references HOB nodes but does not fill the v17 inherited-obligation statuses.

Needed per HOB child:

```text
node_id
applies | not_applicable | pending
children_inherited
probe_matrix_status
implementation_owner
deferral_or_irrelevance_proof
expected_score_risk
```

### 5.4 Probe-first contract

The audit recommends repair order, but the next worker should receive a stronger rule:

```text
No source patch until the targeted HOB child has a probe matrix.
```

The probe matrix must include:

```text
positive case
negative/error case
boundary case
interaction case
regression sentinel
held-out sibling if feasible
stdout/stderr/exit/files split
```

### 5.5 Official-pressure de-lumping before implementation

The audit should forbid implementation from any bucket named:

```text
misc
unclassified
exactness_or_unclassified
other assertion
```

Those names are useful only for triage. They are not ontology nodes.

---

## 6. v18 meta-program patch

### 6.1 `AUDIT_TO_TREE_COMPILATION_GATE`

Trigger:

```text
A post-eval audit produces failure classes, HOB references, or repair-order
recommendations.
```

Rule:

```text
The audit is not worker-ready until each class is compiled into numbered
ontology nodes with inherited child obligations, closure status, probe rows,
implementation owner, and regression sentinels.
```

Required row:

```yaml
audit_class:
row_count:
primary_hob_nodes:
proposed_parent_discriminator:
child_obligations:
  - node_id:
    semantic_obligation:
    status:
    proof_or_probe_ref:
    implementation_owner:
    regression_sentinels:
    expected_risk_if_deferred:
worker_ready: true | false
```

### 6.2 `BROAD_BUCKET_SPLIT_GATE`

Trigger:

```text
Any audit bucket contains more than 25 rows, spans more than one top-level HOB
class, or includes examples whose first failure surfaces differ by layer.
```

Rule:

```text
The bucket must be split before implementation handoff unless a single parent
law demonstrably generates all child failures.
```

For Phase 16 this gate fires on:

```text
input_dialect_value_and_error_grammar: 194
analyze_config_and_control_plane_schema: 65
misc_exactness_or_unclassified: 31
```

### 6.3 `FIXED_PRESSURE_GENERALIZATION_AUDIT`

Trigger:

```text
A patch improves official rows but leaves the same parent macro open.
```

Rule:

```text
Every fixed row must be mapped to the same numbered tree as persistent and
regressed rows. A parent macro is not improved generically unless fixed,
persistent, and regressed rows show a closed child-subtree boundary.
```

Required table:

```text
node_id | fixed | persistent | regressed | conclusion
```

Allowed conclusions:

```text
child_closed
representative_example_fixed
sibling_still_open
regression_non_commutation
uncertain_needs_probe
```

### 6.4 `REGRESSION_SENTINEL_GATE`

Trigger:

```text
Any official or local row that was green in a prior phase becomes red after a
repair batch.
```

Rule:

```text
Before new feature repair, restore or consciously isolate the regression.
The next batch must include the regressed row as a local sentinel.
```

For Phase 16:

```text
R1 limit + skip + header
R2 tilde expansion in path
```

### 6.5 `UNCLASSIFIED_ROW_ZERO_TOLERANCE_FOR_HANDOFF`

Trigger:

```text
Implementation handoff is proposed.
```

Rule:

```text
Unclassified rows may exist in an audit, but not in a worker implementation
contract. They must be assigned to HOB nodes, deferred, or blocked pending
reference observation.
```

### 6.6 `MODE_AS_PROGRAM_GATE`

Trigger:

```text
A flag or public mode changes output purpose, examples, schema display,
resource topology, or diagnostics.
```

Rule:

```text
Treat the mode as a subprogram with its own input route, transform, renderer,
diagnostics, and exit contract.
```

For trdsql:

```text
analyze mode
config mode
dblist mode
debug mode
help/usage mode
```

### 6.7 `READER_TO_SQL_SCHEMA_GATE`

Trigger:

```text
A program imports external resources into an embedded SQL substrate.
```

Rule:

```text
Reader output must be modeled as a schema-producing transform before SQL
execution. Header policy, fallback names, row windows, null conversion,
blank-row handling, table identity, and column identity are inherited child
obligations.
```

This is the missing bridge between the 194-row input bucket and the 23-row SQL identity bucket.

### 6.8 `CODEC_DEPENDENCY_EQUIVALENCE_GATE`

Trigger:

```text
A public format depends on external codec support such as zstd/lz4 or a runtime
library.
```

Rule:

```text
Before classifying failures as product behavior, prove that the reconstruction
substrate has equivalent codec availability or explicitly implement a fallback
compatible with the expected public surface.
```

---

## 7. Revised next repair contract

Do not ask the next worker to “fix the Phase 16 failures.” Ask it to perform one bounded batch.

### Batch 0: audit-to-tree compilation and sentinels

Before any source edit:

```text
1. Expand the 194-row input bucket into child HOB nodes.
2. Expand the 65-row analyze/config bucket into mode-as-program nodes.
3. De-lump all 31 unclassified rows.
4. Build fixed/persistent/regressed table by HOB node.
5. Add regression sentinels for:
   - limit + skip + header
   - tilde path expansion
6. Define probe matrices for the first implementation batch.
```

### Batch 1: SQL/resource/schema bridge

Scope:

```text
READER_TO_SQL_SCHEMA_GATE
SQL identity and resource rewrite
row-window interaction only where required for schema binding
```

Children:

```text
quoted path token
path with spaces
comma join
explicit JOIN
subquery repeated resource
alias over quoted path
table-name flag with query file
stdin alias
table-name collision
SQL injection / semicolon handling
```

Required sentinels:

```text
simple already-green FROM path
already-green two-file join from Phase 15
limit+skip+header regression
tilde expansion regression
```

### Batch 2: dialect/error grammar

Scope:

```text
CSV delimiter/header/skip/limit
fixed-width
JSON/JSONL root/malformed
YAML/TBLN/LTSV invalid and sparse shapes
jq selector syntax
empty/blank file fatal grammar
```

### Batch 3: mode-as-program analyze/config

Scope:

```text
analyze schema detector
analyze renderer grammar
format-advice heuristic
example-query generator
driver quote policy
config/db/dsn topology
help/usage channel exactness
```

### Batch 4: renderer byte grammar

Scope:

```text
raw
CSV
JSON/JSONL
YAML
Markdown
ASCII table
Vertical
TBLN
LTSV
output flag precedence
output route guessing
```

### Batch 5: codecs and dependency parity

Scope:

```text
gzip/bz2/xz/zstd/lz4 input
compressed output writer
explicit -oz override
extension guessing
magic bytes
stdout compressed route
```

---

## 8. Bookkeeper rejections for the next run

Reject the worker if it says:

```text
fixed input dialect grammar
fixed analyze/config
fixed renderer grammar
fixed SQL binder
```

without numbered child closure.

Reject if:

```text
- unclassified rows remain in the implementation handoff;
- the two regressions are not local sentinels;
- broad buckets are patched without split child obligations;
- fixed-pressure rows are not mapped back to HOB nodes;
- probes are created only after source edits;
- stdout/stderr/exit/files are not split;
- output byte grammar is patched by visual approximation;
- codec failures are treated as parser failures without dependency equivalence;
- analyze mode is treated as ordinary diagnostic text;
- SQL resource binding is patched only in FROM/JOIN but not quoted paths,
  aliases, subqueries, comma joins, stdin aliases, and query-file/table-name
  composition where in scope.
```

---

## 9. Bottom line

The Phase 16 audit is a good support-level pressure attribution. Its main conclusion is right:

```text
Phase 15 still shows incomplete sibling descent in the larger public schema.
```

The necessary v18 upgrade is to make the audit itself executable:

```text
post-eval audit
  -> numbered HOB subtree compilation
  -> broad-bucket split
  -> fixed/persistent/regressed delta by node
  -> regression sentinel gate
  -> probe matrix
  -> bounded implementation batch
```

The next improvement will be more robust only if the worker is forced to close inherited child obligations, not merely address representative examples under broad parent names.
