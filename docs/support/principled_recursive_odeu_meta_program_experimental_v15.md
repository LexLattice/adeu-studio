# Principled Recursive ODEU Meta-Program Experimental v15

Authority layer: support / experimental meta-program revision.

v15 preserves the v14 methodological-equivalence invariant and adds a repair
doctrine for the remaining `noborus__trdsql.d8c5ff6` failures after the v14
scoped recheck.

Controlling inputs:

```text
docs/support/principled_recursive_odeu_meta_program_experimental_v14.md
artifacts/manual_runs/programbench_trdsql_v12_gpt55_medium_clean_20260520T203115+0300/run_A_gpt55_medium_clean/phase9c_remaining_failure_layer_audit.md
artifacts/manual_runs/programbench_trdsql_v12_gpt55_medium_clean_20260520T203115+0300/run_A_gpt55_medium_clean/phase9c_v15_remaining_failure_meta_program_patch.md
```

Evidence boundary:

```text
official eval failures remain post_eval_pressure
not clean first-pass reconstruction evidence
```

## 1. v15 Thesis

The v14 repair moved the `trdsql` run from a broken witness measurement to a
usable scoped product-pressure surface:

```text
score 3:
  broken E3/E4 witness-bundle / target-substrate equivalence

score 60:
  scoped product-behavior pressure after witness equivalence repair
```

The remaining failures are not primarily another packaging/substrate failure.
They show that the abstract program statement is still under-derived.

The largest actionable parent miss is:

```text
RESOURCE_BACKED_EMBEDDED_LANGUAGE_PROGRAM
```

For this class, the program is not:

```text
language string + file reader + renderer
```

It is closer to:

```text
public resource routes
  -> resource resolution / expansion / decoding / naming
  -> host-language namespace binding
  -> embedded language execution
  -> output routing / rendering / diagnostics
```

## 2. De-Lump Large Assertion Buckets

The Phase 9c audit listed a large bucket:

```text
Other stdout/assertion leaves: 144
```

v15 treats this as a bookkeeper failure, not as a real parent category.

Rule:

```text
A residual "other assertion" bucket over 5% of total failures or over 25 rows
blocks implementation repair until each row is assigned to a parent
discriminator.
```

Allowed parent discriminators:

```text
value domain
resource route
renderer byte grammar
channel contract
file side effect
state persistence
embedded-language binder
dialect grammar
diagnostic mode
control-plane grammar
```

Required de-lumping row:

```yaml
assertion_row_ref: string
observed_surface: stdout | stderr | exit | file | side_effect | exception
nearest_existing_node: string
candidate_parent_discriminator: string
missing_child_if_any: string
probe_needed_before_patch: true | false
implementation_owner_if_terminal: string | null
```

## 3. v15 Parent Discriminators

For `trdsql`-class programs, re-bucket remaining pressure into these parents.

| Parent discriminator | Absorbs | Primary transition |
| --- | --- | --- |
| `SQL_RESOURCE_BINDER` | path tokens, joins/subqueries over files, wildcard SQL syntax, no-table/no-column, update/delete over resources | L1 -> L2 and L2 -> L3 |
| `RESOURCE_ROUTE_TOPOLOGY` | globs, tilde paths, stdin, output-file guessing, codecs, config paths, DB files, drivers, DSNs | L1 -> L2 / E6 |
| `INPUT_DIALECT_GRAMMAR_MATRIX` | JSONL, YAML, TBLN, LTSV, text, fixed width, jq, nulls, type conversion, invalid syntax | L2 -> L3 |
| `OUTPUT_ROUTER_RENDERER_MATRIX` | raw, markdown, ascii, vertical, CSV, JSON, YAML, LTSV, TBLN, headers, final newline, file routing | L2 -> L3 / E2 |
| `CONFIG_DB_TOPOLOGY` | config files, default config, db list, driver, DSN, debug-config, persistent DB | L1 -> L2 / E6 |
| `MODE_DIAGNOSTIC_CHANNEL_CONTRACT` | analyze/debug/help/no-args/invalid surfaces | L3 -> L4 / E2 |
| `UNCLASSIFIED_ASSERTION_DE_LUMPING` | large assertion buckets not yet assigned to a parent | bookkeeper gap |

## 4. Embedded Language Substrate Gate

Trigger:

```text
The program exposes or consumes a language-like string:
SQL, jq, regex, formula, selector, query, path expression, template, script
fragment, or DSL.
```

Rule:

```text
Do not treat the language string as opaque unless a public/reference warrant
proves pass-through behavior. Split language syntax, host-resource binding,
namespace construction, side effects, diagnostics, and output consumers.
```

Required rows:

```yaml
embedded_language_substrate:
  language_kind: SQL | jq | regex | selector | query | template | other
  host_program_role: evaluator | transformer | router | filter | renderer | other
  expression_only_mode: supported | unsupported | unknown
  resource_backed_mode: supported | unsupported | unknown
  resource_reference_syntax: string | unknown
  namespace_binding_rule: string | unknown
  aliasing_rule: string | unknown
  multi_statement_rule: string | unknown
  side_effect_statement_rule: string | unknown
  diagnostic_surface: stdout | stderr | exit | file | mixed | unknown
  pass_through_warrant_or_rewrite_warrant: string
```

## 5. Resource To Language Binder Gate

Trigger:

```text
Language expressions can refer to files, URLs, tables, paths, globs, stdin,
configured databases, generated resources, or external resources.
```

Rule:

```text
Resource expansion, decoding, import, and naming must be modeled before language
execution. Syntax errors containing path or glob tokens often indicate binder
failure, not merely embedded-language parser failure.
```

Required rows:

```yaml
resource_to_language_binder:
  resource_token_kind: path | glob | stdin | table | config_db | url | generated | other
  resource_resolution_order: string
  path_normalization_policy: string
  glob_expansion_policy: string
  codec_resolution_policy: string
  importer_ref: string
  table_name_derivation: string
  alias_or_quote_policy: string
  collision_policy: string
  statement_rewrite_policy: string
  failure_surface: stdout | stderr | exit | exception | file | mixed
```

## 6. Dialect Terminalization Matrix

Trigger:

```text
A public schema or help surface names input/output formats, dialects,
encodings, renderers, serializers, or table styles.
```

Rule:

```text
A dialect name cannot remain a label. It must become grammar + value-domain
conversion + error contract + projection byte contract + route contract, or be
explicitly excluded from gold readiness.
```

Minimum axes:

```text
empty input
single row
multi row
scalar value
array value
nested value
null value
number/string/bool conversion
invalid syntax
header/no-header
field delimiter/escape/quote
final newline
stdout/stderr/file route
exit behavior
```

## 7. Codec Route Gate

Trigger:

```text
The public program supports compressed input/output, encoded files, extension
guessing, or codec flags.
```

Rule:

```text
Compression is a resource-route transform, not a row parser detail. It runs
before import for input and after renderer bytes for output.
```

Required rows:

```yaml
codec_route:
  codec_kind: gzip | bzip2 | zstd | lz4 | xz | zip | other
  selection_source: extension | flag | magic | config | unknown
  read_sequence: string
  write_sequence: string
  wildcard_composition: string
  output_magic_or_header: string
  error_surface: stdout | stderr | exit | exception | mixed
  side_effect_surface: file | stdout | none | mixed
```

## 8. Config / DB Resource Topology Gate

Trigger:

```text
Flags, env vars, config files, persistent DB files, drivers, DSNs, default
locations, DB lists, or debug-config modes are exposed.
```

Rule:

```text
Config and DB controls are resource topology. They can alter startup, resource
lookup, embedded-language substrate, diagnostics, side effects, and exit.
```

Required rows:

```yaml
config_db_resource_topology:
  config_source_order: string
  default_config_path: string
  explicit_config_path_policy: string
  missing_config_policy: string
  invalid_config_policy: string
  debug_config_projection: string
  db_file_creation_policy: string
  driver_validation_policy: string
  dsn_validation_policy: string
  dblist_projection: string
  persistent_state_lifecycle: string
```

## 9. Gold Ledger Breadth Gate

Trigger:

```text
A local probe set is green or near-green while the public schema still contains
large unlocked dialect, resource, or mode families.
```

Rule:

```text
Local parity must be measured against the public schema denominator, not only
against the hand-built probe denominator.
```

Fields:

```yaml
gold_ledger_breadth:
  public_schema_items_total: integer
  terminalized_schema_items: integer
  locked_schema_items: integer
  deferred_schema_items_with_expected_risk: integer
  unclassified_schema_items: integer
  gold_ledger_breadth_status:
    gold_breadth_satisfied |
    scoped_only_known_unlocked_schema |
    blocked_unclassified_schema |
    blocked_large_unterminalized_families
```

## 10. Probe Families Before Implementation Repair

Do not patch from failing official rows first. Regenerate probe families from
parent discriminators.

```text
P0 public schema / mode re-entry sanity
P1 embedded-language resource binder matrix
P2 resource route topology matrix
P3 codec route matrix
P4 input dialect grammar matrix
P5 output router and renderer byte matrix
P6 config / database topology matrix
P7 diagnostics / channel contract matrix
P8 anti-replay held-out sibling matrix
```

Every P-family row must lock:

```text
stdout bytes
stderr bytes
exit
files created/changed
side effects
schema item refs
parent discriminator refs
```

## 11. Task-Specific Repair Scaffold For `trdsql`

The next `trdsql` scaffold should be owned by semantic modules, not evaluator
test files.

```text
TRDSQLProgram
  ├─ PublicSchema
  ├─ EmbeddedSQLSubstrate
  │   ├─ expression-only SQL
  │   ├─ resource-backed SQL
  │   ├─ table namespace / aliasing
  │   ├─ joins / subqueries / functions / nulls
  │   ├─ multi-statement and update/delete
  │   └─ diagnostics
  ├─ SourceBinder
  │   ├─ path token discovery
  │   ├─ glob expansion
  │   ├─ stdin route
  │   ├─ compressed route
  │   ├─ path normalization / tilde
  │   ├─ table-name derivation
  │   └─ collision policy
  ├─ ResourceTopology
  │   ├─ config files
  │   ├─ DB files
  │   ├─ drivers / DSNs
  │   ├─ output files
  │   └─ codec readers/writers
  ├─ InputDialectImporters
  │   ├─ CSV/TSV
  │   ├─ JSON/JSONL/jq
  │   ├─ YAML
  │   ├─ TBLN
  │   ├─ LTSV
  │   ├─ text
  │   └─ fixed width
  ├─ ValueDomain
  │   ├─ null policy
  │   ├─ numeric conversion
  │   ├─ scalar/array/object conversion
  │   └─ invalid value surfaces
  ├─ OutputRouterAndRenderers
  │   ├─ stdout/file routing
  │   ├─ extension guessing
  │   ├─ compressed output
  │   ├─ raw/ascii/markdown/vertical
  │   ├─ CSV/JSON/JSONL/YAML/LTSV/TBLN
  │   └─ byte grammar parts
  └─ ModeDiagnostics
      ├─ analyze / analyze-all
      ├─ debug
      ├─ help/no-args/errors
      └─ stdout/stderr/exit contracts
```

Suggested implementation owners:

```text
source_router
codec_router
sql_binder
sqlite_executor
input_importer_registry
value_normalizer
renderer_registry
output_router
config_db_topology
diagnostic_emitter
observation_probe_runner
```

## 12. v15 Repair Schedule

```text
1. Run P0 to refresh the public schema item ledger.
2. Run P1/P2 to lock SQL binder and resource route topology.
3. Patch only source_router + sql_binder once P1/P2 identify parent rules.
4. Run P3 to lock codec route behavior.
5. Patch codec_router and output codec sequencing.
6. Run P4 to terminalize input dialect grammars.
7. Patch importer registry and value_normalizer.
8. Run P5 to terminalize renderers and output routes.
9. Patch renderer_registry and output_router.
10. Run P6/P7 for config/database and diagnostics.
11. Patch config_db_topology and diagnostic_emitter.
12. Run P8 anti-replay siblings.
13. Only then run broad official-like local parity.
```

## 13. v15 Bookkeeper Rejects

Reject:

```text
large residual "other assertion" buckets
format names without dialect terminalization matrices
embedded-language tools without embedded-language substrate rows
file-backed language tools without resource-to-language binder rows
compressed resources modeled as parser branches rather than route branches
config/DB flags modeled as passive CLI metadata
local parity claims without public-schema denominator accounting
merged stdout/stderr diagnostics for mode/error rows
implementation handoff while public-schema dialect leaves remain unlabeled
```

## 14. Bottom Line

v14 says:

```text
Evidence transfers only through witnessed equivalence.
```

v15 adds:

```text
For resource-backed embedded-language programs, do not descend directly from
feature labels to implementation. First derive the resource route, host-language
binder, dialect grammar, renderer byte grammar, and diagnostic channel contracts.
```

For `trdsql`, this means the next useful move is a theory repair and
probe-generation pass over:

```text
SQL_RESOURCE_BINDER
RESOURCE_ROUTE_TOPOLOGY
INPUT_DIALECT_GRAMMAR_MATRIX
OUTPUT_ROUTER_RENDERER_MATRIX
CONFIG_DB_TOPOLOGY
MODE_DIAGNOSTIC_CHANNEL_CONTRACT
```

Implementation should follow only after those parents have terminal leaves with
split observations.
