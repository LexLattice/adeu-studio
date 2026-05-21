# Principled Recursive ODEU Meta-Program Experimental v14

## Purpose

v14 is a methodological-equivalence hardening revision after the
`noborus__trdsql.d8c5ff6` v11/v12/v13 audit. It preserves v12 public-schema
re-entry and v13 witness-bundle validity, then promotes the underlying lesson
into a general ADEU / ODEU invariant:

```text
No reconstruction result may transfer across two programs, two executions, two
substrates, two observers, or two artifact states unless the relevant
equivalence relation has been named, scoped, and witnessed.
```

The v13 target-substrate failure was not merely a Python-version bug. It was a
methodology failure: the loop assumed equivalence between local candidate
witness and official candidate witness without proving it.

v13 background retained below:

v13 is a witness-bundle and transfer-validity revision after the
`noborus__trdsql.d8c5ff6` v11/v12 audit. It preserves v12's public-schema
re-entry doctrine and inserts a required layer between implementation and local
parity:

```text
candidate implementation
  -> packaged witness bundle
  -> target-substrate ABI proof
  -> packaged-artifact parity
  -> anti-replay / held-out transfer checks
  -> official-intended eval
```

The v12 GPT-5.5 run showed why this layer is necessary: it reached `90 / 91`
workspace local parity but official eval collapsed to score `3` because the
submitted Python witness did not parse under the evaluator substrate. That is a
witness-bundle validity failure before it is a product-theory failure.

v12 background retained below:

v11 correctly promoted observation ecology, I/O topology after ecology, witness scope, observer horizon, and harness side-effect surfaces. The new run exposed a different failure mode:

```text
reference/public observation revealed a much larger public schema
  -> the loop recorded that observation as text
  -> but did not re-enter recursive ontology descent from it
  -> scoped leaves were promoted as if they were official-ready
  -> candidate probes covered only a subset of locked/reference-observed rows
  -> official eval became the first broad schema terminalization test
```

v12 therefore adds a stronger re-entry doctrine:

```text
public observation can create new program ontology, not merely confirm leaves.
```

A help/usage/list/config/debug/version/schema observation is not just a transcript. It can be a public schema source. Once such a schema source appears, the run must pause implementation, diff the observed schema against the current branch tree, create behavior nodes for every new item, and assign each item a readiness outcome before any official-intended handoff.

Evidence boundary carried forward:

```text
official eval failures = post_eval_failure pressure
not clean first-pass reconstruction evidence
```

Adjacent source-boundary lesson carried forward:

```text
a high score from public upstream source use is not a clean ADEU reconstruction
result. Implementation source origin must be audited before local parity or
official-intended eval can be treated as evidence for the method.
```

## 1. Run B audit distilled as layer-transition evidence

The audit result was:

```text
score: 52
raw rows: 755 passed / 647 failed / 1 skipped / 1403 total
```

The layer model used by the audit was:

```text
L0 visible seed
  -> L1 native ontology
  -> L2 recursive descent / branch tree
  -> L3 terminal leaves / probe contract
  -> L4 reference observation and reconciliation
  -> L5 gold scaffold / implementation handoff
  -> L6 local candidate probe gate
  -> L7 official eval pressure
```

The main failure distribution was not a random patch backlog. It showed repeated layer-transition misses:

| Layer transition | Audit symptom | v12 interpretation | v12 remedy |
| --- | --- | --- | --- |
| L4 -> L2 | Help observation exposed modes, formats, drivers, encodings, and options, but the tree did not regenerate. | Public observation was treated as flat evidence instead of schema-producing evidence. | `PUBLIC_SCHEMA_REENTRY_GATE` and `SCHEMA_ITEM_OBLIGATION_LEDGER`. |
| L1 -> L2 | SQL was modeled as query over discovered file tables only. | Embedded language substrate was under-derived. | `EMBEDDED_LANGUAGE_SUBSTRATE` with SQL computation vs file-backed table binding split. |
| L1 -> L2 / L2 -> L3 | TBLN, YAML, text, fixed-width, JSON/JSONL, jq were recognized as labels but not grammars. | Format names were not terminalized into input/output dialects. | `FORMAT_DIALECT_GRAMMAR_MATRIX` and `FORMAT_REALISM_LADDER`. |
| L2 -> L3 | Output options/formats were listed but not byte-terminalized. | Projection byte grammar existed as doctrine but was not forced for every help-discovered renderer. | `OUTPUT_ROUTER_AND_RENDERER_CONTRACT`. |
| L3 -> L4 | Reference runner merged stdout and stderr. | Observation lock was not typed enough for byte/channel branches. | `OBSERVATION_LOCK_V2_SPLIT_SURFACES`. |
| L3 -> L5 | Known scoped gaps were promoted into official-run ready posture. | The readiness product existed but was not hard-enforced. | `KNOWN_GAP_OFFICIAL_BLOCKER` and `GOLD_SCOPE_CONTRACT`. |
| L5 -> L6 | Candidate passed selected probes rather than all locked reference rows. | Local gate did not compare candidate against the whole locked observation ledger. | `LOCKED_REFERENCE_PARITY_GATE`. |

## 2. v12 main correction

v11 already had:

```text
Gate C4: observed help control instantiation
Gate C11: gold implementation handoff gate
blind public-surface scout
granularity fitness
gold readiness vs scoped readiness
```

The audit shows those were not yet sufficiently executable. The missing rule is:

```text
Observed public schema must invalidate and reopen the pre-observation scaffold
for every newly discovered behavior-bearing item.
```

v12 changes the model from:

```text
help observation -> observed_help_control_instantiation_table -> continue
```

to:

```text
help/list/schema observation
  -> public schema harvest
  -> schema diff against current ontology
  -> recursive re-entry for every new item
  -> terminalize / defer / prove pass-through
  -> update readiness ledger
  -> only then implementation handoff
```

This is the same scientific discipline as earlier versions, but applied one level earlier: the program statement itself can expand after public observation.

## 3. New hard gate: PUBLIC_SCHEMA_REENTRY_GATE

### Trigger

```text
Any public observation from help, usage, version, list, schema, config, debug,
examples, invalid-value diagnostics, driver listings, format listings, or mode
listings exposes controls, modes, formats, drivers, dialects, encodings,
examples, subcommands, input routes, output routes, or environment assumptions
not present as behavior nodes in the current ontology tree.
```

This is broader than help. It covers any public surface that emits a grammar or schema.

### Required output

```yaml
public_schema_reentry_gate:
  observation_ref: OBS-...
  schema_source_kind:
    help | usage | version | list | config | debug | diagnostic |
    examples | driver_listing | format_listing | mode_listing | other
  current_ontology_snapshot_ref: TREE-...
  discovered_schema_item_refs: [PSI-...]
  schema_diff_status:
    no_new_items | new_items_attached | new_items_missing_parent |
    contradicts_current_tree | needs_re_descent
  reentry_required: true | false
  reentry_blocker_status:
    blocked_until_re_descent | re_descent_complete |
    explicitly_deferred_with_expected_risk
  handoff_effect:
    blocks_gold_handoff | downgrades_to_scoped_handoff |
    no_handoff_effect
```

### Rule

```text
A discovered public schema item cannot remain a help-text string. It must be one
of:

1. terminalized now;
2. explicitly deferred from gold with expected risk;
3. proved pass-through or no-op by reference observation;
4. attached to a parent as a non-behavior-bearing alias with warrant.
```

If none of those holds, implementation handoff is blocked. If the run proceeds anyway, the handoff type must be:

```text
scoped_implementation_attempt
not_gold_implementation_attempt
```

## 4. New ledger: SCHEMA_ITEM_OBLIGATION_LEDGER

Each public schema item gets its own obligation row.

```yaml
schema_item_obligation:
  schema_item_id: PSI-...
  source_observation_ref: OBS-...
  raw_spelling: string
  aliases: []
  item_kind:
    flag | flag_value | mode | format | input_format | output_format |
    driver | dsn | config_key | encoding | compression | route |
    example | subcommand | environment | debug_surface | other
  source_context:
    help | usage | example | diagnostic | listing | public_probe
  parent_ontology_node: N-... | missing
  behavior_role_candidates:
    parser | input_decoder | source_router | SQL_substrate | embedded_language |
    analyzer | renderer | output_router | null_policy | header_policy |
    delimiter_policy | quote_policy | row_universe | error_surface |
    stream_channel | side_effect | resource | driver_backend |
    diagnostic | exit_denominator | no_op_alias | unknown
  affected_surfaces:
    stdout: possible | yes | no | unknown
    stderr: possible | yes | no | unknown
    exit: possible | yes | no | unknown
    file_side_effect: possible | yes | no | unknown
    resource_side_effect: possible | yes | no | unknown
  recursive_descent_status:
    not_started | in_progress | terminalized | pass_through_locked |
    deferred_from_gold | conflict_isolated
  terminalization_status:
    no_behavior | terminal_leaf_created | parent_only_too_coarse |
    missing_child_grammar | missing_cross_product | deferred_with_risk
  probe_status:
    no_probe_needed | probe_needed | probe_ready | reference_observed |
    candidate_compared | blocked
  gold_readiness_status:
    gold_ready | not_gold_ready | explicitly_deferred_from_gold_with_expected_risk |
    not_gold_required
  defer_reason: string | null
  expected_score_risk_if_deferred: low | medium | high | unknown
  implementation_obligation_ref: IMPL-... | null
```

### Bookkeeper rule

```text
Every schema item discovered by a public observation must appear in this ledger.
A public-schema item missing from the ledger is a blocking bookkeeper failure.
```

## 5. Hardened observation lock: OBSERVATION_LOCK_V2_SPLIT_SURFACES

The audit showed that reference probes used merged transcripts:

```text
> output.txt 2>&1
```

That is acceptable only as commentary. It cannot lock byte/channel branches.

### Trigger

```text
Any reference observation used to terminalize a CLI, renderer, diagnostic,
mode, side-effect, output route, debug, help, error, or exit leaf.
```

### Required observation shape

```yaml
observation_lock_v2:
  observation_id: OBS-...
  command_argv: []
  stdin_bytes_ref: BYTES-... | null
  cwd: string
  env_delta: {}
  stdout_bytes_ref: BYTES-...
  stdout_sha256: string
  stderr_bytes_ref: BYTES-...
  stderr_sha256: string
  exit_code: int
  files_created: []
  files_modified: []
  files_deleted: []
  file_bytes_sha256: {}
  resource_state_before: {} | null
  resource_state_after: {} | null
  timing:
    start_time: string | null
    end_time: string | null
    duration_ms: int | null
    timeout_observed: true | false
  merged_transcript_ref: BYTES-... | null
  merged_transcript_authority:
    commentary_only | forbidden_as_byte_oracle
```

### Rule

```text
stdout, stderr, exit, file effects, timing, and resource state are separate
surfaces. A merged transcript cannot support byte/channel terminalization,
stream identity, debug diagnostics, help/no-args behavior, or output route
claims.
```

## 6. New macro: EMBEDDED_LANGUAGE_SUBSTRATE

The trdsql failure was partly caused by modeling SQL too narrowly as a query over discovered file paths. v12 generalizes this as an embedded-language substrate issue.

### Trigger

```text
The program accepts SQL, jq, path expressions, formulas, regex-like filters,
query languages, field selectors, templates, or any mini-language that can
compute output independent of an external input table or can transform selected
input resources.
```

### Kernel expansion

```text
EMBEDDED_LANGUAGE_SUBSTRATE
  = K1 Factor language text, parser, AST, evaluator, variables, input bindings,
    resource bindings, and output columns
  + K2 Partition empty expression, expression-only program, file-backed program,
    multi-statement program, invalid syntax, invalid semantic reference,
    null/boolean/numeric/string values, aliases, functions/operators
  + K3 Bind language outputs to renderer columns, row universe, errors, exit,
    files, and resource tables
  + K4 Transform language semantics: expression evaluation, joins, subqueries,
    casts, functions, operators, filters, projections, null propagation
  + K5 Sequence parse -> bind resources -> evaluate -> render -> route output
  + K6 Expose parse errors, semantic errors, stdout/stderr split, renderer bytes,
    exit, and side-effect routing
  + K7 Compose language semantics with input format, output format, config,
    null policy, source routing, and output route
  + M0 Warrant public/schema/source/post-eval evidence boundaries
```

### Mandatory child branches

```text
expression_only_language_program
file_backed_language_program
mixed_expression_and_file_program
subquery_or_nested_program
join_alias_program
function_operator_program
multi_statement_program
null_semantics_program
invalid_syntax_program
invalid_reference_program
language_error_projection
```

### Rule

```text
A language-bearing program is not gold-ready if the language ontology is only
"query over inputs". It must split computation substrate from resource binding.
```

For trdsql, this would have forced:

```text
SELECT 1
SELECT NULL
SELECT CAST('123' AS INTEGER)
SELECT 1, 2, 3
```

as computation-substrate probes before deciding that absence of table files is fatal.

## 7. New macro: FORMAT_DIALECT_GRAMMAR_MATRIX

The audit showed repeated format labels that were not grammars: TBLN, YAML, JSON/JSONL, text, fixed-width, CSV-like variants, and output formats.

### Trigger

```text
Any help/spec/public observation exposes named input formats, output formats,
serializers, decoders, encodings, compression formats, table formats, or raw
format options.
```

### Required matrix

```yaml
format_dialect_grammar_matrix:
  format_ref: FMT-...
  direction: input | output | both
  discovered_from: visible_spec | help | list | diagnostic | public_probe
  grammar_status:
    label_only | minimal_terminalized | family_terminalized |
    deferred_with_expected_risk
  input_grammar:
    record_shape: scalar | object | array | row_list | line_records | fixed_width | unknown
    header_policy: required | optional | absent | inferred | flag_controlled | unknown
    delimiter_policy: default | custom | escaped | quoted | not_applicable | unknown
    row_boundary_policy: newline | CRLF | block | width_spec | parser_owned | unknown
    null_policy_ref: NULL-... | null
    numeric_policy_ref: NUM-... | null
    nested_shape_policy: flat_only | nested_projected | nested_error | unknown
    malformed_policy_ref: ERR-... | null
  output_grammar:
    row_universe_ref: N-... | null
    header_policy: present | absent | flag_controlled | unknown
    delimiter_policy: default | custom | raw | quoted | unknown
    quoting_policy: none | minimal | always | escape_owned | unknown
    line_ending_policy: LF | CRLF | flag_controlled | unknown
    null_projection_ref: NULL-... | null
    final_newline_policy: present | absent | unknown
    file_route_policy_ref: ROUTE-... | null
  cross_product_refs:
    input_format_x_output_format: []
    format_x_null_policy: []
    format_x_header_policy: []
    format_x_output_route: []
    format_x_compression: []
```

### Rule

```text
A named format is not a terminal leaf. It is a grammar family. A format cannot
be gold-ready as `label_only` unless explicitly deferred from gold with expected
risk.
```

### FORMAT_REALISM_LADDER

The audit table names `FORMAT_REALISM_LADDER`; v12 defines it as the minimum
graduated realism ladder for any format family that the run wants to call
gold-ready.

```text
format label observed
  -> minimal synthetic specimen
  -> representative public/example-shaped specimen
  -> malformed/wrong-shape specimen
  -> empty/header/null specimen where applicable
  -> route/guessing specimen where applicable
  -> cross-product specimen with output rendering or embedded language semantics
```

Rule:

```text
A single happy-path specimen proves only minimal syntax contact. It does not
terminalize the format family unless the format is explicitly scoped down.
```

## 8. New macro: OUTPUT_ROUTER_AND_RENDERER_CONTRACT

v11 had projection row-universe and byte-grammar child leaves. v12 adds a more explicit router layer because trdsql output failures combined renderer bytes, output guessing, output-file routing, delimiters, headers, quoting, CRLF, and null policy.

### Trigger

```text
Any program can choose an output format, output file, output route, output
wrapper, raw mode, format guessing policy, line ending policy, delimiter policy,
quote policy, header policy, or compression policy.
```

### Expansion

```text
OUTPUT_ROUTER_AND_RENDERER_CONTRACT
  = K1 Factor renderer, router, file target, stdout target, inferred format,
    explicit format, wrapper, line ending, delimiter, quote, null/header controls
  + K2 Partition explicit vs guessed format, stdout vs file, overwrite/create,
    absent extension, recognized extension, unknown extension, no header,
    custom delimiter, CRLF, raw, quoted, null token
  + K3 Bind semantic rows and columns to renderer columns, output route, file
    side effects, stdout/stderr, and exit denominator
  + K5 Sequence evaluate -> serialize -> route -> flush -> exit
  + K6 Expose exact stdout bytes, file bytes, stderr diagnostics, exit, and
    created/modified files
  + K7 Compose output format with input format, null policy, header policy,
    SQL output columns, compression, output route, and error precedence
```

### Required child rows

```text
explicit_output_format
extension_guessed_output_format
out_without_guess_policy
stdout_output_route
file_output_route
compressed_output_route
header_presence_policy
delimiter_policy
quote_policy
line_ending_policy
null_output_token_policy
raw_output_policy
renderer_error_projection
```

## 9. New macro: INPUT_DECODING_AND_RESOURCE_TOPOLOGY

The audit found unmodeled compression, wildcards, stdin keyword, empty files, path-to-table identity, extension guessing, DB/config/driver/DSN surfaces, and file formats.

### Trigger

```text
Any program reads files, stdin, globs/wildcards, compressed files, DB/DSN/config
resources, drivers, encoded inputs, or extension-guessed input formats.
```

### Expansion

```text
INPUT_DECODING_AND_RESOURCE_TOPOLOGY
  = K1 Factor source route, resource kind, decoder, compression layer, driver,
    config, DSN, table identity, path identity, stdin identity
  + K2 Partition absent source, stdin keyword, piped stdin, path source,
    wildcard source, empty file, missing file, directory, compressed file,
    unsupported compression, DB source, driver missing, config malformed,
    extension-guessed format, explicit format
  + K3 Bind resources to table names, SQL binding, row universe, diagnostics,
    renderer, side effects, and exit
  + K5 Sequence route selection -> decompress -> decode -> bind table -> query
  + K6 Expose source errors, decoder errors, table identity, stdout/stderr split,
    exit, and output route
  + K7 Compose input route with SQL expression-only mode, output format,
    null policy, jq/path sublanguage, config/driver, and output guessing
```

### Mandatory child rows

```text
no_source_route
stdin_keyword_route
piped_stdin_route
path_file_route
wildcard_route
empty_file_route
extension_guess_route
explicit_input_format_route
compression_decode_route
DB_driver_route
config_DSN_route
path_to_table_identity
source_error_projection
```

### Rule

```text
Source absence is not globally fatal until the embedded language substrate says
there is no expression-only branch and no DB/config route. Route selection must
be composed with language substrate before fatal no-source diagnostics are
promoted.
```

## 10. New macro: MODE_FAMILY_CONTRACT

The audit specifically called out analyze modes `-a` / `-A`, debug, DB list/config/driver modes, and other public controls that alter the program mode.

### Trigger

```text
A control discovered from visible spec or public observation changes the program
from the default data-transform path into an analyze, list, config, debug,
version, schema, validation, driver, or diagnostic mode.
```

### Expansion

```text
MODE_FAMILY_CONTRACT
  = K1 Factor mode, entrypoint, required resources, optional resources, output
    projection, diagnostics, and exit
  + K2 Partition default mode, analyze mode, list mode, config mode, debug mode,
    DB mode, version/help mode, incompatible mode combinations
  + K3 Bind mode to row universe, resource requirements, renderer, stdout/stderr,
    side effects, and exit
  + K5 Sequence mode detection before/after flag validation, source route,
    SQL parse, terminal/init, output route
  + K6 Expose mode-specific stdout/stderr bytes, files, and exit
  + K7 Compose mode with formats, source routes, DB/config, debug, and errors
```

### Rule

```text
A mode flag is not an option leaf. It can create a different program theorem.
Any discovered mode remains gold-blocking until terminalized, deferred, or
proved no-op/pass-through.
```

## 11. New macro: NULL_SEMANTICS_AND_VALUE_DOMAIN

The audit grouped null policy and SQL null semantics separately. v12 makes null a cross-layer value-domain macro.

### Trigger

```text
The program has SQL, JSON/YAML null, CSV empty fields, input null conversion,
output null tokens, nullable DB values, typed conversion, or null-related flags.
```

### Expansion

```text
NULL_SEMANTICS_AND_VALUE_DOMAIN
  = K2 Partition absent, empty string, literal null token, JSON/YAML null,
    SQL NULL, typed zero, false, empty array/object, missing field
  + K3 Bind null state to SQL truth, input decoder, renderer, output null token,
    filters, aggregates, and exit
  + K4 Transform null propagation, NULLIF/IS NULL, casts, comparison, aggregate
    behavior, input conversion, output conversion
  + K6 Expose null rendering, diagnostics, and byte grammar
  + K7 Compose null with format dialects and embedded language semantics
```

### Rule

```text
Null behavior cannot be delegated to a renderer only. It is a value-domain
contract shared by input decoding, embedded language evaluation, and output
projection.
```

## 12. Updated descent algorithm for v12

Replace v11 descent steps 2-4 with the following stricter loop:

```text
1. Create base ontology graph from README/spec.
2. Run hard-gate discovery from visible spec.
3. Run minimal public bootstrap observations when a reference executable exists:
   help/usage/version/list/invalid flag/no-args with split surfaces.
4. If any public observation emits schema, run PUBLIC_SCHEMA_REENTRY_GATE.
5. Populate SCHEMA_ITEM_OBLIGATION_LEDGER for every discovered schema item.
6. Diff discovered schema items against current ontology:
   - attach to existing terminal leaf;
   - attach to parent-only leaf and mark too coarse;
   - create missing ontology node;
   - mark contradiction/conflict;
   - mark no-op/pass-through candidate.
7. For every new or too-coarse schema item, re-enter recursive descent using
   K1-K7 + M0 and applicable macros.
8. Trigger v12 macros as needed:
   EMBEDDED_LANGUAGE_SUBSTRATE,
   FORMAT_DIALECT_GRAMMAR_MATRIX,
   OUTPUT_ROUTER_AND_RENDERER_CONTRACT,
   INPUT_DECODING_AND_RESOURCE_TOPOLOGY,
   MODE_FAMILY_CONTRACT,
   NULL_SEMANTICS_AND_VALUE_DOMAIN.
9. Lock observations only through OBSERVATION_LOCK_V2_SPLIT_SURFACES.
10. Run terminalization for every gold-required schema item.
11. Run gold/scoped readiness accounting.
12. If any schema item is unresolved, implementation is blocked or scoped-only.
13. Declare implementation-origin constraints before handoff.
14. Implement only after handoff type is explicitly declared.
15. Run IMPLEMENTATION_ORIGIN_BOUNDARY_GATE over the candidate source/package.
16. Run LOCKED_REFERENCE_PARITY_GATE over every locked observation before
    official eval.
```

## 13. New readiness/gate: KNOWN_GAP_OFFICIAL_BLOCKER

### Trigger

```text
Any phase artifact says a behavior family is not gold-ready, not terminalized,
not probed, deferred, scoped-only, or expected-risk, and the run proposes an
official-intended implementation/eval.
```

### Rule

```text
Known non-gold branches cannot silently ride along into an official-ready handoff.
```

The handoff must choose one of:

```text
1. close the gap now;
2. explicitly defer the gap from gold with expected score risk;
3. downgrade the run to scoped_implementation_attempt;
4. block official-intended eval.
```

### Required row

```yaml
known_gap_official_blocker:
  gap_ref: GAP-...
  originating_phase_ref: PHASE-...
  affected_schema_items: [PSI-...]
  affected_terminal_leaves: [N-...]
  declared_status:
    not_gold_ready | terminalization_open | probe_missing | scoped_only |
    deferred_with_risk | conflict_isolated
  proposed_handoff_type:
    scoped_implementation_attempt | gold_implementation_attempt |
    official_experiment
  allowed: true | false
  required_action:
    close_gap | explicit_gold_deferral | downgrade_to_scoped |
    block_handoff
```

## 14. New gate: LOCKED_REFERENCE_PARITY_GATE

The audit says the candidate passed selected probes, not every declared reference observation. v12 makes the local gate mechanically stronger.

### Trigger

```text
Candidate implementation exists and any reference observations are locked.
```

### Required local runner

```yaml
locked_reference_parity_gate:
  runner_ref: RUNNER-...
  locked_observation_manifest_ref: OBSMAN-...
  candidate_binary_ref: BIN-...
  total_locked_rows: int
  rows_compared: int
  rows_passed: int
  rows_failed: int
  skipped_rows: []
  skipped_row_warrants: {}
  compared_surfaces:
    stdout_bytes: true
    stderr_bytes: true
    exit_code: true
    file_effects: true
    resource_state: true | false
    timing: true | false
  failure_rows: []
  handoff_effect:
    blocks_official_eval | scoped_only | green_for_declared_scope
```

### Rule

```text
A candidate cannot be called locally green unless it is compared against every
locked row in the declared scope, across every locked surface. A selected subset
is a development smoke test, not a local gold gate.
```

## 15. New gate: IMPLEMENTATION_ORIGIN_BOUNDARY_GATE

The trdsql parallel run also exposed a separate method-risk: a candidate can
score well by drawing from public upstream implementation source. That may be a
useful engineering shortcut in another lane, but it is not clean ADEU
reconstruction evidence.

### Trigger

```text
A candidate implementation is about to be produced, patched, packaged, compared
against locked observations, or run through official-intended eval.
```

### Rule

```text
Clean ADEU implementation source may be derived only from approved
reconstruction artifacts:
  - visible task packet/spec;
  - public executable/reference observations locked through OBSERVATION_LOCK_V2;
  - generated probe fixtures and expected observations;
  - fresh authored candidate code inside the implementation workspace;
  - explicitly labeled post_eval_failure pressure when the run is a repair run.

It may not be derived from:
  - public upstream repository implementation files;
  - hidden/evaluator tests or source;
  - decompiled binaries;
  - copied source-like files from reference containers or cleanroom images;
  - previous contaminated candidate source trees;
  - postmortem patches laundered as clean first-pass evidence.
```

### Required row

```yaml
implementation_origin_boundary_gate:
  candidate_ref: CAND-...
  candidate_package_ref: PKG-...
  declared_run_lane:
    clean_reconstruction | postmortem_repair | source_assisted_engineering
  allowed_input_artifact_refs:
    visible_spec_refs: []
    locked_public_observation_refs: []
    generated_probe_refs: []
    approved_post_eval_pressure_refs: []
  authored_file_manifest_ref: MANIFEST-...
  generated_file_manifest_ref: MANIFEST-...
  copied_source_refs: []
  public_upstream_source_refs: []
  hidden_or_evaluator_source_refs: []
  decompiled_or_container_source_refs: []
  previous_candidate_source_refs: []
  contamination_verdict:
    clean | contaminated | unknown
  handoff_effect:
    clean_ready | scoped_only | source_assisted_non_comparable |
    blocks_official_eval
```

### Handoff rule

```text
If contamination_verdict is contaminated or unknown, the run cannot be reported
as a clean ADEU reconstruction result. It must be labeled
source_assisted_non_comparable, downgraded to scoped/non-method evidence, or
blocked before official-intended eval.
```

## 16. Public scout vs conceptual descent: trdsql audit split

The audit’s failures separate into surfaces that should have been caught by public scout and surfaces that should have been caught by conceptual descent.

### Better public scout should have found

```text
- full option/mode/format inventory from help;
- -a / -A analyze modes;
- -config / -db / -dblist / -driver / -dsn surfaces;
- -debug and stream identity;
- explicit input formats and input options;
- explicit output formats and output options;
- -oz and compressed output/input implications;
- -ijq and file.json::.items path/filter syntax;
- stdout/stderr/exit split for help, no-args, unknown, debug, diagnostics;
- output-file route and output-guessing behavior.
```

### Better conceptual descent should have found

```text
- SQL as computation substrate, not only file-table query;
- expression-only SQL branch;
- SQL null semantics and typed value domains;
- format names as grammar families, not labels;
- TBLN/YAML/text/fixed-width/JSONL as input/output grammar families;
- output renderer byte grammars for every declared format;
- source route lattice: no source, stdin keyword, stdin pipe, files, wildcards,
  empty files, extension guessing, DB/DSN/config routes;
- null policy as cross-layer input/language/output behavior;
- mode flags as program-mode contracts.
```

### Mixed scout + descent

```text
- compression / encoded files: public scout discovers flags and extensions;
  conceptual descent builds decode/resource topology.
- jq: public scout discovers `-ijq` and suffix syntax; conceptual descent treats
  jq as embedded language substrate.
- DB/config/driver: public scout discovers controls; conceptual descent creates
  external backend topology and error/diagnostic surfaces.
```

## 17. Mandatory probe packets before implementation on trdsql-like tasks

v12 does not recommend patching first. It recommends rebuilding the scaffold and then probing.

### P0: public schema harvest with split surfaces

```text
commands:
  no args
  -h / --help / help aliases
  --version / version aliases when plausible
  unknown flag
  missing value for value flags
  invalid values for typed/enumerated flags
  format/list/driver/listing modes exposed by help

capture:
  stdout bytes
  stderr bytes
  exit code
  created/modified files
  timing
```

### P1: schema item obligation coverage

```text
For every help-discovered flag/mode/format/driver/encoding/route:
  classify behavior role;
  attach to ontology node;
  create terminalization status;
  declare gold-ready/deferred/pass-through.
```

### P2: embedded SQL substrate probes

```text
expression-only:
  SELECT 1
  SELECT NULL
  SELECT CAST('123' AS INTEGER)
  SELECT 1, 2, 3

file-backed:
  SELECT * FROM table
  aliases
  joins/subqueries
  functions/operators
  multiple statements if public behavior suggests it

negative:
  invalid syntax
  invalid column/table reference
  no source plus expression-only
  no source plus file-backed query
```

### P3: input decoding/resource topology probes

```text
stdin pipe
stdin keyword
single file
wildcard file
empty file
extension-guessed input
explicit input format
compressed input/route if public controls expose it
DB/config/driver route if public controls expose it
missing/malformed resource
```

### P4: format dialect grammar matrix

```text
Input families:
  CSV/TSV-like, LTSV, JSON, JSONL, YAML, TBLN, text, fixed-width.

Per family, probe:
  minimal row
  header/no-header
  null/empty/scalar/nested where applicable
  malformed/wrong-shape
  explicit vs guessed format
```

### P5: output router and renderer contract

```text
Formats/options:
  table-like, raw, CSV, JSON, JSONL, LTSV, markdown, TBLN, vertical form,
  YAML, delimiter, quote, header/no-header, CRLF, null token, nowrap, file route,
  output guessing, out-without-guess, compression if applicable.

Capture exact stdout/file bytes, stderr, exit, and final newline.
```

### P6: mode family probes

```text
analyze -a / -A
config/db/driver/list modes
debug mode
mode combined with valid and invalid sources
mode combined with output route/format when meaningful
mode precedence against source absence and SQL errors
```

### P7: local reference parity runner

```text
Machine-readable runner comparing every locked row, not selected rows.
```

### P8: held-out/metamorphic probes

```text
format-preserving data perturbation
SQL expression value perturbation
header/no-header sibling
stdin/file equivalent source sibling
output-to-file vs stdout sibling
null token sibling
line-ending sibling
```

## 18. Task-specific repair scaffold for trdsql-like reconstruction

The next trdsql scaffold should be structured like this:

```text
TRDSQLProgram
  ├─ PublicSchema
  │   ├─ help/usage/version/no-args/unknown/debug channel grammar
  │   ├─ schema item obligation ledger
  │   └─ re-entry diff from README ontology
  ├─ ControlPlane
  │   ├─ parser token binding
  │   ├─ value shapes
  │   ├─ mode family controls
  │   └─ diagnostics / exit / streams
  ├─ EmbeddedSQLSubstrate
  │   ├─ expression-only SQL
  │   ├─ file-backed SQL
  │   ├─ resource binding and table identity
  │   ├─ joins/subqueries/aliases/functions/operators
  │   ├─ null semantics
  │   └─ SQL diagnostics
  ├─ SourceRouteAndResourceTopology
  │   ├─ no source / stdin / stdin keyword / file / wildcard
  │   ├─ empty and malformed resources
  │   ├─ extension guessing
  │   ├─ compression/encoded files
  │   ├─ DB/config/driver/DSN routes
  │   └─ route fatal precedence
  ├─ InputFormatDialects
  │   ├─ CSV-like / LTSV / JSON / JSONL / YAML / TBLN / text / fixed-width
  │   ├─ header/null/numeric/delimiter/record-shape policies
  │   └─ jq/path sublanguage when selected
  ├─ TransformSemantics
  │   ├─ rows/columns to SQL tables
  │   ├─ value typing and casts
  │   ├─ null propagation
  │   └─ aggregation/query result model
  ├─ OutputRouterAndRenderers
  │   ├─ explicit vs guessed output format
  │   ├─ stdout vs file route
  │   ├─ CSV/raw/table/markdown/JSON/YAML/TBLN/VF/etc.
  │   ├─ quote/delimiter/header/CRLF/null/final-newline policies
  │   └─ output compression
  ├─ AnalyzeAndDiagnosticModes
  │   ├─ -a / -A
  │   ├─ -debug
  │   ├─ db/list/config/driver modes
  │   └─ stream identity and exit
  └─ ReadinessAndParity
      ├─ observation lock v2
      ├─ scoped vs gold ledger
      ├─ known-gap official blocker
      ├─ implementation origin boundary gate
      └─ locked reference parity gate
```

Implementation ownership follows the same tree:

```text
public_schema_parser
arg_parser_and_mode_router
source_router_and_decoder
embedded_sql_engine
format_decoders
transform/value/null layer
output_router
format_renderers
observation_lock_runner
parity_runner
implementation_origin_auditor
```

## 19. v12 operator refinements beyond v11

The v8/v11 kernel remains:

```text
Factor
Partition
Bind
Transform
Sequence
Expose
Compose
Warrant
```

v12 refines operator duties:

### K1 Factor

Now explicitly factors **public schema items** as entities:

```text
A flag, mode, format, driver, example, encoding, route, or schema listing is a
program entity if it can change behavior.
```

### K2 Partition

Now treats **label-only format recognition** as an open partition, not a terminal state:

```text
format label != grammar
mode label != mode contract
SQL flag != SQL substrate
```

### K3 Bind

Now binds discovered public schema items to:

```text
behavior role
parent ontology node
affected surfaces
readiness state
implementation obligation
```

### K4 Transform

Now explicitly covers embedded language semantics and value-domain transforms:

```text
SQL/jq/formula/path language evaluation
resource-to-table binding
null propagation
casts/functions/operators
format decoding to semantic rows
semantic rows to output bytes
```

### K5 Sequence

Now includes **schema-observation re-entry order**:

```text
observe public schema
  -> diff ontology
  -> re-enter descent
  -> terminalize/defer
  -> implementation handoff
```

Skipping this sequence is a gate failure.

### K6 Expose

Now splits:

```text
schema-emitting surfaces
byte-output surfaces
channel surfaces
file-effect surfaces
mode-listing surfaces
```

### K7 Compose

Now forces cross-products for:

```text
input format x output format
SQL substrate x source route
null policy x input/output format
mode family x source route
output route x output format
compression x source/output route
public schema item x fatal precedence
```

### M0 Warrant

Adds new warrant labels:

```text
schema_observed_pending_reentry
schema_item_terminalized
schema_item_pass_through_locked
schema_item_deferred_from_gold
known_gap_blocks_official
merged_transcript_commentary_only
locked_reference_parity_green
locked_reference_parity_failed
```

## 20. v12 bookkeeper additions

The adversarial bookkeeper must reject:

```text
public_schema_item_missing_from_ledger
public_schema_observed_without_reentry
schema_item_attached_to_parent_only_but_promoted
format_label_promoted_without_grammar
mode_label_promoted_without_mode_contract
embedded_language_treated_as_file_query_only
no_source_fatal_promoted_without_expression_only_language_branch
merged_stdout_stderr_used_as_byte_or_channel_oracle
known_scoped_gap_promoted_to_official_ready
candidate_green_on_selected_subset_only
locked_reference_row_not_compared
candidate_source_origin_unproven
public_upstream_source_used_as_clean_implementation
copied_reference_source_used_as_fresh_authored_code
output_route_without_file/stdout split
null_policy_renderer_only_without_input/language split
DB/config/driver flag left as help text only
compression_flag_without decode/resource topology
jq/path/filter flag without embedded-language substrate
```

When a blocking objection appears, the bookkeeper must return the smallest repair:

```text
missing schema item
missing parent node
missing macro gate
missing terminal leaf
missing observation split
missing parity row
missing implementation origin row
wrong handoff type
```

## 21. v12 generator prompt patch

Add this block to the generator prompt after public scouting/observation:

```text
After any public observation, do not merely summarize the output.
Ask whether the output emits a public schema.

If it emits flags, modes, formats, drivers, encodings, examples, input routes,
output routes, config keys, environment assumptions, or subcommands, run
PUBLIC_SCHEMA_REENTRY_GATE.

For every discovered item:
  - create a SCHEMA_ITEM_OBLIGATION_LEDGER row;
  - attach it to a behavior node or create the missing node;
  - decide terminalize now / pass-through / defer from gold / conflict-isolate;
  - apply the kernel recursively and trigger macros.

Do not implement while any discovered schema item is missing, parent-only,
label-only, or unclassified unless the run is explicitly downgraded to scoped.

Never use merged stdout+stderr observations to lock byte/channel leaves.
Reference observations must record stdout, stderr, exit, files, resource state,
and timing separately.

Before official-intended eval, run LOCKED_REFERENCE_PARITY_GATE over every
locked observation in the declared scope. Selected probes are smoke tests, not
local gold.

Before parity or official-intended eval, create an
IMPLEMENTATION_ORIGIN_BOUNDARY_GATE row. A candidate built from public upstream
source, hidden/evaluator code, decompiled source, copied reference-container
source, or an unknown origin cannot be labeled as a clean ADEU reconstruction.
It may be useful engineering evidence, but it is source_assisted_non_comparable
for method scoring unless the run explicitly selected that lane.
```

## 22. v12 immediate run recipe for the next trdsql attempt

The next run should not start with code repair. It should start with scaffold repair:

```text
1. Re-run public help/no-args/unknown/debug/version scout with OBSERVATION_LOCK_V2.
2. Build SCHEMA_ITEM_OBLIGATION_LEDGER from every discovered control, mode,
   format, driver, route, and option.
3. Run PUBLIC_SCHEMA_REENTRY_GATE and regenerate ontology branches for all
   missing/coarse items.
4. Terminalize or explicitly defer each discovered family:
   - SQL substrate;
   - source/resource topology;
   - input format dialects;
   - output router/renderers;
   - mode families;
   - null/value semantics;
   - debug/diagnostic streams.
5. Generate P0-P8 probes above.
6. Only then implement.
7. Record implementation source origin through IMPLEMENTATION_ORIGIN_BOUNDARY_GATE.
8. Compare candidate against every locked row through LOCKED_REFERENCE_PARITY_GATE.
9. Run official eval only if the handoff type says gold, or label the run as an
   official experiment with known scope gaps.
```

## 23. v12 self-amendment record

```yaml
self_amendment_record:
  candidate_advancement_ref: failure_layer_transition_audit.md
  integration_class: structural_integration
  ontology_delta:
    - public observations can be schema-producing, not only leaf-confirming
    - discovered public schema items become ontology nodes with readiness state
    - embedded language substrate becomes mandatory for SQL/jq/formula/query programs
    - format labels become grammar matrices before gold promotion
    - input decoding/resource topology and output routing are separate macro gates
    - null/value semantics becomes cross-layer rather than renderer-only
    - candidate implementation origin becomes a method-evidence boundary
  epistemic_delta:
    - official eval failures remain post_eval_failure pressure
    - help/list/schema observations can force clean recursive re-entry
    - merged transcripts lose byte/channel authority
    - selected local probes become smoke evidence, not parity evidence
    - public upstream source use can be source-assisted engineering evidence,
      but not clean ADEU reconstruction evidence
  deontic_delta:
    - implementation handoff is blocked if public schema items are missing or unresolved
    - known scoped gaps block official-ready posture unless explicitly deferred
    - candidate must pass all locked rows in declared scope before gold official eval
    - candidate source origin must be clean, explicitly scoped, or non-comparable
  utility_delta:
    - prevents low scores caused by implementing a subset of a public grammar
    - converts broad official-red surfaces into pre-implementation schema obligations
    - routes repair by layer rather than by failing test names
  governance_preservation_posture: O/E/D/U legibility preserved
  ratification_status: experimental_support_revision
```

## 24. v13 main correction: witness-bundle transfer validity

v11 made resource ecology first-class. v12 made **public schema re-entry**
first-class. v13 makes **witness-bundle validity** first-class.

The new invariant is:

```text
No code witness can be evaluated as a program witness until the packaged
witness bundle is proven to run under the target substrate.
```

This is not a trdsql-specific rule. Any agentic implementation run can fail
before product behavior if the candidate does not inhabit the evaluator's
runtime, packaging, dependency, permission, shebang, or compile substrate.

v13 therefore splits the post-implementation lane:

```text
workspace source/executable smoke
  -> packaged artifact construction
  -> target-substrate ABI proof
  -> packaged-artifact parity
  -> dynamic observation normalization
  -> anti-replay / held-out transfer checks
  -> official-intended eval
```

## 25. New macro: TARGET_SUBSTRATE_ABI_GATE

```text
TARGET_SUBSTRATE_ABI_GATE
  = K1 Factor target runtime: interpreter/compiler, version, OS, stdlib,
    dependency availability, shebang resolution, PATH, cwd, permissions.
  + K2 Partition language/runtime feature lattice: accepted syntax, missing
    libraries, version-specific behavior, locale/path/line-ending behavior.
  + K3 Bind candidate artifact to substrate: source file, generated executable,
    compile.sh output, package root, shebang, import path.
  + K5 Sequence build -> syntax check -> smoke -> packaged parity -> eval.
  + K6 Expose pre-product failure surfaces: SyntaxError, ImportError,
    compile_failed, missing executable, bad shebang, permission denied.
  + M0 Warrant product evidence only if candidate product behavior is reached.
```

Trigger:

```text
Any candidate is interpreted, compiled, generated, packaged, shebang-driven,
uses external libraries, depends on stdlib version, or is evaluated in a
container/substrate different from the authoring environment.
```

Rule:

```text
A candidate cannot be local-parity-ready until it parses/builds and passes
minimal smoke commands under the declared target ABI or an evaluator-equivalent
compatibility matrix.
```

For Python candidates, the minimum check is:

```text
py_compile under target or conservative Python matrix
./compile.sh in package root
./executable -version or no-args smoke
./executable minimal success command
./executable minimal failure command
```

If the exact evaluator runtime is unknown, use a conservative matrix where
feasible and block syntax that only the newest local interpreter accepts unless
the evaluator is proven to support it.

## 26. New macro: PACKAGED_ARTIFACT_PARITY_GATE

```text
PACKAGED_ARTIFACT_PARITY_GATE
  = K1 Factor witness bundle into source, compile script, executable, tarball,
    permissions, generated resources, dependency pins, entrypoints.
  + K5 Sequence pack -> unpack -> compile -> smoke -> locked parity.
  + K6 Expose package-level failures before product rows.
  + M0 Warrant local parity only for the exact artifact official eval will run.
```

Rule:

```text
Local parity over workspace source is smoke evidence only. Official-intended
parity must execute the packaged artifact after the same compile/install path
the official harness uses.
```

Required record:

```yaml
packaged_artifact_parity_gate:
  package_ref: submission.tar.gz
  unpack_root_listing_hash: ...
  compile_script_ref: compile.sh
  compile_exit: ...
  executable_ref: executable
  executable_shebang: ...
  executable_permissions: ...
  target_runtime_ref: ...
  smoke_refs:
    - no_args_or_help
    - version_if_available
    - minimal_success
    - minimal_failure
  locked_parity_runner_ref: ...
  parity_artifact_identity:
    workspace_executable | packaged_artifact
  promotion_effect:
    blocks_official_if_not_packaged_artifact | scoped_smoke_only |
    official_preflight_ready
```

## 27. New macro: OFFICIAL_FAILURE_SURFACE_DOMINANCE_GATE

```text
OFFICIAL_FAILURE_SURFACE_DOMINANCE_GATE
  = K2 Partition official failures by first externally visible failure surface.
  + K3 Bind repeated pre-product errors to witness-bundle invalidity.
  + M0 Warrant product-theory repair only after pre-product dominance is ruled out.
```

Trigger:

```text
Official failures contain repeated compile/runtime/import/shebang/package errors.
```

Rule:

```text
If >= 20% of failed rows, >= 50 rows, or any compile_failed/missing-executable
condition share the same pre-product candidate failure surface, stop product
diagnosis and repair the witness bundle first.
```

Failure classes:

```text
witness_bundle_invalid
substrate_abi_failure
package_failure
resource_ecology_failure
dependency_failure
product_behavior_failure
```

## 28. New macro: DYNAMIC_OBSERVATION_CANONICALIZATION_GATE

```text
DYNAMIC_OBSERVATION_CANONICALIZATION_GATE
  = K1 Factor observed bytes into deterministic tokens and dynamic tokens.
  + K3 Bind dynamic tokens to source: timestamp, PID, tempdir, random id,
    environment path, locale, version, error prefix.
  + K4 Transform dynamic source into grammar or normalization rule.
  + K6 Expose oracle as exact, regex/semantic, normalized-hash, or conflict.
  + M0 Warrant exact-byte promotion only when dynamic tokens are controlled.
```

Trigger:

```text
Observed stdout/stderr/file bytes contain timestamps, temp paths, random IDs,
PIDs, generated names, environment-specific paths, or duplicate argv with
non-identical bytes.
```

Rule:

```text
Dynamic observations cannot be ordinary exact-byte leaves unless the dynamic
source is controlled. They must be normalized, modeled as grammar classes, or
conflict-isolated.
```

## 29. New macro: DUPLICATE_ARGV_NONDETERMINISM_GATE

```text
DUPLICATE_ARGV_NONDETERMINISM_GATE
  = Detect two or more locked observations with identical argv, stdin, and
    files_before but different stdout/stderr/exit/files_after.
  + Classify the difference as dynamic token, substrate difference, conflict,
    or observation contamination.
  + Block exact-byte parity claims until resolved.
```

Rule:

```text
Identical input cannot define two deterministic exact-byte leaves unless an
unrecorded hidden variable is added to the observation key.
```

Required action:

```text
add hidden variable to probe contract
or normalize dynamic token
or conflict-isolate the pair
```

## 30. New macro: CANDIDATE_LITERAL_OVERLAP_AUDIT

```text
CANDIDATE_LITERAL_OVERLAP_AUDIT
  = Scan candidate source and generated resources for high-entropy substrings
    from locked outputs, exact timestamps, exact fixture names, exact probe
    argv tuples, and exact file contents.
  + Classify overlaps as legitimate public constants, renderer grammar,
    suspicious replay, or prohibited oracle embedding.
```

Rule:

```text
A candidate with unexplained high-overlap literals may be scoped-smoke-ready,
but cannot be anti-replay-ready or broad-transfer-ready.
```

Common public strings such as flag names, format names, `Usage`, and declared
version text may be legitimate. The audit targets dynamic values, high-entropy
diagnostic fragments, and fixture-specific branch logic.

## 31. New macro: IMPLEMENTATION_STRATEGY_FITNESS_GATE

```text
IMPLEMENTATION_STRATEGY_FITNESS_GATE
  = K3 Bind each high-risk ontology parent to an implementation strategy,
    not merely to locked outputs.
  + K4 Require a generative owner for the program's core substrate.
  + K7 Require held-out siblings that prove the strategy rather than
    argv/fixture replay.
```

Rule:

```text
A scoped implementation may be limited in branch coverage, but it must still be
generative for the parent families it includes.
```

For embedded-language tools, minimum rows:

```text
EmbeddedLanguageSubstrate:
  strategy = real evaluator/engine or explicitly bounded parser/interpreter

SourceBinder:
  strategy = resource identity + route binding + table/object naming

InputDialects:
  strategy = decoder family with stated column/value/null/malformed rules

OutputRouter:
  strategy = renderer family plus stdout/file/compression route strategy

Diagnostics:
  strategy = parse/resource/language/debug dynamic grammar, not exact replay
```

## 32. New macro: REPRESENTATIVE_LEAF_TRANSFER_LIMIT

```text
REPRESENTATIVE_LEAF_TRANSFER_LIMIT
  = Mark a leaf observed by one representative fixture as representative-only,
    not family-ready, unless sibling/metamorphic coverage proves the generator.
```

Recommended readiness statuses:

```text
representative_scoped_ready
representative_transfer_limited
family_gold_ready
family_deferred_with_expected_risk
```

Rule:

```text
`gold-ready representative` is not `family gold-ready`. The handoff must state
which one is intended.
```

## 33. Revised local parity semantics

v13 splits parity into three distinct claims:

```text
workspace_smoke_parity:
  runs source/executable in authoring workspace; never enough for official.

packaged_substrate_parity:
  runs packaged artifact after compile in target/eval-like substrate; required
  before official-intended eval.

anti_replay_transfer_parity:
  runs held-out/metamorphic siblings not used to author implementation; required
  for broad transfer claims.
```

A run may report `90/91 workspace parity`, but it must not call that an
official preflight unless `packaged_substrate_parity` also passes.

## 34. Updated descent / implementation algorithm for v13

Replace the v12 implementation lane with:

```text
1. Complete v12 public schema re-entry and observation locking.
2. Classify every locked observation as exact, dynamic-normalized, semantic,
   representative-only, or conflict-isolated.
3. Run DUPLICATE_ARGV_NONDETERMINISM_GATE.
4. Declare implementation strategy rows for core ontology parents.
5. Generate held-out/metamorphic sibling probes for included parent families.
6. Implement under declared handoff type.
7. Record IMPLEMENTATION_ORIGIN_BOUNDARY_GATE.
8. Build packaged witness bundle.
9. Run TARGET_SUBSTRATE_ABI_GATE.
10. Run PACKAGED_ARTIFACT_PARITY_GATE.
11. Run CANDIDATE_LITERAL_OVERLAP_AUDIT.
12. Run held-out/metamorphic anti-replay transfer parity.
13. Emit official_preflight.
14. Run official eval only if preflight passes or the run is explicitly labeled
    as a scoped experiment with expected transfer risk.
15. After official eval, run OFFICIAL_FAILURE_SURFACE_DOMINANCE_GATE before any
    product-theory diagnosis.
```

## 35. v13 bookkeeper additions

The adversarial bookkeeper must reject:

```text
target_substrate_abi_unproven
packaged_artifact_not_parity_checked
workspace_parity_promoted_to_official_parity
pre_product_failure_surface_dominates
syntax_or_compile_failure_misclassified_as_product_gap
dynamic_observation_locked_as_exact_without_source_control
duplicate_argv_conflict_unresolved
candidate_literal_overlap_unexplained
representative_leaf_promoted_to_family_gold
held_out_metamorphic_gate_reserved_but_not_run
implementation_strategy_missing_for_core_substrate
scoped_handoff_without_expected_transfer_band
```

For every official failure cluster, the bookkeeper first asks:

```text
Did the candidate reach product behavior?
```

If no, classify as witness-bundle, substrate, package, dependency, or resource
ecology failure before product repair.

## 36. v13 generator prompt patch

Add this block after implementation handoff and before local parity:

```text
Do not treat workspace parity as official preflight.

Before local parity can support official-intended eval:
  - pack the exact submission artifact;
  - unpack it in a clean directory;
  - run compile.sh through the target or closest evaluator-like substrate;
  - syntax-check interpreted candidates under the target ABI or conservative
    runtime matrix;
  - run minimal success/failure smoke commands from the packaged executable;
  - run locked parity against the packaged artifact, not workspace source.

Classify dynamic observations before exact-byte locking. If identical argv,
stdin, and files produce different bytes, locate the hidden variable,
normalize the dynamic token, or conflict-isolate the observation pair.

Audit candidate source for suspicious high-entropy overlap with locked outputs.
Public constants are allowed; timestamp replay, fixture-specific dispatch, and
copied diagnostic fragments require justification or downgrade.

A scoped implementation may be scoped in branch coverage, but it still needs a
generative strategy for every included core parent family. Exact probe replay is
not a program witness.
```

## 37. v13 official preflight record

Before official-intended eval, emit:

```yaml
official_preflight:
  target_substrate_abi_gate:
    status: passed | failed | scoped_risk
    runtime_refs: []
    syntax_check_refs: []
    smoke_refs: []
  packaged_artifact_parity_gate:
    status: passed | failed | workspace_smoke_only
    package_ref: submission.tar.gz
    compile_ref: compile.sh
    parity_rows_total: int
    parity_rows_passed: int
    parity_rows_failed: int
  dynamic_observation_gate:
    status: passed | normalized | conflict_isolated | failed
    dynamic_rows: []
  literal_overlap_audit:
    status: passed | scoped_risk | failed
    suspicious_overlap_refs: []
  held_out_metamorphic_gate:
    status: passed | failed | not_run_scoped_risk
    probe_refs: []
  implementation_strategy_fitness_gate:
    status: passed | scoped_risk | failed
    parent_strategy_rows: []
  handoff_type:
    scoped_implementation_attempt | official_experiment_with_known_scope_gaps |
    gold_implementation_attempt
  expected_transfer_band: ...
  known_uncovered_families: []
```

If target-substrate or packaged-artifact gates fail, official eval is blocked.

## 38. v13 trdsql test recipe

For the next clean trdsql run, start with the v12 schema re-entry scaffold, then
add v13-specific probes before implementation:

```text
T0 target ABI scout:
  python/runtime versions, shebang resolution, PATH, cwd, py_compile matrix.

T1 packaged artifact smoke:
  unpack submission, run compile.sh, execute no-args/version/SELECT 1/error.

T2 dynamic diagnostics:
  run identical debug and SQL-error probes twice; normalize timestamp tokens.

T3 literal-overlap audit:
  scan candidate for timestamp literals, fixture-specific dispatch, exact
  high-entropy stderr/stdout fragments.

T4 strategy fitness:
  require SQL substrate, source binder, input dialects, output router/renderers,
  diagnostics, and witness-bundle owners.

T5 held-out siblings:
  expression perturbation, CSV fixture perturbation, stdin/file route sibling,
  JSON/YAML nested sibling, renderer special-character sibling.
```

## 39. v13 self-amendment record

```yaml
self_amendment_record:
  candidate_advancement_ref: trdsql_v13_layer_transition_audit_and_patch.md
  integration_class: structural_integration
  ontology_delta:
    - witness-bundle validity becomes a required layer between implementation and parity
    - target substrate ABI becomes a first-class substrate node
    - dynamic byte observations become grammar/normalization leaves
    - packaged artifact identity becomes the parity object, not workspace source
    - representative leaves are separated from family gold leaves
  epistemic_delta:
    - local parity is invalid as transfer evidence unless target-substrate parity passes
    - official failures dominated by pre-product candidate errors cannot become product-theory evidence
    - high local parity with literal overlap is replay-risk evidence, not anti-replay evidence
  deontic_delta:
    - official eval is blocked by target_substrate_abi_unproven or packaged_artifact_not_parity_checked
    - implementation handoff must include a generative architecture floor for core program substrate
    - dynamic observations must be normalized or conflict-isolated before exact-byte parity claims
  utility_delta:
    - prevents score-3 style collapses where the candidate never inhabits the evaluator substrate
    - preserves v12 public schema gains while restoring v11-like generative implementation pressure
  governance_preservation_posture: O/E/D/U legibility preserved; source contamination remains forbidden
  ratification_status: experimental_support_revision
```

## 40. v14 main correction: methodological equivalence

v13 made target-substrate and packaged-artifact validity explicit. v14
generalizes that patch into a typed equivalence invariant:

```text
Before using behavior observed in object A as evidence about object B, the run
must provide a typed equivalence judgment between A and B at every lower layer
on which the inference depends.
```

Canonical judgment:

```text
W ⊢ A ≃[L, S, R] B
```

Meaning:

```text
Under warrant W, object A and object B are equivalent at layer L, within scope
S, under observable relation R.
```

For constructive witnesses:

```text
W ; Π ; Σ ⊢ Cᴡ : Ω*
```

Any transfer of that judgment must also prove:

```text
W ⊢ (Cᴡ₁, Π₁, Σ₁) ≃[transfer, S, R] (Cᴡ₂, Π₂, Σ₂)
```

If that transfer equivalence is missing, a local green result is only local
evidence.

## 41. Objects that must not be silently identified

The meta-program must not treat these as equivalent by default:

```text
P_ref        reference / target program whose behavior is being reconstructed
P_cand       candidate program as an abstract source/witness design
Cᴡ_src       source-level witness bundle produced by the worker
Cᴡ_local     locally materialized candidate witness bundle
Cᴡ_eval      packaged/submitted/evaluator-side witness bundle
Σ_ref        reference substrate
Σ_local      local probe substrate
Σ_eval       official/evaluator substrate
Π_ref        reference-observation probes/checkers
Π_local      local candidate probes/checkers
Π_eval       official/evaluator probes/checkers
O_ref        reference observations
O_local      local candidate observations
O_eval       official observations
Ω?           candidate inferred ontology
Ω*           best warranted completion of the visible program statement
Ωg           gold/reference ontology, if later known
```

Rule:

```text
None of these pairs are equivalent by default. They can be related only by
explicit typed equivalence claims.
```

## 42. Equivalence ladder

### E0 Statement equivalence

```text
Ω? ≃ Ω* ≃ Ωg?
```

Question:

```text
Did we reconstruct the same theorem statement the reference program inhabits?
```

### E1 Public-interface equivalence

```text
P_ref interface ≃ P_cand interface
```

Question:

```text
Does the candidate expose the same CLI/API/control grammar, including help,
unknown flags, modes, aliases, env/config surfaces, entrypoints, and streams?
```

### E2 Observation-oracle equivalence

```text
Π_ref / Π_local / Π_eval observe the same surface relation
```

Question:

```text
Are stdout, stderr, exit, files, timing, process lifetime, resources, and
dynamic normalization captured with the same semantics?
```

A merged transcript is not equivalent to a split stdout/stderr/exit/file oracle.

### E3 Witness-bundle equivalence

```text
Cᴡ_src ≃ Cᴡ_local ≃ Cᴡ_eval
```

Question:

```text
Is the exact witness bundle being tested locally the same witness bundle
submitted to the evaluator?
```

Includes source files, configs, entrypoints, build scripts, generated resources,
dependency pins, runtime assumptions, filesystem layout, submission filters,
line endings, shebangs, and permissions.

### E4 Target-substrate / ABI equivalence

```text
Σ_local ≃ Σ_eval
```

Question:

```text
Does the local runtime accept, import, execute, encode, and buffer the witness
the same way as the evaluator runtime?
```

Includes language version, stdlib/dependency versions, OS/architecture, shell
and argv parsing, locale/timezone, filesystem semantics, compiler/interpreter
flags, and line endings.

### E5 Execution-topology equivalence

```text
run_local(Cᴡ, Σ_local) ≃ run_eval(Cᴡ, Σ_eval)
```

Question:

```text
Are cwd, argv, env, stdin/stdout/stderr, temp dirs, resource paths, scheduler,
timeouts, signals, and cleanup topology equivalent enough for the branch?
```

### E6 Resource/observation-ecology equivalence

```text
resource graph local ≃ resource graph eval
```

Question:

```text
Are ports, sockets, PTYs, subprocesses, temp files, DB files, locks, caches,
coverage artifacts, reruns, and parallel schedules clean and comparable?
```

### E7 Behavioral terminal-leaf equivalence

```text
O_ref(λ) ≃ O_cand(λ)
```

Question:

```text
For each terminal leaf λ, do reference and candidate observations match under
the chosen observable relation?
```

Only E7 is the ordinary “program behavior matches” claim. It is invalid if any
required lower equivalence is missing or failed.

### E8 Warrant equivalence

```text
W_ref / W_local / W_eval authority levels are compatible
```

Question:

```text
Are we using evidence with the same authority class, or laundering scoped,
diagnostic, source-postmortem, or post-eval pressure into gold truth?
```

## 43. Dominance rule

```text
A failure is evidence about the earliest unproven or broken equivalence layer
that can explain it.
```

If a candidate cannot compile under `Σ_eval`, official failures are not yet
strong evidence about SQL semantics, output formats, input grammars, renderer
byte exactness, or model capability. They are evidence about E3/E4.

If a local observation merged stdout and stderr, byte/channel mismatches are
first evidence about E2 observation-oracle non-equivalence.

If an HTTP row fails with `Address already in use`, the row is first evidence
about E6 resource ecology, not graph rendering or protocol semantics.

## 44. Commuting-diagram requirement

For any candidate handoff, the following diagram must commute up to explicitly
declared normalization:

```text
             package_local                    run under Πlocal,Σlocal
Cᴡ_src ----------------------> Cᴡ_local ----------------------------> O_local
  |                               |                                      |
  | package_eval                  | E3 witness-bundle equivalence        | E2/E5 observation equivalence
  v                               v                                      v
Cᴡ_eval ----------------------> Cᴡ_eval_ready ----------------------> O_eval
             package_eval                    run under Πeval,Σeval

E4/E5 substrate and execution-topology equivalence is the relation between
the local run edge and the evaluator-intended run edge, not a replacement for
E3 witness-bundle equivalence.
```

If packaging, runtime, entrypoint, dependency, resource, or observer relation
changes, local evidence does not transfer to official evidence without a new
proof.

## 45. New macro: METHODOLOGICAL_EQUIVALENCE_GATE

Trigger:

```text
Any result, readiness state, probe result, scout observation, implementation
claim, or official eval pressure is transferred across two non-identical
objects.
```

Typical transfers:

```text
reference program -> candidate program
README ontology -> public executable behavior
public scout -> implementation obligation
local probe result -> official-readiness claim
source witness -> packaged witness
local runtime -> evaluator runtime
fixture oracle -> generative rule
fork exemplar -> direct-shell support
provider intent -> local authority
diagnostic evidence -> readiness promotion
post-eval pressure -> clean theory
```

Required row shape:

```yaml
equivalence_claim_id: EQ-...
source_object: P_ref | Ω? | Cᴡ_src | Cᴡ_local | Π_local | Σ_local | O_local | other
target_object: P_cand | Ω* | Cᴡ_eval | Π_eval | Σ_eval | O_eval | other
equiv_layer:
  E0_statement | E1_interface | E2_observation_oracle |
  E3_witness_bundle | E4_target_substrate | E5_execution_topology |
  E6_resource_ecology | E7_behavior_leaf | E8_warrant
scope:
  branch_refs: []
  command_refs: []
  terminal_leaf_refs: []
  artifact_refs: []
observable_relation:
  stdout: exact | normalized | ignored | not_applicable
  stderr: exact | normalized | ignored | not_applicable
  exit: exact | ignored | not_applicable
  files: exact | normalized | ignored | not_applicable
  timing: bounded | ignored | not_applicable
  resources: clean_equivalent | isolated | ignored | not_applicable
required_invariants: []
proof_refs: []
negative_control_refs: []
status:
  unclaimed | claimed_unproven | probe_ready | scoped_equivalent |
  blocked_counterexample | conflict_isolated | gold_equivalent
promotion_allowed: true | false
if_failed_dominates_layers: []
repair_owner:
  ontology | probe_contract | witness_packaging | substrate |
  execution_topology | resource_ecology | implementation | warrant
```

Rule:

```text
A handoff may promote behavior only across equivalence rows with status
scoped_equivalent or gold_equivalent for every lower layer on which that
behavior depends.
```

## 46. Derived equivalence gates

### LOCAL_OFFICIAL_TRANSFER_GATE

```text
= E3 witness-bundle equivalence
+ E4 target-substrate equivalence
+ E5 execution-topology equivalence
+ E2 observation-oracle equivalence
+ E8 warrant equivalence
```

Required before treating local green results as official-readiness evidence.

Minimum probes:

```text
pack exact submitted artifact;
unpack in a clean temp root;
compute manifest/hash of files, permissions, line endings, entrypoint metadata;
run target interpreter/compiler syntax checks;
run import and entrypoint smoke tests;
run no-args/help/one representative command under evaluator-like argv/env/cwd;
record stdout/stderr/exit separately;
record runtime fingerprint;
record dependency and package-resource availability;
record dynamic fields requiring canonicalization;
record resource cleanliness before and after.
```

### TWO_PROGRAM_BEHAVIORAL_EQUIVALENCE_GATE

```text
= E0/E1 statement and interface equivalence
+ E7 terminal-leaf behavioral equivalence
+ E8 warrant equivalence
```

Required before saying the candidate implements the reference program rather
than only a scoped subprogram.

### PROBE_ORACLE_EQUIVALENCE_GATE

```text
= E2 observation-oracle equivalence
+ E5 execution-topology equivalence
+ E8 warrant equivalence
```

Hard rule:

```text
A merged stdout/stderr transcript cannot prove a byte-sensitive split-channel
leaf.
```

### PACKAGED_WITNESS_EQUIVALENCE_GATE

```text
= E3 witness-bundle equivalence
+ E4 target ABI / runtime syntax validity
```

Hard rule:

```text
No code witness can be evaluated as a program witness until the witness bundle
is proven to run under the target substrate.
```

## 47. v14 kernel refinement

v14 adds a cross-cutting equivalence interpretation to the kernel:

```text
Factor:
  factor program copies, artifact states, substrates, observers, and harnesses.

Partition:
  split equivalence into scoped relations, not global sameness.

Bind:
  bind each equivalence claim to the consumers that rely on it.

Transform:
  model packaging, transpilation, compilation, serialization, normalization,
  and dynamic canonicalization as transforms that can change witness identity.

Sequence:
  include build -> package -> unpack -> syntax-check -> import -> run -> observe
  before behavior evidence can be used.

Expose:
  include pre-product failures such as syntax errors, import errors, wrong
  entrypoint, missing resources, environment mismatch, oracle/channel mismatch.

Compose:
  check non-commutation between local/official substrate, packaging, probes,
  resource ecology, and semantic leaves.

Warrant:
  attach equivalence authority separately from product behavior authority.
```

## 48. v14 readiness additions

Add `equivalence_status` to every handoff, probe family, and implementation
claim:

```text
equivalence_unstated
equivalence_claimed_unproven
equivalence_probe_ready
equivalence_scoped_ready
equivalence_blocked
equivalence_conflict_isolated
equivalence_gold_ready
```

Handoff rule:

```text
implementation_ready is impossible while required equivalence_status is
equivalence_unstated, equivalence_claimed_unproven, or equivalence_blocked.
```

## 49. Minimal required equivalence sets by handoff type

The methodological equivalence invariant is general, but each handoff type
needs an executable minimum set. v14 therefore adds a handoff table so workers
cannot treat the invariant as advisory philosophy.

| Handoff / claim type | Required equivalence layers | Meaning |
| --- | --- | --- |
| `local_candidate_gate` | `E2 + E5 + E7` | Local probe evidence can speak about candidate behavior only if the local oracle, execution topology, and terminal behavior relation are aligned for the branch. |
| `workspace_smoke_parity` | `E2 + E5 + E7` scoped to workspace artifact | Workspace source/executable passed local smoke only; no official-transfer claim. |
| `packaged_substrate_parity` | `E2 + E3 + E4 + E5 + E7 + E8` | The exact packaged witness was built and observed under target/eval-like substrate and warrant. |
| `official_preflight` | `E2 + E3 + E4 + E5 + E8` plus scoped `E7` smoke | The run may enter official eval only if witness, substrate, topology, oracle, and warrant transfer are proved. |
| `scoped_implementation_attempt` | required lower equivalences for declared scope, with explicit `representative_transfer_limited` leaves | The run may execute, but cannot claim broad program equivalence. |
| `gold_implementation_attempt` | `E0 + E1 + E2 + E3 + E4 + E5 + E6 + E7 + E8` for all gold-required branches or explicit deferrals | The candidate can be treated as a full constructive witness for the declared program statement. |
| `method_comparison` | `E0 + E1 + E2 + E3 + E4 + E5 + E8` | Comparing methods/models/runs requires comparable theorem statement, interface, observation, artifact, substrate, topology, and warrant. |
| `product_behavior_claim` | all lower required equivalences plus relevant `E7` terminal leaves | A behavior claim is invalid if any lower equivalence layer needed by that behavior is unproven or broken. |

Rule:

```text
The required set is monotone with claim strength. A weaker local claim may use a
smaller equivalence set, but it cannot be promoted later without proving the
additional layers required by the stronger claim.
```

## 50. v14 bookkeeper additions

The adversarial bookkeeper must reject:

```text
equivalence_unstated_for_transfer
local_green_promoted_without_local_official_transfer_gate
source_witness_promoted_without_packaged_witness_parity
runtime_fingerprint_missing_for_target_substrate
syntax_import_entrypoint_smoke_missing
merged_oracle_used_for_split_surface
resource_ecology_unproven_but_product_truth_promoted
post_eval_surface_dominated_by_pre_product_failure
fork_or_provider_evidence_promoted_without_direct_capability_proof
scoped_equivalence_used_as_global_equivalence
equivalence_counterexample_ignored
handoff_type_missing_required_equivalence_set
method_comparison_without_common_equivalence_basis
```

For every transfer claim, the bookkeeper must ask:

```text
Which two objects are being identified?
At what layer?
Under what observable relation?
For which branch/scope?
Which consumers rely on this equivalence?
What witness proves it?
What counterexample would break it?
If it fails, which higher layers are dominated and therefore not interpretable?
```

## 51. v14 generator prompt patch

Add this block before implementation handoff:

```text
Before using any observation or local result as evidence about another program,
artifact, substrate, observer, or official row, emit a
METHODOLOGICAL_EQUIVALENCE_GATE row.

Do not assume:
  - reference program behavior transfers to candidate behavior;
  - local candidate artifact equals official candidate artifact;
  - local runtime equals official runtime;
  - local probes observe the same surfaces as official probes;
  - stdout/stderr merged output can prove split-channel behavior;
  - fixture byte equality proves a generative rule;
  - fork exemplars imply direct-shell support;
  - provider/tool intent implies local authority;
  - diagnostic evidence implies readiness.

For each transfer, state:
  1. source object;
  2. target object;
  3. equivalence layer;
  4. scope;
  5. observable relation;
  6. proof probes/manifests/fingerprints;
  7. promotion status;
  8. dominated higher layers if the equivalence fails.

If a failure surface occurs before the product behavior layer, classify it as
an equivalence failure at the earliest explaining layer and block product-theory
repair until the equivalence is proved or repaired.

Before declaring a handoff type, consult the minimal required equivalence set
table. Do not label a handoff as official_preflight, gold, or method-comparable
unless every required equivalence layer for that label is proved, explicitly
scoped, or explicitly deferred with risk.
```

## 52. v14 self-amendment record

```yaml
self_amendment_record:
  candidate_advancement_ref:
    - trdsql_v13_layer_transition_audit_and_patch.md
    - program_reconstruction_methodological_equivalence_meta_invariant_v14.md
  integration_class: structural_integration
  ontology_delta:
    - target-substrate ABI becomes an instance of a broader typed equivalence calculus
    - program copies, artifact states, substrates, observers, and harnesses become first-class Factor nodes
    - local-to-official transfer requires explicit equivalence ledgers
    - behavior evidence is dominated by lower-layer equivalence failures
    - handoff labels receive minimal required equivalence sets
  epistemic_delta:
    - evidence transfer is no longer allowed by default
    - official failures are interpreted at the earliest broken equivalence layer
    - local green is local unless local-official equivalence is proven
  deontic_delta:
    - implementation handoff is blocked by missing required equivalence gates
    - product-theory repair is blocked while lower transfer equivalence is broken
    - method/model/run comparisons require common equivalence basis
  utility_delta:
    - avoids semantic repair cycles when the measured object was not the intended witness
    - unifies target ABI, resource ecology, observation lock, fork/direct support,
      provider/local authority, and scaffold/gold promotion under one invariant
  governance_preservation_posture: O/E/D/U legibility preserved; capability transfer requires warrant
  ratification_status: experimental_support_revision
```

## 53. Bottom line

```text
Never compare two programs, two witnesses, two substrates, or two observations
without first saying what kind of sameness is being claimed and how that
sameness was proved.
```

The v14 path is:

```text
public schema re-entry
  -> grammar terminalization
  -> split-surface observation lock
  -> methodological equivalence ledger
  -> dynamic-byte canonicalization
  -> implementation strategy fitness
  -> source-origin gate
  -> target-substrate / packaged-witness equivalence gates
  -> anti-replay / held-out transfer parity
  -> official eval
  -> earliest-broken-equivalence classification
```
