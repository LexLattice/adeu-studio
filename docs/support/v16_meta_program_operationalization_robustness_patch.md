# V16 Meta-Program Patch: Operationalization Robustness

## Purpose

This patch addresses the gap between post-hoc meta-program audits that correctly identify parent causes and worker runs that apply the revised rules only partially. The current failure mode is not primarily that the audits are wrong. It is that the audit-to-worker transition is lossy.

The worker receives parent discriminators such as:

```text
SQL_RESOURCE_BINDER
RESOURCE_ROUTE_TOPOLOGY
INPUT_DIALECT_GRAMMAR_MATRIX
OUTPUT_ROUTER_RENDERER_MATRIX
CONFIG_DB_TOPOLOGY
MODE_DIAGNOSTIC_CHANNEL_CONTRACT
```

but implements representative subbranches rather than compiling each parent into a closed branch matrix, reference probe set, candidate probe set, implementation owner map, and readiness ledger.

The v16 invariant is:

```text
A meta-program rule is not operationally applied until it has been lowered into
machine-checkable obligations whose coverage can be audited before and after
implementation.
```

## Diagnosis of the 52 -> 60 -> 68 Pattern

The progression is real but structurally incomplete:

```text
52 -> 60:
  methodological/witness equivalence repair exposed real scoped product behavior.

60 -> 68:
  representative repairs to v15 parent gates fixed many high-value examples.

68 plateau risk:
  parent gates remain open because sibling branches were not expanded into full
  matrices before patching.
```

The v15 worker patched many parent rules, but its own report still classifies the same parents as partially terminalized or still scoped. That is the signature of representative transfer, not macro closure.

## New Core Distinction

Add a distinction between:

```text
parent_discriminator_identified
parent_discriminator_operationalized
parent_discriminator_representatively_patched
parent_discriminator_matrix_locked
parent_discriminator_gold_ready
```

A worker may not write:

```text
Parent Rules Patched
```

unless the parent has reached at least `parent_discriminator_matrix_locked`.

For most current runs, the correct statement is:

```text
Representative subbranches patched under parent P.
Parent P remains open until its sibling matrix is locked.
```

## V16 Macro: OPERATIONALIZATION_EQUIVALENCE_GATE

### Judgment

```text
W ⊢ AuditTheory ≃[operationalization, S, R] WorkerTask
```

Meaning:

```text
Under warrant W, the worker task is equivalent to the audit theory within scope S
under relation R: every actionable audit node has been converted into explicit
obligations, probes, owners, stop conditions, and deferrals.
```

### Required outputs

```yaml
operationalization_equivalence_gate:
  audit_node_ref: string
  worker_task_ref: string
  scope: scoped | gold | experiment
  relation:
    ontology_nodes_preserved: true | false
    macro_subbranches_expanded: true | false
    probes_generated_before_patch: true | false
    implementation_owners_bound: true | false
    deferrals_explicit: true | false
    closure_metric_defined: true | false
  status:
    equivalent | partial | not_equivalent | blocked
  blocker_refs: []
```

### Rule

```text
If AuditTheory is only partially operationalized, the run must be labeled a
scoped implementation experiment. It must not be interpreted as a test of the
full updated meta-program.
```

## V16 Macro: MACRO_EXPANSION_COMPLETENESS_GATE

### Trigger

Any audit bucket or meta-program patch names a macro parent such as:

```text
SQL_RESOURCE_BINDER
RESOURCE_ROUTE_TOPOLOGY
INPUT_DIALECT_GRAMMAR_MATRIX
OUTPUT_ROUTER_RENDERER_MATRIX
CONFIG_DB_TOPOLOGY
MODE_DIAGNOSTIC_CHANNEL_CONTRACT
```

### Required output

```yaml
macro_expansion_completeness_gate:
  macro_ref: string
  parent_operator_refs: [Factor, Partition, Bind, Transform, Sequence, Expose, Compose, Warrant]
  required_axes: []
  generated_leaf_count: int
  probed_leaf_count: int
  candidate_green_leaf_count: int
  deferred_leaf_count: int
  unexpanded_axis_refs: []
  closure_status:
    label_only | representative_examples | branch_matrix_ready |
    reference_locked | candidate_locked | scoped_ready | gold_ready
```

### Rule

```text
A macro cannot be called patched while closure_status is label_only or
representative_examples.
```

## V16 Macro: PROBE_MATRIX_COMPILER

The model should not jump from a diagnosis to source edits. It must first compile each macro into a probe matrix.

Each matrix row must include:

```yaml
probe_matrix_row:
  row_id: string
  macro_ref: string
  ontology_path: string
  sibling_axis: string
  positive_case: string
  negative_or_boundary_case: string
  interaction_case: string | null
  reference_command: string
  candidate_command: string
  expected_surfaces:
    stdout: bytes | grammar | ignored
    stderr: bytes | grammar | ignored
    exit: int | set | ignored
    files: []
  dynamic_normalization: []
  implementation_owner: string
  closure_role:
    representative | boundary | interaction | regression | held_out
  status:
    planned | reference_locked | candidate_green | candidate_red |
    deferred_with_risk | conflict_isolated
```

### Rule

```text
No implementation patch is accepted unless it names which probe matrix rows it
is intended to turn green and which previously green rows it is retaining.
```

## V16 Macro: STALE_LOCAL_LEDGER_INVALIDATION

### Trigger

A meta-program patch adds new macro axes or official pressure reveals a parent branch absent from the current local probe ledger.

### Rule

```text
The old local parity suite remains a regression suite, not a readiness suite.
A new macro-specific probe matrix must be generated before official readiness
claims resume.
```

This directly addresses the pattern where a candidate can pass an old locked parity set while still failing hundreds of rows in newly discovered macro families.

## V16 Macro: REPRESENTATIVE_PATCH_NONCLOSURE_RULE

### Rule

```text
A patch that fixes one example under a parent macro proves only that example and
its explicitly probed siblings. It does not close the parent macro.
```

Required language in worker reports:

```text
patched_example_branch
retained_regression_branch
unpatched_sibling_axes
expected_remaining_failure_pressure
next_matrix_rows_required
```

Forbidden language unless matrix closure is proven:

```text
fixed SQL_RESOURCE_BINDER
fixed OUTPUT_ROUTER_RENDERER_MATRIX
fixed INPUT_DIALECT_GRAMMAR_MATRIX
```

Preferred language:

```text
transferred representative JOIN/resource-token branches under SQL_RESOURCE_BINDER;
macro remains open for aliases, DML, CTEs, persistent DB mutation, and typed aggregates.
```

## V16 Macro: IMPLEMENTATION_BATCH_CONTRACT

Large macros must be implemented in bounded release batches. Each batch must have a closed local oracle.

### Batch shape

```yaml
implementation_batch_contract:
  batch_id: string
  target_macro_refs: []
  max_macro_count: 2
  included_probe_rows: []
  excluded_probe_rows: []
  expected_score_pressure: string
  patch_owner_modules: []
  regression_rows: []
  held_out_rows: []
  submit_allowed: true | false
```

### Rule

```text
A worker may not attempt to patch SQL binder, all input dialects, all output
renderers, config topology, diagnostics, and compression in one unbounded pass.
```

The intended sequence for the current trdsql-like state is:

```text
Batch A: SQL_RESOURCE_BINDER + RESOURCE_ROUTE_TOPOLOGY
Batch B: INPUT_DIALECT_GRAMMAR_MATRIX
Batch C: OUTPUT_ROUTER_RENDERER_MATRIX
Batch D: CONFIG_DB_TOPOLOGY + MODE_DIAGNOSTIC_CHANNEL_CONTRACT
Batch E: projection exactness / final byte sharpening
```

Each batch must define its own reference/candidate probe matrix and held-out sibling rows.

## V16 Macro: DELTA_ATTRIBUTION_LEDGER

After every official or official-like run, score movement must be attributed back to matrix rows.

```yaml
delta_attribution_row:
  run_before: string
  run_after: string
  score_before: int
  score_after: int
  changed_failed_rows: int
  macro_ref: string
  matrix_rows_green: []
  rows_moved_to_other_failure: []
  regressions: []
  interpretation:
    representative_transfer_success |
    macro_closure_success |
    resource_or_substrate_masking |
    implementation_transfer_error |
    theory_gap_persists
```

### Rule

```text
A score increase is not automatically evidence that the macro was closed.
It is evidence only for the matrix rows that were actually locked.
```

## V16 Macro: WORKER_EXECUTION_FIT_GATE

The meta-program must distinguish what a worker can reliably execute in one pass.

```yaml
worker_execution_fit_gate:
  worker_model: string
  context_size: int | unknown
  implementation_surface_size: small | medium | large | huge
  macro_count: int
  unterminalized_leaf_estimate: int
  codebase_complexity: small | medium | large
  fit_status:
    single_pass_fit | batch_required | scaffold_only | needs_tooled_runner |
    needs_source_postmortem | blocked
```

### Rule

```text
If the work requires more matrix rows than the worker can reliably hold and
execute, the correct output is a batch scaffold, not a broad patch attempt.
```

This is not a weakness of the theory. It is an operational constraint: broad parent causes must be lowered into small proof obligations.

## Current Task-Specific Repair Scaffold

For the current trdsql-like state, the next run should not say:

```text
Apply v15 rules.
```

It should say:

```text
Build and execute Batch A only.
```

### Batch A: SQL binder + resource route topology

Minimum branch axes:

```text
SQL form:
  expression-only SELECT
  FROM one file
  JOIN two files
  comma join
  aliases
  quoted identifiers
  repeated resource in subquery
  wildcard resource
  UPDATE/DELETE plus SELECT
  multiple semicolon statements

Resource route:
  plain path
  tilde path
  glob path
  stdin route
  compressed path .gz/.bz2/.xz/.zst/.lz4 where available
  output path with extension guess
  database file route

Binding outcome:
  table import
  table name rewrite
  duplicate import avoidance
  missing file diagnostic
  malformed file diagnostic
  SQL error diagnostic
  persistent side effect if applicable
```

### Batch B: input dialect grammar

Minimum branch axes:

```text
CSV/TSV delimiter/header/null
JSON object array / scalar array / nested object / JSONL
YAML table / sparse / scalar / null / nested array-map
TBLN parse/write grammar
LTSV grammar
fixed-width grammar
text input row numbering
jq selector path / invalid jq / array extraction
value-domain conversion into SQLite types
```

### Batch C: output router / renderer grammar

Minimum branch axes:

```text
raw multi-column / delimiter / final newline
CSV quoting / header / no-header / CRLF
JSON object array / null / numeric/string typing
JSONL line grammar
YAML final grammar
TBLN final grammar
LTSV final grammar
Markdown/ascii/vertical spacing
output file format guessing
output compression guessing
stdout vs file route split
```

## Bookkeeper Additions

The bookkeeper must reject a worker patch report if:

```text
1. It says a parent macro is fixed without a macro expansion matrix.
2. It adds local probes after patching rather than before patching.
3. It uses old locked parity as readiness after the meta-program added new axes.
4. It reports score delta without row-to-macro attribution.
5. It lacks regression-retention rows for previously green siblings.
6. It fails to list unpatched sibling axes under each patched parent.
7. It lacks held-out or boundary rows for each high-risk generating rule.
8. It attempts more macros than the worker_execution_fit_gate allows.
```

## Generator Prompt Delta

Add this instruction to the worker prompt:

```text
Before editing source, compile each targeted parent macro into a probe matrix.
Do not patch from the narrative diagnosis. Patch only from matrix rows.
If you cannot generate and run a matrix for the macro, mark it
representative_examples only and do not claim macro closure.
```

Add this status vocabulary:

```text
macro_label_discovered
macro_matrix_planned
macro_reference_locked
macro_candidate_green_scoped
macro_candidate_green_gold
macro_representative_only
macro_open_unpatched_siblings
```

## Bottom Line

The post-hoc audits are successfully finding higher-level causes. The current robustness gap is that the updated meta-program is being handed to workers as prose rather than as an executable obligation compiler.

V16 therefore adds an operationalization layer:

```text
audit parent cause
  -> macro expansion matrix
  -> reference/candidate probe matrix
  -> bounded implementation batch
  -> regression + held-out gate
  -> delta attribution ledger
  -> only then readiness promotion
```

This should make future 52 -> 60 -> 68 style improvements less partial by preventing the worker from converting a broad theory repair into a few locally plausible representative patches.
