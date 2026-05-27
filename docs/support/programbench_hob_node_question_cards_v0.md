# ProgramBench HOB Node Question Cards v0

Authority layer: support.

This note adds canonical question cards for ProgramBench HOB runs. It does not
replace `programbench_hob_obligation_catalog_v0.json`; it supplements the
catalog with branch-specific question obligations that workers must answer
before marking broad nodes as `covered_by_probe_matrix`.

The purpose is to prevent this failure mode:

```text
node label recognized
  -> one representative probe created
  -> node marked covered
  -> sibling discriminators silently omitted
```

## General Rule

For every active HOB node marked `covered_by_probe_matrix`, the worker must
produce a question-card row:

```yaml
question_card_row:
  node_id: string
  question_family: string
  answered_questions: []
  unanswered_questions: []
  concrete_probe_refs: []
  negative_or_boundary_probe_refs: []
  sibling_coverage_posture:
    all_known_siblings_represented |
    representative_only |
    blocked_pending_schema_reentry |
    scoped_deferred_with_expected_risk
  closure_effect:
    supports_gold_probe_ownership |
    supports_scoped_probe_ownership_only |
    blocks_official_intended_eval
```

`covered_by_probe_matrix` is not valid for official-intended handoff unless:

```text
answered_questions is non-empty
concrete_probe_refs is non-empty
negative_or_boundary_probe_refs is non-empty where the node has error/failure branches
sibling_coverage_posture != representative_only
closure_effect != blocks_official_intended_eval
```

## 1. Control Plane / Invocation Grammar

Ask:

```text
Which invocation forms exist: no-args, help, version, list, analyze, debug?
Which flags are bool, value, enum, repeated, or positional-sensitive?
Are equals and separate forms equivalent?
What happens for unknown flag, missing value, invalid enum, repeated flags?
Which branch wins when multiple modes are supplied?
Which stream receives usage, diagnostics, and normal output?
What is the exit code for each control-plane branch?
```

Required probe shapes:

```text
positive mode probe
unknown/invalid probe
mode precedence probe when modes can combine
split stdout/stderr/exit lock
```

## 2. Public Schema And Mode Family

Ask:

```text
What schema items does help/list/debug/config/version expose?
Does each item map to an existing ontology node?
Which items change input route, transform semantics, output, diagnostics, or state?
Which schema items are aliases or no-ops?
Which newly observed items require L2 re-entry?
```

Required probe shapes:

```text
schema harvest probe
schema-item obligation ledger
re-entry diff against current tree
one terminalization/defer/pass-through outcome per schema item
```

## 3. Input Resource And Route Topology

Ask:

```text
Which routes exist: stdin, file, directory, multiple files, glob, URL, config, DB/DSN?
How are paths normalized: cwd, tilde, absolute, relative, escaped, quoted?
What happens for no match, unreadable file, malformed file, directory path?
Do compressed inputs resolve by extension, flag, or content?
Can multiple resource types mix in one query or route?
Does resource expansion order affect row order or diagnostics?
```

Required probe shapes:

```text
one positive route probe per live route
one negative route probe per route with failure semantics
mixed-resource probe when multiple routes can compose
order/identity probe for glob or multiple resources
```

## 4. Input Dialect And Value-Domain Grammar

Ask:

```text
Which dialects exist: CSV, TSV, JSON, JSONL, YAML, TBLN, LTSV, text, fixed-width?
How is dialect selected: explicit flag, extension, content, default?
What are header, no-header, delimiter, quote, escape, comment, skip, limit, row-number rules?
How do null, empty string, scalar, array, object, nested object, and mixed types map to rows/columns?
Which invalid forms error before binding, and which import as data?
Do dialect-specific options compose with each other?
```

Required probe shapes:

```text
positive minimal dialect probe
negative malformed dialect probe
value-domain cross-product probe
option composition probe for skip/limit/header/null/row-number/selector
```

Critical subquestions for trdsql-like tasks:

```text
JSON object: one row or key/value rows?
JSON array of objects: rows from objects?
JSON array of scalars: one scalar column or one row per scalar?
JSON nested object/array: stringified, flattened, jq-selected, or error?
JSON/YAML selector: does selector run before table creation?
CSV null conversion: does NULL render as blank or quoted empty string?
LTSV/TBLN invalid syntax: data row or import error?
Text/fixed-width blank lines: skipped, empty rows, or errors?
```

## 5. Embedded Language / Transform Substrate

Ask:

```text
Is the embedded language expression-only, resource-backed, or both?
How do language tokens bind to resources?
How are aliases, quoted names, path-like names, globs, and selector-qualified names resolved?
Which statement classes are allowed: SELECT, JOIN, subquery, aggregate, INSERT, UPDATE, DELETE?
Can multiple statements run, and which result is emitted?
Which functions/operators exist through host runtime or backing DB?
What is parse vs bind vs execute vs render error precedence?
```

Required probe shapes:

```text
expression-only probe
resource-backed query probe
join/subquery probe
mutation or statement-class negative/positive probe when public behavior suggests state
diagnostic precedence probe
```

## 6. Subject, Identity, Binding, And Aggregation

Ask:

```text
What is the subject identity: raw path, basename, extension-stripped name, table alias, stdin sentinel?
What are column identity rules for headers, synthetic columns, duplicate columns, invalid names?
What is the row universe before and after filters, limits, joins, aggregation, or hidden rows?
Which denominator controls exit status or aggregate counts?
What collision policy applies for duplicate resources or table names?
```

Required probe shapes:

```text
identity rendering probe
duplicate/collision probe
aggregation denominator probe when aggregates or counts exist
```

## 7. State, Lifecycle, And Mutation

Ask:

```text
What initialization and import order applies?
Do side effects happen before later failures?
Are mutations visible within one statement batch, across files, or across invocations?
Does failure roll back, partially commit, or leave temp state?
Are output files, DB files, temp files, caches, locks, or coverage files created?
What cleanup is observable?
```

Required probe shapes:

```text
multi-statement state probe
mutation visibility probe
failure-after-side-effect probe
rerun/cross-invocation probe when persistent state is public
file side-effect hash probe
```

Activation rule:

```text
If public/reference observation shows multiple statements, mutation statements,
output-file routing, DB files, temp files, or persistent resources, node 7 must
be `applies`, not merely `candidate_pending`.
```

## 8. Output Router, Renderer, And Byte Grammar

Ask:

```text
Where can output go: stdout, stderr, file, compressed file?
How is format selected: explicit flag, extension guessing, default, route inference?
What is the exact byte grammar for each renderer?
How do headers, nulls, empty strings, final newline, delimiters, quote policy, CRLF, width, and wrapping work?
What happens for multi-column, zero-row, one-row, one-column, unicode, long field, and nested values?
Do file side effects happen before or after render errors?
```

Required probe shapes:

```text
positive renderer probe per live renderer
multi-column renderer probe
null/empty/final-newline probe
file-output probe where route exists
compression-byte or decompressed-payload policy probe
```

## 9. Diagnostics, Fatal Gates, And Channel Contracts

Ask:

```text
Which failures exist: bad flag, bad value, missing resource, bad config, bad dialect, bad SQL, bind error, render error?
Which failure wins when several are present?
Which stream carries the diagnostic?
Are dynamic fields present: timestamps, paths, command echoes?
Does the program expose suggestions, usage text, debug trace, or analyze advice?
What is the exit code for each fatal gate?
```

Required probe shapes:

```text
one representative fatal gate per error family
one precedence probe with two possible failures
split stdout/stderr/exit lock
dynamic-field normalization policy
```

## 10. Runtime Substrate And Observation Ecology

Ask:

```text
What interpreter/compiler and dependency ABI will official eval use?
Does packaged artifact execute the same code as workspace candidate?
Are optional libraries, compression tools, locale, time, terminal width, and filesystem semantics equivalent?
Can the program reach product behavior under official packaging?
What side effects does the harness introduce or observe?
```

Required probe shapes:

```text
packaged artifact smoke probe
target-substrate ABI probe
dependency availability probe
reached-product-behavior probe
```

## 11. Methodological Equivalence And Warrant

Ask:

```text
What transfer is being claimed: visible spec to theory, scout to probe, probe to implementation, local to official?
What equivalence relation witnesses that transfer?
Which lower equivalence layer could dominate a later failure?
Which evidence is clean public/reference, and which is post-eval pressure?
```

Required probe shapes:

```text
witness-bundle equivalence row
local-official equivalence row
evidence-boundary row for post-eval pressure
```

## 12. Probe, Readiness, And Implementation Handoff

Ask:

```text
Does every active node have concrete probe ownership?
Do probes include positive, negative, boundary, and composition cases where required?
Do held-out/metamorphic probes exist before official-intended eval?
Does the candidate pass the same locked probe suite it was built from?
Are scoped and gold readiness separated?
Does implementation ownership map to concrete files/modules?
```

Required probe shapes:

```text
node-to-probe ownership table
held-out/metamorphic probe table
candidate-vs-reference parity report
packaged artifact parity report
bookkeeper acceptance report
```

Hard gate:

```text
Official-intended eval is blocked until node 12.4 has concrete held-out or
metamorphic probes, and those probes are either passed, explicitly scoped
deferred with expected risk, or the run is labeled non-gold scoped experiment.
```
