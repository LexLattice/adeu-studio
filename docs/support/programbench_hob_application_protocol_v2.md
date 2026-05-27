# ProgramBench HOB Application Protocol v2

Authority layer: support.

This note is a support-layer overlay on
`docs/support/programbench_hob_application_protocol_v1.md`. It incorporates the
Phase 16 audit-of-audit v18 correction: a post-eval audit is not worker-ready
until broad pressure buckets have been compiled into numbered HOB child
obligations, regression sentinels, and probe-matrix rows.

## Controlling Artifacts

```text
base protocol:
  docs/support/programbench_hob_application_protocol_v0.md

question-card overlay:
  docs/support/programbench_hob_application_protocol_v1.md
  docs/support/programbench_hob_node_question_cards_v0.md

audit-of-audit patch:
  docs/support/phase16_audit_of_audit_v18_patch.md

catalog:
  docs/support/programbench_hob_obligation_catalog_v0.json
```

## V2 Hardening Summary

V1 prevents a node from being called probe-covered by one representative
example. V2 prevents a post-eval audit from becoming an implementation handoff
while its buckets are still broad labels.

```text
post-eval pressure bucket
  -> numbered HOB subtree compilation
  -> fixed / persistent / regressed rows by node
  -> regression sentinels
  -> probe matrix
  -> bounded implementation batch
```

Implementation is blocked until this lowering is complete.

## Audit-To-Tree Compilation Gate

Trigger:

```text
A post-eval audit emits failure classes, HOB references, or repair-order
recommendations.
```

Rule:

```text
The audit is not worker-ready until each class is compiled into numbered HOB
nodes with child obligations, closure status, probe rows, implementation owner,
and regression sentinels.
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
worker_ready:
  probe_worker: true | false
  implementation_worker: true | false
```

## Broad-Bucket Split Gate

Any audit bucket must be split before implementation if it:

```text
contains more than 25 rows,
spans more than one top-level HOB class,
or includes examples whose first failure surfaces differ by layer.
```

Exception:

```text
A single parent law may remain if the audit proves that one law generates all
child failures and supplies probes that exercise the child branches.
```

## Fixed-Pressure Generalization Audit

When a patch improves official rows while the parent macro remains open, every
fixed row must be mapped to the same numbered tree as persistent and regressed
rows.

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

Do not claim a parent macro was fixed generically unless fixed, persistent, and
regressed rows show a closed child-subtree boundary.

## Regression Sentinel Gate

If any local or official row was green in a prior phase and becomes red after a
repair batch, it becomes a required local sentinel before the next patch is
accepted.

For the trdsql score-72 run, the immediate sentinels are:

```text
R1:
  limit + skip + header row-window sentinel

R2:
  tilde path expansion sentinel
```

These sentinels must be included before and after each subsequent patch batch.

## Unclassified-Row Zero Tolerance

Unclassified rows may exist in a descriptive audit. They may not exist in an
implementation handoff.

Each unclassified row must become one of:

```text
assigned_to_hob_node
scoped_deferred_with_expected_risk
gold_deferred_with_expected_risk
blocked_pending_observation
blocked_pending_equivalence
catalog_extension_pressure
```

No worker may receive a task to implement `misc`, `unclassified`, or
`exactness_or_unclassified`.

## Mode-As-Program Gate

If a public flag or mode changes output purpose, examples, schema display,
resource topology, diagnostics, or exit behavior, treat it as a subprogram.

For trdsql-like tasks this includes:

```text
analyze mode
config / dblist mode
debug mode
help / usage mode
version mode
```

Each mode needs its own input route, transform, renderer, diagnostic, exit, and
resource-topology rows.

## Reader-To-SQL Schema Gate

When a program imports external resources into an embedded SQL substrate, reader
output must be modeled as a schema-producing transform before SQL execution.

Inherited child obligations include:

```text
format selection
header / no-header policy
fallback column names
row-window policy
blank-row policy
null conversion
table identity
column identity
resource token rewrite
alias and quoted-name behavior
error precedence
```

This gate is the bridge between input dialect rows and SQL identity rows.

## Codec Dependency Equivalence Gate

If a public format depends on codec support such as zstd, lz4, gzip, bzip2, or
xz, the run must prove one of:

```text
the reconstruction substrate has equivalent codec support,
the candidate implements a compatible fallback,
or the branch is explicitly scoped-deferred with expected risk.
```

Do not classify codec failures as ordinary parser failures before this
equivalence check.

## Batch 0 Contract

Before the next trdsql implementation patch:

```text
1. Split broad Phase 16 buckets into numbered child obligations.
2. De-lump all unclassified rows.
3. Build fixed / persistent / regressed tables by HOB node.
4. Install regression sentinels.
5. Define probe matrices for one bounded implementation batch.
6. Mark implementation handoff blocked until those probes are run.
```

The first bounded implementation batch should normally target the
reader-to-SQL schema bridge, because it shares obligations across SQL resource
identity, row windows, aliases, quoted paths, subqueries, stdin aliases, and
query-file/table-name composition.

