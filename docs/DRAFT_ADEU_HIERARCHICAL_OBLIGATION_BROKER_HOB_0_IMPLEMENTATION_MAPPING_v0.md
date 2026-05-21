# Draft ADEU Hierarchical Obligation Broker HOB-0 Implementation Mapping v0

Status: support / implementation mapping record for planned `HOB-0`.

Authority layer: support.

This note maps likely implementation for the `HOB-0` family into package,
schema, validator, fixture, and slice surfaces. It does not authorize
implementation by itself and does not replace a future `vNext+<n>` lock,
stop-gate decision, or edge assessment.

## Family Scope

`HOB-0` should add a deterministic broker for hierarchical obligation
traversal after semantic adjudication.

It should not decide what a concept means. It should not decide whether a
parent class applies. It should not generate an ontology catalog by itself.
It should not run probes, inspect target source code, dispatch workers, patch
implementation code, grant product authority, or select future families.

The family should answer:

```text
Given a fixed numbered obligation catalog and model-authored activation rows,
which child obligations become live, which rows are missing or invalid, and
where must the model descend next?
```

It must not answer:

```text
What should the ontology mean?
Which parent classes apply?
What probes should be executed?
What code should be written?
Is the product correct?
```

## Likely Package Ownership

Create a new deterministic package:

- `packages/adeu_obligation_broker`

Likely files for later implementation:

- `packages/adeu_obligation_broker/pyproject.toml`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/__init__.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/models.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/catalog.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/activation.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/inheritance.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/validation.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/frontier.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/hashing.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/export_schema.py`
- `packages/adeu_obligation_broker/schema/*.v1.json`
- `packages/adeu_obligation_broker/tests/test_hob_0a.py`
- `packages/adeu_obligation_broker/tests/test_hob_0b.py`
- `packages/adeu_obligation_broker/tests/test_hob_0c.py`
- `packages/adeu_obligation_broker/tests/test_obligation_broker_export_schema.py`
- `spec/*.schema.json`
- `apps/api/fixtures/obligation_broker/vnext_plus272/`
- later:
  - `apps/api/fixtures/obligation_broker/vnext_plus273/`
  - `apps/api/fixtures/obligation_broker/vnext_plus274/`

## Planned Record Shapes

| Shape | Slice | Purpose |
|---|---|---|
| `repo_hierarchical_obligation_catalog@1` | `HOB-0-A` | fixed numbered catalog with nodes, child links, defaults, status vocabulary, proof vocabulary, and closure policies |
| `repo_obligation_activation_assessment@1` | `HOB-0-A` | model/upstream-authored semantic activation rows and warrants |
| `repo_inherited_obligation_ledger@1` | `HOB-0-A` | deterministic child-obligation ledger generated from activated parents and supplied statuses/proofs |
| `repo_obligation_traversal_validation_report@1` | `HOB-0-A` | structural validation diagnostics and next-frontier rows |
| `repo_obligation_broker_non_authority_guardrail@1` | `HOB-0-A` | guardrail preventing semantic, execution, implementation, or product authority |
| `repo_obligation_closure_report@1` | `HOB-0-B` | full subtree closure/readiness aggregation |
| `repo_obligation_next_frontier_report@1` | `HOB-0-B` | consolidated frontier report over selected subtrees |
| `repo_obligation_probe_matrix_plan@1` | `HOB-0-B` | planned probe matrix rows from terminal/near-terminal obligations |
| `repo_obligation_implementation_batch_contract@1` | `HOB-0-B` | bounded implementation batch plan over selected subtree nodes |
| `repo_obligation_operationalization_report@1` | `HOB-0-B` | audit-to-worker operationalization equivalence report |
| `repo_obligation_delta_attribution_ledger@1` | `HOB-0-C` | score/failure movement attribution to numbered nodes |
| `repo_obligation_stale_ledger_invalidation_report@1` | `HOB-0-C` | stale local/probe ledger invalidation when catalog or active subtree changes |
| `repo_obligation_broker_integration_handoff@1` | `HOB-0-C` | pressure-only handoff to later semantic compiler, ProgramBench, UX, or other integrations |
| `repo_obligation_broker_family_closeout_alignment@1` | `HOB-0-C` | family closeout alignment over A/B/C slices |

## Shared Vocabulary Source

The package should define one canonical vocabulary source and export it into
JSON schema. A/B/C should import the same vocabulary rather than each defining
slice-local strings.

Shared enums should include:

```text
activation_status
inheritance_status
obligation_status
readiness_status
proof_kind
proof_type
frontier_reason
authority_posture
closure_status
```

## Cross-Slice Validation Spine

The future implementation should validate:

- A accepts fixed catalog rows and model-authored activation rows, but does not
  adjudicate semantic applicability;
- A expands activated parents into inherited children;
- A rejects missing inherited children and invalid proof/status rows;
- A emits next-frontier rows but not full closure summaries;
- A denies probe execution, implementation authority, worker dispatch, product
  authority, and future-family selection;
- B consumes released A records;
- B computes closure/readiness summaries from A ledgers;
- B compiles probe-matrix plans and implementation batch contracts only as
  plans, not observed evidence or execution authority;
- C consumes released A/B records;
- C attributes deltas to numbered nodes without converting official failures
  into clean first-pass evidence;
- C emits integration handoffs as pressure-only and closes only `HOB-0`.

## Determinism Requirements

The package should be deterministic:

- no network;
- no provider calls;
- no command execution in library functions;
- no wall-clock dependence;
- canonical JSON serialization for hashes;
- lexicographic ordering for output rows;
- stable diagnostic codes;
- `extra="forbid"` schemas;
- unknown vocabulary fails closed;
- shuffled input rows produce the same canonical output and hash.

## Reference Fixture Plan

For `HOB-0-A`, fixtures should include:

- parent applies and all children are inherited;
- missing child fails closed;
- scoped deferral plus parent gold-ready claim fails closed;
- `proved_irrelevant` without proof object fails closed;
- unknown status vocabulary fails closed;
- open or blocked child emits deterministic frontier row;
- shuffled input order preserves canonical output order and hash.

For `HOB-0-B`, later fixtures should include:

- closure summary for a fully closed subtree;
- representative-only subtree cannot be marked fixed;
- probe-matrix plan generated from terminal leaves only;
- batch contract bounded to declared subtree and max macro count;
- stale old ledger is invalidated when catalog hash changes.

For `HOB-0-C`, later fixtures should include:

- score delta attributed to numbered nodes;
- representative-transfer success distinguished from macro-closure success;
- regressions and rows moved to other failure classes recorded;
- integration handoff remains pressure-only and non-selecting.

## Package Gate Expectation

Any implementation PR touching Python package, schema, fixture, or tests should
run:

```text
make check
```

Docs-only starter or closeout bundles may use the repo arc shortcut when their
diff remains docs/artifacts-only.
