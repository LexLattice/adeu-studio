# Draft ADEU Hierarchical Obligation Broker HOB-0-B Implementation Mapping v0

Status: support / planning implementation mapping record for planned
`HOB-0-B`.

Authority layer: support / planning.

This note maps likely implementation for `HOB-0-B`. It does not authorize
implementation by itself and does not replace a future `vNext+<n>` lock,
stop-gate decision, or edge assessment. `HOB-0-B` should be refreshed when its
slice turn comes.

## Slice Intent

`HOB-0-B` should consume released `HOB-0-A` catalog, activation, inherited
ledger, validation, and frontier records to compute full closure posture and
plan operationalization.

It should answer:

```text
Which selected subtrees are closed, partial, blocked, representative-only, or
scoped-ready, and what probe matrix / implementation batch plan follows?
```

It must not answer:

```text
Should a parent apply?
Did probes pass?
Should code be patched?
What official score changed?
```

## Planned Surfaces

Likely schema / model surfaces:

- `repo_obligation_closure_report@1`
- `repo_obligation_next_frontier_report@1`
- `repo_obligation_probe_matrix_plan@1`
- `repo_obligation_implementation_batch_contract@1`
- `repo_obligation_operationalization_report@1`

Likely source files:

- `packages/adeu_obligation_broker/src/adeu_obligation_broker/closure.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/probe_matrix.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/batch.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/operationalization.py`
- `packages/adeu_obligation_broker/tests/test_hob_0b.py`
- `apps/api/fixtures/obligation_broker/vnext_plus273/`

## Consumed Basis

`HOB-0-B` should require released `HOB-0-A` records:

- catalog;
- activation assessment;
- inherited obligation ledger;
- traversal validation report;
- non-authority guardrail.

No `HOB-0-B` report should be valid if the consumed A ledger has validation
errors that block the selected subtree.

## Field-Level Expectations

`repo_obligation_closure_report@1` should include:

- `obligation_closure_report_ref`
- `catalog_id`
- `catalog_version`
- `catalog_hash`
- `inherited_obligation_ledger_ref`
- `traversal_validation_report_ref`
- `subtree_closure_rows`
- `weakest_child_readiness_rows`
- `closure_basis_rows`
- `closure_status`
- `closure_blocker_refs`

Closure basis values should include:

```text
all_children_gold_ready
all_children_scoped_ready
representative_only
blocked_by_child
blocked_by_A_validation
deferred_with_risk
```

`repo_obligation_next_frontier_report@1` should include:

- `obligation_next_frontier_report_ref`
- `obligation_closure_report_ref`
- `frontier_rows`
- `frontier_priority_rows`
- `frontier_batchability_rows`

`repo_obligation_probe_matrix_plan@1` should include:

- `obligation_probe_matrix_plan_ref`
- `obligation_closure_report_ref`
- `probe_matrix_rows`
- `terminal_node_refs`
- `boundary_node_refs`
- `held_out_node_refs`
- `probe_plan_non_execution_posture`
- `probe_authority_posture`

Required probe authority posture:

```text
probe_authority_posture = plan_only_not_observed
```

`repo_obligation_implementation_batch_contract@1` should include:

- `obligation_implementation_batch_contract_ref`
- `obligation_probe_matrix_plan_ref`
- `target_subtree_refs`
- `included_node_refs`
- `excluded_node_refs`
- `max_macro_count`
- `implementation_owner_rows`
- `regression_node_refs`
- `held_out_node_refs`
- `submit_allowed_posture`

`repo_obligation_operationalization_report@1` should include:

- `obligation_operationalization_report_ref`
- `audit_node_refs`
- `worker_task_ref`
- `ontology_nodes_preserved`
- `macro_subbranches_expanded`
- `probes_generated_before_patch`
- `implementation_owners_bound`
- `deferrals_explicit`
- `closure_metric_defined`
- `operationalization_status`
- `blocker_refs`

## Validation Expectations

`HOB-0-B` should fail closed when:

- consumed A records do not share the same catalog id/version/hash;
- a closure report ignores A validation blockers;
- parent readiness is stronger than the weakest required child readiness;
- representative-only branches are marked fixed;
- probe matrix rows reference non-terminal or unknown nodes without blocker
  posture;
- probe matrix rows imply observed behavior rather than planned observation;
- `probe_authority_posture` is not `plan_only_not_observed`;
- batch contracts include nodes outside the selected subtree;
- batch contracts exceed declared macro-count limits;
- implementation batches omit owner rows for implementation-owned nodes;
- probe plans imply probe execution authority.

## Deferred

Deferred to `HOB-0-C`:

- score/failure delta attribution;
- stale-ledger invalidation as released standalone report;
- integration handoff;
- family closeout.

Deferred to later families:

- actually running generated probes;
- dispatching workers;
- patching code;
- ProgramBench or semantic compiler integration.
