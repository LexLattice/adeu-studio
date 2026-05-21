# LOCKED_CONTINUATION_vNEXT_PLUS273

## Status

Bounded starter lock draft for `HOB-0-B` (closure report, next-frontier report,
probe-matrix plan, implementation batch contract, and operationalization
report).

This file remains a starter lock draft until the associated starter-bundle gate
is accepted and the bundle is intentionally committed as the operative
`HOB-0-B` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `HOB-0`
- slice: `HOB-0-B`
- branch-local execution target: `arc/hob-0-b`

## Purpose

Freeze the bounded `HOB-0-B` starter slice so the repo can compute closure and
operationalization plans from released `HOB-0-A` traversal artifacts without
turning the broker into a semantic judge, probe observer, probe executor,
worker dispatcher, code patcher, or product authority.

`vNext+273` authorizes docs plus the next implementation path over the existing
repo-owned `adeu_obligation_broker` package. It does not authorize semantic
adjudication by the broker, ontology generation, catalog mutation by the broker,
probe execution, command execution outside the implementation/test lane, worker
dispatch, product behavior claims, ProgramBench integration, score attribution,
delta attribution, stale-ledger invalidation, integration handoff,
future-family selection, release authority, or recursive policy amendment.

Controlling invariant:

```text
HOB-0-A can say which inherited obligations are present, invalid, blocked, or
frontier-bearing.

HOB-0-B may compute closure posture, frontier priority, plan-only probe matrix
rows, and bounded implementation batch contracts from those A records.

HOB-0-B may not decide whether a parent applies, observe whether probes passed,
execute probes, dispatch workers, patch code, or convert closure planning into
product truth.
```

## Instantiated Here

- `HOB-0-B` instantiates the second deterministic broker seam:
  - existing repo-owned package:
    - `adeu_obligation_broker`
  - consumed released inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v86.md`
    - `docs/ARCHITECTURE_ADEU_HIERARCHICAL_OBLIGATION_BROKER_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_HIERARCHICAL_OBLIGATION_BROKER_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_HIERARCHICAL_OBLIGATION_BROKER_HOB_0B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS272.md`
    - `docs/ASSESSMENT_vNEXT_PLUS272_EDGES.md`
    - `artifacts/agent_harness/v272/evidence_inputs/hob_0a_closeout_evidence_v272.json`
  - consumed package surfaces:
    - `packages/adeu_obligation_broker/src/adeu_obligation_broker/hob_0a.py`
    - `packages/adeu_obligation_broker/tests/test_hob_0a.py`
    - `packages/adeu_obligation_broker/schema/`
  - emitted starter record shapes:
    - `repo_obligation_closure_report@1`
    - `repo_obligation_next_frontier_report@1`
    - `repo_obligation_probe_matrix_plan@1`
    - `repo_obligation_implementation_batch_contract@1`
    - `repo_obligation_operationalization_report@1`

## Required Starter Vocabulary

Minimum `repo_obligation_closure_report@1` fields:

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
- `closure_authority_posture`

Required closure basis values:

```text
all_children_gold_ready
all_children_scoped_ready
representative_only
blocked_by_child
blocked_by_A_validation
deferred_with_risk
```

Minimum `repo_obligation_next_frontier_report@1` fields:

- `obligation_next_frontier_report_ref`
- `obligation_closure_report_ref`
- `frontier_rows`
- `frontier_priority_rows`
- `frontier_batchability_rows`
- `frontier_plan_authority_posture`

Minimum `repo_obligation_probe_matrix_plan@1` fields:

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

Minimum `repo_obligation_implementation_batch_contract@1` fields:

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
- `worker_dispatch_authority_posture`

Required worker-dispatch posture:

```text
worker_dispatch_authority_posture = no_worker_dispatch_authority
```

Minimum `repo_obligation_operationalization_report@1` fields:

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
- `operationalization_non_authority_posture`

## Required APIs

`HOB-0-B` must provide deterministic functions or equivalent module APIs that:

- load released `HOB-0-A` catalog, activation, inherited ledger, validation, and
  guardrail records;
- reject closure planning when consumed A records disagree on catalog
  id/version/hash;
- compute subtree closure posture without semantic applicability decisions;
- compute weakest-child readiness rows;
- emit next-frontier priority and batchability plans from A frontier rows;
- emit plan-only probe matrix rows for terminal/boundary/held-out nodes;
- emit bounded implementation batch contracts without worker dispatch
  authority;
- emit operationalization reports that preserve deferrals and blockers;
- compute stable canonical hashes independent of input order.

## Required Validation

`HOB-0-B` must fail closed when:

- consumed A records do not share the same catalog id/version/hash;
- a closure report ignores A validation blockers;
- parent readiness is stronger than the weakest required child readiness;
- representative-only branches are marked fixed or gold-ready;
- probe matrix rows reference unknown nodes without blocker posture;
- probe matrix rows imply observed behavior rather than planned observation;
- `probe_authority_posture` is not `plan_only_not_observed`;
- batch contracts include nodes outside the selected subtree;
- batch contracts exceed declared macro-count limits;
- implementation batches omit owner rows for implementation-owned nodes;
- probe plans imply probe execution authority;
- batch contracts imply worker-dispatch authority;
- operationalization reports imply product behavior truth.

## Required Starter Fixtures

`HOB-0-B` must include focused fixtures for:

1. all required children gold-ready -> parent closure can be gold-ready;
2. all required children scoped-ready -> parent closure is scoped-ready, not
   gold-ready;
3. blocked child -> parent closure is blocked by child;
4. A validation report with blockers -> B closure blocked by A validation;
5. representative-only branch -> representative-only closure, not fixed/gold;
6. probe matrix plan rows are plan-only and not observed/executed;
7. batch contract cannot include nodes outside the selected subtree;
8. batch contract cannot exceed declared macro-count limit;
9. worker dispatch posture remains denied;
10. shuffled input order preserves output order and canonical hashes.

## Deferred

Deferred to `HOB-0-C`:

- score/failure delta attribution;
- stale-ledger invalidation as a released standalone report;
- integration handoff;
- family closeout.

Deferred to later families:

- actually running generated probes;
- dispatching workers;
- patching product code;
- ProgramBench or semantic compiler integration.

## Starter Contract

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+273",
  "target_path": "HOB-0-B",
  "authority_layer": "lock",
  "selected_family": "HOB-0",
  "selected_slice": "HOB-0-B",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS273.md",
  "allowed_package": "packages/adeu_obligation_broker",
  "selected_record_shapes": [
    "repo_obligation_closure_report@1",
    "repo_obligation_next_frontier_report@1",
    "repo_obligation_probe_matrix_plan@1",
    "repo_obligation_implementation_batch_contract@1",
    "repo_obligation_operationalization_report@1"
  ],
  "local_gate": "make arc-start-check ARC=273",
  "non_authority_summary": "No semantic adjudication by the broker, ontology generation, catalog mutation, probe execution, worker dispatch, product truth, ProgramBench integration, score attribution, stale-ledger invalidation, integration handoff, or future-family selection is authorized by this lock."
}
```

## Verification Plan

Before implementation starts:

```text
make arc-start-check ARC=273
```

Before opening the implementation PR:

```text
make check
```
