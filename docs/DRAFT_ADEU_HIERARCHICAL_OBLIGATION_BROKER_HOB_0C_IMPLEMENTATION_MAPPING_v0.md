# Draft ADEU Hierarchical Obligation Broker HOB-0-C Implementation Mapping v0

Status: support / planning implementation mapping record for planned
`HOB-0-C`.

Authority layer: support / planning.

This note maps likely implementation for `HOB-0-C`. It does not authorize
implementation by itself and does not replace a future `vNext+<n>` lock,
stop-gate decision, or edge assessment. `HOB-0-C` should be refreshed when its
slice turn comes.

## Slice Intent

`HOB-0-C` should consume released A/B broker substrate and make post-run
pressure attributable to numbered nodes, without turning score movement or
official failures into clean semantic evidence.

It should answer:

```text
Which numbered nodes explain the observed delta, did the run show macro
closure or only representative transfer, and what integration pressure remains?
```

It must not answer:

```text
What is clean product truth?
Should implementation authority be granted?
Should ProgramBench integration be selected?
Should future families be selected?
```

## Planned Surfaces

Likely schema / model surfaces:

- `repo_obligation_delta_attribution_ledger@1`
- `repo_obligation_stale_ledger_invalidation_report@1`
- `repo_obligation_broker_integration_handoff@1`
- `repo_obligation_broker_family_closeout_alignment@1`

Likely source files:

- `packages/adeu_obligation_broker/src/adeu_obligation_broker/delta.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/stale_ledger.py`
- `packages/adeu_obligation_broker/src/adeu_obligation_broker/handoff.py`
- `packages/adeu_obligation_broker/tests/test_hob_0c.py`
- `apps/api/fixtures/obligation_broker/vnext_plus274/`

## Consumed Basis

`HOB-0-C` should require released `HOB-0-A` and `HOB-0-B` records:

- catalog;
- activation assessment;
- inherited obligation ledger;
- traversal validation report;
- closure report;
- next-frontier report;
- probe-matrix plan;
- implementation batch contract;
- operationalization report.

## Field-Level Expectations

`repo_obligation_delta_attribution_ledger@1` should include:

- `obligation_delta_attribution_ledger_ref`
- `catalog_id`
- `catalog_version`
- `catalog_hash`
- `run_before_ref`
- `run_after_ref`
- `score_before`
- `score_after`
- `changed_failed_rows`
- `delta_attribution_rows`
- `regression_rows`
- `rows_moved_to_other_failure_rows`
- `evidence_boundary_posture`

Delta attribution rows should include:

- `node_id`
- `macro_ref`
- `matrix_rows_green`
- `rows_moved_to_other_failure`
- `regressions`
- `interpretation`
- `evidence_boundary_posture`

Allowed interpretation values should include:

- `representative_transfer_success`
- `macro_closure_success`
- `resource_or_substrate_masking`
- `implementation_transfer_error`
- `theory_gap_persists`

Allowed per-row evidence boundary posture values should include:

```text
post_eval_pressure_only
local_locked_probe_delta
official_like_pressure
source_postmortem_pressure
clean_first_pass_disallowed
```

`repo_obligation_stale_ledger_invalidation_report@1` should include:

- `obligation_stale_ledger_invalidation_report_ref`
- `prior_catalog_id`
- `prior_catalog_version`
- `prior_catalog_hash`
- `current_catalog_id`
- `current_catalog_version`
- `current_catalog_hash`
- `invalidated_ledger_refs`
- `invalidated_probe_plan_refs`
- `invalidation_reason_rows`
- `stale_ledger_reuse_posture`

`repo_obligation_broker_integration_handoff@1` should include:

- `obligation_broker_integration_handoff_ref`
- `handoff_pressure_rows`
- `handoff_pressure_kind`
- `handoff_non_selection_posture`
- `programbench_integration_authority_posture`
- `semantic_compiler_integration_authority_posture`
- `probe_execution_authority_posture`
- `implementation_authority_posture`
- `future_family_selection_posture`

`repo_obligation_broker_family_closeout_alignment@1` should include:

- `obligation_broker_family_closeout_alignment_ref`
- `family_ref`
- `closed_slices`
- `slice_a_closeout_ref`
- `slice_b_closeout_ref`
- `slice_c_closeout_ref`
- `family_scope_posture`
- `integration_authority_posture`
- `implementation_authority_posture`
- `future_family_selection_posture`

## Validation Expectations

`HOB-0-C` should fail closed when:

- delta attribution references unknown node IDs;
- score movement is interpreted as macro closure without matrix closure
  evidence;
- attribution rows omit per-row evidence boundary posture;
- official failures are labeled clean first-pass product truth;
- stale ledgers are reused after catalog hash changes without invalidation;
- integration handoff grants ProgramBench, semantic compiler, probe execution,
  implementation, or future-family authority;
- family closeout lists slices other than `HOB-0-A`, `HOB-0-B`, and
  `HOB-0-C`.

## Deferred To Later Families

`HOB-0-C` may emit pressure for later:

- ProgramBench-specific broker integration;
- semantic compiler integration;
- probe execution;
- worker taskpack generation;
- implementation authority.

It cannot select those families or grant their authority.
