# LOCKED_CONTINUATION_vNEXT_PLUS259

## Status

Bounded starter lock draft for `PB-RETRY-0-C` (retry outcome audit,
same-lineage retry delta observation summary, remand settlement, and family
closeout alignment).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-RETRY-0-C` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-RETRY-0`
- slice: `PB-RETRY-0-C`
- branch-local execution target: `arc/pb-retry-0-c`

## Purpose

Freeze the bounded `PB-RETRY-0-C` starter slice so the repo can audit one
released local retry specimen, summarize same-lineage local retry deltas,
settle the declared local remand without second-retry authority, and close
only the `PB-RETRY-0` family.

`vNext+259` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize a
second retry request, retry dispatch, command execution, candidate
materialization, official ProgramBench participation, official task
execution, official runner integration, official evaluator integration,
hidden-test handling, hidden-test inference, hidden-test equivalence,
original source lookup, decompilation, internet lookup inside ProgramBench
tasks, external repository lookup, benchmark submission, benchmark scoring,
benchmark truth, model ranking, generated official submissions, official
submission authority, unbounded command execution, target mutation outside
released local artifacts, runtime transition, product authorization,
graph-memory authority, recursive policy amendment, or future-family
selection.

Controlling invariant:

```text
PB-RETRY-0-C may audit and settle one same-lineage local retry under released
A/B rows, but it may not convert that local settlement into official
ProgramBench truth, hidden-test equivalence, model ranking, second retry
authority, official submission authority, or future-family selection.
```

## Instantiated Here

- `PB-RETRY-0-C` instantiates the third local cleanroom retry-governance seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-RETRY-0-A` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS257.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS257.md`
    - `docs/ASSESSMENT_vNEXT_PLUS257_EDGES.md`
    - retry request
    - retry lineage registry
    - trial remand source index
    - retry eligibility review
    - retry scope contract
    - retry non-authority guardrail
  - consumed released `PB-RETRY-0-B` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS258.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS258.md`
    - `docs/ASSESSMENT_vNEXT_PLUS258_EDGES.md`
    - retry dispatch record
    - retry execution capture
    - retry candidate delta snapshot
    - retry lifecycle projection
    - retry sandbox application trace
  - inherited released `PB-TRIAL-0` basis through A/B:
    - source trial outcome audit
    - source trial observation summary
    - source trial remand decision
    - source trial family closeout alignment
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v81.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0C_IMPLEMENTATION_MAPPING_v0.md`
  - emitted third-slice record shapes:
    - `programbench_local_retry_outcome_audit@1`
    - `programbench_local_retry_delta_observation_summary@1`
    - `programbench_local_retry_remand_settlement@1`
    - `programbench_local_retry_family_closeout_alignment@1`

## Required Starter Vocabulary

Minimum `programbench_local_retry_outcome_audit@1` fields:

- `retry_outcome_audit_ref`
- `retry_request_ref`
- `retry_lineage_ref`
- `retry_eligibility_review_ref`
- `retry_scope_contract_ref`
- `retry_dispatch_record_ref`
- `retry_execution_capture_ref`
- `retry_candidate_delta_snapshot_ref`
- `retry_lifecycle_projection_ref`
- `retry_sandbox_trace_ref`
- `local_remand_refs`
- `remand_satisfaction_rows`
- `local_probe_basis_refs`
- `carried_blocker_refs`
- `carried_warning_refs`
- `local_retry_result_posture`
- `hidden_test_equivalence_posture`
- `official_submission_posture`
- `model_ranking_posture`
- `limitation_note`

Allowed `local_retry_result_posture` values:

- `local_retry_resolved`
- `local_retry_remand_unresolved`
- `local_retry_blocked_by_sandbox_violation`
- `local_retry_blocked_by_contamination`
- `local_retry_blocked_by_execution_capture_gap`
- `local_retry_blocked_by_candidate_delta_gap`
- `local_retry_blocked_by_lifecycle_projection_gap`
- `local_retry_inconclusive_local_only`
- `future_family_only`

Minimum `programbench_local_retry_delta_observation_summary@1` fields:

- `retry_delta_observation_summary_ref`
- `retry_outcome_audit_ref`
- `source_trial_observation_summary_ref`
- `retry_execution_capture_refs`
- `retry_candidate_delta_snapshot_refs`
- `same_lineage_delta_rows`
- `observation_scope_posture`
- `comparison_scope_posture`
- `benchmark_truth_posture`
- `model_ranking_posture`
- `limitation_note`

Minimum `programbench_local_retry_remand_settlement@1` fields:

- `retry_remand_settlement_ref`
- `retry_outcome_audit_ref`
- `source_trial_remand_decision_ref`
- `settled_remand_refs`
- `unresolved_remand_refs`
- `new_local_remand_refs`
- `settlement_posture`
- `second_retry_requestability_posture`
- `unresolved_remand_future_posture`
- `settlement_scope_posture`
- `second_retry_authority_posture`
- `future_family_posture`
- `limitation_note`

Required settlement posture values:

- `second_retry_requestability_posture =
  no_second_retry_authority_granted_by_pb_retry_0c`
- `settlement_scope_posture =
  local_retry_lineage_only_not_benchmark_truth`
- `second_retry_authority_posture =
  no_second_retry_dispatch_authority_granted_by_pb_retry_0c`
- `future_family_posture =
  no_future_family_selected_by_pb_retry_0c`

Minimum `programbench_local_retry_family_closeout_alignment@1` fields:

- `retry_family_closeout_ref`
- `retry_request_refs`
- `retry_eligibility_review_refs`
- `retry_scope_contract_refs`
- `retry_dispatch_record_refs`
- `retry_execution_capture_refs`
- `retry_candidate_delta_snapshot_refs`
- `retry_lifecycle_projection_refs`
- `retry_outcome_audit_refs`
- `retry_delta_observation_summary_refs`
- `retry_remand_settlement_refs`
- `closed_slice_refs`
- `family_closeout_posture`
- `future_family_authority_posture`
- `limitation_note`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_local_retry_outcome_audit@1`
  - `programbench_local_retry_delta_observation_summary@1`
  - `programbench_local_retry_remand_settlement@1`
  - `programbench_local_retry_family_closeout_alignment@1`
- mirrored `spec/` schema exports for the same shapes;
- validators requiring released `PB-RETRY-0-A` and `PB-RETRY-0-B` refs before
  C-specific audit, summary, settlement, or closeout rows validate;
- validators requiring all C rows to resolve to the same retry lineage, trial
  lineage, cleanroom case lineage, worker-visible boundary, declared local
  probe basis, and local-only benchmark-not-truth posture;
- validators revalidating the released B retry execution bundle before
  C-specific acceptance and closeout checks;
- validators rejecting local retry resolution when contamination, sandbox
  violation, hidden/evaluator/source evidence, execution capture gaps,
  candidate delta gaps, lifecycle projection gaps, or remand satisfaction gaps
  remain;
- validators requiring local retry resolution to have candidate delta evidence
  inside released write scope and lifecycle projection validation;
- validators rejecting delta observation summaries that compare models,
  workers, unrelated attempts, official scores, benchmark ranking,
  leaderboard standing, hidden-test outcomes, cross-task outcomes, or soft
  model/benchmark ranking phrases;
- validators requiring remand settlement to be local-only and to deny
  second-retry authority;
- validators rejecting remand settlement sourced from hidden-test failure,
  official evaluator feedback, original source fact, decompilation fact,
  internet lookup fact, or external repository fact;
- validators requiring `new_local_remand_refs` to create pressure only, not
  retry eligibility, dispatch authority, or second retry request authority;
- validators requiring family closeout alignment to close exactly
  `PB-RETRY-0-A`, `PB-RETRY-0-B`, and `PB-RETRY-0-C`;
- reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus259/`;
- focused tests for `PB-RETRY-0-C` plus schema export coverage;
- no second retry, dispatch, execution, official benchmark, or future-family
  artifact kinds.

Expected implementation scope:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_retry.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_local_retry_outcome_audit.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_delta_observation_summary.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_remand_settlement.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_family_closeout_alignment.v1.json`
- `spec/programbench_local_retry_outcome_audit.schema.json`
- `spec/programbench_local_retry_delta_observation_summary.schema.json`
- `spec/programbench_local_retry_remand_settlement.schema.json`
- `spec/programbench_local_retry_family_closeout_alignment.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_retry_pb_retry_0c.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus259/`

## Explicit Non-Outputs

`PB-RETRY-0-C` must not output:

- retry request or retry eligibility rows;
- retry dispatch record;
- retry execution capture;
- retry candidate delta snapshot;
- retry lifecycle projection;
- retry sandbox application trace;
- second retry request;
- second retry dispatch authority;
- official ProgramBench runner/evaluator integration;
- official task execution;
- official submission artifact;
- hidden-test handling;
- hidden-test equivalence;
- benchmark score;
- benchmark truth;
- model ranking or leaderboard row;
- multi-lineage comparison;
- source lookup, decompilation, internet lookup, or external repo diagnostic;
- product, graph-memory, release, recursive-policy, or future-family
  selection.

## Starter Contract

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+259",
  "target_path": "PB-RETRY-0-C",
  "authority_layer": "lock",
  "selected_family": "PB-RETRY-0",
  "selected_slice": "PB-RETRY-0-C",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS259.md",
  "allowed_package": "packages/adeu_benchmarking",
  "selected_record_shapes": [
    "programbench_local_retry_outcome_audit@1",
    "programbench_local_retry_delta_observation_summary@1",
    "programbench_local_retry_remand_settlement@1",
    "programbench_local_retry_family_closeout_alignment@1"
  ],
  "local_gate": "make arc-start-check ARC=259",
  "non_authority_summary": "No second retry authority, official ProgramBench participation, hidden-test handling, benchmark truth, model ranking, official submission, dispatch, execution, or future-family selection is authorized by this lock."
}
```

## Verification Plan

Before implementation starts:

```text
make arc-start-check ARC=259
```

For the implementation PR:

```text
.venv/bin/python -m pytest packages/adeu_benchmarking/tests/test_programbench_cleanroom_retry_pb_retry_0c.py -q
make check
```
