# LOCKED_CONTINUATION_vNEXT_PLUS256

## Status

Bounded starter lock draft for `PB-TRIAL-0-C` (local outcome audit, trial
observation summary, remand decision, and family closeout alignment).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-TRIAL-0-C` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-TRIAL-0`
- slice: `PB-TRIAL-0-C`
- branch-local execution target: `arc/pb-trial-0-c`

## Purpose

Freeze the bounded `PB-TRIAL-0-C` starter slice so the repo can audit the
single local cleanroom trial specimen, summarize its local observation without
ranking or benchmark claims, record local remand pressure without retry
authority, and close only `PB-TRIAL-0`.

`vNext+256` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize retry
dispatch authority, multi-attempt comparison, official ProgramBench
participation, official task execution, official runner integration, official
evaluator integration, hidden-test handling, hidden-test inference,
hidden-test equivalence, original source lookup, decompilation, internet
lookup inside ProgramBench tasks, external repository lookup, benchmark
submission, benchmark scoring, benchmark truth, model ranking, generated
official submissions, official submission authority, unbounded command
execution, target mutation outside released local artifacts, runtime
transition, product authorization, graph-memory authority, recursive policy
amendment, or future-family selection.

Controlling invariant:

```text
PB-TRIAL-0-C may audit and close one local cleanroom trial under released
A/B rows, but it may not convert that local outcome into official ProgramBench
truth, hidden-test equivalence, retry authority, model ranking, official
submission authority, or future-family selection.
```

## Instantiated Here

- `PB-TRIAL-0-C` instantiates the third local cleanroom reconstruction trial
  seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-TRIAL-0-A` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS254.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS254.md`
    - `docs/ASSESSMENT_vNEXT_PLUS254_EDGES.md`
    - trial docket
    - execution runbook
    - sandbox readiness review
    - trial non-authority guardrail
  - consumed released `PB-TRIAL-0-B` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS255.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS255.md`
    - `docs/ASSESSMENT_vNEXT_PLUS255_EDGES.md`
    - worker dispatch record
    - execution capture
    - candidate artifact snapshot
    - lifecycle projection
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v80.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0C_IMPLEMENTATION_MAPPING_v0.md`
  - emitted third-slice record shapes:
    - `programbench_local_trial_outcome_audit@1`
    - `programbench_local_trial_observation_summary@1`
    - `programbench_local_trial_remand_decision@1`
    - `programbench_local_trial_family_closeout_alignment@1`

## Required Starter Vocabulary

Minimum `programbench_local_trial_outcome_audit@1` fields:

- `trial_outcome_audit_ref`
- `trial_docket_ref`
- `trial_runbook_ref`
- `sandbox_readiness_review_ref`
- `trial_worker_dispatch_ref`
- `trial_execution_capture_ref`
- `candidate_artifact_snapshot_ref`
- `trial_lifecycle_projection_ref`
- `local_evidence_rows`
- `runbook_satisfaction_rows`
- `sandbox_satisfaction_rows`
- `carried_blocker_refs`
- `carried_warning_refs`
- `local_outcome_posture`
- `hidden_test_equivalence_posture`
- `benchmark_truth_posture`
- `model_ranking_posture`
- `official_submission_posture`
- `limitation_note`

Allowed `local_outcome_posture` values:

- `trial_locally_accepted`
- `trial_remand_recommended`
- `trial_blocked_by_sandbox_violation`
- `trial_blocked_by_lifecycle_projection_gap`
- `trial_blocked_by_output_capture_gap`
- `trial_inconclusive_local_only`
- `future_family_only`

Minimum `programbench_local_trial_observation_summary@1` fields:

- `trial_observation_summary_ref`
- `trial_outcome_audit_ref`
- `trial_docket_ref`
- `observed_input_packet_hash`
- `observed_candidate_snapshot_hash`
- `observed_result_posture`
- `observation_rows`
- `limitation_rows`
- `single_trial_scope_posture`
- `benchmark_truth_posture`
- `model_ranking_posture`
- `comparison_authority_posture`
- `limitation_note`

Minimum `programbench_local_trial_remand_decision@1` fields:

- `trial_remand_decision_ref`
- `trial_outcome_audit_ref`
- `trial_observation_summary_ref`
- `remand_decision_rows`
- `remand_source_kinds`
- `retry_authority_posture`
- `hidden_test_diagnostic_posture`
- `source_lookup_posture`
- `future_family_selection_posture`
- `limitation_note`

Allowed `remand_source_kinds` values:

- `local_execution_capture_gap`
- `local_candidate_snapshot_gap`
- `local_lifecycle_projection_gap`
- `sandbox_readiness_or_application_gap`
- `worker_declared_uncertainty`
- `runbook_satisfaction_gap`
- `local_evidence_inconclusive`

Minimum `programbench_local_trial_family_closeout_alignment@1` fields:

- `family_closeout_ref`
- `closed_family_ref`
- `closed_slice_refs`
- `trial_docket_refs`
- `trial_execution_capture_refs`
- `candidate_artifact_snapshot_refs`
- `trial_outcome_audit_refs`
- `trial_observation_summary_refs`
- `trial_remand_decision_refs`
- `family_alignment_posture`
- `official_programbench_non_authority_posture`
- `hidden_test_non_inference_posture`
- `benchmark_truth_non_authority_posture`
- `model_ranking_non_authority_posture`
- `retry_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_local_trial_outcome_audit@1`
  - `programbench_local_trial_observation_summary@1`
  - `programbench_local_trial_remand_decision@1`
  - `programbench_local_trial_family_closeout_alignment@1`
- mirrored `spec/` schema exports for the same shapes;
- validators requiring released A and B refs before outcome audit validation;
- validators rejecting benchmark truth, hidden-test equivalence, official
  evaluator truth, model ranking, official submission authority, official
  ProgramBench participation, and retry authority;
- validators requiring `trial_locally_accepted` to have no carried blockers,
  no sandbox violation, no output capture gap, no lifecycle projection gap, a
  candidate snapshot inside released write scope, and lifecycle projection
  validation against released `PB-ATTEMPT-0` validator bindings;
- validators rejecting observation summaries that compare models, retries,
  attempts, benchmark rows, leaderboard standing, or benchmark scores;
- validators requiring remand decisions to cite only local trial/attempt/
  workbench evidence source kinds;
- validators rejecting remand decisions sourced from hidden tests, official
  evaluator output, original source, decompilation, internet lookup, or
  external repository lookup;
- validators rejecting remand decisions that grant retry authority;
- validators requiring family closeout alignment to close exactly
  `PB-TRIAL-0-A`, `PB-TRIAL-0-B`, and `PB-TRIAL-0-C`;
- reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus256/`;
- focused tests for `PB-TRIAL-0-C` plus schema export coverage;
- no execution, retry, official benchmark, or future-family artifact kinds.

Expected implementation scope:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_trial.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_local_trial_outcome_audit.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_observation_summary.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_remand_decision.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_family_closeout_alignment.v1.json`
- `spec/programbench_local_trial_outcome_audit.schema.json`
- `spec/programbench_local_trial_observation_summary.schema.json`
- `spec/programbench_local_trial_remand_decision.schema.json`
- `spec/programbench_local_trial_family_closeout_alignment.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_trial_pb_trial_0c.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus256/`

## Explicit Non-Outputs

`PB-TRIAL-0-C` must not output:

- worker dispatch record;
- execution capture;
- candidate artifact snapshot or materialization;
- official ProgramBench runner/evaluator integration;
- official task execution;
- official submission artifact;
- hidden-test handling;
- hidden-test equivalence;
- benchmark score;
- benchmark truth;
- model ranking or leaderboard row;
- retry dispatch authority;
- multi-attempt comparison;
- source lookup, decompilation, internet lookup, or external repo diagnostic;
- product, graph-memory, release, recursive-policy, or future-family
  selection.

## Starter Contract

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+256",
  "target_path": "PB-TRIAL-0-C",
  "authority_layer": "lock",
  "selected_family": "PB-TRIAL-0",
  "selected_slice": "PB-TRIAL-0-C",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS256.md",
  "allowed_package": "packages/adeu_benchmarking",
  "selected_record_shapes": [
    "programbench_local_trial_outcome_audit@1",
    "programbench_local_trial_observation_summary@1",
    "programbench_local_trial_remand_decision@1",
    "programbench_local_trial_family_closeout_alignment@1"
  ],
  "local_gate": "make arc-start-check ARC=256",
  "non_authority_summary": "No official ProgramBench participation, hidden-test handling, benchmark truth, model ranking, retry authority, official submission, execution, or future-family selection is authorized by this lock."
}
```

## Verification Plan

- run `make arc-start-check ARC=256` while this bundle remains docs-only;
- during implementation, run the focused `PB-TRIAL-0-C` tests and
  `make check` before opening a PR.
