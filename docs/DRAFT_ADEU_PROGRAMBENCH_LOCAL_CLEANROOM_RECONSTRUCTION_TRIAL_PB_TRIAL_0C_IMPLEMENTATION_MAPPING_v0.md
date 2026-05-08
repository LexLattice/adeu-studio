# Draft ADEU ProgramBench Local Cleanroom Reconstruction Trial PB-TRIAL-0-C Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-TRIAL-0-C`.

Authority layer: support.

This note maps the third candidate slice for `PB-TRIAL-0`. It is not a slice
lock. `PB-TRIAL-0-C` should activate only after `PB-TRIAL-0-B` closes on
`main` and a later canonical starter lock selects this slice.

## Slice Intent

`PB-TRIAL-0-C` should audit the single local trial outcome, summarize the
observation without ranking or benchmark claims, decide whether local remand
pressure remains, and close only `PB-TRIAL-0`.

It should answer:

```text
What did this one local cleanroom trial demonstrate under released runbook and
attempt lifecycle law, what blockers or warnings remain, and is there remand
pressure without retry authority?
```

It must not claim official benchmark truth, hidden-test equivalence, model
ranking, official submission authority, retry dispatch authority, or
next-family selection.

## Expected File Scope

Likely implementation files:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_trial.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_local_trial_outcome_audit.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_observation_summary.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_remand_decision.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_family_closeout_alignment.v1.json`
- mirrored `spec/` schema exports for the above
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_trial_pb_trial_0c.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus256/`

## Record Shapes

### `programbench_local_trial_outcome_audit@1`

Minimum fields:

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

Local acceptance must remain scoped to declared local trial evidence and must
not imply hidden-test equivalence. It requires a candidate artifact snapshot
inside released write scope and a lifecycle projection that passed released
`PB-ATTEMPT-0` validator bindings.

### `programbench_local_trial_observation_summary@1`

Minimum fields:

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

Observation summaries describe one local trial only. They are not model
ranking, leaderboard, benchmark score, or multi-attempt comparison rows.
They must not contain comparative language across models, attempts, retries,
benchmark rows, or leaderboard posture.

### `programbench_local_trial_remand_decision@1`

Minimum fields:

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

Allowed remand source kinds:

- `local_execution_capture_gap`;
- `local_candidate_snapshot_gap`;
- `local_lifecycle_projection_gap`;
- `sandbox_readiness_or_application_gap`;
- `worker_declared_uncertainty`;
- `runbook_satisfaction_gap`;
- `local_evidence_inconclusive`.

Remand decisions may carry local pressure only. They are not retry authority.

### `programbench_local_trial_family_closeout_alignment@1`

Minimum fields:

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

Family closeout closes only `PB-TRIAL-0`.

## Consumed Released Inputs

`PB-TRIAL-0-C` should consume released `PB-TRIAL-0-A/B` rows:

- trial docket;
- execution runbook;
- sandbox readiness review;
- trial non-authority guardrail;
- worker dispatch record;
- execution capture;
- candidate artifact snapshot;
- lifecycle projection.

It should also consume released `PB-ATTEMPT-0` validator bindings or lifecycle
projection validation refs rather than bypassing the attempt lifecycle.

## Validation Expectations

`PB-TRIAL-0-C` should validate:

- released A and B refs are required;
- outcome audits cannot exist without one trial docket, runbook, readiness
  review, dispatch record, execution capture, candidate snapshot, and
  lifecycle projection;
- outcome audits cannot claim benchmark truth, hidden-test equivalence, model
  ranking, official evaluator truth, official submission authority, official
  ProgramBench participation, or retry authority;
- `trial_locally_accepted` requires no carried blockers, no sandbox violation,
  no lifecycle projection gap, no output capture gap, no hidden-test
  equivalence posture, and no official submission posture;
- `trial_locally_accepted` requires the candidate snapshot to exist inside
  released write scope;
- `trial_locally_accepted` requires lifecycle projection validation to pass
  released `PB-ATTEMPT-0` validator bindings;
- observation summaries are single-trial-only and cannot compare models,
  compare retry attempts, claim leaderboard standing, or emit benchmark
  scores;
- observation summaries reject comparative language across models, attempts,
  retries, benchmark rows, or leaderboard posture;
- remand recommended, blocked, or inconclusive outcomes require carried
  blockers, warnings, or limitation rows;
- remand decisions cite only local trial/attempt/workbench evidence sources;
- remand decisions cannot cite hidden tests, official evaluator output,
  original source, decompilation, internet lookup, or external repository
  lookup;
- remand decisions cannot become retry authority by themselves;
- family closeout alignment closes exactly `PB-TRIAL-0-A`,
  `PB-TRIAL-0-B`, and `PB-TRIAL-0-C`;
- family closeout alignment does not select retry dispatch authority,
  multi-attempt comparison, larger fixture matrices, official ProgramBench,
  benchmark-result governance, conceptual broker work, V86/V87/V88, product,
  graph, release, recursive-policy work, or any other future family.

## Reference Fixture Sketch

Expected reference fixture set under `apps/api/fixtures/benchmarking/vnext_plus256/`:

- `programbench_local_trial_outcome_audit_v256_reference.json`
- `programbench_local_trial_observation_summary_v256_reference.json`
- `programbench_local_trial_remand_decision_v256_reference.json`
- `programbench_local_trial_family_closeout_alignment_v256_reference.json`
- `programbench_local_trial_v256_reject_outcome_without_lifecycle_projection.json`
- `programbench_local_trial_v256_reject_local_acceptance_with_blockers.json`
- `programbench_local_trial_v256_reject_local_acceptance_without_snapshot.json`
- `programbench_local_trial_v256_reject_local_acceptance_without_lifecycle_projection_validation.json`
- `programbench_local_trial_v256_reject_hidden_test_remand_source.json`
- `programbench_local_trial_v256_reject_model_ranking_summary.json`
- `programbench_local_trial_v256_reject_comparative_observation_summary.json`
- `programbench_local_trial_v256_reject_retry_authority.json`
- `programbench_local_trial_v256_reject_future_family_selection.json`

## Explicit Non-Outputs

`PB-TRIAL-0-C` must not output:

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
