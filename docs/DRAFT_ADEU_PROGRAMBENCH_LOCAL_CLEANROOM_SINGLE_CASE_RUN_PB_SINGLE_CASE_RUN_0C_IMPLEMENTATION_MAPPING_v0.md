# Draft ADEU ProgramBench Local Cleanroom Single Case Run PB-SINGLE-CASE-RUN-0-C Implementation Mapping v0

Status: support / implementation mapping record for planned
`PB-SINGLE-CASE-RUN-0-C`.

Authority layer: support.

This note maps the likely implementation for `PB-SINGLE-CASE-RUN-0-C`. It is
not a starter lock. `PB-SINGLE-CASE-RUN-0-C` should activate only after
`PB-SINGLE-CASE-RUN-0-B` closes on `main` and a later canonical starter lock
selects this slice.

## Slice Intent

`PB-SINGLE-CASE-RUN-0-C` should audit one local execution specimen, summarize
local observations, emit local-only acceptance/remand posture, and close the
family. It should not score ProgramBench, compare baselines, rank models,
grant retry authority, submit officially, or select a future family.

It classifies one selected case-lineage run specimen. It does not create
official ProgramBench pass/fail truth and does not replace the released
attempt/trial/workbench lifecycle law.

The slice should answer:

```text
How should the one local specimen be classified against its declared local
probe/oracle and lifecycle evidence?
```

It must not answer:

```text
What is the benchmark score?
Is the model better than a baseline?
Should we run more cases?
Should we submit officially?
```

## Selected Surfaces

Likely schema / model surfaces:

- `programbench_single_case_local_outcome_audit@1`
- `programbench_single_case_run_observation_summary@1`
- `programbench_single_case_remand_or_acceptance_decision@1`
- `programbench_single_case_run_handoff@1`
- `programbench_single_case_run_family_closeout_alignment@1`

Likely source files for a future implementation:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_single_case_run.py`
- `packages/adeu_benchmarking/tests/test_programbench_single_case_run_pb_single_case_run_0c.py`
- `apps/api/fixtures/benchmarking/vnext_plus271/`

## Consumed Lineage

`PB-SINGLE-CASE-RUN-0-C` should consume released A/B rows:

- A request, target selection, execution preflight, run control contract, and
  guardrail refs;
- B worker dispatch specimen, execution trace, probe observation bundle,
  candidate artifact capture, and lifecycle projection refs.

It should also consume released validator bindings for any projected
`PB-ATTEMPT-0`, `PB-TRIAL-0`, or `PB-RECON-0` evidence rows used to classify
the local specimen.

## Field-Level Expectations

`programbench_single_case_local_outcome_audit@1` should include:

- `single_case_local_outcome_audit_ref`
- `single_case_run_request_ref`
- `single_case_worker_dispatch_specimen_ref`
- `single_case_execution_trace_ref`
- `single_case_probe_observation_bundle_ref`
- `single_case_candidate_artifact_capture_ref`
- `single_case_lifecycle_projection_ref`
- `local_probe_audit_rows`
- `candidate_artifact_audit_rows`
- `sandbox_audit_rows`
- `lifecycle_projection_audit_rows`
- `contamination_audit_rows`
- `audit_status`
- `local_acceptance_scope_posture`
- `single_case_local_scope_statement`
- `benchmark_truth_posture`
- `limitation_note`

`programbench_single_case_run_observation_summary@1` should include:

- `single_case_run_observation_summary_ref`
- `single_case_local_outcome_audit_ref`
- `single_case_scope_statement`
- `observed_local_behavior_rows`
- `local_probe_inventory_rows`
- `local_artifact_inventory_rows`
- `execution_trace_summary_rows`
- `non_comparative_language_posture`
- `not_benchmark_score_statement`
- `not_baseline_comparison_statement`
- `not_model_ranking_statement`
- `limitation_note`

`programbench_single_case_remand_or_acceptance_decision@1` should include:

- `single_case_remand_or_acceptance_decision_ref`
- `single_case_local_outcome_audit_ref`
- `local_decision_posture`
- `local_non_acceptance_reason_rows`
- `remand_pressure_rows`
- `remand_source_kind_rows`
- `retry_authority_posture`
- `remand_pressure_posture`
- `official_submission_authority_posture`
- `benchmark_truth_posture`
- `future_family_selection_posture`
- `limitation_note`

Allowed local decision posture:

- `local_accepted_against_declared_probe_set`
- `remand_required_local_only`
- `blocked_by_sandbox_violation`
- `blocked_by_contamination`
- `inconclusive_local_only`

`programbench_single_case_run_handoff@1` should include:

- `single_case_run_handoff_ref`
- `single_case_remand_or_acceptance_decision_ref`
- `handoff_pressure_rows`
- `handoff_pressure_kind`
- `handoff_non_selection_posture`
- `retry_authority_posture`
- `batch_execution_authority_posture`
- `benchmark_scoring_authority_posture`
- `baseline_comparison_authority_posture`
- `model_ranking_authority_posture`
- `official_programbench_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

`programbench_single_case_run_family_closeout_alignment@1` should include:

- `single_case_run_family_closeout_alignment_ref`
- `closed_family`
- `closed_slice_refs`
- `shipped_record_shape_refs`
- `a_slice_closeout_ref`
- `b_slice_closeout_ref`
- `c_slice_closeout_ref`
- `single_specimen_scope_posture`
- `official_programbench_authority_posture`
- `benchmark_truth_posture`
- `baseline_comparison_authority_posture`
- `model_ranking_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

## Validation Expectations

The future implementation should validate:

- C requires released A and B refs;
- local accepted posture requires valid execution trace, probe observation
  bundle, candidate artifact capture inside write scope, and lifecycle
  projection validator pass;
- local accepted posture requires no contamination audit blockers, no sandbox
  audit blockers, no lifecycle projection blockers, no output capture
  blockers, and no missing required evidence blockers;
- local accepted posture requires all required positive local probes to pass
  and all required negative local probes to pass or be explicitly
  not-applicable with reason;
- stdout, stderr, exit-code, and filesystem expectations must be satisfied for
  local acceptance;
- local accepted posture is scoped only to the declared local probe/oracle
  basis;
- blocked or inconclusive posture is required when contamination, sandbox
  violation, output capture gap, lifecycle projection gap, or missing required
  evidence is present;
- observation summary cannot contain pass-rate, solve-rate, success-rate,
  official score, baseline comparison, model ranking, leaderboard, or
  representative benchmark language;
- remand pressure cannot grant retry authority;
- `retry_authority_posture` must be
  `no_retry_authority_granted_by_pb_single_case_run_0c`;
- `remand_pressure_posture` must be
  `pressure_only_requires_later_retry_or_trial_governance`;
- handoff pressure cannot select a future family or grant batch execution,
  official participation, benchmark scoring, baseline comparison, or model
  ranking authority;
- family closeout closes exactly A/B/C and cannot overclaim official
  ProgramBench or benchmark-truth authority.

## Reference Fixtures

Future C fixtures should include:

- one local outcome audit for a complete B specimen;
- one local-only observation summary;
- one local accepted or remand-required decision;
- one pressure-only handoff;
- one family closeout alignment.

Reject fixtures should include:

- local accepted with missing probe observation bundle;
- local accepted with candidate artifact outside write scope;
- local accepted with lifecycle projection gap;
- observation summary with pass-rate, baseline, model-ranking, or leaderboard
  language;
- observation summary claiming `passed ProgramBench`, `solved the case`,
  `case score`, `success rate`, `baseline win`, `model improved`,
  `representative result`, or `official-like result`;
- remand decision granting retry authority;
- handoff selecting batch execution or benchmark scoring;
- family closeout claiming official ProgramBench participation.

## Non-Outputs

`PB-SINGLE-CASE-RUN-0-C` must not output:

- worker dispatch rows;
- additional execution specimens;
- retry request rows;
- batch execution rows;
- official ProgramBench participation rows;
- official evaluator rows;
- hidden-test inference rows;
- benchmark score rows;
- baseline comparison rows;
- model ranking rows;
- official submission rows;
- future-family selection rows.
