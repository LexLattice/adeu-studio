# Draft ADEU ProgramBench Local Cleanroom Reconstruction Trial PB-TRIAL-0-A Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-TRIAL-0-A`.

Authority layer: support.

This note maps the first candidate slice for `PB-TRIAL-0`. It is not a slice
lock and does not authorize worker dispatch, command execution, candidate
materialization, official ProgramBench participation, hidden-test handling,
benchmark scoring, model ranking, retry authority, or future-family selection.

## Slice Intent

`PB-TRIAL-0-A` should answer:

```text
Given a released PB-ATTEMPT-0 lifecycle package, can the repo create a bounded
single-trial docket, execution runbook, and sandbox readiness review for one
later local cleanroom reconstruction trial?
```

It should not run the worker. It should not execute commands. It should not
create candidate files. It should make only the docket, runbook, readiness
review, and non-authority boundary reviewable.

## Expected File Scope

Likely implementation files:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_trial.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_local_reconstruction_trial_docket.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_execution_runbook.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_sandbox_readiness_review.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_non_authority_guardrail.v1.json`
- `spec/programbench_local_reconstruction_trial_docket.schema.json`
- `spec/programbench_local_trial_execution_runbook.schema.json`
- `spec/programbench_local_trial_sandbox_readiness_review.schema.json`
- `spec/programbench_local_trial_non_authority_guardrail.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_trial_pb_trial_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus254/`

## Record Shapes

### `programbench_local_reconstruction_trial_docket@1`

Minimum fields:

- `trial_docket_ref`
- `attempt_request_ref`
- `worker_input_packet_ref`
- `dispatch_preflight_ref`
- `attempt_guardrail_ref`
- `prior_attempt_result_review_context_ref`
- `attempt_family_closeout_ref`
- `workbench_lineage_refs`
- `case_packet_refs`
- `worker_profile_ref`
- `trial_purpose`
- `trial_cardinality_posture`
- `official_programbench_posture`
- `benchmark_truth_posture`
- `model_ranking_posture`
- `retry_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

Required postures:

- `trial_cardinality_posture = single_trial_only`
- `official_programbench_posture =
  no_official_programbench_participation_by_pb_trial_0a`
- `benchmark_truth_posture = not_benchmark_truth`
- `model_ranking_posture = no_model_ranking_claimed_by_pb_trial_0a`
- `retry_authority_posture = no_retry_authority_granted_by_pb_trial_0a`
- `future_family_selection_posture = no_future_family_selected_by_pb_trial_0a`

### `programbench_local_trial_execution_runbook@1`

Minimum fields:

- `trial_runbook_ref`
- `trial_docket_ref`
- `worker_input_packet_hash`
- `worker_visible_context_hash`
- `runbook_hash`
- `trial_input_materialization_policy_ref`
- `sandbox_policy_ref`
- `run_budget_ref`
- `allowed_step_rows`
- `forbidden_step_rows`
- `capture_obligation_rows`
- `write_scope_refs`
- `tool_manifest_refs`
- `timeout_policy_ref`
- `environment_policy_ref`
- `sandbox_witness_requirement_refs`
- `runbook_scope_posture`
- `dispatch_authority_posture`
- `execution_authority_posture`
- `limitation_note`

Required postures:

- `runbook_scope_posture = execution_plan_only_no_dispatch_by_pb_trial_0a`
- `dispatch_authority_posture =
  no_worker_dispatch_authority_granted_by_pb_trial_0a`
- `execution_authority_posture =
  no_command_execution_authority_granted_by_pb_trial_0a`

### `programbench_local_trial_sandbox_readiness_review@1`

Minimum fields:

- `sandbox_readiness_review_ref`
- `trial_docket_ref`
- `trial_runbook_ref`
- `sandbox_policy_ref`
- `run_budget_ref`
- `readiness_check_rows`
- `sandbox_witness_requirement_refs`
- `network_readiness_posture`
- `source_lookup_readiness_posture`
- `decompilation_readiness_posture`
- `docker_socket_readiness_posture`
- `host_secret_readiness_posture`
- `write_scope_readiness_posture`
- `tool_manifest_readiness_posture`
- `budget_readiness_posture`
- `readiness_posture`
- `execution_authority_posture`
- `limitation_note`

Allowed `readiness_posture` values:

- `ready_for_later_local_trial_execution_review`
- `blocked_by_missing_released_attempt_ref`
- `blocked_by_worker_input_hash_gap`
- `blocked_by_sandbox_gap`
- `blocked_by_budget_gap`
- `blocked_by_tool_manifest_gap`
- `blocked_by_guardrail_gap`
- `future_family_only`

Readiness passed is not execution authority.

### `programbench_local_trial_non_authority_guardrail@1`

Minimum fields:

- `trial_guardrail_ref`
- `trial_docket_ref`
- `forbidden_authority_rows`
- `official_programbench_non_authority_posture`
- `hidden_test_non_inference_posture`
- `source_lookup_non_authority_posture`
- `submission_non_authority_posture`
- `benchmark_truth_non_authority_posture`
- `model_ranking_non_authority_posture`
- `retry_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

## Consumed Released Inputs

`PB-TRIAL-0-A` should consume released `PB-ATTEMPT-0` rows:

- `programbench_reconstruction_attempt_request@1`
- `programbench_reconstruction_attempt_worker_input_packet@1`
- `programbench_reconstruction_attempt_dispatch_preflight@1`
- `programbench_reconstruction_attempt_non_authority_guardrail@1`
- `programbench_reconstruction_attempt_result_review@1`
- `programbench_reconstruction_attempt_family_closeout_alignment@1`

It may cite released `PB-ATTEMPT-0-B/C` rows as prior lifecycle evidence, but
slice A should not produce new invocation, output capture, materialization, or
result review rows.

The consumed `programbench_reconstruction_attempt_result_review@1` row is
allowed only as lifecycle-shape / closeout-lineage / eligibility context. It
must not be counted as evidence of this `PB-TRIAL-0` trial outcome. The trial
outcome can be recorded only by later `PB-TRIAL-0-C` outcome audit rows after
`PB-TRIAL-0-B` emits the dispatch/capture/snapshot/projection specimen.

The selected attempt package must remain local-only and non-official. It must
not be contamination-blocked, hidden-test-derived, benchmark-truth-postured,
model-ranking-postured, or future-family-selected.

## Validation Expectations

`PB-TRIAL-0-A` should validate:

- all consumed `PB-ATTEMPT-0` refs resolve to one attempt lifecycle lineage;
- attempt family closeout closes only `PB-ATTEMPT-0`;
- trial docket cites exactly one attempt request, worker input packet,
  dispatch preflight, attempt guardrail, and prior attempt result-review
  context ref;
- prior attempt result-review context cannot be counted as trial outcome
  evidence;
- trial docket cardinality is single-trial only;
- trial docket cannot cite hidden-test, original-source, decompilation,
  internet, external-repo, host-secret, Docker-socket, official evaluator, or
  benchmark-score evidence;
- execution runbook references the trial docket, worker input packet hash,
  runbook hash, trial input materialization policy ref, and sandbox witness
  requirement refs;
- execution runbook allowed steps are local-only and argv-shaped where
  command-shaped;
- execution runbook forbidden steps include official runner/evaluator contact,
  hidden-test access, original-source lookup, internet/decompilation/external
  repo lookup, retry dispatch, model ranking, benchmark scoring, and official
  submission;
- sandbox readiness review requires readiness rows for network disabled,
  source lookup disabled, decompilation disabled, Docker socket absent, host
  secrets absent, bounded write scope, closed tool manifest, and run budget;
- readiness review marked `ready_for_later_local_trial_execution_review`
  requires every readiness check row to map to a later B sandbox witness
  requirement ref;
- readiness review marked ready rejects a non-closed tool manifest;
- readiness passed does not grant execution authority;
- trial guardrail forbids official ProgramBench, hidden-test inference,
  source lookup, official submissions, benchmark truth, model ranking, retry
  authority, and future-family selection;
- A-slice fixtures reject B/C artifact kinds.

## Reference Fixture Sketch

Expected reference fixture set under `apps/api/fixtures/benchmarking/vnext_plus254/`:

- `programbench_local_reconstruction_trial_docket_v254_reference.json`
- `programbench_local_trial_execution_runbook_v254_reference.json`
- `programbench_local_trial_sandbox_readiness_review_v254_reference.json`
- `programbench_local_trial_non_authority_guardrail_v254_reference.json`
- `programbench_local_trial_v254_reject_missing_attempt_closeout.json`
- `programbench_local_trial_v254_reject_multiple_attempt_requests.json`
- `programbench_local_trial_v254_reject_hidden_test_ref_in_docket.json`
- `programbench_local_trial_v254_reject_runbook_dispatch_authority.json`
- `programbench_local_trial_v254_reject_prior_result_review_as_trial_outcome.json`
- `programbench_local_trial_v254_reject_ready_with_non_closed_tool_manifest.json`
- `programbench_local_trial_v254_reject_readiness_claims_execution_authority.json`
- `programbench_local_trial_v254_reject_retry_authority.json`

## Explicit Non-Outputs

`PB-TRIAL-0-A` must not output:

- worker dispatch record;
- execution capture;
- candidate artifact snapshot;
- lifecycle projection;
- outcome audit;
- trial observation summary;
- remand decision;
- family closeout alignment;
- local command execution;
- official ProgramBench runner/evaluator integration;
- official task execution;
- hidden-test handling;
- hidden-test equivalence;
- benchmark score;
- model ranking;
- retry authority;
- official submission or generated official submission;
- future-family selection.
