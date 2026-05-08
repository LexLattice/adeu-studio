# Draft ADEU ProgramBench Cleanroom Reconstruction Attempt PB-ATTEMPT-0-A Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-ATTEMPT-0-A`.

Authority layer: support.

This note maps the first candidate slice for `PB-ATTEMPT-0`. It is not a
slice lock and does not authorize worker invocation, command execution,
candidate materialization, official ProgramBench participation, hidden-test
handling, benchmark scoring, model ranking, or future-family selection.

## Slice Intent

`PB-ATTEMPT-0-A` should answer:

```text
Given a released PB-RECON-0 workbench row set, can the repo package a bounded
worker-attempt request and exact worker-visible input packet for later local
attempt review?
```

It should not run the worker. It should not create candidate files. It should
not execute local probes. It should make only the request, input, preflight,
and non-authority boundary reviewable.

## Expected File Scope

Likely implementation files:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_attempt.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_attempt_request.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_attempt_worker_input_packet.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_attempt_dispatch_preflight.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_attempt_non_authority_guardrail.v1.json`
- `spec/programbench_reconstruction_attempt_request.schema.json`
- `spec/programbench_reconstruction_attempt_worker_input_packet.schema.json`
- `spec/programbench_reconstruction_attempt_dispatch_preflight.schema.json`
- `spec/programbench_reconstruction_attempt_non_authority_guardrail.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_attempt_pb_attempt_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus251/`

## Record Shapes

### `programbench_reconstruction_attempt_request@1`

Minimum fields:

- `attempt_request_ref`
- `work_order_ref`
- `worker_context_packet_ref`
- `context_exclusion_manifest_ref`
- `sandbox_policy_ref`
- `run_budget_ref`
- `result_summary_ref`
- `workbench_family_closeout_ref`
- `attempt_purpose`
- `worker_profile_ref`
- `attempt_scope_posture`
- `dispatch_authority_posture`
- `official_programbench_posture`
- `benchmark_truth_posture`
- `model_ranking_posture`
- `limitation_note`

Required postures:

- `dispatch_authority_posture =
  no_worker_dispatch_authority_granted_by_pb_attempt_0a`
- `official_programbench_posture =
  no_official_programbench_participation_by_pb_attempt_0a`
- `benchmark_truth_posture = not_benchmark_truth`
- `model_ranking_posture = no_model_ranking_claimed_by_pb_attempt_0a`

### `programbench_reconstruction_attempt_worker_input_packet@1`

Minimum fields:

- `worker_input_packet_ref`
- `attempt_request_ref`
- `worker_visible_source_refs`
- `advisory_concept_profile_refs`
- `advisory_realization_refs`
- `probe_expectation_refs`
- `sandbox_summary_refs`
- `run_budget_summary_refs`
- `excluded_ref_summary_rows`
- `context_derivation_rows`
- `worker_input_manifest_hash`
- `worker_visible_ref_count`
- `forbidden_ref_exposure_check_hash`
- `worker_visibility_posture`
- `input_materialization_posture`
- `limitation_note`

Worker-visible refs must be a subset of released workbench
`worker_visible_source_refs` and explicitly allowed advisory refs. Auditor-only
exclusion refs may appear only in exclusion summary rows that do not reveal
their content.

`excluded_ref_summary_rows` may include only:

- exclusion category;
- count;
- reason code;
- authority posture;
- non-exposure statement.

They must not include:

- source path;
- source name;
- content excerpt;
- semantic summary;
- derived fact;
- test name;
- hidden artifact identifier;
- original-source clue.

### `programbench_reconstruction_attempt_dispatch_preflight@1`

Minimum fields:

- `dispatch_preflight_ref`
- `attempt_request_ref`
- `worker_input_packet_ref`
- `sandbox_policy_ref`
- `run_budget_ref`
- `guardrail_ref`
- `preflight_check_rows`
- `sandbox_enforcement_requirement_refs`
- `budget_enforcement_requirement_refs`
- `preflight_scope_posture`
- `preflight_posture`
- `dispatch_authority_posture`
- `execution_authority_posture`
- `limitation_note`

Allowed `preflight_posture` values:

- `preflight_passed_for_later_local_attempt_review`
- `blocked_by_missing_released_workbench_ref`
- `blocked_by_visibility_gap`
- `blocked_by_sandbox_gap`
- `blocked_by_budget_gap`
- `blocked_by_guardrail_gap`
- `future_family_only`

Preflight passed is not dispatch authority.

Required scope posture:

- `preflight_scope_posture = eligibility_review_only_no_invocation`

### `programbench_reconstruction_attempt_non_authority_guardrail@1`

Minimum fields:

- `guardrail_ref`
- `attempt_request_ref`
- `forbidden_authority_rows`
- `official_programbench_non_authority_posture`
- `hidden_test_non_inference_posture`
- `source_lookup_non_authority_posture`
- `submission_non_authority_posture`
- `benchmark_truth_non_authority_posture`
- `model_ranking_non_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

## Consumed Released Inputs

`PB-ATTEMPT-0-A` should consume released `PB-RECON-0` rows:

- `programbench_reconstruction_work_order@1`
- `programbench_reconstruction_worker_context_packet@1`
- `programbench_reconstruction_context_exclusion_manifest@1`
- `programbench_reconstruction_sandbox_policy@1`
- `programbench_reconstruction_run_budget@1`
- `programbench_reconstruction_workbench_non_authority_guardrail@1`
- `programbench_reconstruction_result_summary@1`
- `programbench_reconstruction_workbench_family_closeout_alignment@1`

The result summary may be `local_remand_required` if the attempt request is
explicitly scoped to a later remand/correction attempt. It may not be
benchmark truth, official success, or hidden-test equivalence.

Compatible result-summary postures:

- `local_remand_required`;
- `inconclusive_local_audit`;
- `blocked_by_missing_evidence`, if the attempt purpose is explicitly
  evidence-gap remediation.

Blocked result-summary postures:

- `local_accepted`;
- `blocked_by_contamination`;
- `blocked_by_sandbox_violation`;
- `future_family_only`.

## Validation Expectations

`PB-ATTEMPT-0-A` should validate:

- all consumed `PB-RECON-0` refs resolve to one workbench lineage;
- workbench family closeout closes only `PB-RECON-0`;
- attempt request cites exactly one work order, context packet, exclusion
  manifest, sandbox policy, run budget, and result summary;
- worker input packet references the attempt request;
- worker input packet contains no auditor-only, forbidden, hidden,
  postmortem-only, original-source, decompilation, internet-lookup, external
  repo, host-secret, or Docker-socket refs as worker-visible material;
- exclusion summary rows may name exclusion categories without exposing
  excluded content;
- exclusion summary rows reject source-identifying and content-bearing fields;
- `worker_input_manifest_hash`, `worker_visible_ref_count`, and
  `forbidden_ref_exposure_check_hash` are present;
- dispatch preflight references the attempt request, worker input packet,
  sandbox policy, run budget, and guardrail;
- dispatch preflight carries
  `preflight_scope_posture = eligibility_review_only_no_invocation`;
- dispatch preflight cannot claim worker invocation or command execution
  authority;
- attempt requests reject incompatible `PB-RECON-0` result-summary postures;
- guardrail rejects official ProgramBench, hidden-test inference, source
  lookup, official submission, benchmark truth, model ranking, and
  future-family selection authority;
- A-slice fixtures reject B/C artifact kinds.

## Reference Fixture Sketch

Expected reference fixture set under `apps/api/fixtures/benchmarking/vnext_plus251/`:

- `programbench_reconstruction_attempt_request_v251_reference.json`
- `programbench_reconstruction_attempt_worker_input_packet_v251_reference.json`
- `programbench_reconstruction_attempt_dispatch_preflight_v251_reference.json`
- `programbench_reconstruction_attempt_non_authority_guardrail_v251_reference.json`
- `programbench_reconstruction_attempt_v251_reject_worker_visible_exclusion_ref.json`
- `programbench_reconstruction_attempt_v251_reject_exclusion_summary_leaks_source_name.json`
- `programbench_reconstruction_attempt_v251_reject_dispatch_authority_in_slice_a.json`
- `programbench_reconstruction_attempt_v251_reject_local_accepted_result_for_remand_attempt.json`
- `programbench_reconstruction_attempt_v251_reject_official_programbench_authority.json`
- `programbench_reconstruction_attempt_v251_reject_future_slice_artifact_kind.json`

## Explicit Non-Outputs

`PB-ATTEMPT-0-A` must not output:

- worker invocation record;
- worker transcript or output capture;
- candidate materialization record;
- sandbox application trace;
- local run trace;
- probe result log;
- workbench evidence export;
- attempt result review;
- remand queue;
- family closeout alignment;
- official ProgramBench runner/evaluator integration;
- hidden-test handling;
- benchmark score;
- model ranking;
- official submission or generated official submission;
- future-family selection.
