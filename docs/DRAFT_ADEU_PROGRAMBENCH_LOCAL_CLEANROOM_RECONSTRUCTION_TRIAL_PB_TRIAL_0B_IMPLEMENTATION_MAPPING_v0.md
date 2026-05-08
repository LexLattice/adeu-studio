# Draft ADEU ProgramBench Local Cleanroom Reconstruction Trial PB-TRIAL-0-B Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-TRIAL-0-B`.

Authority layer: support.

This note maps the second candidate slice for `PB-TRIAL-0`. It is not a slice
lock. `PB-TRIAL-0-B` should activate only after `PB-TRIAL-0-A` closes on
`main` and a later canonical starter lock selects this slice.

## Slice Intent

`PB-TRIAL-0-B` is the local execution slice. It should record exactly one
bounded local worker dispatch specimen, capture execution evidence, snapshot
candidate artifacts inside the released sandbox, and project that specimen
back onto released `PB-ATTEMPT-0` lifecycle rows.

It should answer:

```text
What happened in this single local cleanroom trial, what did the worker see,
what did it emit, what candidate artifacts were snapshotted, and how does the
specimen map to released attempt lifecycle evidence?
```

It must not become official ProgramBench execution, hidden-test repair,
benchmark scoring, model ranking, retry authority, or official submission
authority.

## Expected File Scope

Likely implementation files:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_trial.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_local_trial_worker_dispatch_record.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_execution_capture.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_candidate_artifact_snapshot.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_lifecycle_projection.v1.json`
- mirrored `spec/` schema exports for the above
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_trial_pb_trial_0b.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus255/`

## Record Shapes

### `programbench_local_trial_worker_dispatch_record@1`

Minimum fields:

- `trial_worker_dispatch_ref`
- `trial_docket_ref`
- `trial_runbook_ref`
- `sandbox_readiness_review_ref`
- `worker_profile_ref`
- `dispatch_index`
- `dispatch_authority_ref`
- `sandbox_instance_ref`
- `sandbox_attestation_bundle_ref`
- `input_packet_materialization_hash`
- `worker_input_packet_hash`
- `worker_visible_context_hash`
- `tool_manifest_ref`
- `allowed_tool_manifest_hash`
- `forbidden_tool_manifest_hash`
- `dispatch_start_posture`
- `dispatch_completion_posture`
- `tool_access_posture`
- `network_access_posture`
- `source_lookup_posture`
- `hidden_test_access_posture`
- `retry_authority_posture`
- `limitation_note`

Required cardinality:

- one dispatch specimen per trial docket.

### `programbench_local_trial_execution_capture@1`

Minimum fields:

- `trial_execution_capture_ref`
- `trial_worker_dispatch_ref`
- `trial_docket_ref`
- `captured_transcript_hash`
- `bounded_transcript_excerpt`
- `stdout_hash`
- `stdout_excerpt_bounded`
- `stderr_hash`
- `stderr_excerpt_bounded`
- `exit_code`
- `duration_ms`
- `timeout_status`
- `full_output_capture_policy_ref`
- `worker_tool_call_manifest_ref`
- `declared_uncertainty_rows`
- `forbidden_content_screening_rows`
- `forbidden_content_screen_verdict`
- `forbidden_content_screening_posture`
- `sandbox_witness_refs`
- `execution_capture_posture`
- `limitation_note`

Worker output may be captured as local trial evidence only. It is not
official evaluation evidence and is not benchmark truth.

### `programbench_local_trial_candidate_artifact_snapshot@1`

Minimum fields:

- `candidate_artifact_snapshot_ref`
- `trial_execution_capture_ref`
- `trial_docket_ref`
- `write_scope_ref`
- `pre_state_manifest_ref`
- `post_state_manifest_ref`
- `fs_diff_ref`
- `snapshot_manifest_hash`
- `materialized_file_rows`
- `generated_file_hash_rows`
- `official_submission_posture`
- `benchmark_truth_posture`
- `snapshot_inside_write_scope`
- `snapshot_posture`
- `limitation_note`

Candidate artifact snapshots are local-only. They must not claim official
submission or benchmark truth posture.

### `programbench_local_trial_lifecycle_projection@1`

Minimum fields:

- `trial_lifecycle_projection_ref`
- `trial_docket_ref`
- `trial_worker_dispatch_ref`
- `trial_execution_capture_ref`
- `candidate_artifact_snapshot_ref`
- `mapped_attempt_invocation_refs`
- `mapped_attempt_output_capture_refs`
- `mapped_attempt_materialization_refs`
- `mapped_attempt_sandbox_trace_refs`
- `projection_validation_rows`
- `projection_posture`
- `new_evidence_law_posture`
- `limitation_note`

Lifecycle projection maps trial specimen evidence to released `PB-ATTEMPT-0`
shapes. It must not define new evidence law or bypass attempt lifecycle
validators.

## Consumed Released Inputs

`PB-TRIAL-0-B` should consume released `PB-TRIAL-0-A` rows:

- `programbench_local_reconstruction_trial_docket@1`
- `programbench_local_trial_execution_runbook@1`
- `programbench_local_trial_sandbox_readiness_review@1`
- `programbench_local_trial_non_authority_guardrail@1`

It should also validate against released `PB-ATTEMPT-0` attempt package refs
inherited through A.

## Validation Expectations

`PB-TRIAL-0-B` should validate:

- released A docket/runbook/readiness/guardrail refs are required;
- dispatch records cannot exist if sandbox readiness was blocked;
- dispatch records require `dispatch_authority_ref` from the released B-slice
  lock before execution-shaped records can validate;
- dispatch records enforce one dispatch specimen per trial docket;
- dispatch records bind to worker input packet hash, worker-visible context
  hash, tool manifest ref, allowed tool manifest hash, and forbidden tool
  manifest hash;
- dispatch records require sandbox instance ref, sandbox attestation bundle
  ref, and input packet materialization hash;
- dispatch records must be local-only and cannot claim official ProgramBench
  task execution, runner/evaluator contact, hidden-test access, source lookup,
  internet lookup, decompilation, external repo access, Docker socket access,
  host-secret access, benchmark score, model ranking, official submission, or
  retry authority;
- execution capture rows require hashes and bounded excerpts;
- execution capture rows require full output capture policy refs, worker
  tool-call manifest refs, and an explicit forbidden-content screen verdict;
- forbidden-content screening rows must block candidate snapshotting when
  hidden, forbidden, postmortem-only, or excluded-derived material appears in
  worker output;
- candidate snapshotting requires `forbidden_content_screen_verdict = passed`;
- candidate artifact snapshots require released sandbox write scope and
  generated-file hashes;
- candidate artifact snapshots require `snapshot_inside_write_scope = true`;
- candidate artifact snapshots cannot claim official submission posture;
- lifecycle projections bind to released `PB-ATTEMPT-0` lifecycle refs and
  cannot define new evidence law;
- B-slice fixtures reject C artifact kinds.

## Reference Fixture Sketch

Expected reference fixture set under `apps/api/fixtures/benchmarking/vnext_plus255/`:

- `programbench_local_trial_worker_dispatch_record_v255_reference.json`
- `programbench_local_trial_execution_capture_v255_reference.json`
- `programbench_local_trial_candidate_artifact_snapshot_v255_reference.json`
- `programbench_local_trial_lifecycle_projection_v255_reference.json`
- `programbench_local_trial_v255_reject_dispatch_without_readiness.json`
- `programbench_local_trial_v255_reject_second_dispatch_specimen.json`
- `programbench_local_trial_v255_reject_hidden_test_access.json`
- `programbench_local_trial_v255_reject_forbidden_output_snapshotted.json`
- `programbench_local_trial_v255_reject_snapshot_outside_write_scope.json`
- `programbench_local_trial_v255_reject_lifecycle_projection_new_evidence_law.json`

## Explicit Non-Outputs

`PB-TRIAL-0-B` must not output:

- outcome audit;
- trial observation summary;
- remand decision;
- family closeout alignment;
- official ProgramBench runner/evaluator integration;
- official task execution;
- hidden-test handling;
- hidden-test equivalence;
- benchmark score;
- model ranking;
- retry authority;
- official submission or generated official submission;
- future-family selection.
