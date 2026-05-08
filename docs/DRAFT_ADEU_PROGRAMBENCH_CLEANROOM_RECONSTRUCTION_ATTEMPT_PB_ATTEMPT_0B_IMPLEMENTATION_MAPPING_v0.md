# Draft ADEU ProgramBench Cleanroom Reconstruction Attempt PB-ATTEMPT-0-B Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-ATTEMPT-0-B`.

Authority layer: support.

This note maps the second candidate slice for `PB-ATTEMPT-0`. It is not a
slice lock. `PB-ATTEMPT-0-B` should activate only after `PB-ATTEMPT-0-A`
closes on `main` and a later canonical starter lock selects this slice.

## Slice Intent

`PB-ATTEMPT-0-B` is the execution-adjacent slice. It should record a bounded
local worker invocation and candidate materialization under released A attempt
refs, without becoming official ProgramBench execution, hidden-test repair,
benchmark scoring, model ranking, or official submission authority.

It should answer:

```text
What did the local worker receive, what did it emit, what candidate material
was materialized inside the sandbox, and what sandbox application evidence was
captured?
```

## Expected File Scope

Likely implementation files:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_attempt.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_attempt_worker_invocation_record.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_attempt_output_capture.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_attempt_candidate_materialization.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_attempt_sandbox_application_trace.v1.json`
- mirrored `spec/` schema exports for the above
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_attempt_pb_attempt_0b.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus252/`

## Record Shapes

### `programbench_reconstruction_attempt_worker_invocation_record@1`

Minimum fields:

- `worker_invocation_ref`
- `attempt_request_ref`
- `worker_input_packet_ref`
- `dispatch_preflight_ref`
- `worker_profile_ref`
- `attempt_invocation_index`
- `input_packet_hash`
- `worker_visible_context_hash`
- `tool_manifest_ref`
- `allowed_tool_manifest_hash`
- `forbidden_tool_manifest_hash`
- `invocation_kind`
- `invocation_start_posture`
- `invocation_completion_posture`
- `tool_access_posture`
- `network_access_posture`
- `source_lookup_posture`
- `hidden_test_access_posture`
- `invocation_transcript_hash`
- `bounded_transcript_excerpt`
- `limitation_note`

Required posture:

- local-only invocation;
- no hidden-test access;
- no source lookup;
- no official ProgramBench evaluator contact;
- no model ranking.

Required cardinality:

- one worker invocation per attempt request unless a later lock introduces
  retry parent and retry authority rows.

### `programbench_reconstruction_attempt_output_capture@1`

Minimum fields:

- `output_capture_ref`
- `worker_invocation_ref`
- `attempt_request_ref`
- `captured_output_rows`
- `declared_uncertainty_rows`
- `forbidden_content_screening_rows`
- `forbidden_content_screening_posture`
- `output_hash_rows`
- `bounded_excerpt_rows`
- `output_capture_posture`
- `candidate_materialization_authority_posture`
- `limitation_note`

Worker output may be captured as local candidate material only. It is not
materialized until a candidate materialization record accepts it inside the
released sandbox write scope.

Allowed `forbidden_content_screening_posture` values:

- `passed`;
- `blocked_hidden_evidence`;
- `blocked_forbidden_source`;
- `blocked_postmortem_only`;
- `blocked_excluded_derived`;
- `inconclusive_requires_review`.

Candidate materialization is allowed only when screening posture is `passed`.

### `programbench_reconstruction_attempt_candidate_materialization@1`

Minimum fields:

- `candidate_materialization_ref`
- `attempt_request_ref`
- `output_capture_ref`
- `sandbox_policy_ref`
- `materialization_input_hash`
- `materialization_output_manifest_hash`
- `materialized_file_rows`
- `generated_file_hash_rows`
- `write_scope_ref`
- `write_scope_attestation_ref`
- `official_submission_posture`
- `benchmark_truth_posture`
- `materialized_inside_write_scope`
- `materialization_posture`
- `limitation_note`

Candidate materialization is local-only. It must not claim official
submission or benchmark truth posture.

### `programbench_reconstruction_attempt_sandbox_application_trace@1`

Minimum fields:

- `sandbox_application_trace_ref`
- `attempt_request_ref`
- `candidate_materialization_ref`
- `sandbox_policy_ref`
- `run_budget_ref`
- `application_step_rows`
- `pre_state_manifest_ref`
- `post_state_manifest_ref`
- `fs_diff_ref`
- `network_attestation_ref`
- `secret_absence_attestation_ref`
- `docker_socket_absence_attestation_ref`
- `source_lookup_absence_attestation_ref`
- `application_posture`
- `limitation_note`

Application traces describe local sandbox application only. They are not
official execution or evaluation traces.

## Consumed Released Inputs

`PB-ATTEMPT-0-B` should consume released `PB-ATTEMPT-0-A` rows:

- `programbench_reconstruction_attempt_request@1`
- `programbench_reconstruction_attempt_worker_input_packet@1`
- `programbench_reconstruction_attempt_dispatch_preflight@1`
- `programbench_reconstruction_attempt_non_authority_guardrail@1`

It should also validate against released `PB-RECON-0` sandbox, run budget,
worker context, and exclusion manifest refs inherited through A.

## Validation Expectations

`PB-ATTEMPT-0-B` should validate:

- released A attempt request/input/preflight/guardrail refs are required;
- invocation records cannot exist if preflight was blocked;
- invocation records enforce one invocation per attempt request unless retry
  parent and authority rows are selected later;
- invocation records bind to input packet hash, worker-visible context hash,
  tool manifest ref, allowed tool manifest hash, and forbidden tool manifest
  hash;
- invocation records must be local-only and cannot claim official ProgramBench
  task execution, runner/evaluator contact, hidden-test access, source lookup,
  internet lookup, decompilation, external repo access, Docker socket access,
  host-secret access, benchmark score, model ranking, or official submission;
- output capture rows require hashes and bounded excerpts;
- output capture rows require `forbidden_content_screening_posture`;
- forbidden-content screening rows must block materialization when hidden,
  forbidden, postmortem-only, or excluded-derived material appears in worker
  output;
- candidate materialization requires screening posture `passed`;
- candidate materialization rows require released sandbox write scope and
  generated-file hashes;
- candidate materialization rows require materialization input hash,
  materialization output manifest hash, and
  `materialized_inside_write_scope = true`;
- candidate materialization rows cannot claim official submission posture;
- sandbox application traces must bind to sandbox policy and run budget refs;
- application traces require network, secret, Docker socket, and source lookup
  absence attestations;
- B-slice fixtures reject C artifact kinds.

## Reference Fixture Sketch

Expected reference fixture set under `apps/api/fixtures/benchmarking/vnext_plus252/`:

- `programbench_reconstruction_attempt_worker_invocation_record_v252_reference.json`
- `programbench_reconstruction_attempt_output_capture_v252_reference.json`
- `programbench_reconstruction_attempt_candidate_materialization_v252_reference.json`
- `programbench_reconstruction_attempt_sandbox_application_trace_v252_reference.json`
- `programbench_reconstruction_attempt_v252_reject_invocation_without_released_preflight.json`
- `programbench_reconstruction_attempt_v252_reject_hidden_test_access.json`
- `programbench_reconstruction_attempt_v252_reject_forbidden_output_materialized.json`
- `programbench_reconstruction_attempt_v252_reject_materialization_outside_write_scope.json`
- `programbench_reconstruction_attempt_v252_reject_official_submission_posture.json`

## Explicit Non-Outputs

`PB-ATTEMPT-0-B` must not output:

- workbench evidence export;
- attempt result review;
- remand queue;
- family closeout alignment;
- official ProgramBench runner/evaluator integration;
- official task execution;
- hidden-test handling;
- hidden-test equivalence;
- benchmark score;
- model ranking;
- official submission or generated official submission;
- future-family selection.
