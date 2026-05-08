# Draft ADEU ProgramBench Local Cleanroom Retry Governance PB-RETRY-0-B Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-RETRY-0-B`.

Authority layer: support.

This note maps the likely implementation for `PB-RETRY-0-B`. It does not
authorize implementation by itself and does not replace a future lock,
stop-gate decision, or edge assessment.

## Slice Intent

`PB-RETRY-0-B` should record one bounded local retry dispatch specimen under
released `PB-RETRY-0-A` eligibility and scope rows.

The slice should answer:

```text
Was exactly one local retry specimen dispatched inside the released retry
scope, and what local execution, sandbox, output, and candidate-delta evidence
was captured?
```

It must not answer:

```text
Did the retry solve ProgramBench?
Should the model be ranked?
Can another retry run automatically?
Can hidden-test or official-evaluator feedback be used?
```

## Selected Surfaces

Likely schema / model surfaces:

- `programbench_local_retry_dispatch_record@1`
- `programbench_local_retry_execution_capture@1`
- `programbench_local_retry_candidate_delta_snapshot@1`
- `programbench_local_retry_lifecycle_projection@1`
- `programbench_local_retry_sandbox_application_trace@1`

Likely source files for a future implementation:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_retry.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_local_retry_dispatch_record.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_execution_capture.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_candidate_delta_snapshot.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_lifecycle_projection.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_sandbox_application_trace.v1.json`
- `spec/programbench_local_retry_dispatch_record.schema.json`
- `spec/programbench_local_retry_execution_capture.schema.json`
- `spec/programbench_local_retry_candidate_delta_snapshot.schema.json`
- `spec/programbench_local_retry_lifecycle_projection.schema.json`
- `spec/programbench_local_retry_sandbox_application_trace.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_retry_pb_retry_0b.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus258/`

## Execution-Adjacent Boundary

`PB-RETRY-0-B` is action-adjacent. It should require a B-slice dispatch
authority ref and released A eligibility before any retry dispatch record can
validate.

Minimum dispatch law:

```text
one_retry_request
one_retry_lineage
one_retry_depth
one_retry_dispatch_specimen
released_A_eligibility_ready
released_A_scope_contract
B_lock_dispatch_authority
cleanroom_boundary_unchanged
```

The implementation should reject any attempt to use A eligibility as dispatch
authority by itself.

## Field-Level Expectations

`programbench_local_retry_dispatch_record@1` should include:

- `retry_dispatch_record_ref`
- `retry_request_ref`
- `retry_lineage_ref`
- `source_trial_dispatch_ref`
- `retry_eligibility_review_ref`
- `retry_scope_contract_ref`
- `retry_dispatch_authority_ref`
- `retry_depth`
- `worker_profile_ref`
- `worker_input_packet_hash`
- `worker_visible_context_hash`
- `retry_scope_delta_hash`
- `retry_input_packet_hash`
- `retry_worker_visible_context_hash`
- `retry_scope_contract_hash`
- `retry_allowed_tool_manifest_hash`
- `retry_forbidden_tool_manifest_hash`
- `retry_sandbox_policy_hash`
- `retry_run_budget_hash`
- `tool_manifest_ref`
- `allowed_tool_manifest_hash`
- `forbidden_tool_manifest_hash`
- `sandbox_instance_ref`
- `sandbox_attestation_bundle_ref`
- `input_packet_materialization_hash`
- `dispatch_cardinality_posture`
- `official_programbench_posture`
- `limitation_note`

`programbench_local_retry_execution_capture@1` should include:

- `retry_execution_capture_ref`
- `retry_dispatch_record_ref`
- `stdout_hash`
- `stdout_excerpt_bounded`
- `stderr_hash`
- `stderr_excerpt_bounded`
- `transcript_hash`
- `transcript_excerpt_bounded`
- `exit_code`
- `duration_ms`
- `timeout_status`
- `worker_tool_call_manifest_ref`
- `full_output_capture_policy_ref`
- `forbidden_content_screen_verdict`
- `forbidden_content_screening_basis_refs`
- `screened_output_hashes`
- `screening_reviewer_or_policy_ref`
- `sandbox_violation_refs`
- `limitation_note`

`programbench_local_retry_candidate_delta_snapshot@1` should include:

- `retry_candidate_delta_snapshot_ref`
- `retry_execution_capture_ref`
- `source_trial_candidate_snapshot_ref`
- `generated_file_manifest_ref`
- `materialization_input_hash`
- `materialization_output_manifest_hash`
- `write_scope_ref`
- `inside_released_write_scope`
- `forbidden_content_screen_verdict`
- `official_submission_posture`
- `limitation_note`

`programbench_local_retry_lifecycle_projection@1` should include:

- `retry_lifecycle_projection_ref`
- `retry_request_ref`
- `retry_dispatch_record_ref`
- `retry_execution_capture_ref`
- `retry_candidate_delta_snapshot_ref`
- `trial_lifecycle_projection_ref`
- `attempt_lifecycle_projection_refs`
- `pb_trial_validator_binding_refs`
- `pb_attempt_validator_binding_refs`
- `projection_validation_posture`
- `new_evidence_law_posture`
- `limitation_note`

`programbench_local_retry_sandbox_application_trace@1` should include:

- `retry_sandbox_trace_ref`
- `retry_dispatch_record_ref`
- `sandbox_instance_ref`
- `sandbox_attestation_bundle_ref`
- `network_mode_witness_ref`
- `docker_socket_absence_witness_ref`
- `secret_absence_witness_ref`
- `source_lookup_absence_witness_ref`
- `decompilation_absence_witness_ref`
- `write_scope_attestation_ref`
- `resource_limit_attestation_ref`
- `tool_manifest_match_ref`
- `sandbox_violation_refs`
- `limitation_note`

## Validation Expectations

The future implementation should validate:

- B requires released `PB-RETRY-0-A` rows;
- retry dispatch record cannot exist unless A eligibility is ready and A scope
  contract has no blockers;
- retry dispatch record requires `retry_dispatch_authority_ref` from the
  released B lock;
- exactly one retry dispatch specimen may validate per retry request unless a
  later family grants retry-chain authority;
- retry depth must remain within the A scope contract limit;
- worker input hash, context hash, tool manifests, sandbox instance, and
  sandbox attestation bundle must bind to released A scope;
- dispatch must bind to retry input, worker-visible context, scope contract,
  allowed tool, forbidden tool, sandbox policy, and run budget hashes;
- execution capture requires bounded excerpts and full hashes;
- execution capture cannot cite hidden-test, official-evaluator, original
  source, decompilation, internet, external-repository, host-secret,
  Docker-socket, postmortem-only, or excluded-derived sources;
- candidate delta snapshot is valid only if forbidden-content screening passed;
- candidate delta snapshot is valid only if screened output hashes match the
  materialization input hash;
- candidate delta snapshot must be inside released write scope;
- candidate delta snapshot must be a local artifact, not an official
  submission;
- lifecycle projection cannot define new evidence law;
- sandbox application trace must prove network/source/decompilation/Docker
  socket/host-secret posture with witness refs;
- B rejects C artifacts and model-ranking or benchmark-score rows.

## Reference Fixtures

Future `vNext+258` reference fixtures should include:

- one retry dispatch record with B lock authority and one retry depth;
- one execution capture with bounded output excerpts and full hashes;
- one candidate delta snapshot inside released write scope;
- one lifecycle projection back to released trial and attempt rows;
- one sandbox application trace with clean witness refs.

## Reject Fixtures

Future `vNext+258` reject fixtures should include:

- retry dispatch with A eligibility but no B dispatch authority;
- second retry dispatch for the same retry request;
- retry dispatch that widens worker-visible context;
- retry execution capture with hidden/evaluator/source/decompilation/internet
  evidence;
- candidate delta snapshot before forbidden-content screening passed;
- candidate delta snapshot outside released write scope;
- lifecycle projection that defines new evidence law;
- sandbox trace missing network, Docker socket, host secret, source lookup, or
  decompilation absence witnesses;
- retry row that claims official benchmark or model-ranking authority.

## Non-Outputs

`PB-RETRY-0-B` must not output:

- retry outcome audit;
- retry delta observation summary;
- remand settlement;
- family closeout alignment;
- benchmark score;
- model ranking;
- official ProgramBench submission;
- hidden-test equivalence;
- second-retry authority.
