# Draft ADEU ProgramBench Local Cleanroom Single Case Run PB-SINGLE-CASE-RUN-0-B Implementation Mapping v0

Status: support / implementation mapping record for planned
`PB-SINGLE-CASE-RUN-0-B`.

Authority layer: support.

This note maps the likely implementation for `PB-SINGLE-CASE-RUN-0-B`. It is
not a starter lock. `PB-SINGLE-CASE-RUN-0-B` should activate only after
`PB-SINGLE-CASE-RUN-0-A` closes on `main` and a later canonical starter lock
selects this slice.

## Slice Intent

`PB-SINGLE-CASE-RUN-0-B` should record exactly one local cleanroom execution
specimen under released A controls. It is the action-adjacent slice. It should
not run official ProgramBench, contact official evaluators, infer hidden
tests, score benchmarks, compare baselines, rank models, or run a batch.

It is not a parallel trial semantics surface. It records one selected
case-lineage run specimen and projects that specimen back into released
attempt/trial/workbench evidence vocabulary.

The slice should answer:

```text
What happened in one bounded local execution specimen under the released A
run controls?
```

It must not answer:

```text
What official benchmark result did we get?
Which model is better?
Should we retry?
Should we submit?
```

## Selected Surfaces

Likely schema / model surfaces:

- `programbench_single_case_worker_dispatch_specimen@1`
- `programbench_single_case_execution_trace@1`
- `programbench_single_case_probe_observation_bundle@1`
- `programbench_single_case_candidate_artifact_capture@1`
- `programbench_single_case_lifecycle_projection@1`

Likely source files for a future implementation:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_single_case_run.py`
- `packages/adeu_benchmarking/tests/test_programbench_single_case_run_pb_single_case_run_0b.py`
- `apps/api/fixtures/benchmarking/vnext_plus270/`

## Consumed Lineage

`PB-SINGLE-CASE-RUN-0-B` should consume released A rows:

- `programbench_single_case_run_request@1`
- `programbench_single_case_target_selection@1`
- `programbench_single_case_execution_preflight@1`
- `programbench_single_case_run_control_contract@1`
- `programbench_single_case_run_non_authority_guardrail@1`

It should also consume the released B starter lock or dispatch-authority row
that explicitly authorizes one local specimen for this slice. A preflight
alone is not dispatch authority.

## Field-Level Expectations

`programbench_single_case_worker_dispatch_specimen@1` should include:

- `single_case_worker_dispatch_specimen_ref`
- `single_case_run_request_ref`
- `single_case_target_selection_ref`
- `single_case_execution_preflight_ref`
- `single_case_run_control_contract_ref`
- `b_slice_dispatch_authority_ref`
- `dispatch_authority_kind`
- `dispatch_specimen_index`
- `single_case_dispatch_cardinality_posture`
- `worker_profile_ref`
- `input_packet_materialization_hash`
- `worker_visible_context_materialization_hash`
- `tool_manifest_materialization_hash`
- `sandbox_policy_materialization_hash`
- `run_control_contract_hash`
- `worker_visible_packet_hash`
- `runbook_hash`
- `sandbox_policy_hash`
- `tool_manifest_hash`
- `write_scope_hash`
- `local_probe_basis_hash`
- `sandbox_instance_ref`
- `sandbox_attestation_bundle_ref`
- `network_mode_witness_ref`
- `docker_socket_absence_witness_ref`
- `secret_absence_witness_ref`
- `source_lookup_absence_witness_ref`
- `decompilation_absence_witness_ref`
- `dispatch_status`
- `limitation_note`

`programbench_single_case_execution_trace@1` should include:

- `single_case_execution_trace_ref`
- `single_case_worker_dispatch_specimen_ref`
- `command_argv_rows`
- `execution_trace_kind`
- `command_rows_must_be_argv_shaped`
- `raw_shell_string_posture`
- `command_allowlist_match_ref`
- `working_directory_ref`
- `environment_policy_hash`
- `stdout_hash`
- `stdout_excerpt_bounded`
- `stderr_hash`
- `stderr_excerpt_bounded`
- `exit_code`
- `duration_ms`
- `timeout_status`
- `resource_limit_status`
- `worker_tool_call_manifest_ref`
- `pre_fs_manifest_ref`
- `post_fs_manifest_ref`
- `fs_diff_ref`
- `sandbox_violation_refs`
- `forbidden_content_screen_verdict`
- `limitation_note`

`programbench_single_case_probe_observation_bundle@1` should include:

- `single_case_probe_observation_bundle_ref`
- `single_case_execution_trace_ref`
- `local_probe_basis_ref`
- `local_probe_basis_hash`
- `probe_observation_rows`
- `positive_probe_result_refs`
- `negative_probe_result_refs`
- `missing_probe_refs`
- `inconclusive_probe_refs`
- `hidden_test_equivalence_posture`
- `official_evaluator_posture`
- `limitation_note`

`programbench_single_case_candidate_artifact_capture@1` should include:

- `single_case_candidate_artifact_capture_ref`
- `single_case_execution_trace_ref`
- `artifact_capture_policy_ref`
- `write_scope_ref`
- `write_scope_hash`
- `materialization_input_hash`
- `materialization_output_manifest_hash`
- `generated_artifact_rows`
- `artifact_hash_rows`
- `inside_write_scope_posture`
- `forbidden_content_screen_verdict`
- `official_submission_posture`
- `limitation_note`

`programbench_single_case_lifecycle_projection@1` should include:

- `single_case_lifecycle_projection_ref`
- `single_case_worker_dispatch_specimen_ref`
- `single_case_execution_trace_ref`
- `single_case_probe_observation_bundle_ref`
- `single_case_candidate_artifact_capture_ref`
- `projected_attempt_lifecycle_refs`
- `projected_trial_lifecycle_refs`
- `projected_workbench_evidence_refs`
- `projection_validator_binding_refs`
- `projection_gap_refs`
- `projection_is_not_new_truth_posture`
- `benchmark_truth_posture`
- `limitation_note`

## Validation Expectations

The future implementation should validate:

- B requires released A refs and B dispatch authority;
- exactly one dispatch specimen may exist for one A run request;
- `dispatch_specimen_index` must be `1`;
- `single_case_dispatch_cardinality_posture` must be
  `exactly_one_dispatch_specimen`;
- `dispatch_authority_kind` must be
  `b_slice_lock_local_single_specimen_only`;
- dispatch hashes must match A worker-visible packet, runbook, sandbox policy,
  tool manifest, write scope, and probe basis hashes;
- materialization hashes must bind input packet, worker-visible context, tool
  manifest, sandbox policy, and run control contract payloads;
- execution trace must use argv-shaped command rows, not raw shell strings,
  unless a later explicit authority grants and justifies shell wrapping;
- `execution_trace_kind` must distinguish worker dispatch, candidate local
  probe, candidate artifact build, and harness capture traces;
- execution trace must bind sandbox attestations and absence witnesses;
- forbidden-content screening must pass before artifact capture is valid;
- candidate artifacts must be inside released write scope;
- candidate artifact materialization hashes must match captured output and
  materialization input hashes;
- candidate artifact capture is invalid if hidden, forbidden, postmortem, or
  excluded-derived content is present;
- probe observations must be local declared probes only;
- lifecycle projection cannot create new evidence law or benchmark truth;
- no B row may cite hidden tests, official evaluator output, original source,
  decompilation, internet lookup, external repo facts, benchmark scores,
  baseline comparison, model ranking, or official submission authority.

## Reference Fixtures

Future B fixtures should include:

- one dispatch specimen bound to released A refs and B lock authority;
- one execution trace with stdout/stderr hashes, exit code, duration, timeout
  status, and filesystem diff refs;
- one local probe observation bundle;
- one candidate artifact capture inside write scope;
- one lifecycle projection back into released attempt/trial/workbench law.

Reject fixtures should include:

- B dispatch without B lock authority;
- two dispatch specimens for one A request;
- dispatch specimen index other than `1`;
- dispatch hash mismatch against A controls;
- execution trace missing `execution_trace_kind`;
- execution trace with raw shell command not authorized by A controls;
- missing sandbox attestation;
- output capture with forbidden-content screen failure;
- artifact materialization hash mismatch;
- artifact capture outside write scope;
- hidden-test or official-evaluator observation;
- lifecycle projection claiming benchmark truth.

## Non-Outputs

`PB-SINGLE-CASE-RUN-0-B` must not output:

- local outcome audit rows;
- final acceptance/remand decision rows;
- benchmark scores;
- baseline comparison rows;
- model ranking rows;
- leaderboard claims;
- official ProgramBench participation rows;
- official submission artifacts;
- retry authority rows;
- batch execution rows;
- future-family selection rows.
