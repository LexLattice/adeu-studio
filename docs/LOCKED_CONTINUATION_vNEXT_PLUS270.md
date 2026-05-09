# LOCKED_CONTINUATION_vNEXT_PLUS270

## Status

Bounded starter lock draft for `PB-SINGLE-CASE-RUN-0-B` (one local worker
dispatch specimen, execution trace, probe observation bundle, candidate
artifact capture, and lifecycle projection).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-SINGLE-CASE-RUN-0-B` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-SINGLE-CASE-RUN-0`
- slice: `PB-SINGLE-CASE-RUN-0-B`
- branch-local execution target: `arc/pb-single-case-run-0-b`

## Purpose

Freeze the bounded `PB-SINGLE-CASE-RUN-0-B` starter slice so the repo can
record exactly one local cleanroom execution specimen under released
`PB-SINGLE-CASE-RUN-0-A` run controls.

`vNext+270` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize
official ProgramBench participation, official task execution, official
runner/evaluator integration, hidden-test handling, hidden-test inference,
hidden-test equivalence, original source lookup, decompilation, internet
lookup inside ProgramBench tasks, external repository lookup, benchmark
submission, benchmark scoring, benchmark truth, pass rate, solve rate,
success rate, baseline comparison, model ranking, leaderboard standing,
official submission authority, retry authority, second retry authority,
retry-chain authority, batch execution over a matrix, unbounded command
execution, target mutation outside released local artifacts, local outcome
audit, remand or acceptance decision, runtime transition beyond this local
specimen, product authorization, graph-memory authority, release authority,
recursive policy amendment, or future-family selection.

Controlling invariant:

```text
PB-SINGLE-CASE-RUN-0-B may record one bounded local execution specimen under
released A controls and a B-slice dispatch authority.

It may not score ProgramBench, compare a baseline, rank a model, submit
officially, decide acceptance/remand, grant retry authority, or run a batch.
```

Dispatch invariant:

```text
A preflight is not dispatch authority.

PB-SINGLE-CASE-RUN-0-B rows require:
  released PB-SINGLE-CASE-RUN-0-A refs
  + B-slice dispatch authority
  + exactly one dispatch specimen
  + sandbox/tool/write-scope witness bindings.
```

Candidate artifact invariant:

```text
Candidate artifact capture is valid only after forbidden-content screening
passes, generated artifacts stay inside released write scope, and artifact
hashes bind to captured/materialized output.
```

Lifecycle projection invariant:

```text
Lifecycle projection maps the specimen into released attempt/trial/workbench
vocabulary. It is not new benchmark truth and not hidden-test equivalence.
```

## Instantiated Here

- `PB-SINGLE-CASE-RUN-0-B` instantiates the action-adjacent local specimen
  capture seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-SINGLE-CASE-RUN-0-A` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS269.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS269.md`
    - `docs/ASSESSMENT_vNEXT_PLUS269_EDGES.md`
    - `apps/api/fixtures/benchmarking/vnext_plus269/`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v85.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_SINGLE_CASE_RUN_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_SINGLE_CASE_RUN_PB_SINGLE_CASE_RUN_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_SINGLE_CASE_RUN_PB_SINGLE_CASE_RUN_0B_IMPLEMENTATION_MAPPING_v0.md`
  - emitted starter record shapes:
    - `programbench_single_case_worker_dispatch_specimen@1`
    - `programbench_single_case_execution_trace@1`
    - `programbench_single_case_probe_observation_bundle@1`
    - `programbench_single_case_candidate_artifact_capture@1`
    - `programbench_single_case_lifecycle_projection@1`

## Required Starter Vocabulary

Minimum `programbench_single_case_worker_dispatch_specimen@1` fields:

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
- `write_scope_attestation_ref`
- `dispatch_status`
- `limitation_note`

Required dispatch posture:

- `dispatch_authority_kind = b_slice_lock_local_single_specimen_only`
- `dispatch_specimen_index = 1`
- `single_case_dispatch_cardinality_posture = exactly_one_dispatch_specimen`

Minimum `programbench_single_case_execution_trace@1` fields:

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

Required execution trace posture:

- command rows are argv-shaped;
- raw shell strings are forbidden unless later explicit authority grants and
  justifies shell wrapping;
- `execution_trace_kind` distinguishes worker dispatch, candidate local probe,
  candidate artifact build, and harness capture traces.

Minimum `programbench_single_case_probe_observation_bundle@1` fields:

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

Minimum `programbench_single_case_candidate_artifact_capture@1` fields:

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

Minimum `programbench_single_case_lifecycle_projection@1` fields:

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

The implementation must validate:

- B requires released A refs and B dispatch authority;
- A preflight alone is never dispatch authority;
- exactly one dispatch specimen may exist for one A run request;
- dispatch hashes match released A worker-visible packet, runbook, sandbox
  policy, tool manifest, write scope, and probe basis hashes;
- materialization hashes bind input packet, visible context, tool manifest,
  sandbox policy, and run control contract payloads;
- execution traces use argv-shaped command rows and reject unauthorized raw
  shell strings;
- execution traces bind sandbox attestations and absence witnesses;
- forbidden-content screening must pass before artifact capture is valid;
- candidate artifacts must be inside released write scope;
- candidate artifact materialization hashes match captured output and
  materialization input hashes;
- local probe observations remain declared local probes only;
- lifecycle projection cannot create new evidence law, benchmark truth, or
  hidden-test equivalence;
- no B row may cite hidden tests, official evaluator output, original source,
  decompilation, internet lookup, external repo facts, benchmark scores,
  baseline comparison, model ranking, or official submission authority.

## Expected Verification

- focused pytest:
  - `.venv/bin/python -m pytest packages/adeu_benchmarking/tests/test_programbench_single_case_run_pb_single_case_run_0b.py -q`
- full Python lane:
  - `make check`

## Explicit Non-Outputs

`PB-SINGLE-CASE-RUN-0-B` must not output:

- local outcome audit rows;
- observation summary rows;
- final remand or acceptance decision rows;
- benchmark score rows;
- pass-rate, solve-rate, success-rate, or official-score rows;
- baseline comparison rows;
- model ranking rows;
- leaderboard claims;
- official ProgramBench participation rows;
- official submission artifacts;
- retry authority rows;
- batch execution rows;
- future-family selection rows.

## Machine-Checkable Contract Seed

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+270",
  "target_path": "PB-SINGLE-CASE-RUN-0-B",
  "authority_layer": "lock",
  "selected_family": "PB-SINGLE-CASE-RUN-0",
  "selected_slice": "PB-SINGLE-CASE-RUN-0-B",
  "selected_record_shapes": [
    "programbench_single_case_worker_dispatch_specimen@1",
    "programbench_single_case_execution_trace@1",
    "programbench_single_case_probe_observation_bundle@1",
    "programbench_single_case_candidate_artifact_capture@1",
    "programbench_single_case_lifecycle_projection@1"
  ],
  "package_scope": "packages/adeu_benchmarking",
  "requires_released_pb_single_case_run_0a_refs": true,
  "requires_b_slice_dispatch_authority": true,
  "dispatch_specimen_index": 1,
  "single_dispatch_specimen_only": true,
  "argv_shaped_command_rows_required": true,
  "forbidden_content_screen_required_before_artifact_capture": true,
  "official_programbench_authority_granted": false,
  "benchmark_score_authority_granted": false,
  "baseline_comparison_authority_granted": false,
  "model_ranking_authority_granted": false,
  "batch_execution_authority_granted": false,
  "retry_authority_granted": false,
  "future_family_selection_granted": false
}
```
