# Draft ADEU ProgramBench Cleanroom Reconstruction Workbench PB-RECON-0-B Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-RECON-0-B`.

Authority layer: support.

This note maps the second candidate slice for `PB-RECON-0`. It is not a slice
lock and does not authorize local execution by itself. Any later active slice
must define exactly which released `PB-RECON-0-A` work order, context,
sandbox, and budget rows constrain candidate artifact capture and local probe
evidence.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v78.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0A_IMPLEMENTATION_MAPPING_v0.md`

## Slice Role

`PB-RECON-0-B` should make worker-generated candidate artifacts and local
sandbox observations row-shaped under a released work order. It should capture
what was generated, what local commands ran, what local probes observed, and
what remand/correction steps occurred without claiming official submission
authority, hidden-test equivalence, benchmark truth, or model ranking.

The slice should implement only:

- `programbench_reconstruction_candidate_artifact_manifest@1`
- `programbench_reconstruction_local_run_trace@1`
- `programbench_reconstruction_probe_result_log@1`
- `programbench_reconstruction_remand_correction_record@1`

## Candidate Schema Fields

### `programbench_reconstruction_candidate_artifact_manifest@1`

Minimum fields:

- `candidate_artifact_manifest_ref`
- `work_order_ref`
- `worker_context_packet_ref`
- `sandbox_policy_ref`
- `run_budget_ref`
- `adapter_candidate_ref`
- `task_instance_ref`
- `candidate_attempt_ref`
- `generated_file_rows`
- `generated_artifact_hash_rows`
- `artifact_visibility_posture`
- `submission_authority_posture`
- `official_programbench_posture`
- `limitation_note`

Candidate artifacts are local workbench outputs only. They are not official
ProgramBench submissions.

### `programbench_reconstruction_local_run_trace@1`

Minimum fields:

- `local_run_trace_ref`
- `candidate_artifact_manifest_ref`
- `work_order_ref`
- `sandbox_policy_ref`
- `run_budget_ref`
- `command_authority_ref`
- `command_allowlist_match_ref`
- `sandbox_attestation_ref`
- `network_attestation_ref`
- `secret_absence_attestation_ref`
- `dependency_resolution_posture`
- `write_scope_attestation_ref`
- `artifact_capture_policy_ref`
- `command_argv_rows`
- `working_directory_ref`
- `environment_ref`
- `stdin_artifact_ref`
- `stdout_hash`
- `stdout_excerpt_bounded`
- `stderr_hash`
- `stderr_excerpt_bounded`
- `exit_code`
- `duration_ms`
- `timeout_status`
- `pre_fs_manifest_ref`
- `post_fs_manifest_ref`
- `fs_diff_ref`
- `sandbox_violation_refs`
- `hidden_test_posture`
- `benchmark_truth_posture`
- `limitation_note`

Local run traces must use argv-shaped commands and bounded output evidence.
Raw shell strings require explicit later authorization and reason.

Admissible local run traces must bind to a released sandbox policy, released
run budget, command allowlist match, and sandbox attestation rows. A trace
without those attestations is not valid local workbench evidence.

### `programbench_reconstruction_probe_result_log@1`

Minimum fields:

- `probe_result_log_ref`
- `work_order_ref`
- `candidate_artifact_manifest_ref`
- `local_run_trace_refs`
- `probe_result_rows`
- `expected_behavior_refs`
- `observed_behavior_refs`
- `stdout_stderr_separation_posture`
- `exit_code_posture`
- `filesystem_side_effect_posture`
- `probe_truth_posture`
- `hidden_test_equivalence_posture`
- `limitation_note`

Probe results remain local workbench evidence. They are not hidden-test
equivalence or benchmark truth.

### `programbench_reconstruction_remand_correction_record@1`

Minimum fields:

- `remand_correction_record_ref`
- `work_order_ref`
- `candidate_attempt_ref`
- `remand_reason_source`
- `remand_reason_rows`
- `correction_attempt_rows`
- `semantic_route_preservation_posture`
- `case_packet_mutation_posture`
- `hidden_evidence_use_posture`
- `budget_consumption_refs`
- `remand_outcome_posture`
- `limitation_note`

Remand/correction rows may repair local candidate defects only. They must not
invent hidden evidence, original source facts, decompilation evidence, or
official evaluator feedback.

Allowed `remand_reason_source` values:

- `local_probe_failure`
- `local_sandbox_violation`
- `missing_required_artifact`
- `unsupported_behavior_gap`
- `inconclusive_trace`

Forbidden remand sources:

- `hidden_test_failure`
- `official_evaluator_feedback`
- `original_source_observation`
- `decompilation_observation`

## Expected Package Edits Later

If selected by a later slice lock, likely touched files:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_reconstruction.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_candidate_artifact_manifest.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_local_run_trace.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_probe_result_log.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_remand_correction_record.v1.json`
- matching mirror schemas under `spec/`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_reconstruction_pb_recon_0b.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- future fixtures under the selected `vNext+` fixture directory.

## Reference Fixture Intent

Reference fixtures should cover:

- released `PB-RECON-0-A` work order, worker context, sandbox, run budget, and
  guardrail refs required for every B row;
- local candidate artifact manifest with hashes and no official submission
  posture;
- local run trace with argv-shaped command rows, bounded stdout/stderr,
  exit-code, duration, timeout, and filesystem-diff evidence;
- local probe result log that separates local evidence from hidden-test
  equivalence;
- remand/correction record that preserves the case packet and does not use
  hidden evidence.

Reject fixtures should cover:

- B row with no released `PB-RECON-0-A` work order;
- candidate artifact manifest claiming official submission authority;
- run trace with internet/source/decompilation/external repo access;
- run trace missing command allowlist match or sandbox attestation refs;
- unbounded stdout/stderr capture;
- sandbox violation treated as success;
- probe result claimed as benchmark score or hidden-test equivalence;
- remand record using hidden evaluator output, original source, or
  decompilation evidence;
- remand record mutating the released case packet;
- model-ranking claim inside local result rows.

## Split Fallback

If the active implementation footprint grows too large, split this slice
without changing the family selector:

- `PB-RECON-0-B1`:
  candidate artifact manifest and local run trace;
- `PB-RECON-0-B2`:
  probe result log and remand/correction record.

That fallback should be handled through per-slice continuation docs, not a new
family-level selector.

## Slice Non-Outputs

`PB-RECON-0-B` must not output:

- `programbench_reconstruction_equivalence_audit@1`
- `programbench_reconstruction_result_summary@1`
- `programbench_reconstruction_handoff@1`
- `programbench_reconstruction_workbench_family_closeout_alignment@1`
- official evaluator integration;
- official benchmark result rows;
- model ranking rows;
- hidden-test repair loops;
- official submission artifacts.
