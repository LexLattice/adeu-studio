# Draft ADEU ProgramBench Cleanroom Adapter PB-ADAPTER-0-B Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-ADAPTER-0-B`.

Authority layer: support.

This note maps the second candidate slice for `PB-ADAPTER-0`. It is not a
slice lock and does not authorize probe execution by itself. Any later active
slice must define exactly what observation rows may be created and under which
released `PB-ADAPTER-0-A` access contract.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v77.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0A_IMPLEMENTATION_MAPPING_v0.md`

## Slice Role

`PB-ADAPTER-0-B` should make allowed local/reference probe plans and
observations row-shaped. It should adapt visible CLI/help/stdin/stdout/stderr,
exit-code, generated-file, and filesystem-side-effect evidence into the
cleanroom reconstruction substrate without claiming hidden-test equivalence.
Probe observations are active evidence creation, not passive retrieval, so the
slice must keep command shape, environment, write scope, and replay limits
inspectable.

The slice should implement only:

- `programbench_adapter_probe_plan@1`
- `programbench_probe_observation_log@1`
- `programbench_io_artifact_observation_index@1`
- `programbench_filesystem_side_effect_observation@1`

## Candidate Schema Fields

### `programbench_adapter_probe_plan@1`

Minimum fields:

- `probe_plan_ref`
- `task_intake_ref`
- `visibility_manifest_ref`
- `worker_access_contract_ref`
- `adapter_candidate_ref`
- `task_instance_ref`
- `probe_phase_posture`
- `command_argv_shape`
- `working_directory_ref`
- `environment_policy`
- `stdin_fixture_ref`
- `timeout_policy`
- `resource_limit_policy`
- `allowed_write_scope`
- `pre_state_snapshot_ref`
- `post_state_snapshot_ref`
- `side_effect_capture_policy`
- `allowed_probe_command_rows`
- `forbidden_probe_command_rows`
- `reference_executable_probe_posture`
- `worker_submission_probe_posture`
- `network_policy`
- `source_visibility_policy`
- `hidden_evaluator_posture`
- `local_probe_not_truth_guardrail`
- `limitation_note`

Minimum `probe_phase_posture` values:

- `plan_only_no_execution_by_this_row`
- `local_reference_probe_allowed_by_later_lock`
- `worker_generated_probe_allowed_by_later_lock`
- `official_evaluator_probe_forbidden`
- `future_family_only`

Probe command rows must not be raw shell strings unless explicitly marked
`shell_wrapped_with_reason`.

### `programbench_probe_observation_log@1`

Minimum fields:

- `probe_observation_ref`
- `probe_plan_ref`
- `task_intake_ref`
- `adapter_candidate_ref`
- `task_instance_ref`
- `observation_source_kind`
- `command_shape_ref`
- `stdin_observation_ref`
- `stdout_observation_ref`
- `stdout_hash`
- `stdout_excerpt_bounded`
- `stderr_observation_ref`
- `stderr_hash`
- `stderr_excerpt_bounded`
- `exit_code_observation_ref`
- `exit_code`
- `duration_ms`
- `timeout_status`
- `pre_fs_manifest_ref`
- `post_fs_manifest_ref`
- `fs_diff_ref`
- `observation_replay_limitations`
- `observation_currentness`
- `hidden_test_equivalence_posture`
- `limitation_note`

`observation_source_kind` should distinguish:

- `reference_executable_observation`
- `worker_generated_probe_observation`
- `worker_generated_submission_observation`
- `support_context_only_observation`
- `postmortem_only_observation`
- `hidden_evaluator_observation_forbidden_in_inference`

### `programbench_io_artifact_observation_index@1`

Minimum fields:

- `io_artifact_index_ref`
- `probe_observation_refs`
- `task_intake_ref`
- `stdout_artifact_refs`
- `stderr_artifact_refs`
- `generated_output_artifact_refs`
- `directory_output_artifact_refs`
- `binary_output_artifact_refs`
- `artifact_visibility_rows`
- `artifact_truth_posture`
- `limitation_note`

### `programbench_filesystem_side_effect_observation@1`

Minimum fields:

- `side_effect_observation_ref`
- `probe_observation_ref`
- `task_intake_ref`
- `created_path_refs`
- `modified_path_refs`
- `deleted_path_refs`
- `untouched_path_refs`
- `side_effect_expectedness_posture`
- `path_scope_posture`
- `hidden_test_equivalence_posture`
- `limitation_note`

## Expected Package Edits Later

If selected by a later slice lock, likely touched files:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_adapter.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_adapter_probe_plan.v1.json`
- `packages/adeu_benchmarking/schema/programbench_probe_observation_log.v1.json`
- `packages/adeu_benchmarking/schema/programbench_io_artifact_observation_index.v1.json`
- `packages/adeu_benchmarking/schema/programbench_filesystem_side_effect_observation.v1.json`
- matching mirror schemas under `spec/`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_adapter_pb_adapter_0b.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- future fixtures under the selected `vNext+` fixture directory.

## Reference Fixture Intent

Reference fixtures should cover:

- released `PB-ADAPTER-0-A` refs required for every observation row;
- plan-only rows that do not execute commands by themselves;
- reference-executable observation rows under local cleanroom posture;
- stdout/stderr/exit-code separation;
- generated output artifact index rows;
- filesystem side-effect observation rows with bounded path scope;
- local probe not truth / not hidden-test-equivalence guardrails.

Reject fixtures should cover:

- observation row with no released `PB-ADAPTER-0-A` access contract;
- hidden evaluator output cited as inference evidence;
- local probe pass claimed as benchmark score or hidden-test equivalence;
- probe plan allowing internet/source/decompilation lookup during inference;
- side-effect observation outside bounded path scope;
- official runner integration or official task execution posture;
- generated submission authority claimed by observation rows.

## Slice Non-Outputs

`PB-ADAPTER-0-B` must not output:

- `programbench_reconstruction_case_packet@1`
- `programbench_adapter_readiness_summary@1`
- `programbench_adapter_handoff@1`
- `programbench_cleanroom_adapter_family_closeout_alignment@1`
- official evaluator integration;
- official benchmark result rows;
- model ranking rows;
- hidden-test repair loops;
- code generation or official submission artifacts.
