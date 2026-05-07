# LOCKED_CONTINUATION_vNEXT_PLUS246

## Status

Bounded starter lock draft for `PB-ADAPTER-0-B` (probe plan and observation
adapter: local/reference probe plans, observation logs, I/O artifact indexes,
and filesystem side-effect observations).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-ADAPTER-0-B` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-ADAPTER-0`
- slice: `PB-ADAPTER-0-B`
- branch-local execution target: `arc/pb-adapter-0-b`

## Purpose

Freeze the bounded `PB-ADAPTER-0-B` starter slice so the repo can make local
and reference probe plans plus observation rows reviewable under the released
`PB-ADAPTER-0-A` task intake, artifact manifest, visibility manifest, worker
access contract, and non-authority guardrail.

`vNext+246` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize
`PB-ADAPTER-0-C`, reconstruction case packets, readiness summaries, handoffs,
family closeout alignment, official ProgramBench participation, official task
execution, official runner integration, hidden-test handling, hidden-test
inference, original source lookup, decompilation, internet lookup inside
ProgramBench tasks, external repository lookup, benchmark submission,
benchmark scoring, benchmark truth, model ranking, generated official
submissions, arbitrary command execution, target mutation, runtime transition,
product authorization, graph-memory authority, recursive policy amendment, or
future-family selection.

Controlling invariant:

```text
PB-ADAPTER-0-B may represent allowed local/reference probe plans and bounded
observation evidence under a released access contract, but probe observations
are active evidence creation, not official evaluation, benchmark truth,
hidden-test equivalence, generated submission authority, or open command
authority.
```

## Instantiated Here

- `PB-ADAPTER-0-B` instantiates the second cleanroom adapter seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS245.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS245.md`
    - `docs/ASSESSMENT_vNEXT_PLUS245_EDGES.md`
    - `artifacts/agent_harness/v245/evidence_inputs/pb_adapter_0a_cleanroom_task_intake_closeout_evidence_v245.json`
    - `artifacts/agent_harness/v245/evidence_inputs/metric_key_continuity_assertion_v245.json`
    - `artifacts/agent_harness/v245/evidence_inputs/runtime_observability_comparison_v245.json`
    - `apps/api/fixtures/benchmarking/vnext_plus245/programbench_cleanroom_task_intake_v245_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus245/programbench_task_artifact_manifest_v245_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus245/programbench_task_visibility_manifest_v245_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus245/programbench_adapter_worker_access_contract_v245_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus245/programbench_adapter_non_authority_guardrail_v245_reference.json`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v77.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0A_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0C_IMPLEMENTATION_MAPPING_v0.md`
  - emitted second-slice record shapes:
    - `programbench_adapter_probe_plan@1`
    - `programbench_probe_observation_log@1`
    - `programbench_io_artifact_observation_index@1`
    - `programbench_filesystem_side_effect_observation@1`

## Required Starter Vocabulary

Minimum `programbench_adapter_probe_plan@1` fields:

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

Required command-shape law:

```text
probe command rows must be argv-shaped by default and must not be raw shell
strings unless explicitly marked shell_wrapped_with_reason.
```

Minimum `programbench_probe_observation_log@1` fields:

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

Minimum `programbench_io_artifact_observation_index@1` fields:

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

Minimum `programbench_filesystem_side_effect_observation@1` fields:

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

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_adapter_probe_plan@1`
  - `programbench_probe_observation_log@1`
  - `programbench_io_artifact_observation_index@1`
  - `programbench_filesystem_side_effect_observation@1`
- deterministic reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus246/`;
- validators that prove:
  - released `PB-ADAPTER-0-A` refs are required and resolve;
  - observation rows cannot exist without a released access contract;
  - probe command rows are argv-shaped unless shell wrapping is explicitly
    declared with a reason;
  - probe plans carry working-directory, environment, stdin, timeout, resource
    limit, write-scope, pre/post snapshot, and side-effect capture policy;
  - observation logs record stdout/stderr hashes, bounded excerpts, exit code,
    duration, timeout status, filesystem manifests, diff refs, and replay
    limitations;
  - hidden evaluator output cannot become inference evidence;
  - local probe pass cannot become benchmark score, benchmark truth,
    hidden-test equivalence, model ranking, or official evaluator result;
  - official runner integration, official task execution, generated submission
    authority, internet/source/decompilation lookup, target mutation, runtime
    transition, product authority, graph authority, recursive-policy amendment,
    and future-family selection remain absent;
  - `PB-ADAPTER-0-C` case packets, readiness summaries, handoffs, and family
    closeout alignment remain deferred.

## Deferred To Later Slice Or Family

- `PB-ADAPTER-0-C`:
  - reconstruction case packet;
  - adapter readiness summary;
  - post-adapter handoff;
  - family closeout alignment.
- later family:
  - official ProgramBench participation;
  - hidden evaluator result governance;
  - generated submission review;
  - broader conceptual broker implementation;
  - reconstruction execution and evaluation review;
  - V86/V87/V88 meta-loop continuations.

## Machine-Checkable Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS246.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+246",
  "target_path": "PB-ADAPTER-0-B",
  "slice": "PB-ADAPTER-0-B",
  "family": "PB-ADAPTER-0",
  "branch_local_execution_target": "arc/pb-adapter-0-b",
  "target_scope": "cleanroom_probe_plan_and_observation_adapter_slice",
  "implementation_packages": [
    "adeu_benchmarking"
  ],
  "api_surfaces": [],
  "prerequisite_locks": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS245.md"
  ],
  "prerequisite_decision_docs": [
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS245.md"
  ],
  "prerequisite_assessments": [
    "docs/ASSESSMENT_vNEXT_PLUS245_EDGES.md"
  ],
  "planning_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v77.md",
    "docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_FAMILY_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0A_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0B_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0C_IMPLEMENTATION_MAPPING_v0.md"
  ],
  "consumed_record_shapes": [
    "programbench_cleanroom_task_intake@1",
    "programbench_task_artifact_manifest@1",
    "programbench_task_visibility_manifest@1",
    "programbench_adapter_worker_access_contract@1",
    "programbench_adapter_non_authority_guardrail@1"
  ],
  "emitted_record_shapes": [
    "programbench_adapter_probe_plan@1",
    "programbench_probe_observation_log@1",
    "programbench_io_artifact_observation_index@1",
    "programbench_filesystem_side_effect_observation@1"
  ],
  "forbidden_claims": [
    "reconstruction_case_packet_created",
    "adapter_readiness_summary_created",
    "adapter_handoff_created",
    "family_closeout_alignment_created",
    "official_programbench_participation",
    "official_programbench_runner_integrated",
    "official_programbench_task_executed",
    "hidden_test_visible_to_worker",
    "hidden_test_inference",
    "hidden_test_equivalence_claimed",
    "local_probe_pass_claimed_as_benchmark_score",
    "benchmark_truth_claimed",
    "model_ranking_claimed",
    "generated_submission_authority",
    "original_source_lookup",
    "decompilation",
    "internet_lookup_for_task",
    "external_repo_lookup_for_task",
    "arbitrary_command_execution_authority",
    "target_mutation",
    "runtime_transition",
    "product_authorization",
    "graph_memory_authority",
    "recursive_policy_amendment",
    "future_family_selection"
  ],
  "local_gate": "make arc-start-check ARC=246"
}
```
