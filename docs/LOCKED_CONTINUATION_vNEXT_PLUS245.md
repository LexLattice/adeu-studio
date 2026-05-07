# LOCKED_CONTINUATION_vNEXT_PLUS245

## Status

Bounded starter lock draft for `PB-ADAPTER-0-A` (ProgramBench-style task
intake, task artifact identity manifest, task visibility manifest, worker
access contract, and adapter non-authority guardrail).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-ADAPTER-0-A` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-ADAPTER-0`
- slice: `PB-ADAPTER-0-A`
- branch-local execution target: `arc/pb-adapter-0-a`

## Purpose

Freeze the bounded `PB-ADAPTER-0-A` starter slice so the repo can record
ProgramBench-style task intake, stable task artifact identity, cleanroom
visibility posture, worker access boundaries, and non-authority guardrails
before any probe observation, reconstruction case packet, generated
submission, official ProgramBench run, or evaluator contact exists.

`vNext+245` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize official
ProgramBench participation, official task execution, official runner
integration, hidden-test handling, hidden-test inference, original source
lookup, decompilation, internet lookup inside ProgramBench tasks, external
repository lookup, benchmark submission, benchmark scoring, benchmark truth,
model ranking, generated official submissions, probe execution, command
execution, tool invocation, target mutation, runtime transition, product
authorization, graph-memory authority, recursive policy amendment, or
future-family selection.

Controlling invariant:

```text
PB-ADAPTER-0-A may describe the exact task-visible artifact set and the worker
access law for later cleanroom reconstruction review, but it may not run probes,
solve tasks, generate submissions, expose forbidden evidence, or create
benchmark authority.
```

## Instantiated Here

- `PB-ADAPTER-0-A` instantiates the first cleanroom adapter seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed closed substrate:
    - `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`
    - `apps/api/fixtures/benchmarking/vnext_plus244/programbench_realization_family_closeout_alignment_v244_reference.json`
    - `artifacts/agent_harness/v244/evidence_inputs/pb_py_0c_local_fixture_comparison_closeout_evidence_v244.json`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v77.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0A_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0C_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
  - emitted first-slice record shapes:
    - `programbench_cleanroom_task_intake@1`
    - `programbench_task_artifact_manifest@1`
    - `programbench_task_visibility_manifest@1`
    - `programbench_adapter_worker_access_contract@1`
    - `programbench_adapter_non_authority_guardrail@1`

## Required Starter Vocabulary

Minimum `programbench_cleanroom_task_intake@1` fields:

- `task_intake_ref`
- `adapter_candidate_ref`
- `task_instance_ref`
- `source_refs`
- `task_artifact_manifest_ref`
- `task_origin_posture`
- `task_identifier_posture`
- `benchmark_context_refs`
- `pb_py_0_profile_refs`
- `pb_py_0_fixture_contract_refs`
- `target_language_posture`
- `reference_executable_ref`
- `usage_docs_refs`
- `visible_input_artifact_refs`
- `forbidden_inference_source_refs`
- `official_participation_posture`
- `benchmark_truth_posture`
- `limitation_note`

Minimum `task_origin_posture` values:

- `synthetic_local_task`
- `repo_internal_task`
- `programbench_style_public_context_only`
- `official_programbench_task_not_selected`
- `unknown_origin_blocked`

Minimum `programbench_task_artifact_manifest@1` fields:

- `task_artifact_manifest_ref`
- `task_intake_ref`
- `adapter_candidate_ref`
- `task_instance_ref`
- `reference_executable_ref`
- `reference_executable_hash`
- `usage_docs_hash_rows`
- `visible_input_artifact_hash_rows`
- `source_set_hash`
- `artifact_origin_posture`
- `observed_at`
- `snapshot_ref`
- `ingestion_method`
- `artifact_identity_posture`
- `limitation_note`

The artifact manifest binds what exact task-visible artifact set the worker
may later be allowed to see. Hash identity is not permission to expose hidden,
forbidden, original-source, decompilation, internet, external-repo, Docker
socket, or host-secret stores.

Minimum `programbench_task_visibility_manifest@1` fields:

- `visibility_manifest_ref`
- `task_intake_ref`
- `task_artifact_manifest_ref`
- `adapter_candidate_ref`
- `task_instance_ref`
- `visible_store_rows`
- `hidden_store_rows`
- `forbidden_store_rows`
- `support_context_rows`
- `visibility_basis_rows`
- `store_presence_rows`
- `derived_summary_policy_rows`
- `worker_exposure_policy_rows`
- `worker_visible_file_refs`
- `worker_hidden_file_refs`
- `inference_visibility_posture`
- `forbidden_store_reachability_posture`
- `source_visibility_policy`
- `limitation_note`

Minimum visibility basis values:

- `known_visible`
- `known_hidden`
- `known_forbidden`
- `known_support_only`
- `unknown_not_indexed`
- `declared_absent`

Hard rule:

```text
hidden or forbidden rows must not be worker-visible, allowed inference refs, or
cleanroom-visible derived worker summaries.
```

Minimum `programbench_adapter_worker_access_contract@1` fields:

- `worker_access_contract_ref`
- `task_intake_ref`
- `task_artifact_manifest_ref`
- `visibility_manifest_ref`
- `adapter_candidate_ref`
- `task_instance_ref`
- `allowed_inference_source_refs`
- `forbidden_inference_source_refs`
- `allowed_network_posture`
- `internet_lookup_posture`
- `external_repo_lookup_posture`
- `source_lookup_posture`
- `decompilation_posture`
- `docker_socket_posture`
- `host_secret_posture`
- `allowed_command_posture`
- `probe_execution_authority_posture`
- `submission_generation_posture`
- `limitation_note`

Required slice-A access posture:

```text
allowed_command_posture = no_command_execution_authority_by_pb_adapter_0a
probe_execution_authority_posture = no_probe_execution_authority_by_pb_adapter_0a
submission_generation_posture = no_submission_generation_authority_by_pb_adapter_0a
```

Minimum `programbench_adapter_non_authority_guardrail@1` fields:

- `guardrail_ref`
- `task_intake_refs`
- `task_artifact_manifest_refs`
- `visibility_manifest_refs`
- `worker_access_contract_refs`
- `non_authority_posture`
- `official_programbench_posture`
- `hidden_test_posture`
- `benchmark_truth_posture`
- `submission_authority_posture`
- `model_ranking_posture`
- `future_family_selection_posture`
- `limitation_note`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_cleanroom_task_intake@1`
  - `programbench_task_artifact_manifest@1`
  - `programbench_task_visibility_manifest@1`
  - `programbench_adapter_worker_access_contract@1`
  - `programbench_adapter_non_authority_guardrail@1`
- deterministic reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus245/`;
- validators that prove:
  - adapter candidate, task instance, intake, artifact manifest, visibility
    manifest, access contract, and guardrail lineage is consistent;
  - artifact manifests include stable identity witnesses for reference
    executable, usage docs, visible input artifacts, source-set hash,
    observed-at or snapshot refs, origin posture, and ingestion method;
  - forbidden and hidden rows cannot be worker-visible, allowed inference refs,
    or cleanroom-visible derived worker summaries;
  - public descriptors remain context-only and do not become benchmark truth;
  - official ProgramBench participation, official runner integration, hidden
    tests, original source, decompilation, internet lookup, external repo
    lookup, host secrets, and Docker socket access are rejected as inference
    exposure;
  - worker access contracts cannot grant command execution, probe execution,
    or submission generation authority in slice A;
  - `PB-ADAPTER-0-A` rejects `PB-ADAPTER-0-B` and `PB-ADAPTER-0-C` artifact
    kinds;
  - no probe observations, reconstruction case packets, readiness summaries,
    handoffs, benchmark scores, model rankings, generated submissions,
    official evaluator integration, product authority, graph authority,
    release authority, recursive-policy authority, or future-family selection
    ship in this slice.

## Deferred To Later Slice Or Family

- `PB-ADAPTER-0-B` probe plans and observation logs;
- `PB-ADAPTER-0-C` reconstruction case packets, readiness summaries, handoffs,
  and family closeout alignment;
- official ProgramBench participation and result governance;
- hidden evaluator feedback governance;
- broader conceptual broker implementation;
- larger fixture matrices and natural task to program-profile inference;
- V86 obligation expansion / evidence contract / edge probe planning;
- V87 reviewer / auditor taskpacks;
- V88 deterministic closeout transition / remand routing;
- product, graph-memory, release, or recursive-policy work.

## Machine-Checkable Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS245.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+245",
  "target_path": "PB-ADAPTER-0-A",
  "slice": "PB-ADAPTER-0-A",
  "family": "PB-ADAPTER-0",
  "branch_local_execution_target": "arc/pb-adapter-0-a",
  "target_scope": "cleanroom_task_intake_visibility_and_worker_access_contract_slice",
  "implementation_packages": [
    "adeu_benchmarking"
  ],
  "api_surfaces": [],
  "prerequisite_locks": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS244.md"
  ],
  "prerequisite_decision_docs": [
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS244.md"
  ],
  "prerequisite_assessments": [
    "docs/ASSESSMENT_vNEXT_PLUS244_EDGES.md"
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
    "programbench_realization_family_closeout_alignment@1"
  ],
  "emitted_record_shapes": [
    "programbench_cleanroom_task_intake@1",
    "programbench_task_artifact_manifest@1",
    "programbench_task_visibility_manifest@1",
    "programbench_adapter_worker_access_contract@1",
    "programbench_adapter_non_authority_guardrail@1"
  ],
  "forbidden_claims": [
    "official_programbench_participation",
    "official_programbench_runner_integrated",
    "official_programbench_task_executed",
    "hidden_test_visible_to_worker",
    "hidden_test_inference",
    "hidden_or_forbidden_summary_marked_cleanroom_visible",
    "original_source_lookup",
    "decompilation",
    "internet_lookup_for_task",
    "external_repo_lookup_for_task",
    "command_execution_authority",
    "probe_execution_authority",
    "submission_generation_authority",
    "benchmark_score_created",
    "benchmark_truth_claimed",
    "model_ranking_claimed",
    "future_family_selection"
  ],
  "local_gate": "make arc-start-check ARC=245"
}
```
