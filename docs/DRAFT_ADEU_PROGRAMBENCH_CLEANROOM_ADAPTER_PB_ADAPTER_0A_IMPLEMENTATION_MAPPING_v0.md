# Draft ADEU ProgramBench Cleanroom Adapter PB-ADAPTER-0-A Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-ADAPTER-0-A`.

Authority layer: support.

This note maps the first candidate slice for `PB-ADAPTER-0`. It is not a
`vNext+245` lock, stop-gate decision, or edge assessment. Those per-slice
starter docs should be drafted only after this family-level bundle is reviewed.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v77.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_IMPLEMENTATION_MAPPING_v0.md`

## Slice Role

`PB-ADAPTER-0-A` should make ProgramBench-style task intake and worker exposure
law reviewable without running probes, solving tasks, generating submissions,
or integrating an official evaluator.

The slice should implement only:

- `programbench_cleanroom_task_intake@1`
- `programbench_task_artifact_manifest@1`
- `programbench_task_visibility_manifest@1`
- `programbench_adapter_worker_access_contract@1`
- `programbench_adapter_non_authority_guardrail@1`

## Candidate Schema Fields

### `programbench_cleanroom_task_intake@1`

Minimum fields:

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

### `programbench_task_artifact_manifest@1`

Minimum fields:

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

The manifest binds exact artifact identity. It does not authorize exposing
hidden, forbidden, original-source, decompilation, internet, external-repo,
Docker socket, or host-secret stores to a worker.

### `programbench_task_visibility_manifest@1`

Minimum fields:

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

Validator expectation:

```text
if any forbidden_store_rows or hidden_store_rows are worker-visible during
inference_phase, the manifest must be rejected.
```

Additional validator expectation:

```text
hidden or forbidden rows must not be converted into cleanroom-visible derived
summaries for worker inference.
```

### `programbench_adapter_worker_access_contract@1`

Minimum fields:

- `worker_access_contract_ref`
- `task_intake_ref`
- `visibility_manifest_ref`
- `task_artifact_manifest_ref`
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

The contract may describe future allowed command posture, but
`PB-ADAPTER-0-A` must not execute commands or create probe observations.
It also must not grant command execution or probe authority in slice A.

### `programbench_adapter_non_authority_guardrail@1`

Minimum fields:

- `guardrail_ref`
- `task_intake_refs`
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

## Expected Package Edits Later

If selected by a later `vNext+245` lock, likely touched files:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_adapter.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_cleanroom_task_intake.v1.json`
- `packages/adeu_benchmarking/schema/programbench_task_artifact_manifest.v1.json`
- `packages/adeu_benchmarking/schema/programbench_task_visibility_manifest.v1.json`
- `packages/adeu_benchmarking/schema/programbench_adapter_worker_access_contract.v1.json`
- `packages/adeu_benchmarking/schema/programbench_adapter_non_authority_guardrail.v1.json`
- matching mirror schemas under `spec/`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_adapter_pb_adapter_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus245/`

## Reference Fixture Intent

Reference fixtures should cover:

- local synthetic task intake consuming released `PB-PY-0` refs;
- artifact manifest with reference executable, usage docs, visible input
  artifact hashes, source-set hash, observed-at/snapshot refs, and ingestion
  method;
- visibility manifest with cleanroom-visible usage docs and reference
  executable refs;
- forbidden stores recorded but unreachable during inference;
- worker access contract with no internet lookup, source lookup,
  decompilation, Docker socket, host secrets, official submission generation,
  or probe execution authority;
- guardrail rows preserving non-official, non-benchmark-truth posture.

Reject fixtures should cover:

- forbidden original source marked worker-visible;
- hidden evaluator output marked inference evidence;
- hidden or forbidden evidence summarized into cleanroom-visible advisory text;
- public descriptor treated as benchmark truth;
- task intake claiming official ProgramBench participation;
- worker access contract allowing internet/source/decompilation lookup during
  inference;
- worker access contract granting command execution or probe authority in
  slice A;
- `PB-ADAPTER-0-B` or `PB-ADAPTER-0-C` artifact kind included in slice A;
- generated submission authority granted by the guardrail.

## Slice Non-Outputs

`PB-ADAPTER-0-A` must not output:

- `programbench_adapter_probe_plan@1`
- `programbench_probe_observation_log@1`
- `programbench_io_artifact_observation_index@1`
- `programbench_filesystem_side_effect_observation@1`
- `programbench_reconstruction_case_packet@1`
- `programbench_adapter_readiness_summary@1`
- `programbench_adapter_handoff@1`
- `programbench_cleanroom_adapter_family_closeout_alignment@1`
- official runner integration;
- official task execution;
- hidden-test handling;
- benchmark scoring;
- model ranking;
- code generation or generated submissions.
