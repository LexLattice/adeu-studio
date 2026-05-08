# Draft ADEU ProgramBench Cleanroom Reconstruction Workbench PB-RECON-0-A Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-RECON-0-A`.

Authority layer: support.

This note maps the first candidate slice for `PB-RECON-0`. It is not a
`vNext+248` lock, stop-gate decision, or edge assessment. Those per-slice
starter docs should be drafted only after this family-level bundle is reviewed.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v78.md`
- `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_FAMILY_v0.md`
- `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_IMPLEMENTATION_MAPPING_v0.md`

## Slice Role

`PB-RECON-0-A` should make a cleanroom reconstruction work order and worker
context reviewable without dispatching a worker, generating code, executing
commands, running probes, scoring results, or integrating an official
ProgramBench evaluator.

The slice should implement only:

- `programbench_reconstruction_work_order@1`
- `programbench_reconstruction_worker_context_packet@1`
- `programbench_reconstruction_context_exclusion_manifest@1`
- `programbench_reconstruction_sandbox_policy@1`
- `programbench_reconstruction_run_budget@1`
- `programbench_reconstruction_non_authority_guardrail@1`

## Candidate Schema Fields

### `programbench_reconstruction_work_order@1`

Minimum fields:

- `work_order_ref`
- `case_packet_ref`
- `adapter_readiness_summary_ref`
- `adapter_handoff_ref`
- `adapter_candidate_ref`
- `task_instance_ref`
- `pb_py_0_profile_refs`
- `python_realization_pack_refs`
- `worker_context_packet_ref`
- `sandbox_policy_ref`
- `run_budget_ref`
- `guardrail_refs`
- `case_packet_readiness_posture`
- `contamination_gate_posture`
- `work_order_scope_posture`
- `dispatch_authority_posture`
- `execution_authority_posture`
- `official_programbench_posture`
- `benchmark_truth_posture`
- `limitation_note`

Validator expectation:

```text
only a released case packet with ready readiness posture, clean contamination,
and no carried blockers may become a work order candidate.
```

### `programbench_reconstruction_worker_context_packet@1`

Minimum fields:

- `worker_context_packet_ref`
- `work_order_ref`
- `case_packet_ref`
- `task_instance_ref`
- `worker_visible_source_refs`
- `advisory_realization_refs`
- `concept_profile_refs`
- `probe_observation_refs`
- `io_artifact_index_refs`
- `side_effect_observation_refs`
- `context_derivation_rows`
- `context_derivation_hash_rows`
- `context_source_set_hash`
- `context_visibility_posture`
- `derived_summary_policy`
- `limitation_note`

Worker context packets may include only cleanroom-visible, worker-authorized
refs. Hidden, forbidden, postmortem-only, original-source, decompilation,
internet lookup, external repo, Docker socket, host-secret, and excluded
derived-summary refs must not appear in the worker-facing packet.

### `programbench_reconstruction_context_exclusion_manifest@1`

Minimum fields:

- `context_exclusion_manifest_ref`
- `work_order_ref`
- `worker_context_packet_ref`
- `case_packet_ref`
- `task_instance_ref`
- `worker_hidden_source_refs`
- `forbidden_source_refs`
- `postmortem_only_refs`
- `excluded_derived_summary_refs`
- `exclusion_reason_rows`
- `auditor_only_posture`
- `worker_visibility_posture`
- `limitation_note`

The exclusion manifest is an auditor-only ledger. It may prove that hidden,
forbidden, postmortem-only, and derived-forbidden material stayed out of the
worker context, but it must not be served as worker-visible context.

### `programbench_reconstruction_sandbox_policy@1`

Minimum fields:

- `sandbox_policy_ref`
- `work_order_ref`
- `worker_context_packet_ref`
- `allowed_runtime_kind`
- `network_policy`
- `filesystem_policy`
- `dependency_policy`
- `environment_policy`
- `command_shape_policy`
- `allowed_write_scope_refs`
- `forbidden_path_refs`
- `timeout_policy`
- `resource_limit_policy`
- `sandbox_enforcement_witness_requirements`
- `secret_exposure_policy`
- `docker_socket_policy`
- `source_lookup_policy`
- `decompilation_policy`
- `external_repo_lookup_policy`
- `limitation_note`

The policy is a future local sandbox boundary, not execution authority by
itself.

Minimum enforcement witness requirements for later slices:

- network disabled;
- no source lookup;
- no decompilation;
- no Docker socket;
- no host secrets;
- bounded filesystem write scope;
- argv-shaped command policy.

### `programbench_reconstruction_run_budget@1`

Minimum fields:

- `run_budget_ref`
- `work_order_ref`
- `max_candidate_artifact_count`
- `max_local_run_count`
- `max_probe_run_count`
- `max_remand_count`
- `timeout_budget_policy`
- `token_budget_policy`
- `filesystem_budget_policy`
- `budget_authority_posture`
- `limitation_note`

Budget rows constrain later work. They do not authorize execution in
`PB-RECON-0-A`.

### `programbench_reconstruction_non_authority_guardrail@1`

Minimum fields:

- `guardrail_ref`
- `work_order_refs`
- `worker_context_packet_refs`
- `context_exclusion_manifest_refs`
- `sandbox_policy_refs`
- `run_budget_refs`
- `non_authority_posture`
- `execution_posture`
- `official_programbench_posture`
- `hidden_test_posture`
- `benchmark_truth_posture`
- `submission_authority_posture`
- `model_ranking_posture`
- `future_family_selection_posture`
- `limitation_note`

## Expected Package Edits Later

If selected by a later `vNext+248` lock, likely touched files:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_reconstruction.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_work_order.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_worker_context_packet.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_context_exclusion_manifest.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_sandbox_policy.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_run_budget.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_non_authority_guardrail.v1.json`
- matching mirror schemas under `spec/`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_reconstruction_pb_recon_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus248/`

## Reference Fixture Intent

Reference fixtures should cover:

- work order consuming released `PB-ADAPTER-0-C` case packet and readiness
  refs;
- worker context packet derived from cleanroom-visible case-packet refs only;
- auditor-only exclusion manifest recording hidden, forbidden, postmortem-only,
  and excluded derived-summary refs without exposing them to the worker;
- advisory `PB-PY-0` concept/profile/realization refs kept non-authoritative;
- sandbox policy with no network, no source lookup, no decompilation, no
  Docker socket, no host secrets, no external repo lookup, bounded filesystem,
  and argv-shaped command policy;
- run budget with local attempt/probe/remand limits but no execution authority;
- guardrail rows preserving non-official, non-benchmark-truth,
  non-model-ranking, non-submission posture.

Reject fixtures should cover:

- blocked or contaminated case packet used as ready work order;
- worker context including hidden or forbidden source refs;
- worker context including derived summaries from forbidden evidence;
- exclusion manifest marked worker-visible instead of auditor-only;
- sandbox policy allowing internet/source/decompilation/external repo lookup;
- sandbox policy exposing Docker socket or host secrets;
- run budget granting execution authority in slice A;
- guardrail claiming official ProgramBench participation, benchmark truth,
  official submission, model ranking, or future-family selection;
- `PB-RECON-0-B` or `PB-RECON-0-C` artifact kind included in slice A.

Bundle validation should resolve the forward/circular refs among work order,
worker context packet, exclusion manifest, sandbox policy, run budget, and
guardrail rows together and reject dangling or mismatched refs.

## Slice Non-Outputs

`PB-RECON-0-A` must not output:

- `programbench_reconstruction_candidate_artifact_manifest@1`
- `programbench_reconstruction_local_run_trace@1`
- `programbench_reconstruction_probe_result_log@1`
- `programbench_reconstruction_remand_correction_record@1`
- `programbench_reconstruction_equivalence_audit@1`
- `programbench_reconstruction_result_summary@1`
- `programbench_reconstruction_handoff@1`
- `programbench_reconstruction_workbench_family_closeout_alignment@1`
- generated Python implementation;
- local command execution traces;
- probe run results;
- official runner or evaluator integration;
- hidden-test handling;
- benchmark scoring;
- model ranking;
- official submission artifacts.
