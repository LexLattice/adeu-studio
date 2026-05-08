# LOCKED_CONTINUATION_vNEXT_PLUS248

## Status

Bounded starter lock draft for `PB-RECON-0-A` (reconstruction work order,
worker-visible context packet, auditor-only context exclusion manifest,
sandbox policy, run budget, and reconstruction non-authority guardrail).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-RECON-0-A` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-RECON-0`
- slice: `PB-RECON-0-A`
- branch-local execution target: `arc/pb-recon-0-a`

## Purpose

Freeze the bounded `PB-RECON-0-A` starter slice so the repo can turn a
released, ready, uncontaminated `PB-ADAPTER-0-C` reconstruction case packet
into a reviewable local reconstruction work order, worker-visible context
packet, auditor-only exclusion manifest, sandbox policy, run budget, and
non-authority guardrail before any worker dispatch, generated implementation,
local command run, probe result, equivalence audit, official ProgramBench
participation, or benchmark score exists.

`vNext+248` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize worker
dispatch, generated Python implementation, candidate submission artifacts,
local command execution, probe execution, equivalence audits, official
ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, model
ranking, arbitrary command execution, target mutation, runtime transition,
product authorization, graph-memory authority, recursive policy amendment, or
future-family selection.

Controlling invariant:

```text
PB-RECON-0-A may define what exact released case packet, worker-visible
context, exclusion ledger, sandbox, and budget a later local reconstruction
worker could use, but it may not dispatch that worker, generate code, execute
commands, run probes, score results, or claim benchmark truth.
```

## Instantiated Here

- `PB-RECON-0-A` instantiates the first local cleanroom reconstruction
  workbench seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-ADAPTER-0` basis:
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS247.md`
    - `docs/ASSESSMENT_vNEXT_PLUS247_EDGES.md`
    - `artifacts/agent_harness/v247/evidence_inputs/pb_adapter_0c_case_packet_closeout_evidence_v247.json`
    - `apps/api/fixtures/benchmarking/vnext_plus247/programbench_reconstruction_case_packet_v247_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus247/programbench_adapter_readiness_summary_v247_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus247/programbench_adapter_handoff_v247_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus247/programbench_cleanroom_adapter_family_closeout_alignment_v247_reference.json`
  - consumed released `PB-PY-0` basis:
    - `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`
    - `apps/api/fixtures/benchmarking/vnext_plus244/programbench_realization_family_closeout_alignment_v244_reference.json`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v78.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0A_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0C_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/support/ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_DIRECTION_v0.md`
  - emitted first-slice record shapes:
    - `programbench_reconstruction_work_order@1`
    - `programbench_reconstruction_worker_context_packet@1`
    - `programbench_reconstruction_context_exclusion_manifest@1`
    - `programbench_reconstruction_sandbox_policy@1`
    - `programbench_reconstruction_run_budget@1`
    - `programbench_reconstruction_non_authority_guardrail@1`

## Required Starter Vocabulary

Minimum `programbench_reconstruction_work_order@1` fields:

- `work_order_ref`
- `case_packet_ref`
- `adapter_readiness_summary_ref`
- `adapter_handoff_ref`
- `adapter_candidate_ref`
- `task_instance_ref`
- `pb_py_0_profile_refs`
- `python_realization_pack_refs`
- `worker_context_packet_ref`
- `context_exclusion_manifest_ref`
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

Required work-order posture:

```text
dispatch_authority_posture = no_worker_dispatch_authority_granted_by_pb_recon_0a
execution_authority_posture = no_execution_authority_granted_by_pb_recon_0a
```

Only a released case packet with ready readiness posture, clean
contamination, and no carried blockers may become a work order candidate.

Minimum `programbench_reconstruction_worker_context_packet@1` fields:

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

Worker context packets are worker-facing. They may include only
cleanroom-visible, worker-authorized refs. Hidden, forbidden, postmortem-only,
original-source, decompilation, internet lookup, external repo, Docker socket,
host-secret, and excluded derived-summary refs must not appear in this packet.

Minimum `programbench_reconstruction_context_exclusion_manifest@1` fields:

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

The exclusion manifest is auditor-only. It can prove that excluded material
stayed out of the worker context, but it must not be served into worker-visible
context.

Minimum `programbench_reconstruction_sandbox_policy@1` fields:

- `sandbox_policy_ref`
- `work_order_ref`
- `worker_context_packet_ref`
- `context_exclusion_manifest_ref`
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

Required sandbox enforcement witness requirements for later slices:

- network disabled;
- no source lookup;
- no decompilation;
- no Docker socket;
- no host secrets;
- bounded filesystem write scope;
- argv-shaped command policy.

Minimum `programbench_reconstruction_run_budget@1` fields:

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

Minimum `programbench_reconstruction_non_authority_guardrail@1` fields:

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

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_reconstruction_work_order@1`
  - `programbench_reconstruction_worker_context_packet@1`
  - `programbench_reconstruction_context_exclusion_manifest@1`
  - `programbench_reconstruction_sandbox_policy@1`
  - `programbench_reconstruction_run_budget@1`
  - `programbench_reconstruction_non_authority_guardrail@1`
- deterministic reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus248/`;
- validators that prove:
  - released `PB-ADAPTER-0-C` case packet, readiness, and handoff refs are
    required before work orders validate;
  - contaminated, blocked, hidden-exposed, forbidden-exposed, or
    future-family-only case packets cannot become ready work orders;
  - work order, worker context packet, exclusion manifest, sandbox policy, run
    budget, and guardrail refs resolve as one bundle and reject dangling or
    mismatched refs;
  - worker context packets include only cleanroom-visible,
    worker-authorized refs;
  - hidden, forbidden, postmortem-only, original-source, decompilation,
    internet lookup, external-repo, Docker-socket, host-secret, and excluded
    derived-summary refs cannot appear in the worker-facing context packet;
  - exclusion manifests are auditor-only and cannot be marked worker-visible;
  - derived summaries from forbidden evidence cannot enter worker context;
  - sandbox policies reject network, source lookup, decompilation, Docker
    socket, host-secret, and external-repo access;
  - sandbox policies declare enforcement witness requirements for later
    slices;
  - run budgets cannot grant execution authority in slice A;
  - guardrails reject official ProgramBench participation, hidden-test
    inference, hidden-test equivalence, benchmark truth, benchmark scoring,
    model ranking, official submissions, product authority, graph authority,
    release authority, recursive-policy authority, and future-family
    selection;
  - `PB-RECON-0-A` rejects `PB-RECON-0-B` and `PB-RECON-0-C` artifact kinds;
  - no candidate artifacts, run traces, probe result logs,
    remand/correction records, equivalence audits, result summaries, handoffs,
    benchmark scores, model rankings, generated submissions, official
    evaluator integration, product authority, graph authority, release
    authority, recursive-policy authority, or future-family selection ship in
    this slice.

## Deferred To Later Slice Or Family

- `PB-RECON-0-B` candidate artifact manifests, local run traces, probe result
  logs, and remand/correction records;
- `PB-RECON-0-C` local equivalence audits, result summaries, handoffs, and
  family closeout alignment;
- local reconstruction execution outside the selected workbench boundary;
- official ProgramBench participation and result governance;
- hidden evaluator feedback governance;
- generated official submissions;
- official runner or evaluator integration;
- benchmark scoring and model ranking;
- broader conceptual broker implementation;
- larger local fixture matrices;
- V86/V87/V88 meta-loop continuations;
- product, graph-memory, release, or recursive-policy work.

## Machine-Checkable Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS248.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+248",
  "target_path": "PB-RECON-0-A",
  "slice": "PB-RECON-0-A",
  "family": "PB-RECON-0",
  "branch_local_execution_target": "arc/pb-recon-0-a",
  "target_scope": "cleanroom_reconstruction_work_order_context_exclusion_sandbox_budget_and_guardrail_slice",
  "implementation_packages": [
    "adeu_benchmarking"
  ],
  "api_surfaces": [],
  "prerequisite_locks": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS247.md"
  ],
  "prerequisite_decision_docs": [
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS247.md"
  ],
  "prerequisite_assessments": [
    "docs/ASSESSMENT_vNEXT_PLUS247_EDGES.md"
  ],
  "planning_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v78.md",
    "docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_FAMILY_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0A_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0B_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0C_IMPLEMENTATION_MAPPING_v0.md"
  ],
  "consumed_record_shapes": [
    "programbench_reconstruction_case_packet@1",
    "programbench_adapter_readiness_summary@1",
    "programbench_adapter_handoff@1",
    "programbench_cleanroom_adapter_family_closeout_alignment@1",
    "programbench_realization_family_closeout_alignment@1"
  ],
  "emitted_record_shapes": [
    "programbench_reconstruction_work_order@1",
    "programbench_reconstruction_worker_context_packet@1",
    "programbench_reconstruction_context_exclusion_manifest@1",
    "programbench_reconstruction_sandbox_policy@1",
    "programbench_reconstruction_run_budget@1",
    "programbench_reconstruction_non_authority_guardrail@1"
  ],
  "forbidden_claims": [
    "worker_dispatch_authority",
    "generated_python_implementation",
    "candidate_submission_artifact",
    "local_command_execution_trace",
    "probe_result_log",
    "equivalence_audit",
    "official_programbench_participation",
    "official_programbench_runner_integrated",
    "official_programbench_evaluator_integrated",
    "official_programbench_task_executed",
    "hidden_test_visible_to_worker",
    "hidden_test_inference",
    "hidden_test_equivalence_claimed",
    "hidden_or_forbidden_ref_in_worker_context",
    "hidden_or_forbidden_summary_exposed_to_worker",
    "original_source_lookup",
    "decompilation",
    "internet_lookup_for_task",
    "external_repo_lookup_for_task",
    "docker_socket_exposed",
    "host_secret_exposed",
    "command_execution_authority",
    "probe_execution_authority",
    "submission_generation_authority",
    "benchmark_score_created",
    "benchmark_truth_claimed",
    "model_ranking_claimed",
    "future_family_selection"
  ],
  "local_gate": "make arc-start-check ARC=248"
}
```
