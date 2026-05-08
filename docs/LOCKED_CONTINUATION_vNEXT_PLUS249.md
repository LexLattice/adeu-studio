# LOCKED_CONTINUATION_vNEXT_PLUS249

## Status

Bounded starter lock draft for `PB-RECON-0-B` (candidate artifact manifest,
local sandbox run trace, probe result log, and remand/correction record).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-RECON-0-B` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-RECON-0`
- slice: `PB-RECON-0-B`
- branch-local execution target: `arc/pb-recon-0-b`

## Purpose

Freeze the bounded `PB-RECON-0-B` starter slice so the repo can make local
worker-generated candidate artifacts, sandboxed run traces, local probe
results, and remand/correction rows reviewable under the released
`PB-RECON-0-A` work order, worker-visible context packet, auditor-only
exclusion manifest, sandbox policy, run budget, and non-authority guardrail.

`vNext+249` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize
official ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling, hidden-test
inference, hidden-test equivalence, original source lookup, decompilation,
internet lookup inside ProgramBench tasks, external repository lookup,
benchmark submission, benchmark scoring, benchmark truth, model ranking,
generated official submissions, equivalence audit, result summary, handoff,
family closeout alignment, unbounded command execution, target mutation
outside the released sandbox, runtime transition, product authorization,
graph-memory authority, recursive policy amendment, or future-family
selection.

Controlling invariant:

```text
PB-RECON-0-B may capture local workbench candidate artifacts, sandboxed local
run traces, local probe result rows, and local remand/correction evidence
under a released PB-RECON-0-A work order, but it may not claim official
submission authority, hidden-test equivalence, benchmark truth, model ranking,
or local accepted status.
```

## Instantiated Here

- `PB-RECON-0-B` instantiates the second local cleanroom reconstruction
  workbench seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-RECON-0-A` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS248.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS248.md`
    - `docs/ASSESSMENT_vNEXT_PLUS248_EDGES.md`
    - `artifacts/agent_harness/v248/evidence_inputs/pb_recon_0a_work_order_closeout_evidence_v248.json`
    - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_work_order_v248_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_worker_context_packet_v248_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_context_exclusion_manifest_v248_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_sandbox_policy_v248_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_run_budget_v248_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_workbench_non_authority_guardrail_v248_reference.json`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v78.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0A_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0C_IMPLEMENTATION_MAPPING_v0.md`
  - emitted second-slice record shapes:
    - `programbench_reconstruction_candidate_artifact_manifest@1`
    - `programbench_reconstruction_local_run_trace@1`
    - `programbench_reconstruction_probe_result_log@1`
    - `programbench_reconstruction_remand_correction_record@1`

## Required Starter Vocabulary

Minimum `programbench_reconstruction_candidate_artifact_manifest@1` fields:

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

Candidate artifact rows are local workbench outputs only. They are not
official ProgramBench submissions.

Minimum `programbench_reconstruction_local_run_trace@1` fields:

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

Required local-run law:

```text
local run traces must bind to a released sandbox policy, released run budget,
command allowlist match, sandbox attestation, network attestation,
secret-absence attestation, and write-scope attestation before they are
admissible local workbench evidence.
```

Minimum `programbench_reconstruction_probe_result_log@1` fields:

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
equivalence, benchmark truth, benchmark scores, or local accepted status.

Minimum `programbench_reconstruction_remand_correction_record@1` fields:

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

Allowed `remand_reason_source` values:

- `local_probe_failure`
- `local_sandbox_violation`
- `missing_required_artifact`
- `unsupported_behavior_gap`
- `inconclusive_trace`

Forbidden `remand_reason_source` values:

- `hidden_test_failure`
- `official_evaluator_feedback`
- `original_source_observation`
- `decompilation_observation`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_reconstruction_candidate_artifact_manifest@1`
  - `programbench_reconstruction_local_run_trace@1`
  - `programbench_reconstruction_probe_result_log@1`
  - `programbench_reconstruction_remand_correction_record@1`
- deterministic reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus249/`;
- validators that prove:
  - released `PB-RECON-0-A` work order, worker context, exclusion manifest,
    sandbox policy, run budget, and guardrail refs are required before B rows
    validate;
  - candidate artifacts remain local workbench artifacts and cannot claim
    official ProgramBench submission authority;
  - local run traces require command allowlist matches, sandbox attestations,
    network attestations, secret-absence attestations, write-scope
    attestations, released sandbox policy, and released run budget refs;
  - local run commands are argv-shaped and bounded by the released sandbox and
    budget;
  - stdout/stderr evidence is represented by hashes plus bounded excerpts, not
    unbounded output blobs;
  - filesystem evidence records pre/post manifests and filesystem diff refs;
  - sandbox violations cannot be treated as successful local evidence;
  - probe result logs cannot claim benchmark truth, hidden-test equivalence,
    official evaluator result, benchmark score, model ranking, or local
    accepted status;
  - remand/correction rows are local-probe/local-sandbox/local-artifact
    bounded and cannot use hidden tests, official evaluator feedback, original
    source, decompilation evidence, or case-packet mutation;
  - `PB-RECON-0-C` equivalence audits, result summaries, handoffs, and family
    closeout alignment remain deferred.

## Deferred To Later Slice Or Family

- `PB-RECON-0-C`:
  - local equivalence audit;
  - reconstruction result summary;
  - post-reconstruction handoff;
  - workbench family closeout alignment.
- later family:
  - official ProgramBench participation;
  - hidden evaluator result governance;
  - generated official submission review;
  - benchmark scoring and model ranking;
  - broader conceptual broker implementation;
  - product, graph-memory, release, or recursive-policy work.

## Machine-Checkable Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS249.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+249",
  "target_path": "PB-RECON-0-B",
  "slice": "PB-RECON-0-B",
  "family": "PB-RECON-0",
  "branch_local_execution_target": "arc/pb-recon-0-b",
  "target_scope": "cleanroom_candidate_artifact_local_run_probe_result_and_remand_capture_slice",
  "implementation_packages": [
    "adeu_benchmarking"
  ],
  "api_surfaces": [],
  "prerequisite_locks": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS248.md"
  ],
  "prerequisite_decision_docs": [
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS248.md"
  ],
  "prerequisite_assessments": [
    "docs/ASSESSMENT_vNEXT_PLUS248_EDGES.md"
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
    "programbench_reconstruction_work_order@1",
    "programbench_reconstruction_worker_context_packet@1",
    "programbench_reconstruction_context_exclusion_manifest@1",
    "programbench_reconstruction_sandbox_policy@1",
    "programbench_reconstruction_run_budget@1",
    "programbench_reconstruction_workbench_non_authority_guardrail@1"
  ],
  "emitted_record_shapes": [
    "programbench_reconstruction_candidate_artifact_manifest@1",
    "programbench_reconstruction_local_run_trace@1",
    "programbench_reconstruction_probe_result_log@1",
    "programbench_reconstruction_remand_correction_record@1"
  ],
  "forbidden_claims": [
    "official_programbench_participation",
    "official_programbench_runner_integrated",
    "official_programbench_evaluator_integrated",
    "hidden_test_visible_to_worker",
    "hidden_test_inference",
    "hidden_test_equivalence_claimed",
    "official_submission_authority",
    "benchmark_score_created",
    "benchmark_truth_claimed",
    "model_ranking_claimed",
    "equivalence_audit_created",
    "local_accepted_status_created",
    "result_summary_created",
    "handoff_created",
    "future_family_selection"
  ],
  "local_gate": "make arc-start-check ARC=249"
}
```
