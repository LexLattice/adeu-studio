# LOCKED_CONTINUATION_vNEXT_PLUS251

## Status

Bounded starter lock draft for `PB-ATTEMPT-0-A` (attempt request,
worker-visible input packet, dispatch preflight, and attempt non-authority
guardrail).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-ATTEMPT-0-A` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-ATTEMPT-0`
- slice: `PB-ATTEMPT-0-A`
- branch-local execution target: `arc/pb-attempt-0-a`

## Purpose

Freeze the bounded `PB-ATTEMPT-0-A` starter slice so the repo can make a
local cleanroom reconstruction attempt request, exact worker-visible input
packet, dispatch eligibility preflight, and attempt non-authority guardrail
reviewable under released `PB-RECON-0` workbench law.

`vNext+251` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize worker
invocation, command execution, candidate materialization, local probe
execution, workbench evidence export, attempt result review, remand queue,
official ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, model
ranking, generated official submissions, official submission authority,
unbounded command execution, target mutation outside released local artifacts,
runtime transition, product authorization, graph-memory authority, recursive
policy amendment, or future-family selection.

Controlling invariant:

```text
PB-ATTEMPT-0-A may package attempt eligibility and worker-visible input for a
later local cleanroom worker attempt review, but it may not dispatch a worker,
materialize candidate files, run probes, export workbench evidence, claim
benchmark truth, create official submissions, rank models, or select a future
family.
```

## Instantiated Here

- `PB-ATTEMPT-0-A` instantiates the first local cleanroom reconstruction
  attempt seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-RECON-0` basis:
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_FAMILY_CLOSEOUT_v0.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS248.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS249.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS250.md`
    - `docs/ASSESSMENT_vNEXT_PLUS248_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS249_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS250_EDGES.md`
    - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_work_order_v248_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_worker_context_packet_v248_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_context_exclusion_manifest_v248_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_sandbox_policy_v248_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_run_budget_v248_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus248/programbench_reconstruction_workbench_non_authority_guardrail_v248_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus250/programbench_reconstruction_result_summary_v250_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus250/programbench_reconstruction_workbench_family_closeout_alignment_v250_reference.json`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v79.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0A_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0C_IMPLEMENTATION_MAPPING_v0.md`
  - emitted first-slice record shapes:
    - `programbench_reconstruction_attempt_request@1`
    - `programbench_reconstruction_attempt_worker_input_packet@1`
    - `programbench_reconstruction_attempt_dispatch_preflight@1`
    - `programbench_reconstruction_attempt_non_authority_guardrail@1`

## Required Starter Vocabulary

Minimum `programbench_reconstruction_attempt_request@1` fields:

- `attempt_request_ref`
- `work_order_ref`
- `worker_context_packet_ref`
- `context_exclusion_manifest_ref`
- `sandbox_policy_ref`
- `run_budget_ref`
- `result_summary_ref`
- `workbench_family_closeout_ref`
- `attempt_purpose`
- `worker_profile_ref`
- `attempt_scope_posture`
- `dispatch_authority_posture`
- `official_programbench_posture`
- `benchmark_truth_posture`
- `model_ranking_posture`
- `limitation_note`

Compatible consumed `PB-RECON-0` result-summary postures:

- `local_remand_required`
- `inconclusive_local_audit`
- `blocked_by_missing_evidence`, only when the attempt purpose is explicitly
  evidence-gap remediation

Blocked consumed result-summary postures:

- `local_accepted`
- `blocked_by_contamination`
- `blocked_by_sandbox_violation`
- `future_family_only`

Required authority postures:

- `dispatch_authority_posture =
  no_worker_dispatch_authority_granted_by_pb_attempt_0a`
- `official_programbench_posture =
  no_official_programbench_participation_by_pb_attempt_0a`
- `benchmark_truth_posture = not_benchmark_truth`
- `model_ranking_posture = no_model_ranking_claimed_by_pb_attempt_0a`

Minimum `programbench_reconstruction_attempt_worker_input_packet@1` fields:

- `worker_input_packet_ref`
- `attempt_request_ref`
- `worker_visible_source_refs`
- `advisory_concept_profile_refs`
- `advisory_realization_refs`
- `probe_expectation_refs`
- `sandbox_summary_refs`
- `run_budget_summary_refs`
- `excluded_ref_summary_rows`
- `context_derivation_rows`
- `worker_input_manifest_hash`
- `worker_visible_ref_count`
- `forbidden_ref_exposure_check_hash`
- `worker_visibility_posture`
- `input_materialization_posture`
- `limitation_note`

Excluded-ref summary rows may include only:

- exclusion category;
- count;
- reason code;
- authority posture;
- non-exposure statement.

Excluded-ref summary rows must not include:

- source path;
- source name;
- content excerpt;
- semantic summary;
- derived fact;
- test name;
- hidden artifact identifier;
- original-source clue.

Minimum `programbench_reconstruction_attempt_dispatch_preflight@1` fields:

- `dispatch_preflight_ref`
- `attempt_request_ref`
- `worker_input_packet_ref`
- `sandbox_policy_ref`
- `run_budget_ref`
- `guardrail_ref`
- `preflight_check_rows`
- `sandbox_enforcement_requirement_refs`
- `budget_enforcement_requirement_refs`
- `preflight_scope_posture`
- `preflight_posture`
- `dispatch_authority_posture`
- `execution_authority_posture`
- `limitation_note`

Required scope posture:

- `preflight_scope_posture = eligibility_review_only_no_invocation`

Allowed `preflight_posture` values:

- `preflight_passed_for_later_local_attempt_review`
- `blocked_by_missing_released_workbench_ref`
- `blocked_by_visibility_gap`
- `blocked_by_sandbox_gap`
- `blocked_by_budget_gap`
- `blocked_by_guardrail_gap`
- `future_family_only`

Minimum `programbench_reconstruction_attempt_non_authority_guardrail@1`
fields:

- `guardrail_ref`
- `attempt_request_ref`
- `forbidden_authority_rows`
- `official_programbench_non_authority_posture`
- `hidden_test_non_inference_posture`
- `source_lookup_non_authority_posture`
- `submission_non_authority_posture`
- `benchmark_truth_non_authority_posture`
- `model_ranking_non_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_reconstruction_attempt_request@1`
  - `programbench_reconstruction_attempt_worker_input_packet@1`
  - `programbench_reconstruction_attempt_dispatch_preflight@1`
  - `programbench_reconstruction_attempt_non_authority_guardrail@1`
- deterministic reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus251/`;
- validators that prove:
  - released `PB-RECON-0` workbench refs and family closeout alignment are
    required before A rows validate;
  - consumed result-summary posture is compatible with a remand/evidence-gap
    attempt request;
  - worker input packets include only worker-visible refs and allowed advisory
    refs;
  - auditor-only, forbidden, hidden, postmortem-only, original-source,
    decompilation, internet-lookup, external-repo, host-secret, or
    Docker-socket refs cannot appear as worker-visible material;
  - excluded-ref summaries reject source-identifying or content-bearing
    fields;
  - worker input manifest hash, worker-visible ref count, and forbidden-ref
    exposure check hash are present;
  - dispatch preflight is eligibility review only and cannot grant worker
    invocation, command execution, or probe execution authority;
  - guardrail rows reject official ProgramBench, hidden-test inference,
    source lookup, official submission, benchmark truth, model ranking, and
    future-family authority;
  - `PB-ATTEMPT-0-B/C` artifact kinds remain absent.

## Deferred To Later Slice

- `PB-ATTEMPT-0-B` worker invocation records, output captures, candidate
  materialization records, and sandbox application traces;
- `PB-ATTEMPT-0-C` workbench evidence exports, attempt result reviews, remand
  queues, and family closeout alignment.

## Deferred To Later Family

- official ProgramBench participation;
- hidden evaluator result governance;
- generated official submission review;
- benchmark scoring and model ranking;
- broader conceptual broker implementation;
- larger local fixture matrix expansion;
- product, graph-memory, release, or recursive-policy work.

## Machine-Checkable Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS251.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+251",
  "target_path": "PB-ATTEMPT-0-A",
  "slice": "PB-ATTEMPT-0-A",
  "family": "PB-ATTEMPT-0",
  "branch_local_execution_target": "arc/pb-attempt-0-a",
  "target_scope": "attempt_request_worker_input_preflight_guardrail_slice",
  "implementation_packages": [
    "adeu_benchmarking"
  ],
  "api_surfaces": [],
  "prerequisite_locks": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS248.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS249.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS250.md"
  ],
  "prerequisite_decision_docs": [
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS248.md",
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS249.md",
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS250.md"
  ],
  "prerequisite_assessments": [
    "docs/ASSESSMENT_vNEXT_PLUS248_EDGES.md",
    "docs/ASSESSMENT_vNEXT_PLUS249_EDGES.md",
    "docs/ASSESSMENT_vNEXT_PLUS250_EDGES.md"
  ],
  "planning_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v79.md",
    "docs/ARCHITECTURE_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_FAMILY_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0A_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0B_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0C_IMPLEMENTATION_MAPPING_v0.md"
  ],
  "consumed_record_shapes": [
    "programbench_reconstruction_work_order@1",
    "programbench_reconstruction_worker_context_packet@1",
    "programbench_reconstruction_context_exclusion_manifest@1",
    "programbench_reconstruction_sandbox_policy@1",
    "programbench_reconstruction_run_budget@1",
    "programbench_reconstruction_result_summary@1",
    "programbench_reconstruction_workbench_family_closeout_alignment@1"
  ],
  "emitted_record_shapes": [
    "programbench_reconstruction_attempt_request@1",
    "programbench_reconstruction_attempt_worker_input_packet@1",
    "programbench_reconstruction_attempt_dispatch_preflight@1",
    "programbench_reconstruction_attempt_non_authority_guardrail@1"
  ],
  "forbidden_claims": [
    "worker_invocation_authority",
    "command_execution_authority",
    "candidate_materialization",
    "local_probe_execution",
    "workbench_evidence_export",
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
    "future_family_selection"
  ],
  "local_gate": "make arc-start-check ARC=251"
}
```
