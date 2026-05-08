# LOCKED_CONTINUATION_vNEXT_PLUS254

## Status

Bounded starter lock draft for `PB-TRIAL-0-A` (trial docket, local execution
runbook, sandbox readiness review, and trial non-authority guardrail).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-TRIAL-0-A` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-TRIAL-0`
- slice: `PB-TRIAL-0-A`
- branch-local execution target: `arc/pb-trial-0-a`

## Purpose

Freeze the bounded `PB-TRIAL-0-A` starter slice so the repo can make one local
cleanroom reconstruction trial docket, execution runbook, sandbox readiness
review, and trial non-authority guardrail reviewable under released
`PB-ATTEMPT-0` lifecycle law.

`vNext+254` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize worker
dispatch, command execution, candidate artifact snapshotting, local trial
execution capture, lifecycle projection, local outcome audit, trial
observation summary, remand decision, retry dispatch authority, official
ProgramBench participation, official task execution, official runner
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
PB-TRIAL-0-A may docket one released local cleanroom attempt lifecycle package
and define the runbook/readiness law for a later local trial, but it may not
dispatch a worker, execute commands, snapshot candidates, audit outcomes,
grant retry authority, claim benchmark truth, create official submissions,
rank models, or select a future family.
```

## Instantiated Here

- `PB-TRIAL-0-A` instantiates the first local cleanroom reconstruction trial
  seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-ATTEMPT-0` basis:
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_FAMILY_CLOSEOUT_v0.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS251.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS252.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS253.md`
    - `docs/ASSESSMENT_vNEXT_PLUS251_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS252_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS253_EDGES.md`
    - `apps/api/fixtures/benchmarking/vnext_plus251/programbench_reconstruction_attempt_request_v251_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus251/programbench_reconstruction_attempt_worker_input_packet_v251_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus251/programbench_reconstruction_attempt_dispatch_preflight_v251_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus251/programbench_reconstruction_attempt_non_authority_guardrail_v251_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus253/programbench_reconstruction_attempt_result_review_v253_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus253/programbench_reconstruction_attempt_family_closeout_alignment_v253_reference.json`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v80.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0A_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0C_IMPLEMENTATION_MAPPING_v0.md`
  - emitted first-slice record shapes:
    - `programbench_local_reconstruction_trial_docket@1`
    - `programbench_local_trial_execution_runbook@1`
    - `programbench_local_trial_sandbox_readiness_review@1`
    - `programbench_local_trial_non_authority_guardrail@1`

## Required Starter Vocabulary

Minimum `programbench_local_reconstruction_trial_docket@1` fields:

- `trial_docket_ref`
- `attempt_request_ref`
- `worker_input_packet_ref`
- `dispatch_preflight_ref`
- `attempt_guardrail_ref`
- `prior_attempt_result_review_context_ref`
- `attempt_family_closeout_ref`
- `workbench_lineage_refs`
- `case_packet_refs`
- `worker_profile_ref`
- `trial_purpose`
- `trial_cardinality_posture`
- `official_programbench_posture`
- `benchmark_truth_posture`
- `model_ranking_posture`
- `retry_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

Required docket law:

```text
prior_attempt_result_review_context_ref may be lifecycle / closeout /
eligibility context only. It must not be counted as the PB-TRIAL-0 trial
outcome.
```

Required postures:

- `trial_cardinality_posture = single_trial_only`
- `official_programbench_posture =
  no_official_programbench_participation_by_pb_trial_0a`
- `benchmark_truth_posture = not_benchmark_truth`
- `model_ranking_posture = no_model_ranking_claimed_by_pb_trial_0a`
- `retry_authority_posture = no_retry_authority_granted_by_pb_trial_0a`
- `future_family_selection_posture = no_future_family_selected_by_pb_trial_0a`

Minimum `programbench_local_trial_execution_runbook@1` fields:

- `trial_runbook_ref`
- `trial_docket_ref`
- `worker_input_packet_hash`
- `worker_visible_context_hash`
- `runbook_hash`
- `trial_input_materialization_policy_ref`
- `sandbox_policy_ref`
- `run_budget_ref`
- `allowed_step_rows`
- `forbidden_step_rows`
- `capture_obligation_rows`
- `write_scope_refs`
- `tool_manifest_refs`
- `timeout_policy_ref`
- `environment_policy_ref`
- `sandbox_witness_requirement_refs`
- `runbook_scope_posture`
- `dispatch_authority_posture`
- `execution_authority_posture`
- `limitation_note`

Required postures:

- `runbook_scope_posture = execution_plan_only_no_dispatch_by_pb_trial_0a`
- `dispatch_authority_posture =
  no_worker_dispatch_authority_granted_by_pb_trial_0a`
- `execution_authority_posture =
  no_command_execution_authority_granted_by_pb_trial_0a`

Minimum `programbench_local_trial_sandbox_readiness_review@1` fields:

- `sandbox_readiness_review_ref`
- `trial_docket_ref`
- `trial_runbook_ref`
- `sandbox_policy_ref`
- `run_budget_ref`
- `readiness_check_rows`
- `sandbox_witness_requirement_refs`
- `network_readiness_posture`
- `source_lookup_readiness_posture`
- `decompilation_readiness_posture`
- `docker_socket_readiness_posture`
- `host_secret_readiness_posture`
- `write_scope_readiness_posture`
- `tool_manifest_readiness_posture`
- `budget_readiness_posture`
- `readiness_posture`
- `execution_authority_posture`
- `limitation_note`

Allowed `readiness_posture` values:

- `ready_for_later_local_trial_execution_review`
- `blocked_by_missing_released_attempt_ref`
- `blocked_by_worker_input_hash_gap`
- `blocked_by_sandbox_gap`
- `blocked_by_budget_gap`
- `blocked_by_tool_manifest_gap`
- `blocked_by_guardrail_gap`
- `future_family_only`

Required readiness law:

```text
ready_for_later_local_trial_execution_review requires every readiness row to
map to a later B sandbox witness requirement, including a closed tool manifest
requirement. Readiness passed is not execution authority.
```

Minimum `programbench_local_trial_non_authority_guardrail@1` fields:

- `trial_guardrail_ref`
- `trial_docket_ref`
- `forbidden_authority_rows`
- `official_programbench_non_authority_posture`
- `hidden_test_non_inference_posture`
- `source_lookup_non_authority_posture`
- `submission_non_authority_posture`
- `benchmark_truth_non_authority_posture`
- `model_ranking_non_authority_posture`
- `retry_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_local_reconstruction_trial_docket@1`
  - `programbench_local_trial_execution_runbook@1`
  - `programbench_local_trial_sandbox_readiness_review@1`
  - `programbench_local_trial_non_authority_guardrail@1`
- mirrored `spec/` schema exports for the same shapes;
- deterministic reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus254/`;
- validators that prove:
  - released `PB-ATTEMPT-0` refs and family closeout alignment are required
    before A rows validate;
  - trial docket selects exactly one attempt lifecycle package;
  - prior `PB-ATTEMPT-0` result-review rows are lifecycle context only and
    cannot become `PB-TRIAL-0` outcome evidence;
  - trial docket rejects hidden-test, original-source, decompilation,
    internet, external-repo, host-secret, Docker-socket, official evaluator,
    benchmark-score, model-ranking, and retry-authority evidence;
  - execution runbook requires worker input packet hash,
    worker-visible context hash, runbook hash, input materialization policy
    ref, sandbox/budget refs, and sandbox witness requirement refs;
  - execution runbook is plan-only and cannot grant worker dispatch or
    command execution authority;
  - sandbox readiness review requires network disabled, source lookup
    disabled, decompilation disabled, Docker socket absent, host secrets
    absent, bounded write scope, closed tool manifest, and run budget;
  - readiness marked ready requires every readiness row to map to a later B
    witness requirement;
  - readiness marked ready rejects non-closed tool manifest posture;
  - trial guardrail forbids official ProgramBench, hidden-test inference,
    source lookup, official submissions, benchmark truth, model ranking,
    retry authority, and future-family selection;
  - `PB-TRIAL-0-B/C` artifact kinds remain absent.

Expected implementation scope:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_trial.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_local_reconstruction_trial_docket.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_execution_runbook.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_sandbox_readiness_review.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_trial_non_authority_guardrail.v1.json`
- `spec/programbench_local_reconstruction_trial_docket.schema.json`
- `spec/programbench_local_trial_execution_runbook.schema.json`
- `spec/programbench_local_trial_sandbox_readiness_review.schema.json`
- `spec/programbench_local_trial_non_authority_guardrail.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_trial_pb_trial_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus254/`

## Explicit Non-Outputs

`PB-TRIAL-0-A` must not output:

- worker dispatch record;
- command execution;
- execution capture;
- candidate artifact snapshot;
- lifecycle projection;
- outcome audit;
- trial observation summary;
- remand decision;
- family closeout alignment;
- official ProgramBench runner/evaluator integration;
- official task execution;
- official submission artifact;
- hidden-test handling;
- hidden-test equivalence;
- benchmark score;
- benchmark truth;
- model ranking or leaderboard row;
- retry dispatch authority;
- source lookup, decompilation, internet lookup, or external repo diagnostic;
- product, graph-memory, release, recursive-policy, or future-family
  selection.

## Starter Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS254.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+254",
  "target_path": "PB-TRIAL-0-A",
  "slice": "PB-TRIAL-0-A",
  "family": "PB-TRIAL-0",
  "branch_local_execution_target": "arc/pb-trial-0-a",
  "target_scope": "trial_docket_runbook_sandbox_readiness_guardrail_slice",
  "implementation_packages": [
    "adeu_benchmarking"
  ],
  "api_surfaces": [],
  "prerequisite_locks": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS251.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS252.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS253.md"
  ],
  "prerequisite_decision_docs": [
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS251.md",
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS252.md",
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS253.md"
  ],
  "prerequisite_assessments": [
    "docs/ASSESSMENT_vNEXT_PLUS251_EDGES.md",
    "docs/ASSESSMENT_vNEXT_PLUS252_EDGES.md",
    "docs/ASSESSMENT_vNEXT_PLUS253_EDGES.md"
  ],
  "planning_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v80.md",
    "docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_FAMILY_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0A_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0B_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0C_IMPLEMENTATION_MAPPING_v0.md"
  ],
  "consumed_record_shapes": [
    "programbench_reconstruction_attempt_request@1",
    "programbench_reconstruction_attempt_worker_input_packet@1",
    "programbench_reconstruction_attempt_dispatch_preflight@1",
    "programbench_reconstruction_attempt_non_authority_guardrail@1",
    "programbench_reconstruction_attempt_result_review@1",
    "programbench_reconstruction_attempt_family_closeout_alignment@1"
  ],
  "emitted_record_shapes": [
    "programbench_local_reconstruction_trial_docket@1",
    "programbench_local_trial_execution_runbook@1",
    "programbench_local_trial_sandbox_readiness_review@1",
    "programbench_local_trial_non_authority_guardrail@1"
  ],
  "forbidden_claims": [
    "worker_dispatch_authority",
    "command_execution_authority",
    "candidate_artifact_snapshot",
    "local_trial_execution_capture",
    "lifecycle_projection",
    "outcome_audit",
    "trial_result_claimed",
    "retry_dispatch_authority",
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
  "local_gate": "make arc-start-check ARC=254"
}
```

## Verification Plan

- run `make arc-start-check ARC=254` while this bundle remains docs-only;
- during implementation, run the focused `PB-TRIAL-0-A` tests and
  `make check` before opening a PR.

