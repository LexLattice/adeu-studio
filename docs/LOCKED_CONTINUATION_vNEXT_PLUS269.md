# LOCKED_CONTINUATION_vNEXT_PLUS269

## Status

Bounded starter lock draft for `PB-SINGLE-CASE-RUN-0-A` (single-case run
request, target selection, execution preflight, run control contract, and
non-authority guardrail).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-SINGLE-CASE-RUN-0-A` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-SINGLE-CASE-RUN-0`
- slice: `PB-SINGLE-CASE-RUN-0-A`
- branch-local execution target: `arc/pb-single-case-run-0-a`

## Purpose

Freeze the bounded `PB-SINGLE-CASE-RUN-0-A` starter slice so the repo can
select exactly one released local cleanroom case lineage, bind its target
origin route, preflight the later local run controls, and preserve a
non-authority guardrail before any execution-shaped slice is selected.

`vNext+269` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize worker
dispatch, command execution, local probe execution, candidate artifact
capture, lifecycle projection, local outcome audit, remand or acceptance
decision, retry authority, batch execution, official ProgramBench
participation, official task execution, official runner/evaluator
integration, hidden-test handling, hidden-test inference, hidden-test
equivalence, original source lookup, decompilation, internet lookup inside
ProgramBench tasks, external repository lookup, benchmark submission,
benchmark scoring, benchmark truth, pass rate, solve rate, success rate,
baseline comparison, model ranking, leaderboard standing, official submission
authority, retry-chain authority, unbounded command execution, target mutation
outside released local artifacts, runtime transition, product authorization,
graph-memory authority, release authority, recursive policy amendment, or
future-family selection.

Controlling invariant:

```text
PB-SINGLE-CASE-RUN-0-A may select and preflight one local cleanroom
case-lineage run candidate.

It may not dispatch a worker, run commands, materialize artifacts, audit an
outcome, score ProgramBench, compare a baseline, rank a model, or select a
future family.
```

Prior-lifecycle invariant:

```text
PB-SINGLE-CASE-RUN-0 is not a replacement for PB-TRIAL-0.

It is a selected case-lineage run wrapper under released adapter, workbench,
attempt, trial, optional retry, matrix, case-expansion, and matrix-inclusion
law.
```

Target-origin invariant:

```text
target_origin_route = matrix_member is the default.

If target_origin_route = matrix_member, the selected case must be included in
a released matrix revision.

If target_origin_route = ready_expanded_case_lineage, the selected case must
have released readiness and no contamination blockers.

If target_origin_route = direct_adapter_case_exception, explicit exception
posture and non-matrix-lineage warning are required.
```

Preflight invariant:

```text
preflight_scope_posture = eligibility_review_only_no_dispatch

dispatch_authority_posture =
  no_worker_dispatch_authority_granted_by_pb_single_case_run_0a
```

## Instantiated Here

- `PB-SINGLE-CASE-RUN-0-A` instantiates the first local cleanroom
  single-case-run seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed family-level planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v85.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_SINGLE_CASE_RUN_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_SINGLE_CASE_RUN_PB_SINGLE_CASE_RUN_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_SINGLE_CASE_RUN_PB_SINGLE_CASE_RUN_0A_IMPLEMENTATION_MAPPING_v0.md`
  - consumed released family closeouts as constraints:
    - `docs/DRAFT_ADEU_PROGRAMBENCH_PYTHON_RECONSTRUCTION_REALIZATION_PB_PY_0_FAMILY_CLOSEOUT_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_ADAPTER_PB_ADAPTER_0_FAMILY_CLOSEOUT_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_WORKBENCH_PB_RECON_0_FAMILY_CLOSEOUT_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_CLEANROOM_RECONSTRUCTION_ATTEMPT_PB_ATTEMPT_0_FAMILY_CLOSEOUT_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_FAMILY_CLOSEOUT_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0_FAMILY_CLOSEOUT_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0_FAMILY_CLOSEOUT_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_PB_CASE_EXPANSION_0_FAMILY_CLOSEOUT_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_MATRIX_INCLUSION_PB_MATRIX_INCLUSION_0_FAMILY_CLOSEOUT_v0.md`
  - emitted starter record shapes:
    - `programbench_single_case_run_request@1`
    - `programbench_single_case_target_selection@1`
    - `programbench_single_case_execution_preflight@1`
    - `programbench_single_case_run_control_contract@1`
    - `programbench_single_case_run_non_authority_guardrail@1`

## Required Starter Vocabulary

Minimum `programbench_single_case_run_request@1` fields:

- `single_case_run_request_ref`
- `requested_case_lineage_ref`
- `requested_case_lineage_hash`
- `request_source_family_ref`
- `request_source_closeout_ref`
- `single_case_run_relation_to_prior_lifecycle`
- `target_origin_route`
- `target_origin_justification`
- `target_origin_exception_posture`
- `run_horizon`
- `run_rationale_rows`
- `single_case_only_posture`
- `official_programbench_posture`
- `benchmark_truth_posture`
- `baseline_comparison_authority_posture`
- `model_ranking_authority_posture`
- `batch_execution_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

Minimum `programbench_single_case_target_selection@1` fields:

- `single_case_target_selection_ref`
- `single_case_run_request_ref`
- `selected_case_lineage_ref`
- `selected_case_lineage_hash`
- `selected_case_origin_posture`
- `target_origin_route`
- `target_origin_required_refs`
- `source_matrix_ref`
- `source_matrix_revision_ref`
- `source_matrix_revision_hash`
- `matrix_membership_row_ref`
- `matrix_membership_status`
- `source_visibility_boundary_hash`
- `cleanroom_boundary_hash`
- `case_artifact_manifest_ref`
- `case_artifact_manifest_hash`
- `worker_visible_packet_ref`
- `worker_visible_packet_hash`
- `local_probe_basis_ref`
- `local_probe_basis_hash`
- `contamination_posture`
- `target_selection_status`
- `target_selection_blocker_refs`
- `limitation_note`

Minimum `programbench_single_case_execution_preflight@1` fields:

- `single_case_execution_preflight_ref`
- `single_case_run_request_ref`
- `single_case_target_selection_ref`
- `runbook_ref`
- `runbook_hash`
- `sandbox_policy_ref`
- `sandbox_policy_hash`
- `sandbox_witness_requirement_refs`
- `required_b_witness_refs`
- `run_budget_ref`
- `run_budget_hash`
- `tool_manifest_ref`
- `tool_manifest_hash`
- `write_scope_ref`
- `write_scope_hash`
- `environment_policy_ref`
- `environment_policy_hash`
- `network_posture`
- `source_lookup_posture`
- `decompilation_posture`
- `docker_socket_posture`
- `host_secret_posture`
- `preflight_check_rows`
- `preflight_status`
- `preflight_scope_posture`
- `dispatch_authority_posture`
- `limitation_note`

Required B witness refs:

- `sandbox_instance_ref`
- `sandbox_attestation_bundle_ref`
- `network_mode_witness_ref`
- `docker_socket_absence_witness_ref`
- `secret_absence_witness_ref`
- `source_lookup_absence_witness_ref`
- `decompilation_absence_witness_ref`
- `write_scope_attestation_ref`

Minimum `programbench_single_case_run_control_contract@1` fields:

- `single_case_run_control_contract_ref`
- `single_case_run_request_ref`
- `worker_visible_packet_hash`
- `runbook_hash`
- `sandbox_policy_hash`
- `run_budget_hash`
- `tool_manifest_hash`
- `write_scope_hash`
- `local_probe_basis_hash`
- `allowed_command_policy`
- `timeout_policy`
- `resource_limit_policy`
- `artifact_capture_policy`
- `forbidden_content_screen_policy`
- `single_dispatch_limit_posture`
- `local_only_probe_posture`
- `official_evaluator_access_posture`
- `hidden_test_access_posture`
- `benchmark_score_authority_posture`
- `limitation_note`

Minimum `programbench_single_case_run_non_authority_guardrail@1` fields:

- `single_case_run_guardrail_ref`
- `single_case_run_request_ref`
- `forbidden_authority_rows`
- `worker_dispatch_deferred_posture`
- `command_execution_deferred_posture`
- `candidate_artifact_capture_deferred_posture`
- `local_outcome_audit_deferred_posture`
- `official_programbench_authority_posture`
- `benchmark_score_authority_posture`
- `baseline_comparison_authority_posture`
- `model_ranking_authority_posture`
- `batch_execution_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_single_case_run_request@1`
  - `programbench_single_case_target_selection@1`
  - `programbench_single_case_execution_preflight@1`
  - `programbench_single_case_run_control_contract@1`
  - `programbench_single_case_run_non_authority_guardrail@1`
- mirrored `spec/` schema exports for the same shapes;
- validators requiring exactly one selected target case lineage;
- validators requiring target-origin route-specific refs;
- validators requiring matrix-member targets to have
  `matrix_membership_status = included`;
- validators rejecting deferred or rejected matrix-inclusion candidates as run
  targets;
- validators requiring direct adapter case targets to carry explicit exception
  posture and non-matrix-lineage warning;
- validators binding selected target lineage, source visibility, cleanroom
  boundary, artifact manifest, worker-visible packet, and local probe basis
  hashes;
- validators requiring execution preflight to bind runbook, sandbox policy,
  run budget, tool manifest, write scope, environment policy, and required B
  witness refs;
- validators rejecting open network, source lookup, decompilation, Docker
  socket exposure, host secret exposure, non-closed tool manifest, or
  unbounded write scope;
- validators keeping A preflight as eligibility review only and no dispatch
  authority;
- validators rejecting B/C record shapes inside A;
- validators rejecting benchmark score, pass rate, solve rate, success rate,
  official score, baseline comparison, model ranking, leaderboard, official
  participation, batch execution, retry-chain authority, and future-family
  authority;
- reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus269/`.

## Explicit Non-Outputs

`PB-SINGLE-CASE-RUN-0-A` must not output:

- worker dispatch specimen rows;
- execution trace rows;
- probe observation bundle rows;
- candidate artifact capture rows;
- lifecycle projection rows;
- local outcome audit rows;
- observation summary rows;
- remand or acceptance decision rows;
- official ProgramBench participation rows;
- benchmark score rows;
- pass-rate, solve-rate, success-rate, or official-score rows;
- baseline comparison rows;
- model ranking rows;
- batch execution rows;
- retry authority rows;
- future-family selection rows.

## Machine-Checkable Contract Seed

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+269",
  "target_path": "PB-SINGLE-CASE-RUN-0-A",
  "authority_layer": "lock",
  "selected_family": "PB-SINGLE-CASE-RUN-0",
  "selected_slice": "PB-SINGLE-CASE-RUN-0-A",
  "selected_record_shapes": [
    "programbench_single_case_run_request@1",
    "programbench_single_case_target_selection@1",
    "programbench_single_case_execution_preflight@1",
    "programbench_single_case_run_control_contract@1",
    "programbench_single_case_run_non_authority_guardrail@1"
  ],
  "package_scope": "packages/adeu_benchmarking",
  "default_target_origin_route": "matrix_member",
  "preflight_scope_posture": "eligibility_review_only_no_dispatch",
  "dispatch_authority_granted": false,
  "execution_authority_granted": false,
  "candidate_artifact_capture_granted": false,
  "official_programbench_authority_granted": false,
  "benchmark_score_authority_granted": false,
  "baseline_comparison_authority_granted": false,
  "model_ranking_authority_granted": false,
  "batch_execution_authority_granted": false,
  "future_family_selection_granted": false
}
```
