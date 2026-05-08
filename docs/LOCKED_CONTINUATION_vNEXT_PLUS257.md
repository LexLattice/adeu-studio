# LOCKED_CONTINUATION_vNEXT_PLUS257

## Status

Bounded starter lock draft for `PB-RETRY-0-A` (retry request intake, retry
lineage registry, remand source index, eligibility review, scope contract, and
retry non-authority guardrail).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-RETRY-0-A` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-RETRY-0`
- slice: `PB-RETRY-0-A`
- branch-local execution target: `arc/pb-retry-0-a`

## Purpose

Freeze the bounded `PB-RETRY-0-A` starter slice so the repo can make one
released `PB-TRIAL-0` local remand decision reviewable as a retry candidate
without dispatching the retry.

`vNext+257` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize retry
dispatch, command execution, retry candidate delta snapshotting, local retry
execution capture, retry lifecycle projection, retry outcome audit, retry
delta observation summary, remand settlement, second retry authority,
multi-attempt comparison, official ProgramBench participation, official task
execution, official runner integration, official evaluator integration,
hidden-test handling, hidden-test inference, hidden-test equivalence,
original source lookup, decompilation, internet lookup inside ProgramBench
tasks, external repository lookup, benchmark submission, benchmark scoring,
benchmark truth, model ranking, generated official submissions, official
submission authority, unbounded command execution, target mutation outside
released local artifacts, runtime transition, product authorization,
graph-memory authority, recursive policy amendment, or future-family
selection.

Controlling invariant:

```text
PB-RETRY-0-A may record and review one local remand-to-retry candidate for
one released PB-TRIAL-0 lineage, but it may not dispatch a retry, execute
commands, materialize retry candidates, widen cleanroom evidence, create many
"single" retries over the same remand, claim benchmark truth, rank models, or
select a future family.
```

## Instantiated Here

- `PB-RETRY-0-A` instantiates the first local cleanroom retry-governance seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-TRIAL-0` basis:
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_FAMILY_CLOSEOUT_v0.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS254.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS255.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS256.md`
    - `docs/ASSESSMENT_vNEXT_PLUS254_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS255_EDGES.md`
    - `docs/ASSESSMENT_vNEXT_PLUS256_EDGES.md`
    - `apps/api/fixtures/benchmarking/vnext_plus254/programbench_local_reconstruction_trial_docket_v254_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus255/programbench_local_trial_worker_dispatch_record_v255_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus255/programbench_local_trial_candidate_artifact_snapshot_v255_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus256/programbench_local_trial_outcome_audit_v256_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus256/programbench_local_trial_observation_summary_v256_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus256/programbench_local_trial_remand_decision_v256_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus256/programbench_local_trial_family_closeout_alignment_v256_reference.json`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v81.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0A_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0B_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0C_IMPLEMENTATION_MAPPING_v0.md`
  - emitted first-slice record shapes:
    - `programbench_local_retry_request@1`
    - `programbench_local_retry_lineage_registry@1`
    - `programbench_trial_remand_source_index@1`
    - `programbench_local_retry_eligibility_review@1`
    - `programbench_local_retry_scope_contract@1`
    - `programbench_local_retry_non_authority_guardrail@1`

## Required Starter Vocabulary

Minimum `programbench_local_retry_request@1` fields:

- `retry_request_ref`
- `retry_lineage_ref`
- `trial_lineage_ref`
- `source_trial_ref`
- `source_remand_decision_ref`
- `retry_lineage_registry_ref`
- `prior_retry_request_refs`
- `retry_sequence_index`
- `trial_outcome_audit_ref`
- `trial_observation_summary_ref`
- `trial_remand_decision_ref`
- `trial_family_closeout_ref`
- `requested_retry_horizon`
- `retry_depth_limit`
- `retry_uniqueness_posture`
- `retry_dispatch_authority_posture`
- `official_benchmark_authority_posture`
- `model_ranking_posture`
- `limitation_note`

Required postures:

- `retry_uniqueness_posture = one_eligible_retry_for_trial_remand`
- `retry_dispatch_authority_posture =
  no_retry_dispatch_authority_granted_by_pb_retry_0a`
- `official_benchmark_authority_posture =
  no_official_programbench_authority_granted_by_pb_retry_0a`
- `model_ranking_posture = no_model_ranking_claimed_by_pb_retry_0a`

Minimum `programbench_local_retry_lineage_registry@1` fields:

- `retry_lineage_registry_ref`
- `trial_lineage_ref`
- `trial_remand_decision_ref`
- `existing_retry_request_refs`
- `eligible_retry_request_refs`
- `retry_sequence_rows`
- `retry_uniqueness_posture`
- `retry_chain_authority_posture`
- `limitation_note`

Required uniqueness law:

```text
For a given trial_lineage_ref + trial_remand_decision_ref, only one
PB-RETRY-0 retry request may be eligible unless a later family grants
retry-chain authority.
```

Minimum `programbench_trial_remand_source_index@1` fields:

- `remand_source_index_ref`
- `retry_request_ref`
- `trial_remand_decision_ref`
- `remand_source_rows`
- `retry_rationale_rows`
- `local_retryable_source_refs`
- `local_non_retryable_source_refs`
- `blocked_source_refs`
- `forbidden_source_refs`
- `support_only_source_refs`
- `source_visibility_posture`
- `hidden_or_forbidden_exposure_posture`
- `limitation_note`

Required remand-source law:

```text
Remand source and retry rationale rows may describe local failure or gap
categories. They must not include hidden or forbidden source names, paths,
excerpts, semantic summaries, test names, original-source clues, or derived
facts.
```

Allowed retry rationale kinds:

- `local_probe_failure`
- `local_output_capture_gap`
- `local_candidate_snapshot_gap`
- `lifecycle_projection_gap`
- `runbook_satisfaction_gap`
- `worker_declared_uncertainty`
- `local_evidence_inconclusive`

Minimum `programbench_local_retry_eligibility_review@1` fields:

- `retry_eligibility_review_ref`
- `retry_request_ref`
- `retry_lineage_registry_ref`
- `remand_source_index_ref`
- `released_trial_lineage_refs`
- `cleanroom_continuity_refs`
- `retry_scope_contract_refs`
- `eligibility_posture`
- `ready_basis_posture`
- `carried_blocker_refs`
- `carried_warning_refs`
- `non_authority_guardrail_refs`
- `limitation_note`

Allowed `eligibility_posture` values:

- `eligible_for_later_local_retry_dispatch_review`
- `blocked_by_missing_trial_closeout`
- `blocked_by_missing_local_remand`
- `blocked_by_prior_local_acceptance`
- `blocked_by_contamination`
- `blocked_by_sandbox_violation`
- `blocked_by_hidden_or_forbidden_source`
- `blocked_by_retry_uniqueness_violation`
- `blocked_by_scope_widening`
- `future_family_only`

Minimum `programbench_local_retry_scope_contract@1` fields:

- `retry_scope_contract_ref`
- `retry_request_ref`
- `retry_lineage_ref`
- `retry_scope_delta_refs`
- `retry_scope_delta_manifest_hash`
- `unchanged_worker_visible_source_refs`
- `unchanged_forbidden_source_refs`
- `unchanged_tool_policy_refs`
- `unchanged_sandbox_policy_refs`
- `unchanged_worker_visible_source_set_hash`
- `unchanged_forbidden_source_set_hash`
- `unchanged_tool_policy_hash`
- `unchanged_sandbox_policy_hash`
- `unchanged_write_scope_hash`
- `unchanged_network_policy_hash`
- `allowed_retry_action_rows`
- `forbidden_retry_action_rows`
- `retry_depth_limit`
- `retry_chain_posture`
- `scope_authority_posture`
- `limitation_note`

Required scope law:

```text
retry_scope_delta_refs may add only local retry instructions or
remand-focused obligations. They may not add new evidence sources, tools,
write scope, source visibility, source lookup, decompilation, Docker socket,
host secret, or network authority.
```

Minimum `programbench_local_retry_non_authority_guardrail@1` fields:

- `retry_guardrail_ref`
- `retry_request_refs`
- `guardrail_source_refs`
- `non_authority_rows`
- `retry_dispatch_posture`
- `official_programbench_posture`
- `hidden_test_posture`
- `benchmark_truth_posture`
- `model_ranking_posture`
- `second_retry_posture`
- `future_family_posture`
- `limitation_note`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_local_retry_request@1`
  - `programbench_local_retry_lineage_registry@1`
  - `programbench_trial_remand_source_index@1`
  - `programbench_local_retry_eligibility_review@1`
  - `programbench_local_retry_scope_contract@1`
  - `programbench_local_retry_non_authority_guardrail@1`
- mirrored `spec/` schema exports for the same shapes;
- deterministic reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus257/`;
- validators that prove:
  - released `PB-TRIAL-0` refs and family closeout alignment are required
    before A rows validate;
  - retry request selects exactly one trial lineage and one local remand
    decision;
  - retry lineage registry prevents many eligible single retries over the
    same trial remand decision;
  - accepted, contaminated, sandbox-violating, hidden/evaluator/source-backed,
    official, or missing-remand trials cannot become retry-ready substrate;
  - remand source and retry rationale rows are local-only and content-shaped
    so hidden/forbidden paths, names, excerpts, semantic summaries, test
    names, original-source clues, and derived facts cannot leak;
  - hidden-test failure, official evaluator feedback, source lookup facts,
    decompilation facts, internet lookup facts, external repository facts,
    benchmark-score pressure, and model-ranking pressure cannot become retry
    rationale;
  - scope contracts separate retry deltas from unchanged cleanroom context;
  - scope contracts preserve unchanged worker-visible source set, forbidden
    source set, tool policy, sandbox policy, write scope, and network policy
    hashes;
  - scope deltas cannot widen evidence, tools, write scope, source visibility,
    source lookup, decompilation, Docker socket, host secret, or network
    authority;
  - guardrails forbid retry dispatch, official ProgramBench participation,
    hidden-test handling, benchmark truth, model ranking, second retry
    authority, and future-family selection;
  - `PB-RETRY-0-B/C` artifact kinds remain absent.

Expected implementation scope:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_retry.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_local_retry_request.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_lineage_registry.v1.json`
- `packages/adeu_benchmarking/schema/programbench_trial_remand_source_index.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_eligibility_review.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_scope_contract.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_retry_non_authority_guardrail.v1.json`
- `spec/programbench_local_retry_request.schema.json`
- `spec/programbench_local_retry_lineage_registry.schema.json`
- `spec/programbench_trial_remand_source_index.schema.json`
- `spec/programbench_local_retry_eligibility_review.schema.json`
- `spec/programbench_local_retry_scope_contract.schema.json`
- `spec/programbench_local_retry_non_authority_guardrail.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_retry_pb_retry_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus257/`

## Explicit Non-Outputs

`PB-RETRY-0-A` must not output:

- retry dispatch record;
- command execution;
- retry execution capture;
- retry candidate delta snapshot;
- retry lifecycle projection;
- retry outcome audit;
- retry delta observation summary;
- remand settlement;
- family closeout alignment;
- official ProgramBench runner/evaluator integration;
- official task execution;
- official submission artifact;
- hidden-test handling;
- hidden-test equivalence;
- benchmark score;
- benchmark truth;
- model ranking or leaderboard row;
- second retry authority;
- multi-attempt comparison;
- source lookup, decompilation, internet lookup, or external repo diagnostic;
- product, graph-memory, release, recursive-policy, or future-family
  selection.

## Starter Contract

```json
{
  "artifact": "docs/LOCKED_CONTINUATION_vNEXT_PLUS257.md",
  "schema": "continuation_contract@1",
  "target_arc": "vNext+257",
  "target_path": "PB-RETRY-0-A",
  "slice": "PB-RETRY-0-A",
  "family": "PB-RETRY-0",
  "branch_local_execution_target": "arc/pb-retry-0-a",
  "target_scope": "retry_intake_lineage_registry_remand_source_eligibility_scope_guardrail_slice",
  "implementation_packages": [
    "adeu_benchmarking"
  ],
  "api_surfaces": [],
  "prerequisite_locks": [
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS254.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS255.md",
    "docs/LOCKED_CONTINUATION_vNEXT_PLUS256.md"
  ],
  "prerequisite_decision_docs": [
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS254.md",
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS255.md",
    "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS256.md"
  ],
  "prerequisite_assessments": [
    "docs/ASSESSMENT_vNEXT_PLUS254_EDGES.md",
    "docs/ASSESSMENT_vNEXT_PLUS255_EDGES.md",
    "docs/ASSESSMENT_vNEXT_PLUS256_EDGES.md"
  ],
  "planning_docs": [
    "docs/DRAFT_NEXT_ARC_OPTIONS_v81.md",
    "docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_FAMILY_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0A_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0B_IMPLEMENTATION_MAPPING_v0.md",
    "docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0C_IMPLEMENTATION_MAPPING_v0.md"
  ],
  "consumed_record_shapes": [
    "programbench_local_trial_outcome_audit@1",
    "programbench_local_trial_observation_summary@1",
    "programbench_local_trial_remand_decision@1",
    "programbench_local_trial_family_closeout_alignment@1"
  ],
  "emitted_record_shapes": [
    "programbench_local_retry_request@1",
    "programbench_local_retry_lineage_registry@1",
    "programbench_trial_remand_source_index@1",
    "programbench_local_retry_eligibility_review@1",
    "programbench_local_retry_scope_contract@1",
    "programbench_local_retry_non_authority_guardrail@1"
  ],
  "forbidden_claims": [
    "retry_dispatch_authority",
    "command_execution_authority",
    "retry_candidate_delta_snapshot",
    "local_retry_execution_capture",
    "retry_lifecycle_projection",
    "retry_outcome_audit",
    "second_retry_authority",
    "multi_attempt_comparison",
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
  "local_gate": "make arc-start-check ARC=257"
}
```

## Verification Plan

- run `make arc-start-check ARC=257` while this bundle remains docs-only;
- during implementation, run the focused `PB-RETRY-0-A` tests and
  `make check` before opening a PR.
