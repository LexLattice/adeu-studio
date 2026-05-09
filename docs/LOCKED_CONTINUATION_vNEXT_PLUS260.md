# LOCKED_CONTINUATION_vNEXT_PLUS260

## Status

Bounded starter lock draft for `PB-MATRIX-0-A` (local case matrix request,
case inclusion manifest, lineage eligibility review, matrix control contract,
and non-authority guardrail).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-MATRIX-0-A` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-MATRIX-0`
- slice: `PB-MATRIX-0-A`
- branch-local execution target: `arc/pb-matrix-0-a`

## Purpose

Freeze the bounded `PB-MATRIX-0-A` starter slice so the repo can review a
small local cleanroom case matrix request, row-shaped case inclusion
manifest, lineage eligibility review, shared matrix control contract, and
non-authority guardrail without projecting results, executing cases, scoring
benchmarks, ranking models, handling hidden tests, or selecting a future
family.

`vNext+260` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize
official ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, model
ranking, leaderboard standing, generated official submissions, official
submission authority, batch command execution, candidate materialization,
second retry authority, retry-chain authority, unbounded command execution,
target mutation outside released local artifacts, runtime transition, product
authorization, graph-memory authority, release authority, recursive policy
amendment, or future-family selection.

Controlling invariant:

```text
PB-MATRIX-0-A may decide which released local cleanroom case lineages are
eligible to enter one local case matrix under declared controls, but it may
not project per-case results, compute benchmark-like scores, rank models,
execute cases, infer hidden-test success, grant batch execution authority, or
select the next family.
```

Aggregate-count invariant:

```text
Local matrix counts are inventory/accounting only. They may count included
cases, local postures, blockers, and coverage gaps, but they may not become
pass rate, solve rate, success rate, benchmark score, official success rate,
model score, or leaderboard metric.
```

## Instantiated Here

- `PB-MATRIX-0-A` instantiates the first local cleanroom case-matrix seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-RETRY-0` basis:
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RETRY_GOVERNANCE_PB_RETRY_0_FAMILY_CLOSEOUT_v0.md`
    - retry outcome audit
    - retry delta observation summary
    - retry remand settlement
    - retry family closeout alignment
  - consumed released `PB-TRIAL-0` basis:
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_RECONSTRUCTION_TRIAL_PB_TRIAL_0_FAMILY_CLOSEOUT_v0.md`
    - trial outcome audit
    - trial observation summary
    - trial remand decision
    - trial family closeout alignment
  - inherited released cleanroom basis:
    - `PB-ATTEMPT-0` family closeout
    - `PB-RECON-0` family closeout
    - `PB-ADAPTER-0` family closeout
    - `PB-PY-0` family closeout
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v82.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0A_IMPLEMENTATION_MAPPING_v0.md`
  - emitted starter record shapes:
    - `programbench_local_case_matrix_request@1`
    - `programbench_local_case_inclusion_manifest@1`
    - `programbench_local_case_lineage_eligibility_review@1`
    - `programbench_local_case_matrix_control_contract@1`
    - `programbench_local_case_matrix_non_authority_guardrail@1`

## Required Starter Vocabulary

Minimum `programbench_local_case_matrix_request@1` fields:

- `case_matrix_ref`
- `matrix_request_ref`
- `matrix_horizon`
- `matrix_max_case_count`
- `matrix_selection_rationale_refs`
- `matrix_case_candidate_refs`
- `case_inclusion_manifest_ref`
- `case_lineage_eligibility_review_ref`
- `matrix_control_contract_ref`
- `requested_case_count`
- `official_benchmark_authority_posture`
- `model_ranking_posture`
- `batch_execution_authority_posture`
- `future_family_selection_posture`
- `representativeness_posture`
- `aggregate_count_posture`
- `limitation_note`

Allowed `matrix_horizon` values:

- `local_smoke_matrix`
- `local_regression_matrix`
- `local_coverage_probe_matrix`
- `local_research_matrix`
- `not_representative_benchmark_sample`

Minimum `programbench_local_case_inclusion_manifest@1` fields:

- `case_inclusion_manifest_ref`
- `case_matrix_ref`
- `case_candidate_rows`
- `matrix_selection_rationale_rows`
- `included_case_refs`
- `blocked_case_refs`
- `deferred_case_refs`
- `support_only_case_refs`
- `released_case_lineage_refs`
- `case_origin_posture`
- `case_visibility_posture`
- `case_result_source_posture`
- `hidden_or_forbidden_exposure_posture`
- `limitation_note`

Minimum `matrix_case_candidate_row` fields:

- `case_ref`
- `case_lineage_kind`
- `trial_lineage_ref`
- `retry_lineage_ref`
- `adapter_case_packet_ref`
- `workbench_ref`
- `attempt_ref`
- `trial_ref`
- `retry_settlement_ref`
- `case_visibility_boundary_hash`
- `case_cleanroom_boundary_hash`
- `case_result_source_posture`
- `case_contamination_posture`
- `case_origin_posture`
- `inclusion_decision`
- `inclusion_reason`

Minimum `programbench_local_case_lineage_eligibility_review@1` fields:

- `case_lineage_eligibility_review_ref`
- `case_matrix_ref`
- `case_eligibility_rows`
- `eligible_case_refs`
- `blocked_case_refs`
- `carried_blocker_refs`
- `carried_warning_refs`
- `released_family_closeout_refs`
- `non_authority_guardrail_refs`
- `limitation_note`

Minimum `programbench_local_case_matrix_control_contract@1` fields:

- `matrix_control_contract_ref`
- `case_matrix_ref`
- `matrix_worker_profile_control_ref`
- `matrix_tool_policy_control_ref`
- `matrix_probe_basis_control_ref`
- `matrix_sandbox_policy_control_ref`
- `matrix_write_scope_control_ref`
- `matrix_visibility_control_ref`
- `matrix_non_ranking_posture`
- `matrix_comparability_posture`
- `multi_profile_matrix_posture`
- `aggregate_count_posture`
- `representativeness_posture`
- `allowed_matrix_action_rows`
- `forbidden_matrix_action_rows`
- `limitation_note`

Minimum `programbench_local_case_matrix_non_authority_guardrail@1` fields:

- `matrix_guardrail_ref`
- `case_matrix_refs`
- `guardrail_source_refs`
- `non_authority_rows`
- `official_programbench_posture`
- `hidden_test_posture`
- `benchmark_truth_posture`
- `model_ranking_posture`
- `batch_execution_posture`
- `second_retry_posture`
- `future_family_posture`
- `limitation_note`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_local_case_matrix_request@1`
  - `programbench_local_case_inclusion_manifest@1`
  - `programbench_local_case_lineage_eligibility_review@1`
  - `programbench_local_case_matrix_control_contract@1`
  - `programbench_local_case_matrix_non_authority_guardrail@1`
- mirrored `spec/` schema exports for the same shapes;
- validators requiring one `case_matrix_ref` across the A bundle;
- validators requiring released `PB-TRIAL-0` lineage for every included case;
- validators requiring released `PB-RETRY-0` refs when retry settlement is
  cited;
- validators rejecting unreleased, contaminated, support-only,
  hidden-test-derived, official-evaluator-derived, source-lookup-derived,
  decompilation-derived, internet-derived, external-repo-derived, or
  postmortem-only cases as included cases;
- validators requiring row-shaped case candidates with lineage refs and
  cleanroom boundary hashes;
- validators requiring `matrix_horizon`, `matrix_max_case_count`, aggregate
  count posture, and representativeness posture;
- validators requiring default single worker/model profile, one tool policy,
  one probe basis, and one sandbox/write-scope posture, unless explicit
  comparability-accounting-only non-ranking posture is declared;
- validators rejecting benchmark score, pass rate, solve rate, success rate,
  official-like score, representative benchmark subset, leaderboard, model
  superiority, or model ranking language;
- validators rejecting command execution, batch execution, official evaluator
  access, source lookup, decompilation, internet lookup, Docker socket, host
  secret, wider write scope, hidden-test access, second retry authority,
  retry-chain authority, or future-family selection;
- validators rejecting `PB-MATRIX-0-B/C` artifact shapes in A fixtures;
- focused tests for `PB-MATRIX-0-A` plus schema export coverage;
- reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus260/`.

## Explicit Non-Outputs

`PB-MATRIX-0-A` must not output:

- per-case result projections;
- observation ledgers;
- coverage registers;
- contamination registers;
- matrix summaries;
- post-matrix handoffs;
- family closeout alignment;
- command execution or batch execution records;
- benchmark scores, pass rates, solve rates, success rates, or model rankings;
- official ProgramBench participation rows;
- hidden-test handling rows;
- official submissions;
- second retry or retry-chain authority;
- future-family selection.

## Starter Contract

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+260",
  "target_path": "PB-MATRIX-0-A",
  "authority_layer": "lock",
  "selected_family": "PB-MATRIX-0",
  "selected_slice": "PB-MATRIX-0-A",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS260.md",
  "allowed_package": "packages/adeu_benchmarking",
  "selected_record_shapes": [
    "programbench_local_case_matrix_request@1",
    "programbench_local_case_inclusion_manifest@1",
    "programbench_local_case_lineage_eligibility_review@1",
    "programbench_local_case_matrix_control_contract@1",
    "programbench_local_case_matrix_non_authority_guardrail@1"
  ],
  "local_gate": "make arc-start-check ARC=260",
  "non_authority_summary": "No official ProgramBench participation, hidden-test handling, benchmark truth, benchmark scoring, model ranking, leaderboard standing, batch execution, result projection, second retry authority, retry-chain authority, or future-family selection is authorized by this lock."
}
```

## Verification Plan

Before implementation starts:

```text
make arc-start-check ARC=260
```

For the implementation PR:

```text
.venv/bin/python -m pytest packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_pb_matrix_0a.py -q
make check
```
