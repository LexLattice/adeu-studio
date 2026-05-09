# LOCKED_CONTINUATION_vNEXT_PLUS268

## Status

Bounded starter lock draft for `PB-MATRIX-INCLUSION-0-C` (local matrix
revision registration, revision readiness summary, pressure-only
post-inclusion handoff, and family closeout alignment).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-MATRIX-INCLUSION-0-C` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-MATRIX-INCLUSION-0`
- slice: `PB-MATRIX-INCLUSION-0-C`
- branch-local execution target: `arc/pb-matrix-inclusion-0-c`

## Purpose

Freeze the bounded `PB-MATRIX-INCLUSION-0-C` starter slice so the repo can
consume released `PB-MATRIX-INCLUSION-0-A` and `PB-MATRIX-INCLUSION-0-B`
rows, register one revised local matrix membership, summarize revision
readiness, emit pressure-only post-inclusion handoff rows, and close only the
matrix-inclusion family.

`vNext+268` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize local
case execution, probe execution, batch command execution, candidate
materialization, result projection, post-execution matrix summary, official
ProgramBench participation, official task execution, official
runner/evaluator integration, hidden-test handling, hidden-test inference,
hidden-test equivalence, original source lookup, decompilation, internet
lookup inside ProgramBench tasks, external repository lookup, benchmark
submission, benchmark scoring, benchmark truth, pass rate, solve rate,
success rate, baseline comparison, model ranking, leaderboard standing,
official submission authority, second retry authority, retry-chain authority,
unbounded command execution, target mutation outside released local artifacts,
runtime transition, product authorization, graph-memory authority, release
authority, recursive policy amendment, or future-family selection.

Controlling invariant:

```text
PB-MATRIX-INCLUSION-0-C may register the revised local matrix membership that
B already decided, summarize readiness as inventory-only local accounting,
emit pressure-only handoff rows, and close the PB-MATRIX-INCLUSION-0 family.

It may not execute the matrix, project results, score the matrix, compare it
to a baseline, rank models, submit officially, or select a future family.
```

No-result-count invariant:

```text
Included/deferred/rejected counts are membership inventory counts only.
They are not pass rates, solve rates, success rates, benchmark scores,
official success rates, model scores, leaderboard metrics, or evidence that
the revised matrix has run.
```

Pressure-only handoff invariant:

```text
Post-inclusion handoff rows may name future review pressure only. They cannot
grant batch execution, result projection, benchmark scoring, official
participation, hidden evaluator access, baseline comparison, model ranking,
retry-chain authority, or future-family selection.
```

## Instantiated Here

- `PB-MATRIX-INCLUSION-0-C` instantiates the final local cleanroom
  matrix-inclusion seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-MATRIX-INCLUSION-0-A` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS266.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS266.md`
    - `docs/ASSESSMENT_vNEXT_PLUS266_EDGES.md`
    - `apps/api/fixtures/benchmarking/vnext_plus266/`
  - consumed released `PB-MATRIX-INCLUSION-0-B` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS267.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS267.md`
    - `docs/ASSESSMENT_vNEXT_PLUS267_EDGES.md`
    - `apps/api/fixtures/benchmarking/vnext_plus267/`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v84.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_MATRIX_INCLUSION_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_MATRIX_INCLUSION_PB_MATRIX_INCLUSION_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_MATRIX_INCLUSION_PB_MATRIX_INCLUSION_0C_IMPLEMENTATION_MAPPING_v0.md`
  - emitted starter record shapes:
    - `programbench_local_matrix_revision_registration@1`
    - `programbench_local_matrix_revision_readiness_summary@1`
    - `programbench_local_matrix_post_inclusion_handoff@1`
    - `programbench_local_matrix_inclusion_family_closeout_alignment@1`

## Required Starter Vocabulary

Minimum `programbench_local_matrix_revision_registration@1` fields:

- `matrix_revision_registration_ref`
- `matrix_inclusion_request_ref`
- `matrix_amendment_plan_ref`
- `matrix_case_delta_manifest_ref`
- `matrix_inclusion_decision_ref`
- `target_matrix_ref`
- `registered_matrix_revision_ref`
- `registered_matrix_revision_hash`
- `base_matrix_revision_hash`
- `matrix_amendment_plan_hash`
- `case_delta_manifest_hash`
- `comparability_delta_review_hash`
- `contamination_delta_review_hash`
- `inclusion_decision_hash`
- `registered_membership_manifest_hash`
- `included_case_lineage_refs`
- `deferred_case_lineage_refs`
- `rejected_case_lineage_refs`
- `matrix_revision_scope_posture`
- `local_accounting_scope_posture`
- `execution_authority_posture`
- `result_projection_authority_posture`
- `benchmark_score_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

Minimum `programbench_local_matrix_revision_readiness_summary@1` fields:

- `matrix_revision_readiness_summary_ref`
- `matrix_revision_registration_ref`
- `registered_matrix_revision_ref`
- `included_case_count`
- `deferred_case_count`
- `rejected_case_count`
- `included_case_lineage_refs`
- `carried_blocker_refs`
- `carried_warning_refs`
- `revision_readiness_posture`
- `inventory_count_posture`
- `matrix_denominator_posture`
- `representativeness_posture`
- `benchmark_truth_posture`
- `limitation_note`

Required readiness values:

- `inventory_count_posture =
  local_membership_inventory_only_not_result_count`
- `matrix_denominator_posture =
  local_matrix_denominator_only_not_benchmark_denominator`
- `representativeness_posture = not_representative_benchmark_sample`
- `benchmark_truth_posture = not_benchmark_truth`

Minimum `programbench_local_matrix_post_inclusion_handoff@1` fields:

- `matrix_post_inclusion_handoff_ref`
- `matrix_revision_registration_ref`
- `registered_matrix_revision_ref`
- `handoff_pressure_rows`
- `handoff_pressure_kind`
- `handoff_non_selection_posture`
- `batch_execution_authority_posture`
- `result_projection_authority_posture`
- `benchmark_score_authority_posture`
- `baseline_comparison_authority_posture`
- `model_ranking_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

Allowed handoff pressure kinds:

- `future_local_matrix_result_projection_review`
- `future_local_batch_execution_governance_review`
- `future_case_expansion_review`
- `future_official_participation_governance_review`
- `future_benchmark_result_governance_review`
- `future_family_only`

Minimum `programbench_local_matrix_inclusion_family_closeout_alignment@1`
fields:

- `matrix_inclusion_family_closeout_ref`
- `closed_family_ref`
- `closed_slice_refs`
- `shipped_record_shapes`
- `matrix_inclusion_request_refs`
- `candidate_intake_refs`
- `eligibility_review_refs`
- `control_contract_refs`
- `guardrail_refs`
- `amendment_plan_refs`
- `case_delta_manifest_refs`
- `comparability_delta_review_refs`
- `contamination_delta_review_refs`
- `inclusion_decision_refs`
- `revision_registration_refs`
- `revision_readiness_summary_refs`
- `post_inclusion_handoff_refs`
- `official_programbench_posture`
- `benchmark_truth_posture`
- `baseline_comparison_posture`
- `model_ranking_posture`
- `future_family_authority_posture`
- `limitation_note`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_local_matrix_revision_registration@1`
  - `programbench_local_matrix_revision_readiness_summary@1`
  - `programbench_local_matrix_post_inclusion_handoff@1`
  - `programbench_local_matrix_inclusion_family_closeout_alignment@1`
- mirrored `spec/` schema exports for the same shapes;
- validators requiring released A and B refs before C rows validate;
- validators requiring revision registration to bind B amendment, case delta,
  comparability, contamination, and inclusion decision refs and hashes;
- validators requiring registered membership to match B inclusion decision
  exactly;
- validators rejecting revision registration that adds cases not admitted by B;
- validators requiring readiness counts to match registered membership sets;
- validators rejecting pass-rate, solve-rate, success-rate, benchmark-score,
  official-score, baseline-delta, likely pass/fail, model-ranking, or
  leaderboard language in readiness summaries;
- validators keeping matrix denominator local-only and not official
  ProgramBench denominator;
- validators requiring post-inclusion handoff rows to be pressure-only and
  non-selecting;
- validators rejecting handoff authority for batch execution, result
  projection, scoring, official participation, hidden evaluator access,
  baseline comparison, model ranking, retry-chain authority, or
  future-family selection;
- validators requiring family closeout closed slice refs to be exactly
  `PB-MATRIX-INCLUSION-0-A`, `PB-MATRIX-INCLUSION-0-B`, and
  `PB-MATRIX-INCLUSION-0-C`;
- validators requiring family closeout shipped shapes to cover A/B/C;
- reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus268/`.

## Explicit Non-Outputs

`PB-MATRIX-INCLUSION-0-C` must not output:

- local case execution records;
- probe execution records;
- batch command execution records;
- candidate implementation artifacts;
- result projection rows;
- post-execution matrix summary rows;
- benchmark scores, baseline-relative results, pass rates, solve rates,
  success rates, or model rankings;
- official ProgramBench participation rows;
- hidden-test handling rows;
- official submissions;
- future-family selection.

## Starter Contract

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+268",
  "target_path": "PB-MATRIX-INCLUSION-0-C",
  "authority_layer": "lock",
  "selected_family": "PB-MATRIX-INCLUSION-0",
  "selected_slice": "PB-MATRIX-INCLUSION-0-C",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS268.md",
  "allowed_package": "packages/adeu_benchmarking",
  "selected_record_shapes": [
    "programbench_local_matrix_revision_registration@1",
    "programbench_local_matrix_revision_readiness_summary@1",
    "programbench_local_matrix_post_inclusion_handoff@1",
    "programbench_local_matrix_inclusion_family_closeout_alignment@1"
  ],
  "local_gate": "make arc-start-check ARC=268",
  "non_authority_summary": "No local case execution, probe execution, batch execution, candidate materialization, result projection, post-execution matrix summary, benchmark score, baseline comparison, model ranking, official ProgramBench participation, hidden-test handling, or future-family selection is authorized by this lock."
}
```

## Verification Plan

Before implementation starts:

```text
make arc-start-check ARC=268
```

For the implementation PR:

```text
.venv/bin/python -m pytest packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_inclusion_pb_matrix_inclusion_0c.py -q
make check
```
