# LOCKED_CONTINUATION_vNEXT_PLUS267

## Status

Bounded starter lock draft for `PB-MATRIX-INCLUSION-0-B` (local matrix
amendment plan, case delta manifest, comparability delta review,
contamination delta review, and inclusion decision record).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-MATRIX-INCLUSION-0-B` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-MATRIX-INCLUSION-0`
- slice: `PB-MATRIX-INCLUSION-0-B`
- branch-local execution target: `arc/pb-matrix-inclusion-0-b`

## Purpose

Freeze the bounded `PB-MATRIX-INCLUSION-0-B` starter slice so the repo can
turn released `PB-MATRIX-INCLUSION-0-A` eligible candidates into a local
matrix amendment basis and local accounting inclusion decisions.

`vNext+267` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize local
case execution, probe execution, batch command execution, candidate
materialization, matrix revision registration, result projection, matrix
summary, official ProgramBench participation, official task execution,
official runner/evaluator integration, hidden-test handling, hidden-test
inference, hidden-test equivalence, original source lookup, decompilation,
internet lookup inside ProgramBench tasks, external repository lookup,
benchmark submission, benchmark scoring, benchmark truth, pass rate, solve
rate, success rate, baseline comparison, model ranking, leaderboard standing,
official submission authority, second retry authority, retry-chain authority,
unbounded command execution, target mutation outside released local
artifacts, runtime transition, product authorization, graph-memory authority,
release authority, recursive policy amendment, or future-family selection.

Controlling invariant:

```text
PB-MATRIX-INCLUSION-0-B may decide added, deferred, or rejected membership
for A-eligible local case lineages in one declared local matrix revision.
Those decisions are local accounting membership decisions only; they are not
result projections, quality scores, benchmark selections, model comparisons,
baseline comparisons, execution authority, or revision registration.
```

No-performance-selection invariant:

```text
Inclusion decisions must be based on governance/accounting reasons such as
lineage eligibility, dedupe, contamination, comparability, matrix capacity,
horizon mismatch, or missing readiness refs. They must not cite likely
pass/fail, score improvement, model advantage, baseline advantage,
leaderboard relevance, hidden-test coverage, or benchmark representativeness.
```

No-contamination-transfer invariant:

```text
Hidden, forbidden, postmortem-only, evaluator-derived, source-derived,
decompilation-derived, internet-derived, or external-repo-derived material may
not enter amendment plans, case deltas, comparability reviews,
contamination reviews, decision rows, labels, rationale rows, summaries, or
handoff pressure by direct reference or derived summary.
```

## Instantiated Here

- `PB-MATRIX-INCLUSION-0-B` instantiates the second local cleanroom
  matrix-inclusion seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-MATRIX-INCLUSION-0-A` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS266.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS266.md`
    - `docs/ASSESSMENT_vNEXT_PLUS266_EDGES.md`
    - `apps/api/fixtures/benchmarking/vnext_plus266/`
  - inherited released case-expansion and matrix basis:
    - `PB-CASE-EXPANSION-0` family closeout
    - `PB-MATRIX-0` family closeout
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v84.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_MATRIX_INCLUSION_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_MATRIX_INCLUSION_PB_MATRIX_INCLUSION_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_MATRIX_INCLUSION_PB_MATRIX_INCLUSION_0B_IMPLEMENTATION_MAPPING_v0.md`
  - emitted starter record shapes:
    - `programbench_local_matrix_amendment_plan@1`
    - `programbench_local_matrix_case_delta_manifest@1`
    - `programbench_local_matrix_comparability_delta_review@1`
    - `programbench_local_matrix_contamination_delta_review@1`
    - `programbench_local_matrix_inclusion_decision_record@1`

## Required Starter Vocabulary

Minimum `programbench_local_matrix_amendment_plan@1` fields:

- `matrix_amendment_plan_ref`
- `matrix_inclusion_request_ref`
- `matrix_inclusion_control_contract_ref`
- `target_matrix_ref`
- `target_matrix_revision_candidate_ref`
- `planned_added_case_lineage_refs`
- `planned_deferred_case_lineage_refs`
- `planned_rejected_case_lineage_refs`
- `amendment_scope_posture`
- `execution_authority_posture`
- `result_projection_authority_posture`
- `benchmark_score_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

Minimum `programbench_local_matrix_case_delta_manifest@1` fields:

- `matrix_case_delta_manifest_ref`
- `matrix_amendment_plan_ref`
- `case_delta_rows`
- `delta_manifest_hash`
- `local_accounting_scope_posture`
- `limitation_note`

Minimum `matrix_case_delta_row` fields:

- `case_delta_ref`
- `case_delta_kind`
- `case_lineage_ref`
- `case_lineage_hash`
- `prior_matrix_membership_status`
- `new_matrix_membership_candidate_status`
- `dedupe_status`
- `delta_reason`
- `decision_basis_posture`
- `limitation_note`

Minimum `programbench_local_matrix_comparability_delta_review@1` fields:

- `matrix_comparability_delta_review_ref`
- `matrix_amendment_plan_ref`
- `matrix_case_delta_manifest_ref`
- `base_worker_profile_hash`
- `candidate_worker_profile_hash`
- `base_model_profile_hash`
- `candidate_model_profile_hash`
- `base_tool_policy_hash`
- `candidate_tool_policy_hash`
- `base_probe_basis_hash`
- `candidate_probe_basis_hash`
- `base_source_visibility_hash`
- `candidate_source_visibility_hash`
- `base_sandbox_write_scope_hash`
- `candidate_sandbox_write_scope_hash`
- `comparability_delta_hash`
- `worker_profile_delta_posture`
- `model_profile_delta_posture`
- `tool_policy_delta_posture`
- `probe_basis_delta_posture`
- `sandbox_write_scope_delta_posture`
- `source_visibility_delta_posture`
- `comparability_accounting_posture`
- `model_ranking_authority_posture`
- `baseline_comparison_authority_posture`
- `limitation_note`

Required comparability posture:

- `comparability_accounting_posture =
  local_accounting_only_no_model_or_baseline_comparison`

Minimum `programbench_local_matrix_contamination_delta_review@1` fields:

- `matrix_contamination_delta_review_ref`
- `matrix_amendment_plan_ref`
- `matrix_case_delta_manifest_ref`
- `contamination_delta_rows`
- `contamination_transfer_status`
- `contamination_redaction_policy`
- `contamination_detail_posture`
- `hidden_or_forbidden_exposure_refs`
- `cleanroom_boundary_status`
- `limitation_note`

Required contamination posture:

- `contamination_redaction_policy = category_count_reason_only`
- `contamination_detail_posture = no_content_bearing_hidden_or_forbidden_detail`

Minimum `programbench_local_matrix_inclusion_decision_record@1` fields:

- `matrix_inclusion_decision_ref`
- `matrix_amendment_plan_ref`
- `matrix_case_delta_manifest_ref`
- `matrix_comparability_delta_review_ref`
- `matrix_contamination_delta_review_ref`
- `included_case_lineage_refs`
- `deferred_case_lineage_refs`
- `rejected_case_lineage_refs`
- `inclusion_decision_status`
- `decision_basis_posture`
- `decision_basis_rows`
- `decision_is_not_result_posture`
- `decision_is_not_quality_score_posture`
- `decision_is_not_benchmark_selection_posture`
- `local_accounting_scope_posture`
- `result_projection_authority_posture`
- `execution_authority_posture`
- `benchmark_truth_posture`
- `future_family_selection_posture`
- `limitation_note`

Allowed decision basis values:

- `lineage_eligible`
- `dedupe_blocked`
- `contamination_blocked`
- `comparability_blocked`
- `matrix_capacity_deferred`
- `horizon_mismatch_deferred`
- `missing_readiness_refs_blocked`

Forbidden decision basis values:

- `expected_to_pass`
- `expected_failure`
- `model_performs_well`
- `improves_score`
- `benchmark_representative`
- `leaderboard_relevant`
- `baseline_improving`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_local_matrix_amendment_plan@1`
  - `programbench_local_matrix_case_delta_manifest@1`
  - `programbench_local_matrix_comparability_delta_review@1`
  - `programbench_local_matrix_contamination_delta_review@1`
  - `programbench_local_matrix_inclusion_decision_record@1`
- mirrored `spec/` schema exports for the same shapes;
- validators requiring released `PB-MATRIX-INCLUSION-0-A` refs;
- validators rejecting A-blocked, A-deferred, or A-unknown candidates;
- validators requiring case delta rows to account for every A-eligible
  candidate exactly once as added, deferred, or rejected;
- validators rejecting dropped or duplicated candidate lineage refs;
- validators binding delta rows to A candidate lineage hashes;
- validators binding comparability review hash pairs before continuity claims;
- validators marking worker/model/tool/probe/sandbox/source-visibility changes
  as non-comparable local accounting only;
- validators rejecting model comparison, baseline comparison, result
  projection, or scoring authority in comparability rows;
- validators preserving redaction and fail-closed contamination transfer
  posture;
- validators rejecting contamination transfer by labels, rationale rows,
  decision rows, summaries, or hidden/forbidden detail;
- validators requiring clean contamination delta review before inclusion
  decision status can be locally accepted for membership accounting;
- validators rejecting performance-selection rationale such as likely pass,
  likely fail, expected score, model advantage, baseline improvement,
  hidden-edge coverage, benchmark relevance, leaderboard relevance, or
  representative benchmark sample;
- validators rejecting execution, result projection, benchmark scoring,
  baseline comparison, model ranking, official ProgramBench authority, and
  future-family selection;
- reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus267/`.

## Explicit Non-Outputs

`PB-MATRIX-INCLUSION-0-B` must not output:

- matrix revision registration rows;
- revision readiness summaries;
- post-inclusion handoff rows;
- family closeout rows;
- result projection rows;
- matrix summary rows;
- local trial or retry rows;
- execution, probe execution, batch execution, or candidate materialization
  rows;
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
  "target_arc": "vNext+267",
  "target_path": "PB-MATRIX-INCLUSION-0-B",
  "authority_layer": "lock",
  "selected_family": "PB-MATRIX-INCLUSION-0",
  "selected_slice": "PB-MATRIX-INCLUSION-0-B",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS267.md",
  "allowed_package": "packages/adeu_benchmarking",
  "selected_record_shapes": [
    "programbench_local_matrix_amendment_plan@1",
    "programbench_local_matrix_case_delta_manifest@1",
    "programbench_local_matrix_comparability_delta_review@1",
    "programbench_local_matrix_contamination_delta_review@1",
    "programbench_local_matrix_inclusion_decision_record@1"
  ],
  "local_gate": "make arc-start-check ARC=267",
  "non_authority_summary": "No local case execution, probe execution, batch execution, candidate materialization, matrix revision registration, result projection, benchmark score, baseline comparison, model ranking, official ProgramBench participation, hidden-test handling, or future-family selection is authorized by this lock."
}
```

## Verification Plan

Before implementation starts:

```text
make arc-start-check ARC=267
```

For the implementation PR:

```text
.venv/bin/python -m pytest packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_inclusion_pb_matrix_inclusion_0b.py -q
make check
```
