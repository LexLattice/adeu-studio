# LOCKED_CONTINUATION_vNEXT_PLUS262

## Status

Bounded starter lock draft for `PB-MATRIX-0-C` (local matrix summary,
post-matrix handoff pressure, and family closeout alignment).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-MATRIX-0-C` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-MATRIX-0`
- slice: `PB-MATRIX-0-C`
- branch-local execution target: `arc/pb-matrix-0-c`

## Purpose

Freeze the bounded `PB-MATRIX-0-C` starter slice so the repo can summarize one
released local cleanroom case matrix, emit pressure-only future handoff rows,
and close the `PB-MATRIX-0` family after released `PB-MATRIX-0-A` inclusion
law and released `PB-MATRIX-0-B` projection/coverage/contamination law exist.

`vNext+262` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize local
case execution, batch command execution, candidate materialization, official
ProgramBench participation, official runner/evaluator integration,
hidden-test handling, hidden-test inference, hidden-test equivalence,
benchmark scoring, benchmark truth, pass rate, solve rate, success rate,
model ranking, leaderboard standing, generated official submissions, official
submission authority, second retry authority, retry-chain authority, future
family selection, product authorization, graph-memory authority, release
authority, or recursive policy amendment.

Controlling invariant:

```text
PB-MATRIX-0-C may summarize released local matrix rows and emit future
pressure, but it may not turn aggregate accounting into benchmark score,
model ranking, official ProgramBench authority, batch execution authority, or
next-family selection.
```

Summary invariant:

```text
The local matrix summary is complete only relative to declared local matrix
cases and released local evidence. It is not official ProgramBench truth and
not hidden-test equivalence.
```

## Instantiated Here

- `PB-MATRIX-0-C` instantiates the final local cleanroom case-matrix seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-MATRIX-0-A` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS260.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS260.md`
    - `docs/ASSESSMENT_vNEXT_PLUS260_EDGES.md`
    - `apps/api/fixtures/benchmarking/vnext_plus260/`
  - consumed released `PB-MATRIX-0-B` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS261.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS261.md`
    - `docs/ASSESSMENT_vNEXT_PLUS261_EDGES.md`
    - `apps/api/fixtures/benchmarking/vnext_plus261/`
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v82.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0C_IMPLEMENTATION_MAPPING_v0.md`
  - emitted final-slice record shapes:
    - `programbench_local_case_matrix_summary@1`
    - `programbench_post_case_matrix_handoff@1`
    - `programbench_local_case_matrix_family_closeout_alignment@1`

## Required Starter Vocabulary

Minimum `programbench_local_case_matrix_summary@1` fields:

- `matrix_summary_ref`
- `case_matrix_ref`
- `matrix_request_ref`
- `case_inclusion_manifest_ref`
- `case_lineage_eligibility_review_ref`
- `matrix_control_contract_ref`
- `matrix_guardrail_ref`
- `matrix_result_projection_ref`
- `matrix_observation_ledger_ref`
- `matrix_coverage_register_ref`
- `matrix_contamination_register_ref`
- `included_case_refs`
- `projected_case_refs`
- `blocked_case_refs`
- `unresolved_case_refs`
- `local_matrix_posture`
- `aggregate_count_posture`
- `representativeness_posture`
- `matrix_scope_statement`
- `not_benchmark_score_statement`
- `coverage_posture`
- `contamination_status`
- `benchmark_truth_posture`
- `model_ranking_posture`
- `carried_blocker_refs`
- `carried_warning_refs`
- `limitation_note`

Required summary posture:

- summary rows may reference only cases admitted by released A and projected
  or explicitly gapped by released B;
- local complete posture requires no projection gaps, no contamination
  blockers, no missing local coverage, and no unresolved blockers;
- aggregate counts are inventory/accounting only, never pass rate, solve
  rate, success rate, benchmark score, official success rate, model score, or
  leaderboard metric;
- summary statements must explicitly state local scope and not-benchmark-score
  posture.

Minimum `programbench_post_case_matrix_handoff@1` fields:

- `post_matrix_handoff_ref`
- `case_matrix_ref`
- `matrix_summary_ref`
- `handoff_rows`
- `future_pressure_refs`
- `handoff_pressure_kind`
- `handoff_non_selection_posture`
- `handoff_authority_posture`
- `official_programbench_posture`
- `model_ranking_posture`
- `batch_execution_posture`
- `future_family_selection_posture`
- `limitation_note`

Minimum `programbench_local_case_matrix_family_closeout_alignment@1` fields:

- `matrix_family_closeout_ref`
- `case_matrix_ref`
- `matrix_request_refs`
- `case_inclusion_manifest_refs`
- `case_lineage_eligibility_review_refs`
- `matrix_control_contract_refs`
- `matrix_result_projection_refs`
- `matrix_observation_ledger_refs`
- `matrix_coverage_register_refs`
- `matrix_contamination_register_refs`
- `matrix_summary_refs`
- `post_matrix_handoff_refs`
- `closed_slice_refs`
- `shipped_record_shapes`
- `future_family_authority_posture`
- `limitation_note`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_local_case_matrix_summary@1`
  - `programbench_post_case_matrix_handoff@1`
  - `programbench_local_case_matrix_family_closeout_alignment@1`
- mirrored `spec/` schema exports for the same shapes;
- validators requiring released A and B refs before C rows validate;
- validators requiring one `case_matrix_ref` across the C bundle;
- validators requiring summary cases to match released A/B case lineage;
- validators blocking complete local matrix posture when projection gaps,
  contamination blockers, missing coverage, or unresolved blockers remain;
- validators requiring aggregate-count posture to remain local accounting only;
- validators rejecting benchmark score, pass rate, solve rate, success rate,
  official success rate, model score, leaderboard metric, model superiority,
  official-submission posture, and soft scoring language;
- validators requiring handoff rows to be pressure-only and non-selecting;
- validators rejecting official ProgramBench participation, hidden evaluator
  access, model-ranking authority, batch execution authority, retry-chain
  authority, and future-family selection in handoff rows;
- validators requiring family closeout alignment to close exactly
  `PB-MATRIX-0-A`, `PB-MATRIX-0-B`, and `PB-MATRIX-0-C`;
- focused tests for `PB-MATRIX-0-C` plus schema export coverage;
- reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus262/`.

## Explicit Non-Outputs

`PB-MATRIX-0-C` must not output:

- local case execution, batch execution, or command execution records;
- candidate materialization records;
- official ProgramBench runner/evaluator integration;
- hidden-test handling, hidden-test inference, or hidden-test equivalence;
- benchmark score, pass rate, solve rate, success rate, leaderboard, or
  model-ranking surfaces;
- generated official submissions or official submission authority;
- second retry or retry-chain authority;
- future-family selection.

## Starter Contract

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+262",
  "target_path": "PB-MATRIX-0-C",
  "authority_layer": "lock",
  "selected_family": "PB-MATRIX-0",
  "selected_slice": "PB-MATRIX-0-C",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS262.md",
  "allowed_package": "packages/adeu_benchmarking",
  "selected_record_shapes": [
    "programbench_local_case_matrix_summary@1",
    "programbench_post_case_matrix_handoff@1",
    "programbench_local_case_matrix_family_closeout_alignment@1"
  ],
  "explicit_non_outputs": [
    "local_case_execution",
    "batch_command_execution",
    "candidate_materialization",
    "official_programbench_participation",
    "hidden_test_handling",
    "benchmark_score",
    "model_ranking",
    "future_family_selection"
  ]
}
```

## Recommended Implementation Scope

```text
packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_matrix.py
packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py
packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py

packages/adeu_benchmarking/schema/programbench_local_case_matrix_summary.v1.json
packages/adeu_benchmarking/schema/programbench_post_case_matrix_handoff.v1.json
packages/adeu_benchmarking/schema/programbench_local_case_matrix_family_closeout_alignment.v1.json

spec/programbench_local_case_matrix_summary.schema.json
spec/programbench_post_case_matrix_handoff.schema.json
spec/programbench_local_case_matrix_family_closeout_alignment.schema.json

packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_pb_matrix_0c.py

apps/api/fixtures/benchmarking/vnext_plus262/
  programbench_local_case_matrix_summary_v262_reference.json
  programbench_post_case_matrix_handoff_v262_reference.json
  programbench_local_case_matrix_family_closeout_alignment_v262_reference.json
  programbench_local_case_matrix_v262_reject_*.json
```
