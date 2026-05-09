# LOCKED_CONTINUATION_vNEXT_PLUS265

## Status

Bounded starter lock draft for `PB-CASE-EXPANSION-0-C` (local case lineage
registration, readiness summary, matrix candidate handoff, and family
closeout alignment).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-CASE-EXPANSION-0-C` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-CASE-EXPANSION-0`
- slice: `PB-CASE-EXPANSION-0-C`
- branch-local execution target: `arc/pb-case-expansion-0-c`

## Purpose

Freeze the bounded `PB-CASE-EXPANSION-0-C` starter slice so the repo can
register validated expanded local cleanroom case lineages, summarize
readiness, emit pressure-only matrix candidate handoff rows, and close only
the `PB-CASE-EXPANSION-0` family.

`vNext+265` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize local
case execution, probe execution, batch command execution, candidate
materialization, direct matrix inclusion, matrix execution, benchmark
scoring, benchmark truth, pass rate, solve rate, success rate,
baseline-relative result claims, model ranking, leaderboard standing,
official ProgramBench participation, official task execution, official
runner/evaluator integration, hidden-test handling, hidden-test inference,
hidden-test equivalence, original source lookup, decompilation, internet
lookup inside ProgramBench tasks, external repository lookup, benchmark
submission, official submission authority, second retry authority,
retry-chain authority, unbounded command execution, runtime transition,
product authorization, graph-memory authority, release authority, recursive
policy amendment, or future-family selection.

Controlling invariant:

```text
PB-CASE-EXPANSION-0-C may register local cleanroom case lineages only after
released A/B rows prove source eligibility, complete blueprint/evidence/probe
/oracle rows, and clean contamination screening. It may summarize readiness
and hand off matrix pressure, but it may not run, include, score, rank, or
claim benchmark truth.
```

Inventory-count invariant:

```text
Ready counts are inventory/accounting only. They are not pass rates, solve
rates, success rates, benchmark scores, model scores, official success rates,
or representative benchmark subset claims.
```

Handoff invariant:

```text
Matrix candidate handoff is pressure only. It cannot include cases directly
in a matrix, grant batch execution, grant scoring authority, grant official
participation, or select a future family.
```

## Instantiated Here

- `PB-CASE-EXPANSION-0-C` instantiates the final local cleanroom
  case-expansion seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-CASE-EXPANSION-0-A` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS263.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS263.md`
    - `docs/ASSESSMENT_vNEXT_PLUS263_EDGES.md`
    - `apps/api/fixtures/benchmarking/vnext_plus263/`
  - consumed released `PB-CASE-EXPANSION-0-B` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS264.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS264.md`
    - `docs/ASSESSMENT_vNEXT_PLUS264_EDGES.md`
    - `apps/api/fixtures/benchmarking/vnext_plus264/`
  - inherited released cleanroom basis:
    - `PB-MATRIX-0`, `PB-TRIAL-0`, `PB-RETRY-0`,
      `PB-ATTEMPT-0`, `PB-RECON-0`, `PB-ADAPTER-0`, and
      `PB-PY-0` family closeouts
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v83.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_PB_CASE_EXPANSION_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_PB_CASE_EXPANSION_0C_IMPLEMENTATION_MAPPING_v0.md`
  - emitted final-slice record shapes:
    - `programbench_local_case_lineage_registration@1`
    - `programbench_local_case_expansion_readiness_summary@1`
    - `programbench_local_case_matrix_candidate_handoff@1`
    - `programbench_local_case_expansion_family_closeout_alignment@1`

## Required Starter Vocabulary

Minimum `programbench_local_case_lineage_registration@1` fields:

- `case_lineage_registration_ref`
- `case_expansion_ref`
- `case_blueprint_ref`
- `cleanroom_evidence_pack_ref`
- `probe_contract_ref`
- `oracle_boundary_ref`
- `contamination_screen_ref`
- `registered_case_lineage_ref`
- `registered_case_lineage_hash`
- `registered_case_lineage_origin_hash`
- `source_pool_subset_hash`
- `blueprint_hash`
- `evidence_pack_hash`
- `probe_contract_hash`
- `oracle_boundary_hash`
- `contamination_screen_hash`
- `lineage_registration_status`
- `local_case_scope_posture`
- `matrix_inclusion_authority_posture`
- `execution_authority_posture`
- `benchmark_score_posture`
- `limitation_note`

Minimum `programbench_local_case_expansion_readiness_summary@1` fields:

- `case_expansion_readiness_summary_ref`
- `case_expansion_ref`
- `ready_case_lineage_refs`
- `blocked_case_lineage_refs`
- `deferred_case_lineage_refs`
- `ready_blueprint_refs`
- `blocked_blueprint_refs`
- `carried_blocker_refs`
- `carried_warning_refs`
- `coverage_summary_rows`
- `contamination_summary_rows`
- `readiness_posture`
- `ready_count_posture`
- `readiness_denominator_posture`
- `representativeness_posture`
- `local_case_count_posture`
- `benchmark_truth_posture`
- `limitation_note`

Required readiness postures:

- `ready_count_posture = inventory_count_only_not_success_rate`
- `readiness_denominator_posture =
  expansion_request_denominator_only_not_benchmark_denominator`
- `representativeness_posture = not_representative_benchmark_sample`

Minimum `programbench_local_case_matrix_candidate_handoff@1` fields:

- `case_matrix_candidate_handoff_ref`
- `case_expansion_ref`
- `ready_case_lineage_refs`
- `handoff_pressure_rows`
- `handoff_pressure_kind`
- `handoff_non_selection_posture`
- `matrix_inclusion_authority_posture`
- `batch_execution_authority_posture`
- `benchmark_score_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

Minimum `programbench_local_case_expansion_family_closeout_alignment@1`
fields:

- `case_expansion_family_closeout_ref`
- `closed_family_ref`
- `closed_slice_refs`
- `shipped_record_shapes`
- `case_expansion_request_refs`
- `source_pool_manifest_refs`
- `eligibility_review_refs`
- `control_contract_refs`
- `guardrail_refs`
- `case_blueprint_refs`
- `cleanroom_evidence_pack_refs`
- `probe_contract_refs`
- `oracle_boundary_refs`
- `contamination_screen_refs`
- `lineage_registration_refs`
- `readiness_summary_refs`
- `matrix_candidate_handoff_refs`
- `official_programbench_posture`
- `benchmark_truth_posture`
- `model_ranking_posture`
- `future_family_authority_posture`
- `limitation_note`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_local_case_lineage_registration@1`
  - `programbench_local_case_expansion_readiness_summary@1`
  - `programbench_local_case_matrix_candidate_handoff@1`
  - `programbench_local_case_expansion_family_closeout_alignment@1`
- mirrored `spec/` schema exports for the same shapes;
- validators requiring released `PB-CASE-EXPANSION-0-A` and
  `PB-CASE-EXPANSION-0-B` refs before C rows validate;
- validators requiring one `case_expansion_ref` across a C bundle;
- validators requiring lineage registration to bind to a complete B
  blueprint, evidence pack, probe contract, oracle boundary, and clean
  contamination screen;
- validators rejecting lineage registration if contamination screen status is
  not clean or the screen verdict is not passed;
- validators rejecting readiness marked ready with missing probe contract,
  missing oracle boundary, missing contamination screen, carried blockers, or
  unresolved contamination;
- validators rejecting ready counts phrased as pass rate, solve rate,
  success rate, benchmark score, official success rate, model score, or
  leaderboard metric;
- validators requiring matrix candidate handoff to be pressure-only and
  non-selecting;
- validators rejecting direct matrix inclusion, batch execution authority,
  scoring authority, model-ranking authority, official participation
  authority, hidden evaluator access, and future-family selection;
- validators requiring family closeout to list exact closed slices:
  `PB-CASE-EXPANSION-0-A`, `PB-CASE-EXPANSION-0-B`, and
  `PB-CASE-EXPANSION-0-C`;
- reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus265/`.

## Explicit Non-Outputs

`PB-CASE-EXPANSION-0-C` must not output:

- local case execution records;
- probe execution records;
- batch command execution records;
- candidate materialization records;
- direct matrix inclusion records;
- matrix result projections;
- matrix summaries;
- benchmark scores, baseline-relative results, pass rates, solve rates,
  success rates, or model rankings;
- official ProgramBench participation rows;
- hidden-test handling rows;
- official submissions;
- second retry or retry-chain authority;
- future-family selection.

## Starter Contract

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+265",
  "target_path": "PB-CASE-EXPANSION-0-C",
  "authority_layer": "lock",
  "selected_family": "PB-CASE-EXPANSION-0",
  "selected_slice": "PB-CASE-EXPANSION-0-C",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS265.md",
  "allowed_package": "packages/adeu_benchmarking",
  "selected_record_shapes": [
    "programbench_local_case_lineage_registration@1",
    "programbench_local_case_expansion_readiness_summary@1",
    "programbench_local_case_matrix_candidate_handoff@1",
    "programbench_local_case_expansion_family_closeout_alignment@1"
  ],
  "local_gate": "make arc-start-check ARC=265",
  "non_authority_summary": "No local case execution, probe execution, batch execution, direct matrix inclusion, benchmark score, baseline comparison, model ranking, official ProgramBench participation, hidden-test handling, or future-family selection is authorized by this lock."
}
```

## Verification Plan

Before implementation starts:

```text
make arc-start-check ARC=265
```

For the implementation PR:

```text
.venv/bin/python -m pytest packages/adeu_benchmarking/tests/test_programbench_cleanroom_case_expansion_pb_case_expansion_0c.py -q
make check
```
