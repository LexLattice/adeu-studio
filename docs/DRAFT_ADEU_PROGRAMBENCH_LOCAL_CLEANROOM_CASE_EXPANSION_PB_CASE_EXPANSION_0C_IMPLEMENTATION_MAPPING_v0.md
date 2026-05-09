# Draft ADEU ProgramBench Local Cleanroom Case Expansion PB-CASE-EXPANSION-0-C Implementation Mapping v0

Status: support / implementation mapping record for planned
`PB-CASE-EXPANSION-0-C`.

Authority layer: support.

This note maps the likely implementation for `PB-CASE-EXPANSION-0-C`. It
does not authorize implementation by itself and does not replace a future
`vNext+265` lock, stop-gate decision, or edge assessment.

## Slice Intent

`PB-CASE-EXPANSION-0-C` should register validated expanded local case
lineages, summarize readiness, emit pressure-only handoff rows, and close
only the case-expansion family. It should not run cases, include cases in a
matrix by itself, execute batches, score cases, compare baselines, or rank
models.

The slice should answer:

```text
Which expanded local cleanroom cases are ready, blocked, or deferred for
later matrix inclusion or later batch-execution governance review?
```

It must not answer:

```text
Can we execute the case now?
What benchmark score did it get?
Is it better than an existing baseline?
Should a batch run start?
Should an official ProgramBench submission be made?
```

## Selected Surfaces

Likely schema / model surfaces:

- `programbench_local_case_lineage_registration@1`
- `programbench_local_case_expansion_readiness_summary@1`
- `programbench_local_case_matrix_candidate_handoff@1`
- `programbench_local_case_expansion_family_closeout_alignment@1`

Likely source files for a future implementation:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_case_expansion.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_case_expansion_pb_case_expansion_0c.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus265/`

## Consumed Lineage

`PB-CASE-EXPANSION-0-C` should require released `PB-CASE-EXPANSION-0-A` and
`PB-CASE-EXPANSION-0-B` rows. It should consume earlier ProgramBench family
closeouts only as inherited cleanroom law and lineage context.

## Field-Level Expectations

`programbench_local_case_lineage_registration@1` should include:

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

`programbench_local_case_expansion_readiness_summary@1` should include:

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

`programbench_local_case_matrix_candidate_handoff@1` should include:

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

`programbench_local_case_expansion_family_closeout_alignment@1` should
include:

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

## Validation Expectations

The future implementation should validate:

- every C bundle resolves to one `case_expansion_ref`;
- C requires released A and B refs before lineage registration, readiness
  summary, handoff, or closeout rows validate;
- lineage registration requires a B blueprint, complete evidence pack,
  complete probe contract, oracle boundary, and clean contamination screen;
- readiness marked ready requires no carried blockers, no contamination,
  complete source identity, complete probe contracts, complete oracle
  boundaries, and local-only posture;
- readiness marked ready requires
  `ready_count_posture = inventory_count_only_not_success_rate`,
  `readiness_denominator_posture =
  expansion_request_denominator_only_not_benchmark_denominator`, and
  `representativeness_posture = not_representative_benchmark_sample`;
- ready local case counts remain inventory/accounting only and cannot become
  pass rate, solve rate, success rate, benchmark score, official success
  rate, model score, or leaderboard metric;
- matrix candidate handoff is pressure-only and cannot include cases in a
  matrix directly;
- handoff rows cannot grant batch execution, official participation, hidden
  evaluator access, model-ranking authority, scoring authority, retry-chain
  authority, or future-family selection;
- family closeout requires exact closed slice refs:
  `PB-CASE-EXPANSION-0-A`, `PB-CASE-EXPANSION-0-B`, and
  `PB-CASE-EXPANSION-0-C`;
- family closeout shipped shapes must cover A/B/C;
- C rejects official ProgramBench, hidden-test, baseline-score,
  model-ranking, and batch-execution claims.

## Reference Fixtures

Future C fixtures should include:

- one lineage registration for a B-validated local case;
- one readiness summary with ready, blocked, and deferred cases;
- one pressure-only matrix candidate handoff;
- one family closeout alignment.

Reject fixtures should include:

- lineage registration without clean contamination screen;
- readiness marked ready with missing probe contract;
- readiness marked ready with missing oracle boundary;
- ready count phrased as pass rate, solve rate, success rate, or benchmark
  subset readiness;
- handoff that grants direct matrix inclusion;
- handoff that grants batch execution or future-family selection;
- family closeout missing A, B, or C slice ref.
