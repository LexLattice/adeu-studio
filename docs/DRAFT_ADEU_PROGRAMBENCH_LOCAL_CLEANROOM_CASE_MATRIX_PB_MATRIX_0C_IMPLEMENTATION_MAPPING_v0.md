# Draft ADEU ProgramBench Local Cleanroom Case Matrix PB-MATRIX-0-C Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-MATRIX-0-C`.

Authority layer: support.

This note maps the likely final slice for `PB-MATRIX-0`. It is not a slice
lock. `PB-MATRIX-0-C` should activate only after `PB-MATRIX-0-A` and
`PB-MATRIX-0-B` have shipped and closed on `main`.

## Slice Intent

`PB-MATRIX-0-C` should summarize one local cleanroom case matrix, emit
pressure-only handoff rows, and close only the `PB-MATRIX-0` family.

The slice should answer:

```text
Given released matrix inclusion controls and released matrix projection /
observation / coverage / contamination rows, what is the local-only matrix
posture and which future review pressures remain?
```

It must not answer:

```text
What benchmark score did we get?
Which model should be ranked higher?
Should we submit officially?
Should hidden tests be inferred?
Should the next family be selected?
```

## Selected Surfaces

Likely schema / model surfaces:

- `programbench_local_case_matrix_summary@1`
- `programbench_post_case_matrix_handoff@1`
- `programbench_local_case_matrix_family_closeout_alignment@1`

Likely source files for a future implementation:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_matrix.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_local_case_matrix_summary.v1.json`
- `packages/adeu_benchmarking/schema/programbench_post_case_matrix_handoff.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_case_matrix_family_closeout_alignment.v1.json`
- `spec/programbench_local_case_matrix_summary.schema.json`
- `spec/programbench_post_case_matrix_handoff.schema.json`
- `spec/programbench_local_case_matrix_family_closeout_alignment.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_pb_matrix_0c.py`
- `apps/api/fixtures/benchmarking/vnext_plus262/`

## Consumed Lineage

`PB-MATRIX-0-C` should require released `PB-MATRIX-0-A` rows:

- matrix request;
- case inclusion manifest;
- case lineage eligibility review;
- matrix control contract;
- matrix non-authority guardrail.

It should require released `PB-MATRIX-0-B` rows:

- result projection;
- observation ledger;
- coverage register;
- contamination register.

## Field-Level Expectations

`programbench_local_case_matrix_summary@1` should include:

- `matrix_summary_ref`
- `case_matrix_ref`
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

`programbench_post_case_matrix_handoff@1` should include:

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

`programbench_local_case_matrix_family_closeout_alignment@1` should include:

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

## Validation Expectations

The future implementation should validate:

- C requires released A and B refs and one `case_matrix_ref`;
- matrix summary references only cases included by A and projected or
  explicitly gapped by B;
- summary cannot mark the matrix clean if the contamination register is not
  clean;
- summary cannot mark local matrix posture complete while projection gaps,
  contamination blockers, missing coverage, or unresolved blockers remain;
- local matrix complete posture is complete only relative to declared local
  cases, not official ProgramBench tasks or hidden tests;
- summary aggregate counts must be inventory/accounting only and cannot be
  pass rate, solve rate, success rate, benchmark score, official success
  rate, model score, or leaderboard metric;
- summary must carry a matrix scope statement and explicit
  not-benchmark-score statement;
- summary posture must be local-only and not benchmark truth;
- summary cannot include benchmark score, hidden-test equivalence, official
  score, leaderboard standing, model superiority, cross-worker ranking, or
  official-submission language;
- handoff rows are pressure-only and cannot grant official participation,
  hidden evaluator access, model-ranking authority, batch execution authority,
  retry-chain authority, or future-family selection;
- handoff rows must type pressure as future local case expansion review,
  future official participation governance review, future hidden evaluator
  governance review, future model comparison governance review, future batch
  execution governance review, or future-family-only;
- family closeout alignment closes exactly `PB-MATRIX-0-A`,
  `PB-MATRIX-0-B`, and `PB-MATRIX-0-C`;
- family closeout includes all shipped record shapes and no official
  ProgramBench, benchmark score, model ranking, hidden-test, second retry,
  batch execution, product, graph, release, or recursive-policy authority.

## Reference Fixtures

Future `vNext+262` reference fixtures should include:

- local matrix summary over released A/B refs;
- pressure-only post-matrix handoff;
- family closeout alignment closing A/B/C.

Reject fixtures should include:

- clean summary with contamination blockers;
- complete summary with missing projection rows;
- benchmark-score or model-ranking language in summary;
- local aggregate counts phrased as pass rate, solve rate, success rate,
  benchmark-like result, official-like score, or representative ProgramBench
  subset;
- handoff granting official ProgramBench participation;
- handoff granting batch execution or future-family selection;
- family closeout missing a slice;
- family closeout selecting official benchmark or model-ranking authority.

## Non-Outputs

`PB-MATRIX-0-C` must not output:

- official ProgramBench runner/evaluator integration;
- hidden-test handling or hidden-test inference;
- official benchmark submission;
- benchmark score, leaderboard, or model-ranking surfaces;
- generated official submissions;
- batch command execution over cases;
- second retry or retry-chain authority;
- source lookup, decompilation, internet lookup, external repo lookup, Docker
  socket, or host-secret access;
- product, graph-memory, release, or recursive-policy authority;
- future-family selection.
