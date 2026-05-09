# Draft ADEU ProgramBench Local Cleanroom Case Matrix PB-MATRIX-0-B Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-MATRIX-0-B`.

Authority layer: support.

This note maps the likely second slice for `PB-MATRIX-0`. It is not a slice
lock. `PB-MATRIX-0-B` should activate only after `PB-MATRIX-0-A` has shipped
and closed on `main`.

## Slice Intent

`PB-MATRIX-0-B` should project released per-case local results into a common
matrix vocabulary and record local matrix observations, coverage, and
contamination posture. It should not execute cases directly or score the
matrix.

The slice should answer:

```text
For each case included by released PB-MATRIX-0-A controls, what released
local trial/retry/attempt/workbench posture can be projected into matrix
rows, and what local observations, coverage, and contamination statuses are
visible?
```

It must not answer:

```text
Which model won?
What is the ProgramBench score?
Can this be submitted officially?
Can hidden tests or official evaluator feedback judge the matrix?
Can this slice run a batch command over cases?
```

## Selected Surfaces

Likely schema / model surfaces:

- `programbench_local_case_matrix_result_projection@1`
- `programbench_local_case_matrix_observation_ledger@1`
- `programbench_local_case_matrix_coverage_register@1`
- `programbench_local_case_matrix_contamination_register@1`

Likely source files for a future implementation:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_matrix.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_local_case_matrix_result_projection.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_case_matrix_observation_ledger.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_case_matrix_coverage_register.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_case_matrix_contamination_register.v1.json`
- `spec/programbench_local_case_matrix_result_projection.schema.json`
- `spec/programbench_local_case_matrix_observation_ledger.schema.json`
- `spec/programbench_local_case_matrix_coverage_register.schema.json`
- `spec/programbench_local_case_matrix_contamination_register.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_pb_matrix_0b.py`
- `apps/api/fixtures/benchmarking/vnext_plus261/`

## Consumed Lineage

`PB-MATRIX-0-B` should require released `PB-MATRIX-0-A` rows:

- matrix request;
- case inclusion manifest;
- case lineage eligibility review;
- matrix control contract;
- matrix non-authority guardrail.

It should also consume released per-case local lineage rows from
`PB-TRIAL-0`, optional `PB-RETRY-0`, and inherited `PB-ATTEMPT-0`,
`PB-RECON-0`, `PB-ADAPTER-0`, and `PB-PY-0` refs already validated by A.

## Field-Level Expectations

`programbench_local_case_matrix_result_projection@1` should include:

- `matrix_result_projection_ref`
- `case_matrix_ref`
- `projection_case_rows`
- `included_case_refs`
- `source_trial_outcome_refs`
- `source_retry_outcome_refs`
- `source_retry_settlement_refs`
- `source_result_ref`
- `source_result_hash`
- `source_family_closeout_ref`
- `projection_rule_ref`
- `projection_basis_rows`
- `projection_currentness`
- `projection_gap_reason`
- `projection_is_not_new_truth_posture`
- `projected_case_result_rows`
- `projection_gap_refs`
- `projection_authority_posture`
- `limitation_note`

`programbench_local_case_matrix_observation_ledger@1` should include:

- `matrix_observation_ledger_ref`
- `case_matrix_ref`
- `observation_rows`
- `local_observation_refs`
- `blocked_observation_refs`
- `non_ranking_posture`
- `benchmark_truth_posture`
- `limitation_note`

`programbench_local_case_matrix_coverage_register@1` should include:

- `matrix_coverage_register_ref`
- `case_matrix_ref`
- `coverage_rows`
- `covered_case_refs`
- `missing_coverage_case_refs`
- `local_coverage_basis_refs`
- `coverage_denominator_posture`
- `coverage_basis_scope`
- `hidden_test_coverage_exclusion_posture`
- `hidden_test_coverage_posture`
- `limitation_note`

`programbench_local_case_matrix_contamination_register@1` should include:

- `matrix_contamination_register_ref`
- `case_matrix_ref`
- `contamination_rows`
- `clean_case_refs`
- `blocked_case_refs`
- `forbidden_exposure_refs`
- `excluded_derived_summary_refs`
- `contamination_redaction_policy`
- `contamination_detail_posture`
- `contamination_status`
- `limitation_note`

## Validation Expectations

The future implementation should validate:

- B requires released A refs and one `case_matrix_ref`;
- B projection rows may reference only cases included by A;
- every included case must have exactly one current projection row or a
  declared projection gap;
- projected result posture must be derived from released local trial/retry
  rows, not authored as new outcome truth;
- projections require source result hashes, source family closeout refs,
  projection rule refs, currentness posture, and explicit
  not-new-truth posture;
- retry settlement projection must preserve unresolved remand pressure;
- observations cannot contain benchmark scores, official scores, hidden-test
  outcomes, leaderboard standing, model superiority, cross-worker ranking, or
  official-submission posture;
- coverage rows must classify local coverage only and cannot claim hidden-test
  coverage or official evaluator equivalence;
- coverage denominators are declared local matrix denominators only, never
  official ProgramBench task or hidden-test denominators;
- contamination register must fail closed when hidden, forbidden,
  postmortem-only, original-source, decompilation, internet, external-repo,
  host-secret, Docker-socket, official-evaluator, or hidden-test refs are
  exposed;
- contamination rows must not reveal forbidden source names, paths, excerpts,
  semantic summaries, test names, hidden artifact identifiers, or
  original-source clues;
- contamination rows must carry a redaction policy and detail posture that
  makes forbidden-source leakage mechanically visible;
- B rejects C artifact kinds and does not emit summaries, handoffs, or family
  closeout;
- B does not execute commands, run cases, materialize candidates, or contact
  official ProgramBench surfaces.

## Reference Fixtures

Future `vNext+261` reference fixtures should include:

- result projection for one A-included local case;
- observation ledger with local-only observations and no ranking language;
- coverage register with local coverage and one missing/local-gap row;
- contamination register with clean posture.

Reject fixtures should include:

- projection for a case not included by A;
- model-ranking observation language;
- benchmark-score or hidden-test-equivalence observation language;
- pass rate, solve rate, success rate, model wins, beats baseline,
  leaderboard-like, representative benchmark subset, or official-like score
  language;
- hidden/forbidden source exposed through contamination row details;
- hidden-test coverage counted as local coverage;
- command execution or batch execution posture in B fixture;
- C artifact shape present in B fixture.

## Non-Outputs

`PB-MATRIX-0-B` must not output:

- matrix summary;
- post-matrix handoff;
- family closeout alignment;
- official ProgramBench runner/evaluator integration;
- hidden-test handling;
- benchmark score or model ranking;
- batch execution rows;
- command execution rows;
- official submission authority;
- future-family selection.
