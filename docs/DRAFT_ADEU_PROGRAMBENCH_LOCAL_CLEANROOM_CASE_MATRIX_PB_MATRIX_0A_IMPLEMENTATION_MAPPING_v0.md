# Draft ADEU ProgramBench Local Cleanroom Case Matrix PB-MATRIX-0-A Implementation Mapping v0

Status: support / implementation mapping record for planned `PB-MATRIX-0-A`.

Authority layer: support.

This note maps the likely implementation for `PB-MATRIX-0-A`. It does not
authorize implementation by itself and does not replace a future
`vNext+260` lock, stop-gate decision, or edge assessment.

## Slice Intent

`PB-MATRIX-0-A` should make a local cleanroom case matrix request reviewable
without projecting results, running cases, scoring benchmarks, or ranking
models.

The slice should answer:

```text
Which released local cleanroom case lineages are eligible to enter one local
case matrix, under what shared controls and non-authority guardrails?
```

It must not answer:

```text
What benchmark score did the matrix get?
Which model is better?
Can we run a batch of cases?
Can hidden tests or official evaluator results judge the cases?
Can this matrix become an official ProgramBench submission?
```

## Selected Surfaces

Likely schema / model surfaces:

- `programbench_local_case_matrix_request@1`
- `programbench_local_case_inclusion_manifest@1`
- `programbench_local_case_lineage_eligibility_review@1`
- `programbench_local_case_matrix_control_contract@1`
- `programbench_local_case_matrix_non_authority_guardrail@1`

Likely source files for a future implementation:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_matrix.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_local_case_matrix_request.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_case_inclusion_manifest.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_case_lineage_eligibility_review.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_case_matrix_control_contract.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_case_matrix_non_authority_guardrail.v1.json`
- `spec/programbench_local_case_matrix_request.schema.json`
- `spec/programbench_local_case_inclusion_manifest.schema.json`
- `spec/programbench_local_case_lineage_eligibility_review.schema.json`
- `spec/programbench_local_case_matrix_control_contract.schema.json`
- `spec/programbench_local_case_matrix_non_authority_guardrail.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_pb_matrix_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus260/`

## Consumed Lineage

`PB-MATRIX-0-A` should require released ProgramBench local cleanroom refs:

- `PB-RETRY-0` family closeout and retry C rows when retry settlement is part
  of a case lineage;
- `PB-TRIAL-0` family closeout and trial C rows for every case lineage;
- `PB-ATTEMPT-0`, `PB-RECON-0`, `PB-ADAPTER-0`, and `PB-PY-0` closeouts as
  inherited cleanroom law;
- support doctrine only as context, never as case eligibility by itself.

## Field-Level Expectations

`programbench_local_case_matrix_request@1` should include:

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

`programbench_local_case_inclusion_manifest@1` should include:

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

`programbench_local_case_lineage_eligibility_review@1` should include:

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

`programbench_local_case_matrix_control_contract@1` should include:

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

`programbench_local_case_matrix_non_authority_guardrail@1` should include:

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

## Validation Expectations

The future implementation should validate:

- every A bundle resolves to one `case_matrix_ref`;
- matrix request declares `matrix_horizon`, `matrix_max_case_count`,
  aggregate count posture, and representativeness posture;
- matrix request and inclusion manifest cite the same matrix;
- inclusion manifest contains concrete case candidate refs, not globs;
- inclusion manifest uses row-shaped candidate case rows with released lineage
  refs and boundary hashes;
- every included case has released `PB-TRIAL-0` lineage;
- retry settlement refs, when present, resolve through released `PB-RETRY-0`
  closeout;
- included cases cannot be support-only, unreleased, contaminated,
  hidden-test-derived, official-evaluator-derived, original-source-derived,
  decompilation-derived, internet-derived, external-repo-derived, or
  postmortem-only;
- included cases cannot claim benchmark truth, official success, hidden-test
  equivalence, model superiority, or leaderboard standing;
- eligibility marked ready requires empty carried blockers, released family
  closeout refs, clean contamination posture, and local-only case result
  source posture;
- matrix control contract must define worker profile, tool policy, probe
  basis, sandbox/write scope, visibility, and non-ranking controls;
- the default control contract posture is one worker/model profile, one tool
  policy, one probe basis, and one sandbox/write-scope posture;
- matrix control contract cannot grant command execution, batch execution,
  official evaluator access, source lookup, decompilation, internet lookup,
  Docker socket, host secrets, wider write scope, or hidden-test access;
- multiple worker/model profile refs require explicit non-ranking and
  `multi_profile_matrix_posture =
  comparability_accounting_only_no_ranking` and still cannot rank models;
- local matrix aggregate counts must be inventory/accounting only and cannot
  be pass rate, solve rate, success rate, benchmark score, or model score;
- guardrail rows must assert no official benchmark authority, no model
  ranking, no hidden-test authority, no batch execution authority, no second
  retry authority, and no future-family selection;
- A rejects B/C artifact kinds.

## Reference Fixtures

Future `vNext+260` reference fixtures should include:

- one matrix request over released local case lineage;
- one inclusion manifest with one eligible local case and one blocked or
  support-only case row;
- one lineage eligibility review carrying local-only inclusion posture;
- one control contract with shared non-ranking controls;
- one non-authority guardrail.

Reject fixtures should include:

- hidden-test-derived case marked eligible;
- official-evaluator-derived case marked eligible;
- unreleased case marked included;
- contaminated case marked included;
- support-only case counted as included;
- model-ranking or benchmark-score language in request/control rows;
- representative benchmark subset claim from a local smoke/research matrix;
- multiple model profiles without comparability controls;
- pass rate, solve rate, success rate, model wins, beats baseline,
  leaderboard-like, or official-like score language;
- batch execution posture granted in A;
- B/C artifact kind present in A fixture.

## Non-Outputs

`PB-MATRIX-0-A` must not output:

- per-case result projections;
- observation ledgers;
- coverage registers;
- contamination registers;
- matrix summaries;
- post-matrix handoffs;
- family closeout alignment;
- command execution or batch execution records;
- benchmark scores or model rankings;
- official ProgramBench participation rows;
- hidden-test handling rows;
- official submissions;
- second retry or retry-chain authority.
