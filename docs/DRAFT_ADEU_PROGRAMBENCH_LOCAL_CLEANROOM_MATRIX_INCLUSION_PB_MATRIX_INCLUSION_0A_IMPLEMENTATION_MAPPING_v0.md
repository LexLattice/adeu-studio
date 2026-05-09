# Draft ADEU ProgramBench Local Cleanroom Matrix Inclusion PB-MATRIX-INCLUSION-0-A Implementation Mapping v0

Status: support / implementation mapping record for planned
`PB-MATRIX-INCLUSION-0-A`.

Authority layer: support.

This note maps the likely implementation for `PB-MATRIX-INCLUSION-0-A`. It
does not authorize implementation by itself and does not replace a future
`vNext+<n>` lock, stop-gate decision, or edge assessment.

## Slice Intent

`PB-MATRIX-INCLUSION-0-A` should make matrix-inclusion candidacy reviewable
for released local case lineages. It should not create an amendment plan,
include cases in a revised matrix, run cases, project results, summarize
outcomes, score benchmarks, compare baselines, or rank models.

The slice should answer:

```text
Which ready local case lineages are recordable and eligible candidates for
later matrix amendment review?
```

It must not answer:

```text
Which cases are included now?
Can the matrix run now?
What result did any case get?
What score did the matrix get?
Is this matrix representative of ProgramBench?
```

## Selected Surfaces

Likely schema / model surfaces:

- `programbench_local_matrix_inclusion_request@1`
- `programbench_local_matrix_candidate_intake@1`
- `programbench_local_matrix_inclusion_eligibility_review@1`
- `programbench_local_matrix_inclusion_control_contract@1`
- `programbench_local_matrix_inclusion_non_authority_guardrail@1`

Likely source files for a future implementation:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_matrix_inclusion.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_inclusion_pb_matrix_inclusion_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus266/`

## Consumed Lineage

`PB-MATRIX-INCLUSION-0-A` should require released `PB-CASE-EXPANSION-0-C`
rows:

- `programbench_local_case_lineage_registration@1`
- `programbench_local_case_expansion_readiness_summary@1`
- `programbench_local_case_matrix_candidate_handoff@1`
- `programbench_local_case_expansion_family_closeout_alignment@1`

It should also require released `PB-MATRIX-0` closeout or matrix-accounting
refs as the target matrix substrate.

## Field-Level Expectations

`programbench_local_matrix_inclusion_request@1` should include:

- `matrix_inclusion_request_ref`
- `base_matrix_ref`
- `base_matrix_revision_ref`
- `base_matrix_revision_hash`
- `target_matrix_revision_candidate_ref`
- `target_matrix_revision_candidate_hash`
- `prior_membership_manifest_hash`
- `proposed_membership_manifest_hash`
- `revision_delta_hash`
- `case_expansion_ref`
- `case_expansion_readiness_summary_ref`
- `case_matrix_candidate_handoff_ref`
- `requested_case_lineage_refs`
- `matrix_inclusion_horizon`
- `matrix_revision_horizon`
- `matrix_max_added_case_count`
- `selection_rationale_rows`
- `representativeness_posture`
- `benchmark_truth_posture`
- `execution_authority_posture`
- `result_projection_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

`programbench_local_matrix_candidate_intake@1` should include:

- `matrix_candidate_intake_ref`
- `matrix_inclusion_request_ref`
- `candidate_case_rows`

Minimum `matrix_inclusion_candidate_row` fields:

- `candidate_case_lineage_ref`
- `lineage_registration_ref`
- `readiness_summary_ref`
- `handoff_pressure_ref`
- `case_lineage_hash`
- `source_boundary_hash`
- `probe_contract_hash`
- `oracle_boundary_hash`
- `contamination_screen_hash`
- `expansion_family_closeout_ref`
- `prior_matrix_membership_status`
- `duplicate_case_refs`
- `dedupe_basis_refs`
- `dedupe_status`
- `duplicate_of_case_lineage_refs`
- `duplicate_allowed_posture`
- `candidate_origin_posture`
- `case_readiness_posture`
- `contamination_posture`
- `matrix_candidate_status`
- `candidate_intake_status`
- `intake_blocker_refs`
- `intake_warning_refs`
- `limitation_note`

`programbench_local_matrix_inclusion_eligibility_review@1` should include:

- `matrix_inclusion_eligibility_review_ref`
- `matrix_inclusion_request_ref`
- `matrix_candidate_intake_ref`
- `eligible_case_lineage_refs`
- `blocked_case_lineage_refs`
- `deferred_case_lineage_refs`
- `eligibility_row_refs`
- `eligibility_status`
- `blocker_refs`
- `warning_refs`
- `cleanroom_boundary_status`
- `probe_oracle_coverage_status`
- `contamination_status`
- `dedupe_status`
- `limitation_note`

`programbench_local_matrix_inclusion_control_contract@1` should include:

- `matrix_inclusion_control_contract_ref`
- `matrix_inclusion_request_ref`
- `matrix_horizon`
- `matrix_revision_scope_posture`
- `representativeness_posture`
- `inventory_count_posture`
- `benchmark_denominator_posture`
- `baseline_comparison_authority_posture`
- `worker_profile_continuity_posture`
- `model_profile_continuity_posture`
- `tool_policy_continuity_posture`
- `probe_basis_continuity_posture`
- `sandbox_write_scope_continuity_posture`
- `source_visibility_continuity_posture`
- `multi_profile_matrix_posture`
- `aggregate_count_posture`
- `non_ranking_posture`
- `non_scoring_posture`
- `limitation_note`

Required defaults:

- `representativeness_posture = not_representative_benchmark_sample`
- `inventory_count_posture = local_membership_accounting_only`
- `benchmark_denominator_posture = not_benchmark_denominator`
- `baseline_comparison_authority_posture =
  no_baseline_comparison_authority`

`programbench_local_matrix_inclusion_non_authority_guardrail@1` should
include:

- `matrix_inclusion_guardrail_ref`
- `matrix_inclusion_request_ref`
- `forbidden_authority_rows`
- `matrix_amendment_deferred_posture`
- `direct_inclusion_authority_posture`
- `execution_authority_posture`
- `result_projection_authority_posture`
- `benchmark_score_authority_posture`
- `baseline_comparison_authority_posture`
- `model_ranking_authority_posture`
- `official_programbench_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

## Validation Expectations

The future implementation should validate:

- every A bundle resolves to one `matrix_inclusion_request_ref`;
- every A request binds to exactly one released base matrix revision and one
  proposed revision candidate;
- A requires released `PB-CASE-EXPANSION-0-C` lineage and handoff refs;
- A requires released `PB-MATRIX-0` closeout or target matrix refs;
- requested lineages must be ready in the expansion readiness summary;
- requested lineages must appear in pressure-only matrix candidate handoff
  rows;
- blocked, deferred, contaminated, support-only, postmortem-only,
  hidden-test-derived, evaluator-derived, source-derived,
  decompilation-derived, internet-derived, or external-repo-derived
  candidates are rejected;
- candidates missing source boundary, probe contract, oracle boundary, or
  contamination screen hash binding are rejected;
- candidate refs cannot duplicate existing target matrix members unless the
  matrix horizon explicitly allows replacement/update or regression/smoke
  duplication;
- control contract cannot widen worker/model profile, tool policy, probe
  basis, write scope, network posture, or source visibility while claiming
  comparable matrix posture;
- aggregate counts remain inventory/accounting only;
- A rejects direct matrix inclusion, amendment decision, result projection,
  execution, batch execution, score, baseline comparison, model ranking,
  official ProgramBench, and future-family authority.

## Reference Fixtures

Future A fixtures should include:

- one inclusion request over a released ready case-expansion lineage;
- one candidate intake with source/probe/oracle/contamination hashes;
- one eligibility review with one eligible and one blocked candidate;
- one control contract preserving local matrix non-ranking posture;
- one non-authority guardrail.

Reject fixtures should include:

- candidate missing released case-expansion closeout;
- candidate not present in pressure-only handoff;
- candidate marked ready but carrying contamination;
- candidate missing probe or oracle coverage hash;
- duplicate candidate without allowed regression/smoke posture;
- control contract widening tool policy while claiming comparability;
- request granting direct matrix inclusion;
- request containing benchmark score, baseline comparison, or model-ranking
  language.

## Non-Outputs

`PB-MATRIX-INCLUSION-0-A` must not output:

- matrix amendment plan rows;
- case delta manifest rows;
- inclusion decision rows;
- matrix revision registration rows;
- result projection rows;
- matrix summary rows;
- local trial or retry rows;
- execution or probe execution rows;
- benchmark scores;
- baseline comparison rows;
- model rankings;
- official ProgramBench participation rows;
- future-family selection.
