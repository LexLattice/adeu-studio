# Draft ADEU ProgramBench Local Cleanroom Matrix Inclusion PB-MATRIX-INCLUSION-0-B Implementation Mapping v0

Status: support / implementation mapping record for planned
`PB-MATRIX-INCLUSION-0-B`.

Authority layer: support.

This note maps the likely implementation for `PB-MATRIX-INCLUSION-0-B`. It
does not authorize implementation by itself and does not replace a future
`vNext+<n>` lock, stop-gate decision, or edge assessment.

## Slice Intent

`PB-MATRIX-INCLUSION-0-B` should produce the local matrix amendment basis and
local accounting inclusion decisions for A-eligible case lineages. It should
not execute cases, project results, summarize outcomes, score benchmarks,
compare baselines, or rank models.

The slice should answer:

```text
Which A-eligible local case lineages are added, deferred, or rejected for one
declared local matrix revision?
```

It must not answer:

```text
Can the revised matrix run?
What result did any included case get?
What score did the revised matrix get?
Is this better than a baseline?
Which model is better?
```

## Selected Surfaces

Likely schema / model surfaces:

- `programbench_local_matrix_amendment_plan@1`
- `programbench_local_matrix_case_delta_manifest@1`
- `programbench_local_matrix_comparability_delta_review@1`
- `programbench_local_matrix_contamination_delta_review@1`
- `programbench_local_matrix_inclusion_decision_record@1`

Likely source files for a future implementation:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_matrix_inclusion.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_inclusion_pb_matrix_inclusion_0b.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus267/`

## Consumed Lineage

`PB-MATRIX-INCLUSION-0-B` should require released `PB-MATRIX-INCLUSION-0-A`
rows:

- inclusion request;
- candidate intake;
- eligibility review;
- control contract;
- non-authority guardrail.

It should consume case-expansion and matrix closeout refs only through the
released A bundle and inherited lineage checks.

## Field-Level Expectations

`programbench_local_matrix_amendment_plan@1` should include:

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
- `limitation_note`

`programbench_local_matrix_case_delta_manifest@1` should include:

- `matrix_case_delta_manifest_ref`
- `matrix_amendment_plan_ref`
- `case_delta_rows`
- `case_delta_kind`
- `case_lineage_ref`
- `case_lineage_hash`
- `prior_matrix_membership_status`
- `new_matrix_membership_candidate_status`
- `dedupe_status`
- `delta_reason`
- `delta_manifest_hash`
- `limitation_note`

`programbench_local_matrix_comparability_delta_review@1` should include:

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
- `non_comparable_local_accounting_posture`
- `model_ranking_authority_posture`
- `baseline_comparison_authority_posture`
- `limitation_note`

Required posture:

- `comparability_accounting_posture =
  local_accounting_only_no_model_or_baseline_comparison`

`programbench_local_matrix_contamination_delta_review@1` should include:

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

`programbench_local_matrix_inclusion_decision_record@1` should include:

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
- `limitation_note`

Allowed decision basis values should be governance/accounting reasons:

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

## Validation Expectations

The future implementation should validate:

- B requires released A refs;
- B cannot add A-blocked, A-deferred, or A-unknown candidates;
- case delta manifest must account for every A-eligible candidate exactly
  once as added, deferred, or rejected;
- case delta manifest cannot silently drop or duplicate candidate lineage refs;
- comparability delta review must mark any worker/model/tool/probe/sandbox
  changes as non-comparable local accounting only;
- comparability delta review cannot claim model comparison or baseline
  comparison authority;
- comparability delta review must bind base/candidate worker, model, tool,
  probe, source visibility, and sandbox/write-scope hashes before claiming
  continuity;
- contamination delta review must preserve redaction and fail closed on
  hidden, forbidden, postmortem-only, evaluator-derived, source-derived,
  decompilation-derived, internet-derived, or external-repo-derived exposure;
- inclusion decision requires clean contamination delta review;
- inclusion decision grants local accounting membership only;
- inclusion decision cannot use performance-selection rationale such as likely
  pass/fail, score improvement, model advantage, baseline advantage, or
  benchmark relevance;
- inclusion decision cannot grant execution, result projection, scoring,
  baseline comparison, model ranking, official ProgramBench participation, or
  future-family selection.

## Reference Fixtures

Future B fixtures should include:

- one amendment plan over A-eligible candidates;
- one case delta manifest with added, deferred, and rejected rows;
- one comparability delta review with no material control widening;
- one contamination delta review with clean transfer;
- one inclusion decision record for local accounting membership only.

Reject fixtures should include:

- B bundle without released A refs;
- included candidate that A marked blocked;
- delta manifest missing an eligible candidate;
- duplicate candidate in delta rows;
- contamination review leaking hidden/forbidden detail;
- inclusion decision granting execution, result projection, score, baseline
  comparison, model ranking, or official ProgramBench authority.

## Non-Outputs

`PB-MATRIX-INCLUSION-0-B` must not output:

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
