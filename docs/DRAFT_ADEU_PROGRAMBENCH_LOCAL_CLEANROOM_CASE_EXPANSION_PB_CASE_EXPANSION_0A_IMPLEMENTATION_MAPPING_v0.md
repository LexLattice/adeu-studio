# Draft ADEU ProgramBench Local Cleanroom Case Expansion PB-CASE-EXPANSION-0-A Implementation Mapping v0

Status: support / implementation mapping record for planned
`PB-CASE-EXPANSION-0-A`.

Authority layer: support.

This note maps the likely implementation for `PB-CASE-EXPANSION-0-A`. It
does not authorize implementation by itself and does not replace a future
`vNext+263` lock, stop-gate decision, or edge assessment.

## Slice Intent

`PB-CASE-EXPANSION-0-A` should make a local case-expansion request and source
pool reviewable without creating case blueprints, registering case lineages,
running trials, executing batches, scoring benchmarks, or ranking models.

The slice should answer:

```text
Which cleanroom-visible source pools and candidate case ideas are eligible
for later local case blueprint review?
```

It must not answer:

```text
Can we run the case?
What score did the case get?
Does this improve against an existing baseline?
Can we include this case in a matrix now?
Can official hidden tests or evaluator results judge it?
```

## Selected Surfaces

Likely schema / model surfaces:

- `programbench_local_case_expansion_request@1`
- `programbench_local_case_source_pool_manifest@1`
- `programbench_local_case_expansion_eligibility_review@1`
- `programbench_local_case_expansion_control_contract@1`
- `programbench_local_case_expansion_non_authority_guardrail@1`

Likely source files for a future implementation:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_case_expansion.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/schema/programbench_local_case_expansion_request.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_case_source_pool_manifest.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_case_expansion_eligibility_review.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_case_expansion_control_contract.v1.json`
- `packages/adeu_benchmarking/schema/programbench_local_case_expansion_non_authority_guardrail.v1.json`
- `spec/programbench_local_case_expansion_request.schema.json`
- `spec/programbench_local_case_source_pool_manifest.schema.json`
- `spec/programbench_local_case_expansion_eligibility_review.schema.json`
- `spec/programbench_local_case_expansion_control_contract.schema.json`
- `spec/programbench_local_case_expansion_non_authority_guardrail.schema.json`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_case_expansion_pb_case_expansion_0a.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus263/`

## Consumed Lineage

`PB-CASE-EXPANSION-0-A` should require released ProgramBench local cleanroom
refs:

- `PB-MATRIX-0` family closeout and C rows as local matrix accounting
  substrate;
- `PB-TRIAL-0` and `PB-RETRY-0` closeouts as existing local case lineage
  context;
- `PB-ATTEMPT-0`, `PB-RECON-0`, `PB-ADAPTER-0`, and `PB-PY-0` closeouts as
  inherited cleanroom law;
- support doctrine only as context, never as source eligibility by itself.

## Field-Level Expectations

`programbench_local_case_expansion_request@1` should include:

- `case_expansion_ref`
- `case_expansion_request_ref`
- `source_pool_manifest_ref`
- `expansion_eligibility_review_ref`
- `expansion_control_contract_ref`
- `expansion_horizon`
- `expansion_max_case_count`
- `candidate_case_idea_refs`
- `requested_case_count`
- `matrix_pressure_refs`
- `matrix_pressure_kind`
- `case_selection_horizon`
- `case_selection_rationale_rows`
- `case_selection_bias_posture`
- `case_diversity_posture`
- `representativeness_posture`
- `dedupe_policy_ref`
- `official_benchmark_authority_posture`
- `benchmark_score_authority_posture`
- `baseline_comparison_authority_posture`
- `model_ranking_posture`
- `batch_execution_authority_posture`
- `future_family_selection_posture`
- `limitation_note`

`programbench_local_case_source_pool_manifest@1` should include:

- `source_pool_manifest_ref`
- `case_expansion_ref`
- `source_pool_rows`
- `candidate_case_idea_rows`
- `allowed_source_refs`
- `blocked_source_refs`
- `auditor_only_source_refs`
- `support_only_source_refs`
- `forbidden_source_refs`
- `source_set_hash`
- `visible_source_set_hash`
- `forbidden_source_set_hash`
- `derived_summary_policy`
- `worker_visible_policy`
- `blueprint_visible_policy`
- `limitation_note`

Minimum `source_pool_row` fields:

- `source_ref`
- `source_kind`
- `source_identity_hash`
- `source_origin_posture`
- `source_visibility_posture`
- `store_presence_posture`
- `derived_summary_policy`
- `allowed_for_expansion`
- `exclusion_reason`
- `limitation_note`

Minimum `candidate_case_idea_row` fields:

- `candidate_case_idea_ref`
- `case_expansion_ref`
- `source_refs`
- `candidate_case_idea_hash`
- `source_pool_subset_hash`
- `dedupe_against_existing_case_lineages`
- `existing_case_lineage_overlap_refs`
- `nearest_existing_case_refs`
- `novelty_or_duplication_posture`
- `case_idea_label`
- `case_origin_posture`
- `case_visibility_posture`
- `candidate_scope_posture`
- `expected_blueprint_deferred_posture`
- `eligibility_claim`
- `limitation_note`

`programbench_local_case_expansion_eligibility_review@1` should include:

- `expansion_eligibility_review_ref`
- `case_expansion_ref`
- `candidate_eligibility_rows`
- `eligible_candidate_case_idea_refs`
- `blocked_candidate_case_idea_refs`
- `deferred_candidate_case_idea_refs`
- `carried_blocker_refs`
- `carried_warning_refs`
- `released_family_closeout_refs`
- `non_authority_guardrail_refs`
- `limitation_note`

`programbench_local_case_expansion_control_contract@1` should include:

- `expansion_control_contract_ref`
- `case_expansion_ref`
- `source_visibility_control_ref`
- `source_derivation_control_ref`
- `candidate_count_control_ref`
- `blueprint_deferred_control_ref`
- `execution_deferred_control_ref`
- `matrix_inclusion_deferred_control_ref`
- `scoring_deferred_control_ref`
- `model_ranking_deferred_control_ref`
- `allowed_expansion_action_rows`
- `forbidden_expansion_action_rows`
- `limitation_note`

`programbench_local_case_expansion_non_authority_guardrail@1` should include:

- `expansion_guardrail_ref`
- `case_expansion_refs`
- `guardrail_source_refs`
- `non_authority_rows`
- `official_programbench_posture`
- `hidden_test_posture`
- `benchmark_truth_posture`
- `benchmark_score_posture`
- `baseline_comparison_posture`
- `model_ranking_posture`
- `batch_execution_posture`
- `trial_execution_posture`
- `future_family_posture`
- `limitation_note`

## Validation Expectations

The future implementation should validate:

- every A bundle resolves to one `case_expansion_ref`;
- expansion request declares horizon, maximum case count, and non-authority
  postures;
- request, source pool, eligibility review, control contract, and guardrail
  cite the same expansion ref;
- source pool manifests list concrete source refs and identity hashes, not
  globs;
- request rows declare selection horizon, selection rationale, selection bias
  posture, diversity posture, dedupe policy, and
  `representativeness_posture = not_representative_benchmark_sample`;
- hidden, forbidden, postmortem-only, original-source-derived,
  decompilation-derived, internet-derived, external-repo-derived, and
  official-evaluator-derived rows cannot be marked allowed for expansion;
- hidden/forbidden source names, paths, excerpts, test names, semantic
  summaries, hidden artifact identifiers, or original-source clues cannot
  appear in worker-visible or blueprint-visible advisory rows;
- forbidden, hidden, postmortem-only, source-derived, evaluator-derived, or
  auditor-only sources cannot be transformed into visible advisory facts,
  labels, case ideas, behavior obligations, probe expectations, or oracle
  boundary claims;
- support-only rows cannot make a candidate eligible by themselves;
- candidate case ideas marked eligible require at least one cleanroom-visible
  source witness;
- candidate case ideas that duplicate existing released local case lineages
  cannot be marked eligible unless duplication is explicitly allowed by the
  expansion horizon and rationale;
- eligibility marked ready requires empty carried blockers, released family
  closeout refs, clean source visibility posture, and local-only expansion
  posture;
- controls cannot grant local execution, batch execution, scoring, baseline
  comparison, model ranking, official evaluator access, source lookup,
  decompilation, internet lookup, Docker socket, host secrets, wider write
  scope, or hidden-test access;
- guardrail rows assert no official benchmark authority, no hidden-test
  authority, no benchmark score, no baseline comparison, no model ranking, no
  batch execution, no trial execution, and no future-family selection;
- A rejects B/C artifact kinds.

## Reference Fixtures

Future A fixtures should include:

- one expansion request over released matrix pressure;
- one source pool manifest with cleanroom-visible, support-only, and
  auditor-only exclusion rows;
- one eligibility review with eligible, blocked, and deferred candidate case
  ideas;
- one control contract preserving source visibility and deferring blueprint,
  execution, matrix inclusion, scoring, and ranking;
- one non-authority guardrail.

Reject fixtures should include:

- hidden-test-derived source marked allowed;
- official-evaluator-derived source marked allowed;
- support-only source making a candidate eligible;
- hidden/forbidden path or test name in visible summary;
- candidate label revealing hidden test name or original source function name;
- request granting local execution or batch execution;
- request claiming baseline score or pass rate;
- duplicate "new" case without explicit smoke/regression rationale;
- candidate idea using a glob instead of concrete source refs;
- B/C artifact shape present in A fixture.
