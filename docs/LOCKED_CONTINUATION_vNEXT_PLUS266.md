# LOCKED_CONTINUATION_vNEXT_PLUS266

## Status

Bounded starter lock draft for `PB-MATRIX-INCLUSION-0-A` (local matrix
inclusion request, candidate intake, eligibility review, control contract,
and non-authority guardrail).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-MATRIX-INCLUSION-0-A` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-MATRIX-INCLUSION-0`
- slice: `PB-MATRIX-INCLUSION-0-A`
- branch-local execution target: `arc/pb-matrix-inclusion-0-a`

## Purpose

Freeze the bounded `PB-MATRIX-INCLUSION-0-A` starter slice so the repo can
review local matrix inclusion request, candidate intake, lineage eligibility,
control, and non-authority rows without creating matrix amendment plans,
including cases in a revised matrix, executing cases, projecting results,
scoring benchmarks, comparing baselines, ranking models, or selecting a
future family.

`vNext+266` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize local
case execution, probe execution, batch command execution, candidate
materialization, matrix amendment decisions, direct matrix inclusion, matrix
revision registration, result projection, matrix summary, official
ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, pass rate,
solve rate, success rate, baseline comparison, model ranking, leaderboard
standing, generated official submissions, official submission authority,
second retry authority, retry-chain authority, unbounded command execution,
target mutation outside released local artifacts, runtime transition, product
authorization, graph-memory authority, release authority, recursive policy
amendment, or future-family selection.

Controlling invariant:

```text
PB-MATRIX-INCLUSION-0-A may decide which ready local case lineages are
recordable and eligible candidates for later local matrix amendment review,
but it may not include those cases, run those cases, project results, score
the matrix, compare to baselines, rank models, infer hidden-test success,
grant batch execution authority, or select the next family.
```

Matrix identity invariant:

```text
Matrix inclusion must bind to exactly one released base matrix revision and
exactly one proposed revision candidate. The base revision, proposed revision,
prior membership manifest, proposed membership manifest, and revision delta
must be hash-bound before eligibility can be marked ready.
```

Inclusion non-scoring invariant:

```text
Matrix inclusion is local accounting membership only. It is not a quality
judgment, not a benchmark-selection judgment, not a result projection, and
not a baseline or model-comparison statement.
```

## Instantiated Here

- `PB-MATRIX-INCLUSION-0-A` instantiates the first local cleanroom
  matrix-inclusion seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-CASE-EXPANSION-0` basis:
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_PB_CASE_EXPANSION_0_FAMILY_CLOSEOUT_v0.md`
    - local case lineage registration
    - expansion readiness summary
    - matrix candidate handoff
    - family closeout alignment
  - consumed released `PB-MATRIX-0` basis:
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0_FAMILY_CLOSEOUT_v0.md`
    - local matrix accounting doctrine
  - inherited released cleanroom basis:
    - `PB-TRIAL-0` family closeout
    - `PB-RETRY-0` family closeout
    - `PB-ATTEMPT-0` family closeout
    - `PB-RECON-0` family closeout
    - `PB-ADAPTER-0` family closeout
    - `PB-PY-0` family closeout
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v84.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_MATRIX_INCLUSION_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_MATRIX_INCLUSION_PB_MATRIX_INCLUSION_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_MATRIX_INCLUSION_PB_MATRIX_INCLUSION_0A_IMPLEMENTATION_MAPPING_v0.md`
  - emitted starter record shapes:
    - `programbench_local_matrix_inclusion_request@1`
    - `programbench_local_matrix_candidate_intake@1`
    - `programbench_local_matrix_inclusion_eligibility_review@1`
    - `programbench_local_matrix_inclusion_control_contract@1`
    - `programbench_local_matrix_inclusion_non_authority_guardrail@1`

## Required Starter Vocabulary

Minimum `programbench_local_matrix_inclusion_request@1` fields:

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

Minimum `programbench_local_matrix_candidate_intake@1` fields:

- `matrix_candidate_intake_ref`
- `matrix_inclusion_request_ref`
- `candidate_case_rows`
- `limitation_note`

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

Minimum `programbench_local_matrix_inclusion_eligibility_review@1` fields:

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

Minimum `programbench_local_matrix_inclusion_control_contract@1` fields:

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

Required control defaults:

- `representativeness_posture = not_representative_benchmark_sample`
- `inventory_count_posture = local_membership_accounting_only`
- `benchmark_denominator_posture = not_benchmark_denominator`
- `baseline_comparison_authority_posture =
  no_baseline_comparison_authority`

Minimum `programbench_local_matrix_inclusion_non_authority_guardrail@1`
fields:

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

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_local_matrix_inclusion_request@1`
  - `programbench_local_matrix_candidate_intake@1`
  - `programbench_local_matrix_inclusion_eligibility_review@1`
  - `programbench_local_matrix_inclusion_control_contract@1`
  - `programbench_local_matrix_inclusion_non_authority_guardrail@1`
- mirrored `spec/` schema exports for the same shapes;
- validators requiring one `matrix_inclusion_request_ref` across the A bundle;
- validators requiring exactly one released base matrix revision and exactly
  one proposed revision candidate;
- validators requiring released `PB-CASE-EXPANSION-0-C` lineage, readiness,
  handoff, and closeout refs;
- validators requiring released `PB-MATRIX-0` closeout or target matrix refs;
- validators requiring requested lineages to be ready and present in
  pressure-only handoff rows;
- validators rejecting blocked, deferred, contaminated, support-only,
  postmortem-only, hidden-test-derived, evaluator-derived, source-derived,
  decompilation-derived, internet-derived, or external-repo-derived
  candidates;
- validators requiring source boundary, probe contract, oracle boundary, and
  contamination screen hashes on candidate rows;
- validators rejecting duplicate base-matrix membership unless explicit
  replacement/update or regression/smoke posture is present;
- validators rejecting profile/tool/probe/write-scope/source-visibility
  widening while claiming comparable matrix posture;
- validators enforcing inventory-only and non-benchmark denominator posture;
- validators rejecting direct matrix inclusion, amendment decision, result
  projection, execution, batch execution, scoring, baseline comparison, model
  ranking, official ProgramBench authority, and future-family selection;
- validators rejecting `PB-MATRIX-INCLUSION-0-B/C` artifact shapes in A
  fixtures;
- focused tests for `PB-MATRIX-INCLUSION-0-A` plus schema export coverage;
- reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus266/`.

## Explicit Non-Outputs

`PB-MATRIX-INCLUSION-0-A` must not output:

- matrix amendment plans;
- case delta manifests;
- comparability delta reviews;
- contamination delta reviews;
- inclusion decision records;
- matrix revision registrations;
- revision readiness summaries;
- post-inclusion handoffs;
- family closeout alignment;
- result projection rows;
- matrix summary rows;
- local trial dockets or executions;
- retry rows;
- command execution or batch execution records;
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
  "target_arc": "vNext+266",
  "target_path": "PB-MATRIX-INCLUSION-0-A",
  "authority_layer": "lock",
  "selected_family": "PB-MATRIX-INCLUSION-0",
  "selected_slice": "PB-MATRIX-INCLUSION-0-A",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS266.md",
  "allowed_package": "packages/adeu_benchmarking",
  "selected_record_shapes": [
    "programbench_local_matrix_inclusion_request@1",
    "programbench_local_matrix_candidate_intake@1",
    "programbench_local_matrix_inclusion_eligibility_review@1",
    "programbench_local_matrix_inclusion_control_contract@1",
    "programbench_local_matrix_inclusion_non_authority_guardrail@1"
  ],
  "local_gate": "make arc-start-check ARC=266",
  "non_authority_summary": "No local case execution, probe execution, batch execution, direct matrix inclusion, matrix amendment decision, result projection, benchmark score, baseline comparison, model ranking, official ProgramBench participation, hidden-test handling, or future-family selection is authorized by this lock."
}
```

## Verification Plan

Before implementation starts:

```text
make arc-start-check ARC=266
```

For the implementation PR:

```text
.venv/bin/python -m pytest packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_inclusion_pb_matrix_inclusion_0a.py -q
make check
```
