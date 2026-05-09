# LOCKED_CONTINUATION_vNEXT_PLUS263

## Status

Bounded starter lock draft for `PB-CASE-EXPANSION-0-A` (local case expansion
request, source pool manifest, eligibility review, expansion control
contract, and non-authority guardrail).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-CASE-EXPANSION-0-A` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-CASE-EXPANSION-0`
- slice: `PB-CASE-EXPANSION-0-A`
- branch-local execution target: `arc/pb-case-expansion-0-a`

## Purpose

Freeze the bounded `PB-CASE-EXPANSION-0-A` starter slice so the repo can
review a local cleanroom case-expansion request, source pool manifest,
eligibility review, control contract, and non-authority guardrail without
creating blueprints, registering case lineages, running local trials,
executing batches, scoring benchmarks, comparing baselines, ranking models,
handling hidden tests, or selecting a future family.

`vNext+263` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize
official ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, pass rate,
solve rate, success rate, baseline-relative result claims, model ranking,
leaderboard standing, generated official submissions, official submission
authority, local trial dispatch, batch command execution, candidate
materialization, second retry authority, retry-chain authority, unbounded
command execution, target mutation outside released local artifacts, runtime
transition, product authorization, graph-memory authority, release authority,
recursive policy amendment, or future-family selection.

Controlling invariant:

```text
PB-CASE-EXPANSION-0-A may decide which cleanroom-visible source pools and
candidate case ideas are eligible for later local case blueprint review, but
it may not create blueprints, register case lineages, run cases, score cases,
compare them to baselines, rank models, infer hidden-test success, grant
batch execution authority, or select the next family.
```

Selection-governance invariant:

```text
New local case supply is not representative benchmark construction. A
candidate case idea must declare selection horizon, rationale, bias posture,
diversity posture, dedupe posture, source subset hash, and overlap with
existing released case lineages. Duplicate smoke/regression cases may be
eligible only with explicit rationale and must not become benchmark coverage.
```

No-derived-summary-laundering invariant:

```text
Forbidden, hidden, postmortem-only, source-derived, evaluator-derived, or
auditor-only sources may not be transformed into visible advisory facts,
labels, case ideas, behavior obligations, probe expectations, oracle boundary
claims, or case-selection rationale.
```

## Instantiated Here

- `PB-CASE-EXPANSION-0-A` instantiates the first local cleanroom
  case-expansion seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-MATRIX-0` basis:
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0_FAMILY_CLOSEOUT_v0.md`
    - matrix summary
    - post-matrix handoff
    - matrix family closeout alignment
  - inherited released cleanroom basis:
    - `PB-TRIAL-0` family closeout
    - `PB-RETRY-0` family closeout
    - `PB-ATTEMPT-0` family closeout
    - `PB-RECON-0` family closeout
    - `PB-ADAPTER-0` family closeout
    - `PB-PY-0` family closeout
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v83.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_PB_CASE_EXPANSION_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_PB_CASE_EXPANSION_0A_IMPLEMENTATION_MAPPING_v0.md`
  - emitted starter record shapes:
    - `programbench_local_case_expansion_request@1`
    - `programbench_local_case_source_pool_manifest@1`
    - `programbench_local_case_expansion_eligibility_review@1`
    - `programbench_local_case_expansion_control_contract@1`
    - `programbench_local_case_expansion_non_authority_guardrail@1`

## Required Starter Vocabulary

Minimum `programbench_local_case_expansion_request@1` fields:

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

Required posture:

- `representativeness_posture =
  not_representative_benchmark_sample`

Minimum `programbench_local_case_source_pool_manifest@1` fields:

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

Minimum `programbench_local_case_expansion_eligibility_review@1` fields:

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

Minimum `programbench_local_case_expansion_control_contract@1` fields:

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

Minimum `programbench_local_case_expansion_non_authority_guardrail@1` fields:

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

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_local_case_expansion_request@1`
  - `programbench_local_case_source_pool_manifest@1`
  - `programbench_local_case_expansion_eligibility_review@1`
  - `programbench_local_case_expansion_control_contract@1`
  - `programbench_local_case_expansion_non_authority_guardrail@1`
- mirrored `spec/` schema exports for the same shapes;
- validators requiring one `case_expansion_ref` across the A bundle;
- validators requiring released `PB-MATRIX-0` closeout lineage before
  matrix-driven expansion pressure is accepted;
- validators requiring concrete source refs and identity hashes, not globs;
- validators requiring selection horizon, selection rationale, bias posture,
  diversity posture, dedupe policy, and non-representative posture;
- validators rejecting hidden, forbidden, postmortem-only,
  original-source-derived, decompilation-derived, internet-derived,
  external-repo-derived, and official-evaluator-derived rows as allowed
  expansion evidence;
- validators rejecting hidden/forbidden names, paths, excerpts, test names,
  semantic summaries, hidden artifact identifiers, original-source clues, or
  derived facts in visible advisory rows;
- validators enforcing no derived-summary laundering;
- validators requiring at least one cleanroom-visible source witness for
  eligible candidate case ideas;
- validators rejecting duplicate existing released case lineage ideas unless
  explicit smoke/regression rationale is present;
- validators rejecting local execution, batch execution, scoring, baseline
  comparison, model ranking, official evaluator access, source lookup,
  decompilation, internet lookup, Docker socket, host secrets, wider write
  scope, hidden-test access, trial execution, or future-family selection;
- validators rejecting `PB-CASE-EXPANSION-0-B/C` artifact shapes in A
  fixtures;
- focused tests for `PB-CASE-EXPANSION-0-A` plus schema export coverage;
- reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus263/`.

## Explicit Non-Outputs

`PB-CASE-EXPANSION-0-A` must not output:

- local case blueprints;
- cleanroom evidence packs;
- probe contracts;
- oracle boundaries;
- contamination screens;
- local case lineage registrations;
- readiness summaries;
- matrix candidate handoffs;
- family closeout alignment;
- local trial dockets or executions;
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
  "target_arc": "vNext+263",
  "target_path": "PB-CASE-EXPANSION-0-A",
  "authority_layer": "lock",
  "selected_family": "PB-CASE-EXPANSION-0",
  "selected_slice": "PB-CASE-EXPANSION-0-A",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS263.md",
  "allowed_package": "packages/adeu_benchmarking",
  "selected_record_shapes": [
    "programbench_local_case_expansion_request@1",
    "programbench_local_case_source_pool_manifest@1",
    "programbench_local_case_expansion_eligibility_review@1",
    "programbench_local_case_expansion_control_contract@1",
    "programbench_local_case_expansion_non_authority_guardrail@1"
  ],
  "local_gate": "make arc-start-check ARC=263",
  "non_authority_summary": "No official ProgramBench participation, hidden-test handling, benchmark truth, benchmark scoring, baseline comparison, model ranking, leaderboard standing, batch execution, local trial execution, case blueprinting, case lineage registration, second retry authority, retry-chain authority, or future-family selection is authorized by this lock."
}
```

## Verification Plan

Before implementation starts:

```text
make arc-start-check ARC=263
```

For the implementation PR:

```text
.venv/bin/python -m pytest packages/adeu_benchmarking/tests/test_programbench_cleanroom_case_expansion_pb_case_expansion_0a.py -q
make check
```
