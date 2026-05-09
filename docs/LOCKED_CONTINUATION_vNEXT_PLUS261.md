# LOCKED_CONTINUATION_vNEXT_PLUS261

## Status

Bounded starter lock draft for `PB-MATRIX-0-B` (per-case result projection,
local matrix observation ledger, matrix coverage register, and contamination
register).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-MATRIX-0-B` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-MATRIX-0`
- slice: `PB-MATRIX-0-B`
- branch-local execution target: `arc/pb-matrix-0-b`

## Purpose

Freeze the bounded `PB-MATRIX-0-B` starter slice so the repo can project
released per-case local results into a common matrix vocabulary and record
local matrix observations, coverage, and contamination posture under released
`PB-MATRIX-0-A` inclusion/control law.

`vNext+261` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize local
case execution, batch command execution, candidate materialization, official
ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, pass rate,
solve rate, success rate, model ranking, leaderboard standing, generated
official submissions, official submission authority, matrix summary,
post-matrix handoff, family closeout, second retry authority, retry-chain
authority, unbounded command execution, product authorization, graph-memory
authority, release authority, recursive policy amendment, or future-family
selection.

Controlling invariant:

```text
PB-MATRIX-0-B may project released local case results into matrix-local rows,
but it may not create new outcome truth, execute cases, score benchmarks,
rank models, infer hidden-test success, grant batch execution authority, or
select the next family.
```

Projection invariant:

```text
Every B projection must be derived from released local trial/retry/attempt
lineage already admitted by PB-MATRIX-0-A. Projection is a local accounting
view, not a new result authority.
```

## Instantiated Here

- `PB-MATRIX-0-B` instantiates the second local cleanroom case-matrix seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-MATRIX-0-A` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS260.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS260.md`
    - `docs/ASSESSMENT_vNEXT_PLUS260_EDGES.md`
    - `apps/api/fixtures/benchmarking/vnext_plus260/programbench_local_case_matrix_request_v260_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus260/programbench_local_case_inclusion_manifest_v260_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus260/programbench_local_case_lineage_eligibility_review_v260_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus260/programbench_local_case_matrix_control_contract_v260_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus260/programbench_local_case_matrix_non_authority_guardrail_v260_reference.json`
  - inherited released local cleanroom lineage through A:
    - `PB-TRIAL-0` outcome and remand rows
    - optional `PB-RETRY-0` outcome and settlement rows
    - inherited `PB-ATTEMPT-0`, `PB-RECON-0`, `PB-ADAPTER-0`, and `PB-PY-0`
      closeout substrate
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v82.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_MATRIX_PB_MATRIX_0B_IMPLEMENTATION_MAPPING_v0.md`
  - emitted second-slice record shapes:
    - `programbench_local_case_matrix_result_projection@1`
    - `programbench_local_case_matrix_observation_ledger@1`
    - `programbench_local_case_matrix_coverage_register@1`
    - `programbench_local_case_matrix_contamination_register@1`

## Required Starter Vocabulary

Minimum `programbench_local_case_matrix_result_projection@1` fields:

- `matrix_result_projection_ref`
- `case_matrix_ref`
- `matrix_request_ref`
- `case_inclusion_manifest_ref`
- `case_lineage_eligibility_review_ref`
- `matrix_control_contract_ref`
- `matrix_guardrail_ref`
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

Required projection posture:

- projection rows may reference only cases admitted by released
  `PB-MATRIX-0-A`;
- every included case must have exactly one current projection row or a
  declared projection gap;
- projected result posture must be derived from released local trial/retry
  rows, not authored as new outcome truth;
- source result hashes, source family closeout refs, projection rule refs,
  currentness posture, and not-new-truth posture are required;
- retry settlement projection must preserve unresolved remand pressure.

Minimum `programbench_local_case_matrix_observation_ledger@1` fields:

- `matrix_observation_ledger_ref`
- `case_matrix_ref`
- `observation_rows`
- `local_observation_refs`
- `blocked_observation_refs`
- `non_ranking_posture`
- `benchmark_truth_posture`
- `soft_scoring_language_posture`
- `limitation_note`

Minimum `programbench_local_case_matrix_coverage_register@1` fields:

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

Minimum `programbench_local_case_matrix_contamination_register@1` fields:

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

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_local_case_matrix_result_projection@1`
  - `programbench_local_case_matrix_observation_ledger@1`
  - `programbench_local_case_matrix_coverage_register@1`
  - `programbench_local_case_matrix_contamination_register@1`
- mirrored `spec/` schema exports for the same shapes;
- validators requiring released `PB-MATRIX-0-A` refs before B rows validate;
- validators requiring one `case_matrix_ref` across the B bundle;
- validators requiring projection rows only for A-included cases;
- validators requiring exactly one current projection row or one declared
  projection gap per included case;
- validators requiring source result hash, source closeout ref, projection
  rule ref, projection currentness, and not-new-truth posture;
- validators rejecting authored new outcome truth;
- validators rejecting benchmark scores, official scores, hidden-test
  outcomes, leaderboard standing, model superiority, cross-worker ranking,
  official-submission posture, and soft scoring language;
- validators requiring coverage denominators to be local matrix denominators
  only, never official ProgramBench or hidden-test denominators;
- validators rejecting hidden-test coverage counted as local coverage;
- validators requiring contamination rows to carry redaction policy and
  detail posture;
- validators rejecting forbidden source names, paths, excerpts, semantic
  summaries, test names, hidden artifact identifiers, original-source clues,
  or excluded derived summaries in contamination details;
- validators rejecting command execution, batch execution, candidate
  materialization, official runner/evaluator contact, hidden-test handling,
  benchmark score, model ranking, and future-family selection;
- validators rejecting `PB-MATRIX-0-C` artifact shapes in B fixtures;
- focused tests for `PB-MATRIX-0-B` plus schema export coverage;
- reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus261/`.

## Explicit Non-Outputs

`PB-MATRIX-0-B` must not output:

- matrix summary;
- post-matrix handoff;
- family closeout alignment;
- command execution or batch execution records;
- candidate materialization records;
- official ProgramBench runner/evaluator integration;
- hidden-test handling;
- benchmark score, pass rate, solve rate, success rate, or model ranking;
- official submission authority;
- second retry or retry-chain authority;
- future-family selection.

## Starter Contract

```json
{
  "schema": "locked_continuation_contract@1",
  "target_arc": "vNext+261",
  "target_path": "PB-MATRIX-0-B",
  "authority_layer": "lock",
  "selected_family": "PB-MATRIX-0",
  "selected_slice": "PB-MATRIX-0-B",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS261.md",
  "allowed_package": "packages/adeu_benchmarking",
  "selected_record_shapes": [
    "programbench_local_case_matrix_result_projection@1",
    "programbench_local_case_matrix_observation_ledger@1",
    "programbench_local_case_matrix_coverage_register@1",
    "programbench_local_case_matrix_contamination_register@1"
  ],
  "local_gate": "make arc-start-check ARC=261",
  "non_authority_summary": "No official ProgramBench participation, hidden-test handling, benchmark truth, benchmark scoring, model ranking, leaderboard standing, batch execution, result summary, second retry authority, retry-chain authority, or future-family selection is authorized by this lock."
}
```

## Verification Plan

Before implementation starts:

```text
make arc-start-check ARC=261
```

For the implementation PR:

```text
.venv/bin/python -m pytest packages/adeu_benchmarking/tests/test_programbench_cleanroom_matrix_pb_matrix_0b.py -q
make check
```
