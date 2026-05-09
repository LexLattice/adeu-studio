# LOCKED_CONTINUATION_vNEXT_PLUS264

## Status

Bounded starter lock draft for `PB-CASE-EXPANSION-0-B` (local case
blueprint, cleanroom evidence pack, probe contract, oracle boundary, and
contamination screen).

This file remains a starter lock draft until the associated starter-bundle
gate is accepted and the bundle is intentionally committed as the operative
`PB-CASE-EXPANSION-0-B` implementation lock.

## Authority Layer

lock

## Family / Slice

- family: `PB-CASE-EXPANSION-0`
- slice: `PB-CASE-EXPANSION-0-B`
- branch-local execution target: `arc/pb-case-expansion-0-b`

## Purpose

Freeze the bounded `PB-CASE-EXPANSION-0-B` starter slice so the repo can turn
released A-eligible local case ideas into local cleanroom case blueprints,
evidence packs, probe contracts, oracle boundaries, and contamination screens
without registering case lineages, running cases, executing probes, including
cases in a matrix, scoring benchmarks, comparing baselines, ranking models, or
selecting a future family.

`vNext+264` authorizes docs plus the next implementation path over the
existing repo-owned `adeu_benchmarking` package. It does not authorize local
case execution, probe execution, batch command execution, candidate
materialization, local trial dispatch, local case lineage registration,
readiness summary, matrix candidate handoff, family closeout, official
ProgramBench participation, official task execution, official runner
integration, official evaluator integration, hidden-test handling,
hidden-test inference, hidden-test equivalence, original source lookup,
decompilation, internet lookup inside ProgramBench tasks, external repository
lookup, benchmark submission, benchmark scoring, benchmark truth, pass rate,
solve rate, success rate, baseline-relative result claims, model ranking,
leaderboard standing, generated official submissions, official submission
authority, second retry authority, retry-chain authority, unbounded command
execution, runtime transition, product authorization, graph-memory authority,
release authority, recursive policy amendment, or future-family selection.

Controlling invariant:

```text
PB-CASE-EXPANSION-0-B may blueprint A-eligible local cleanroom case ideas and
record the local evidence/probe/oracle/contamination boundary for later
lineage registration review, but it may not execute, register, score, rank,
or claim benchmark truth.
```

Evidence-binding invariant:

```text
Behavior obligations are not task truth by label. Each obligation must bind
to source witness rows, support kind, support strength, unresolved
counterevidence posture, and limitation notes.
```

Probe/oracle invariant:

```text
Probe contracts are argv-shaped local plans only. Local oracle boundaries are
blueprint-local expectations, not official ProgramBench truth, hidden-test
equivalence, or evaluator equivalence.
```

## Instantiated Here

- `PB-CASE-EXPANSION-0-B` instantiates the second local cleanroom
  case-expansion seam:
  - existing repo-owned package only:
    - `adeu_benchmarking`
  - consumed released `PB-CASE-EXPANSION-0-A` basis:
    - `docs/LOCKED_CONTINUATION_vNEXT_PLUS263.md`
    - `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS263.md`
    - `docs/ASSESSMENT_vNEXT_PLUS263_EDGES.md`
    - `apps/api/fixtures/benchmarking/vnext_plus263/programbench_local_case_expansion_request_v263_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus263/programbench_local_case_source_pool_manifest_v263_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus263/programbench_local_case_expansion_eligibility_review_v263_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus263/programbench_local_case_expansion_control_contract_v263_reference.json`
    - `apps/api/fixtures/benchmarking/vnext_plus263/programbench_local_case_expansion_non_authority_guardrail_v263_reference.json`
  - inherited released cleanroom basis:
    - `PB-MATRIX-0` family closeout
    - `PB-TRIAL-0` family closeout
    - `PB-RETRY-0` family closeout
    - `PB-ATTEMPT-0`, `PB-RECON-0`, `PB-ADAPTER-0`, and `PB-PY-0`
      family closeouts
  - consumed planning/support inputs:
    - `docs/DRAFT_NEXT_ARC_OPTIONS_v83.md`
    - `docs/ARCHITECTURE_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_FAMILY_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_PB_CASE_EXPANSION_0_IMPLEMENTATION_MAPPING_v0.md`
    - `docs/DRAFT_ADEU_PROGRAMBENCH_LOCAL_CLEANROOM_CASE_EXPANSION_PB_CASE_EXPANSION_0B_IMPLEMENTATION_MAPPING_v0.md`
  - emitted second-slice record shapes:
    - `programbench_local_case_blueprint@1`
    - `programbench_local_case_cleanroom_evidence_pack@1`
    - `programbench_local_case_probe_contract@1`
    - `programbench_local_case_oracle_boundary@1`
    - `programbench_local_case_contamination_screen@1`

## Required Starter Vocabulary

Minimum `programbench_local_case_blueprint@1` fields:

- `case_blueprint_ref`
- `case_expansion_ref`
- `candidate_case_idea_ref`
- `source_pool_manifest_ref`
- `expansion_eligibility_review_ref`
- `expansion_control_contract_ref`
- `expansion_guardrail_ref`
- `cleanroom_evidence_pack_ref`
- `probe_contract_ref`
- `oracle_boundary_ref`
- `contamination_screen_ref`
- `case_kind`
- `case_blueprint_status`
- `expected_submission_shape`
- `expected_input_artifact_refs`
- `expected_output_artifact_refs`
- `filesystem_side_effect_expectation_refs`
- `source_pool_subset_hash`
- `blueprint_hash`
- `execution_deferred_posture`
- `matrix_inclusion_deferred_posture`
- `benchmark_score_posture`
- `baseline_comparison_posture`
- `model_ranking_posture`
- `limitation_note`

Minimum `programbench_local_case_cleanroom_evidence_pack@1` fields:

- `cleanroom_evidence_pack_ref`
- `case_expansion_ref`
- `case_blueprint_ref`
- `source_witness_rows`
- `behavior_obligation_rows`
- `behavior_obligation_basis_rows`
- `io_observation_rows`
- `artifact_obligation_rows`
- `source_identity_hashes`
- `evidence_pack_hash`
- `forbidden_source_exclusion_refs`
- `support_only_context_refs`
- `limitation_note`

Minimum `behavior_obligation_basis_row` fields:

- `obligation_ref`
- `source_witness_refs`
- `support_kind`
- `support_strength`
- `unresolved_counterevidence_refs`
- `limitation_note`

Minimum `programbench_local_case_probe_contract@1` fields:

- `probe_contract_ref`
- `case_expansion_ref`
- `case_blueprint_ref`
- `probe_template_rows`
- `probe_command_shape_rows`
- `positive_probe_requirement_rows`
- `negative_probe_requirement_rows`
- `stdout_stderr_expectation_rows`
- `exit_code_expectation_rows`
- `filesystem_side_effect_expectation_rows`
- `command_execution_posture`
- `probe_execution_deferred_posture`
- `limitation_note`

Minimum `probe_command_shape_row` fields:

- `probe_ref`
- `argv_template`
- `stdin_fixture_ref`
- `expected_stdout_ref`
- `expected_stderr_ref`
- `expected_exit_code_ref`
- `filesystem_expectation_refs`
- `execution_deferred_posture`

Minimum `programbench_local_case_oracle_boundary@1` fields:

- `oracle_boundary_ref`
- `case_expansion_ref`
- `case_blueprint_ref`
- `local_oracle_basis_rows`
- `expected_behavior_boundary_rows`
- `unknown_behavior_boundary_rows`
- `out_of_scope_behavior_rows`
- `oracle_boundary_scope_hash`
- `unknown_behavior_policy`
- `out_of_scope_behavior_policy`
- `local_oracle_not_task_truth_posture`
- `hidden_test_equivalence_posture`
- `official_evaluator_equivalence_posture`
- `benchmark_truth_posture`
- `limitation_note`

Required oracle posture:

- `local_oracle_not_task_truth_posture =
  local_blueprint_oracle_only_not_official_programbench_truth`

Minimum `programbench_local_case_contamination_screen@1` fields:

- `contamination_screen_ref`
- `case_expansion_ref`
- `case_blueprint_ref`
- `screened_source_refs`
- `contamination_status`
- `contamination_rows`
- `forbidden_source_exposure_refs`
- `hidden_evidence_exposure_refs`
- `official_evaluator_exposure_refs`
- `decompilation_or_source_lookup_exposure_refs`
- `redaction_policy`
- `screen_verdict`
- `limitation_note`

## Required Deliverables / Exit Conditions

- typed model and schema exports for:
  - `programbench_local_case_blueprint@1`
  - `programbench_local_case_cleanroom_evidence_pack@1`
  - `programbench_local_case_probe_contract@1`
  - `programbench_local_case_oracle_boundary@1`
  - `programbench_local_case_contamination_screen@1`
- mirrored `spec/` schema exports for the same shapes;
- validators requiring released `PB-CASE-EXPANSION-0-A` refs before B rows
  validate;
- validators requiring one `case_expansion_ref` and one `case_blueprint_ref`
  across a B bundle;
- validators rejecting blueprints for A-blocked candidate case ideas;
- validators requiring blueprint source refs to be a subset of A-allowed
  source refs;
- validators requiring source witness rows with concrete refs and identity
  hashes;
- validators requiring behavior obligation basis rows for every behavior
  obligation, with support kind, support strength, unresolved
  counterevidence refs, and limitation notes;
- validators rejecting hidden/forbidden names, paths, excerpts, test names,
  semantic summaries, hidden artifact identifiers, original-source clues, and
  derived-summary laundering in evidence, oracle, and contamination rows;
- validators requiring probe contracts to be plan-only, argv-shaped, and
  non-executing;
- validators rejecting raw shell strings or command execution authority in
  probe contracts;
- validators requiring local oracle boundaries to reject hidden-test
  equivalence, official evaluator equivalence, and benchmark truth;
- validators requiring contamination screens to fail closed on hidden,
  forbidden, postmortem-only, source-derived, decompilation-derived,
  internet-derived, external-repo-derived, or official-evaluator-derived
  evidence;
- validators rejecting `PB-CASE-EXPANSION-0-C` artifact shapes in B fixtures;
- focused tests for `PB-CASE-EXPANSION-0-B` plus schema export coverage;
- reference and reject fixtures under
  `apps/api/fixtures/benchmarking/vnext_plus264/`.

## Explicit Non-Outputs

`PB-CASE-EXPANSION-0-B` must not output:

- local case lineage registrations;
- readiness summaries;
- matrix candidate handoffs;
- family closeout alignment;
- local trial dockets or executions;
- probe execution records;
- command execution or batch execution records;
- candidate materialization records;
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
  "target_arc": "vNext+264",
  "target_path": "PB-CASE-EXPANSION-0-B",
  "authority_layer": "lock",
  "selected_family": "PB-CASE-EXPANSION-0",
  "selected_slice": "PB-CASE-EXPANSION-0-B",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS264.md",
  "allowed_package": "packages/adeu_benchmarking",
  "selected_record_shapes": [
    "programbench_local_case_blueprint@1",
    "programbench_local_case_cleanroom_evidence_pack@1",
    "programbench_local_case_probe_contract@1",
    "programbench_local_case_oracle_boundary@1",
    "programbench_local_case_contamination_screen@1"
  ],
  "local_gate": "make arc-start-check ARC=264",
  "non_authority_summary": "No local case execution, probe execution, batch execution, case lineage registration, readiness summary, matrix inclusion, benchmark score, baseline comparison, model ranking, official ProgramBench participation, hidden-test handling, or future-family selection is authorized by this lock."
}
```

## Verification Plan

Before implementation starts:

```text
make arc-start-check ARC=264
```

For the implementation PR:

```text
.venv/bin/python -m pytest packages/adeu_benchmarking/tests/test_programbench_cleanroom_case_expansion_pb_case_expansion_0b.py -q
make check
```
