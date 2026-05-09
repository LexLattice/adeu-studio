# Draft ADEU ProgramBench Local Cleanroom Case Expansion PB-CASE-EXPANSION-0-B Implementation Mapping v0

Status: support / implementation mapping record for planned
`PB-CASE-EXPANSION-0-B`.

Authority layer: support.

This note maps the likely implementation for `PB-CASE-EXPANSION-0-B`. It
does not authorize implementation by itself and does not replace a future
`vNext+264` lock, stop-gate decision, or edge assessment.

## Slice Intent

`PB-CASE-EXPANSION-0-B` should turn A-eligible candidate case ideas into
bounded local cleanroom case blueprints and evidence contracts. It should not
execute those blueprints, register them as ready lineages, include them in a
matrix, or score them.

The slice should answer:

```text
Given released A source and eligibility rows, what local cleanroom case
blueprint, evidence pack, probe contract, oracle boundary, and contamination
screen are ready for later lineage registration review?
```

It must not answer:

```text
Can this case run?
Did the case pass?
How does this compare to a baseline?
Should this be included in an official or local matrix now?
```

## Selected Surfaces

Likely schema / model surfaces:

- `programbench_local_case_blueprint@1`
- `programbench_local_case_cleanroom_evidence_pack@1`
- `programbench_local_case_probe_contract@1`
- `programbench_local_case_oracle_boundary@1`
- `programbench_local_case_contamination_screen@1`

Likely source files for a future implementation:

- `packages/adeu_benchmarking/src/adeu_benchmarking/programbench_cleanroom_case_expansion.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- `packages/adeu_benchmarking/tests/test_programbench_cleanroom_case_expansion_pb_case_expansion_0b.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus264/`

## Consumed Lineage

`PB-CASE-EXPANSION-0-B` should require released `PB-CASE-EXPANSION-0-A` rows:

- expansion request;
- source pool manifest;
- eligibility review;
- control contract;
- non-authority guardrail.

B may consume earlier ProgramBench family closeouts only as inherited
cleanroom law. It must not bypass A by selecting sources or candidate case
ideas directly.

## Field-Level Expectations

`programbench_local_case_blueprint@1` should include:

- `case_blueprint_ref`
- `case_expansion_ref`
- `candidate_case_idea_ref`
- `source_pool_manifest_ref`
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
- `execution_deferred_posture`
- `matrix_inclusion_deferred_posture`
- `benchmark_score_posture`
- `limitation_note`

`programbench_local_case_cleanroom_evidence_pack@1` should include:

- `cleanroom_evidence_pack_ref`
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

`programbench_local_case_probe_contract@1` should include:

- `probe_contract_ref`
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

`programbench_local_case_oracle_boundary@1` should include:

- `oracle_boundary_ref`
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

`programbench_local_case_contamination_screen@1` should include:

- `contamination_screen_ref`
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

## Validation Expectations

The future implementation should validate:

- every B bundle resolves to one `case_expansion_ref` and one
  `case_blueprint_ref`;
- B requires released A refs and cannot blueprint an A-blocked candidate case
  idea;
- blueprint source refs must be a subset of A-allowed source refs;
- blueprint rows cannot include command execution, local trial dispatch,
  batch execution, scoring, baseline comparison, official participation, or
  future-family authority;
- evidence packs require source witness rows with concrete refs and hashes;
- behavior obligations require basis rows that bind each obligation to source
  witnesses, support strength, and unresolved counterevidence posture;
- evidence packs cannot include hidden/forbidden names, paths, excerpts, test
  names, semantic summaries, hidden artifact identifiers, or original-source
  clues;
- probe contracts are plan-only and must not contain raw shell strings or
  command execution authority;
- planned probe command shapes must be argv-based templates with execution
  deferred;
- oracle boundaries must separate local oracle expectations from hidden-test
  equivalence, official evaluator equivalence, and benchmark truth;
- oracle boundaries must carry `local_oracle_not_task_truth_posture =
  local_blueprint_oracle_only_not_official_programbench_truth`;
- contamination screens fail closed if hidden, forbidden, postmortem-only,
  source-derived, decompilation-derived, internet-derived,
  external-repo-derived, or official-evaluator-derived evidence is present;
- B rejects C artifact kinds.

## Reference Fixtures

Future B fixtures should include:

- one blueprint from an A-eligible candidate case idea;
- one cleanroom evidence pack with source witness rows and identity hashes;
- one probe contract with positive and negative local probe requirements;
- one oracle boundary with local-only expectations;
- one clean contamination screen.

Reject fixtures should include:

- blueprint from an A-blocked candidate;
- evidence pack containing forbidden source name or excerpt;
- behavior obligation without source witness basis;
- probe contract granting command execution;
- probe contract using a raw shell string instead of argv template;
- oracle boundary claiming hidden-test equivalence;
- oracle boundary claiming local oracle as official task truth;
- contamination screen marked clean despite official evaluator exposure;
- C artifact shape present in B fixture.
