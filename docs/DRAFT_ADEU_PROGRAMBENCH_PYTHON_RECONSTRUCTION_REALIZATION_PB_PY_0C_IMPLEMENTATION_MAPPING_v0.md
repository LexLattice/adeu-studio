# Draft ADEU ProgramBench Python Reconstruction Realization PB-PY-0-C Implementation Mapping v0

Status: support / slice mapping for planned `PB-PY-0-C`.

Authority layer: support.

This note is not a starter lock. `PB-PY-0-C` should activate only after
`PB-PY-0-B` closes on `main` and a later canonical starter lock selects this
slice.

`PB-PY-0-C` should instantiate one local cleanroom fixture under the released
`PB-PY-0-A` fixture contract and compare three local reconstruction lanes. It
should not run official ProgramBench tasks, submit benchmark results, handle
hidden tests, rank models, treat local probes as hidden-test equivalence, or
select a future family.

## Selected Surfaces

- `programbench_local_cleanroom_fixture@1`
- `programbench_reconstruction_comparison_packet@1`
- `programbench_probe_equivalence_audit@1`
- `programbench_realization_family_closeout_alignment@1`

## Package Scope

Expected implementation files:

- `packages/adeu_benchmarking/src/adeu_benchmarking/cleanroom_reconstruction.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`

Expected schema files:

- `packages/adeu_benchmarking/schema/programbench_local_cleanroom_fixture.v1.json`
- `packages/adeu_benchmarking/schema/programbench_reconstruction_comparison_packet.v1.json`
- `packages/adeu_benchmarking/schema/programbench_probe_equivalence_audit.v1.json`
- `packages/adeu_benchmarking/schema/programbench_realization_family_closeout_alignment.v1.json`
- `spec/programbench_local_cleanroom_fixture.schema.json`
- `spec/programbench_reconstruction_comparison_packet.schema.json`
- `spec/programbench_probe_equivalence_audit.schema.json`
- `spec/programbench_realization_family_closeout_alignment.schema.json`

Expected tests and fixtures:

- `packages/adeu_benchmarking/tests/test_cleanroom_reconstruction_pb_py_0c.py`
- `packages/adeu_benchmarking/tests/test_benchmarking_export_schema.py`
- `apps/api/fixtures/benchmarking/vnext_plus244/programbench_local_cleanroom_fixture_v244_reference.json`
- `apps/api/fixtures/benchmarking/vnext_plus244/programbench_reconstruction_comparison_packet_v244_reference.json`
- `apps/api/fixtures/benchmarking/vnext_plus244/programbench_probe_equivalence_audit_v244_reference.json`
- `apps/api/fixtures/benchmarking/vnext_plus244/programbench_realization_family_closeout_alignment_v244_reference.json`
- `apps/api/fixtures/benchmarking/vnext_plus244/programbench_cleanroom_fixture_v244_reject_*.json`

The `vNext+244` number is a planning placeholder only. A later starter lock
must bind the actual arc number.

## Consumed Released Basis

`PB-PY-0-C` should consume released `PB-PY-0-A` and `PB-PY-0-B` rows:

- `programbench_cleanroom_reconstruction_profile@1`
- `program_odeu_concept_boundary_seed@1`
- `programbench_cleanroom_evidence_source_index@1`
- `programbench_reconstruction_non_authority_guardrail@1`
- `programbench_local_cleanroom_fixture_contract@1`
- `concept_realization_record@1`
- `python_reconstruction_realization_pack@1`
- `python_reconstruction_plan@1`
- `python_realization_witness_template@1`

No consumed row becomes official ProgramBench authority, hidden-test
inference, model-ranking authority, or benchmark truth by being consumed.

## Local Cleanroom Fixture

Minimum `programbench_local_cleanroom_fixture@1` fields:

- `fixture_ref`
- `fixture_contract_ref`
- `reference_executable_ref`
- `usage_docs_ref`
- `worker_visible_file_refs`
- `worker_hidden_file_refs`
- `allowed_probe_command_rows`
- `forbidden_source_rows`
- `fixture_origin_posture`
- `network_policy`
- `source_visibility_policy`
- `expected_submission_shape`
- `evaluation_oracle_rows`
- `local_fixture_scope_posture`
- `official_programbench_posture`
- `benchmark_truth_posture`
- `limitation_note`

Required posture:

```text
local_fixture_scope_posture = one_local_cleanroom_fixture_only
official_programbench_posture = no_official_programbench_participation_by_pb_py_0c
benchmark_truth_posture = local_fixture_research_only_not_benchmark_truth
```

Minimum `fixture_origin_posture` values:

- `synthetic_local_fixture`
- `repo_internal_fixture`
- `toy_cleanroom_fixture`
- `official_programbench_task_forbidden_in_pb_py_0c`

The fixture may include a local reference executable and local oracle rows only
if the released fixture contract authorizes them. It must not include official
ProgramBench tasks, hidden tests, original source, decompilation artifacts, or
external source repositories.

## Comparison Packet

Minimum `programbench_reconstruction_comparison_packet@1` fields:

- `comparison_packet_ref`
- `fixture_ref`
- `comparison_control_rows`
- `comparison_lane_rows`
- `profile_refs`
- `realization_pack_refs`
- `witness_template_refs`
- `local_probe_refs`
- `comparison_scope_posture`
- `comparison_contamination_status`
- `benchmark_truth_posture`
- `model_ranking_posture`
- `limitation_note`

Required lane ids:

- `base_adeu_harness`
- `adeu_plus_conceptual_profile`
- `adeu_plus_conceptual_profile_plus_python_overlay`

Required posture:

```text
comparison_scope_posture = local_fixture_research_comparison_only
comparison_contamination_status = same_condition_controls_closed
benchmark_truth_posture = not_benchmark_truth
model_ranking_posture = no_model_ranking_claimed_by_pb_py_0c
```

Minimum `comparison_control_rows` fields:

- `shared_fixture_ref`
- `shared_model_or_worker_profile_ref`
- `shared_budget_policy`
- `shared_allowed_tool_policy`
- `shared_cleanroom_policy`
- `shared_probe_budget`
- `shared_submission_shape`
- `shared_evaluation_oracle_rows`
- `lane_difference_declaration`

The intended lane delta should be only:

- `base_adeu_harness`: no conceptual profile and no Python overlay;
- `adeu_plus_conceptual_profile`: conceptual profile only;
- `adeu_plus_conceptual_profile_plus_python_overlay`: conceptual profile plus
  Python overlay.

If model, worker profile, budget, tool access, probe allowance, fixture,
submission shape, or evaluation oracle differs across lanes, the comparison
packet should mark the result contaminated or non-comparable rather than making
a clean lane-value claim.

The comparison may describe differences across lanes, but it must not produce
benchmark leaderboard claims or general model rankings.

## Probe Equivalence Audit

Minimum `programbench_probe_equivalence_audit@1` fields:

- `audit_ref`
- `fixture_ref`
- `comparison_packet_ref`
- `local_probe_rows`
- `positive_observation_rows`
- `negative_observation_rows`
- `stdout_stderr_observation_rows`
- `exit_code_observation_rows`
- `filesystem_observation_rows`
- `known_limitation_rows`
- `hidden_test_equivalence_posture`
- `benchmark_truth_posture`
- `postmortem_feedback_posture`
- `limitation_note`

Required posture:

```text
hidden_test_equivalence_posture = local_probe_pass_not_hidden_test_equivalence
benchmark_truth_posture = local_audit_not_benchmark_truth
postmortem_feedback_posture = no_hidden_test_feedback_used_for_inference
```

## Family Closeout Alignment

Minimum `programbench_realization_family_closeout_alignment@1` fields:

- `family_closeout_ref`
- `family`
- `closed_slice_refs`
- `released_profile_refs`
- `released_source_index_refs`
- `released_concept_seed_refs`
- `released_fixture_contract_refs`
- `released_realization_pack_refs`
- `released_fixture_refs`
- `released_comparison_packet_refs`
- `released_audit_refs`
- `family_alignment_posture`
- `official_programbench_posture`
- `benchmark_truth_posture`
- `future_family_selection_status`
- `limitation_note`

Required posture:

```text
family_alignment_posture = pb_py_0_closed_local_research_fixture_only
official_programbench_posture = no_official_programbench_participation_by_pb_py_0
benchmark_truth_posture = no_benchmark_truth_claimed_by_pb_py_0
future_family_selection_status = no_future_family_selected_by_pb_py_0
```

## Required Reject Fixtures

Reject fixtures should include:

- local fixture includes original source or decompilation evidence;
- official ProgramBench task marked local fixture;
- fixture origin marked `official_programbench_task_forbidden_in_pb_py_0c` while
  also marked usable as a local fixture;
- hidden test visible to worker;
- network policy allows internet lookup during inference;
- comparison packet missing same-condition controls;
- comparison packet treats changed model, budget, tool policy, probe budget,
  fixture, submission shape, or oracle as a clean lane delta;
- comparison packet ranks models;
- comparison packet claims official benchmark score;
- local probe pass marked hidden-test equivalence;
- postmortem evaluation failure used as inference evidence;
- family closeout selects official ProgramBench participation, V86, V87, V88,
  implementation-lock review, product work, graph work, release, or recursive
  policy work.

## Deferred To Later Family

- official ProgramBench participation and result governance;
- hidden evaluator feedback governance;
- broader conceptual broker implementation;
- multi-language realization overlays beyond Python;
- V86 obligation expansion / evidence contract / edge probe planning;
- V87 reviewer / auditor taskpacks;
- V88 deterministic closeout transition and remand routing.
