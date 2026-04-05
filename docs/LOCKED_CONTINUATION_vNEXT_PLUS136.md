# Locked Continuation vNext+136

Status: `V46-A` implementation contract.

## V136 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v46a_benchmark_substrate_contract@1",
  "target_arc": "vNext+136",
  "target_path": "V46-A",
  "target_scope": "bounded_repo_owned_benchmark_substrate_with_family_spec_projection_spec_execution_context_and_validation_report_prior_to_first_procedural_depth_projection_or_benchmark_scoring_release",
  "implementation_packages": [
    "adeu_benchmarking"
  ],
  "governing_released_stack": "V44_reasoning_assessment_family_on_main",
  "governing_stack_consumption_mode": "released_v44_family_constrains_benchmark_failure_split_and_interpretation_posture_only_no_v44_semantic_redefinition_no_v46b_projection_release",
  "selected_schema_ids": [
    "adeu_benchmark_family_spec@1",
    "adeu_benchmark_projection_spec@1",
    "adeu_benchmark_execution_context@1",
    "adeu_benchmark_validation_report@1"
  ],
  "selected_owner_surface": "packages/adeu_benchmarking",
  "consumed_released_schema_ids": [],
  "released_v44_family_constraints_required": true,
  "released_v44_artifact_ingestion_selected_here": false,
  "selected_subject_under_test_class_vocabulary": [
    "base_model",
    "prompted_model",
    "routed_runtime",
    "multi_agent_system",
    "adeu_runtime_surface"
  ],
  "selected_dominant_failure_family_vocabulary": [
    "clean_success",
    "horizontal_plan_spine",
    "vertical_active_step_compilation",
    "reintegration",
    "mixed"
  ],
  "clean_success_non_failure_sentinel_frozen": true,
  "composite_human_tool_model_subject_class_deferred_from_v46a": true,
  "starter_projection_declares_future_contract_ids_only": true,
  "procedural_depth_projection_release_deferred_to_v46b": true,
  "benchmark_instance_run_metrics_and_diagnostic_contracts_selected_here": false,
  "starter_reference_bundle_deterministic_only": true,
  "starter_validation_case_ref_posture": "fixture_case_ref_only_prior_to_released_run_trace_contract",
  "reliability_and_non_regression_policy_summaries_declarative_only": true,
  "positive_mixed_validation_case_required": true,
  "benchmark_output_epistemic_postures_explicit_required": true,
  "diagnostic_output_non_promotional_required": true,
  "root_spec_mirror_required": true,
  "closeout_artifacts_required": [
    "artifacts/quality_dashboard_v136_closeout.json",
    "artifacts/stop_gate/metrics_v136_closeout.json",
    "artifacts/stop_gate/report_v136_closeout.md"
  ]
}
```

## Objective

Release the bounded `V46-A` benchmark-substrate seam by defining one repo-owned
benchmarking package under `packages/adeu_benchmarking`, releasing exactly four
starter benchmark contracts:

- `adeu_benchmark_family_spec@1`
- `adeu_benchmark_projection_spec@1`
- `adeu_benchmark_execution_context@1`
- `adeu_benchmark_validation_report@1`

This slice is the first repo-owned benchmark substrate release. It is not yet the first
concrete procedural-depth benchmark projection release.

This slice must make explicit:

- one owner package only:
  - `packages/adeu_benchmarking`
- one bounded starter contract set only:
  - `adeu_benchmark_family_spec@1`
  - `adeu_benchmark_projection_spec@1`
  - `adeu_benchmark_execution_context@1`
  - `adeu_benchmark_validation_report@1`
- one explicit benchmark-output epistemic posture only:
  - `observed`
  - `derived_deterministically`
  - `inferred_interpretively`
  - `adjudicated`
  - `settled`
- one bounded dominant benchmark failure-family vocabulary only:
  - `clean_success`
  - `horizontal_plan_spine`
  - `vertical_active_step_compilation`
  - `reintegration`
  - `mixed`
- one deterministic reference validation bundle only:
  - fixture-case replay only
  - no released run-trace contract yet
  - no released metrics or diagnostic-report contract yet
- one deferred-consumer posture only:
  - `V46-B` may later release the first procedural-depth instance, gold trace, run
    trace, metrics, and diagnostic-report contracts
  - later consumer families may consume benchmark outputs only after those benchmark
    artifacts exist
  - `V46-A` does not mint benchmark scoring, leaderboards, routing authority, role
    assignment, or training entitlement

## Required Deliverables

The first `V46-A` release should add exactly these live implementation surfaces:

- `packages/adeu_benchmarking/pyproject.toml`
- `packages/adeu_benchmarking/src/adeu_benchmarking/models.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- package schema exports under:
  - `packages/adeu_benchmarking/schema/`
- root schema mirrors under:
  - `spec/`
- targeted tests under:
  - `packages/adeu_benchmarking/tests/`
- deterministic committed fixtures under:
  - `packages/adeu_benchmarking/tests/fixtures/v46a/`
- repo bootstrap wiring updates when required for the new package lane:
  - `Makefile`

This slice should not add:

- `procedural_depth.py` as a released live implementation surface;
- released `adeu_procedural_depth_instance@1` artifacts;
- released `adeu_procedural_depth_gold_trace@1` artifacts;
- released `adeu_procedural_depth_run_trace@1` artifacts;
- released `adeu_procedural_depth_metrics@1` artifacts;
- released `adeu_procedural_depth_diagnostic_report@1` artifacts;
- benchmark rankings, leaderboards, or one-number promotion surfaces;
- cross-subject comparison surfaces;
- routing, role-assignment, or training-promotion doctrine;
- downstream benchmark-consumer API or web surfaces.

## Frozen Implementation Decisions

1. Ownership and relation to released `V44`

- `packages/adeu_benchmarking` remains the only active implementation package for
  `V46-A`.
- released `V44-A` through `V44-E` constrain the benchmark substrate as governing
  upstream doctrinal context:
  - the benchmark family may reuse the released structural split between:
    - `plan_spine`
    - `active_step_compilation`
    - `reintegration`
  - the benchmark family may not redefine released `V44` probe, taxonomy,
    differential, widened-library, or recursive-depth semantics in `V46-A`
- starter `V46-A` does not yet ingest released `V44` artifacts as required runtime
  inputs:
  - the first slice is contract-first and reference-fixture-first
  - not live benchmark-instance scoring over released `V44` payloads
- the imported GPT Pro benchmarking bundle remains support-only shaping evidence and
  may not define live benchmark law by itself.

2. Benchmark family-spec posture

- admit exactly one released family-spec contract:
  - `adeu_benchmark_family_spec@1`
- each family-spec artifact must carry:
  - `schema`
  - `benchmark_family_spec_id`
  - `family_key`
  - `family_label`
  - `doctrinal_source_refs`
  - `capability_axes`
  - `baseline_regime_summary`
  - `perturbation_axis_posture`
  - `reliability_policy_summary`
  - `non_regression_policy_summary`
  - `subject_under_test_classes`
  - `benchmark_output_epistemic_postures`
  - `diagnostic_posture`
  - `implementation_posture`
- `subject_under_test_classes` in the first slice must remain exactly:
  - `base_model`
  - `prompted_model`
  - `routed_runtime`
  - `multi_agent_system`
  - `adeu_runtime_surface`
- composite `human_plus_tool_plus_model` subject-under-test posture remains deferred
  from the starter vocabulary
- `benchmark_output_epistemic_postures` in the first slice must remain exactly:
  - `observed`
  - `derived_deterministically`
  - `inferred_interpretively`
  - `adjudicated`
  - `settled`
- `diagnostic_posture` in the first slice must remain exactly:
  - `diagnostic_only`
- `implementation_posture` in the first slice must remain exactly:
  - `bounded_repo_owned_non_promotional`
- `reliability_policy_summary` and `non_regression_policy_summary` in the first slice
  are declaration-only substrate policy summaries:
  - they may state intended repeated-run and non-regression posture
  - they may not claim empirical confirmation before later projection lanes release
    benchmark instances, run traces, metrics, and non-regression artifacts

3. Benchmark projection-spec posture

- admit exactly one released projection-spec contract:
  - `adeu_benchmark_projection_spec@1`
- each projection-spec artifact must carry:
  - `schema`
  - `benchmark_projection_spec_id`
  - `benchmark_family_spec_ref`
  - `projection_key`
  - `projection_label`
  - `constraint_source_refs`
  - `target_capability_axes`
  - `target_subject_under_test_classes`
  - `hierarchical_trace_required`
  - `explicit_reintegration_trace_required`
  - `projection_validity_posture`
  - `interpretation_boundary_summary`
  - `declared_instance_contract_id`
  - `declared_gold_trace_contract_id`
  - `declared_run_trace_contract_id`
  - `declared_metrics_contract_id`
  - `declared_diagnostic_report_contract_id`
  - `projection_notes`
- `constraint_source_refs` must point only to released `V44` docs or released `V44`
  schema ids that justify the structural split reused by later benchmark projections
- the five `declared_*_contract_id` fields are declaration-only in `V46-A`:
  - they may name downstream `V46-B` artifact families
  - they do not release those contracts here
  - they may not be used as evidence that instance, gold-trace, run-trace, metrics, or
    diagnostic-report contracts already exist on `main`
- `hierarchical_trace_required` and `explicit_reintegration_trace_required` may be
  `true` in the starter slice for a procedural-depth-oriented projection spec, but
  they do not by themselves release hierarchical trace artifacts.

4. Benchmark execution-context posture

- admit exactly one released execution-context contract:
  - `adeu_benchmark_execution_context@1`
- each execution-context artifact must carry:
  - `schema`
  - `benchmark_execution_context_id`
  - `subject_under_test_class`
  - `subject_label`
  - `subject_version`
  - optional `prompt_wrapper_ref`
  - `tool_availability`
  - `context_budget_posture`
  - `determinism_posture`
  - `repo_snapshot_ref`
  - optional `orchestration_topology_ref`
  - `notes`
- `context_budget_posture` in the starter slice must remain exactly:
  - `fixed_context_budget_declared`
- `determinism_posture` in the starter slice may remain exactly:
  - `deterministic_fixed_context`
  - `stochastic_context`
- the deterministic committed reference bundle in `V46-A` must use:
  - `deterministic_fixed_context`
- `repo_snapshot_ref` is required and may not be synthesized from ambient current-tree
  state.

5. Benchmark validation-report posture

- admit exactly one released validation-report contract:
  - `adeu_benchmark_validation_report@1`
- each validation-report artifact must carry:
  - `schema`
  - `benchmark_validation_report_id`
  - `benchmark_projection_spec_ref`
  - `validation_label`
  - `validation_scope`
  - `scorer_determinism_posture`
  - ordered `validation_case_results`
  - `all_expected_diagnostics_matched`
  - `benchmark_limitations`
- each `validation_case_result` in the starter slice must carry:
  - `validation_case_result_id`
  - `case_label`
  - `case_ref`
  - `expected_dominant_failure_family`
  - `observed_dominant_failure_family`
  - `match`
- `validation_scope` in the starter slice must remain exactly:
  - `tiny_reference_fixture_bundle`
- `scorer_determinism_posture` in the starter slice must remain exactly:
  - `deterministic_fixture_replay_confirmed`
- `case_ref` in the starter slice must remain fixture-scoped only:
  - it may point to deterministic committed reference cases under `tests/fixtures/v46a`
  - it may not claim a released benchmark run-trace contract before `V46-B`
- dominant failure-family vocabulary in the first slice must remain exactly:
  - `clean_success`
  - `horizontal_plan_spine`
  - `vertical_active_step_compilation`
  - `reintegration`
  - `mixed`
- within that starter vocabulary, `clean_success` is the only non-failure sentinel:
  - it remains lawful in the same dominant-family field for deterministic validation
    replay
  - it must not be overread as a normalized failure class
- benchmark validation in `V46-A` is benchmark-self-validation only:
  - scorer replay
  - bounded fixture adequacy
  - benchmark limitations
  - no ranking or benchmark-score release

6. Ordering, hashing, and export law

- ids for all four released contracts must be deterministic and canonical
- `subject_under_test_classes`, `benchmark_output_epistemic_postures`,
  `target_capability_axes`, `target_subject_under_test_classes`, `tool_availability`,
  and `benchmark_limitations` must be ordered deterministically
- `validation_case_results` ordering must follow:
  - `case_label` ascending lexicographic order
- `all_expected_diagnostics_matched` must equal the conjunction of ordered case-result
  `match` values
- authoritative package-local schemas and root `spec/` mirrors must export
  deterministically from the same released models
- starter root `spec/` mirrors are required and may not be omitted in `V46-A`.

7. Fixture posture

- commit only deterministic local fixtures
- include at least:
  - one reference benchmark family-spec fixture
  - one reference benchmark projection-spec fixture
  - one reference benchmark execution-context fixture
  - one reference benchmark validation-report fixture
  - one compact `V46-A` validation-case matrix fixture showing:
    - `case_ref`
    - expected dominant failure family
    - observed dominant failure family
    - `match`
  - positive validation-case coverage for at least:
    - `clean_success`
    - `horizontal_plan_spine`
    - `vertical_active_step_compilation`
    - `reintegration`
    - `mixed`
  - one reject fixture for a projection spec with missing declared downstream contract
    ids
  - one reject fixture for a validation report with unsupported dominant failure-family
    vocabulary
- keep the reference bundle deterministic and fixture-scoped only:
  - no released procedural-depth instance or run-trace fixture is selected here.

## Bounded Starter Vocabularies

The first `V46-A` release should freeze:

- `subject_under_test_class`:
  - `base_model`
  - `prompted_model`
  - `routed_runtime`
  - `multi_agent_system`
  - `adeu_runtime_surface`
- `benchmark_output_epistemic_posture`:
  - `observed`
  - `derived_deterministically`
  - `inferred_interpretively`
  - `adjudicated`
  - `settled`
- `diagnostic_posture`:
  - `diagnostic_only`
- `implementation_posture`:
  - `bounded_repo_owned_non_promotional`
- `context_budget_posture`:
  - `fixed_context_budget_declared`
- `determinism_posture`:
  - `deterministic_fixed_context`
  - `stochastic_context`
- `validation_scope`:
  - `tiny_reference_fixture_bundle`
- `scorer_determinism_posture`:
  - `deterministic_fixture_replay_confirmed`
- `dominant_failure_family`:
  - `clean_success`
  - `horizontal_plan_spine`
  - `vertical_active_step_compilation`
  - `reintegration`
  - `mixed`

## Selected Schema Anchors

The first `V46-A` release should freeze at least these anchors:

- `adeu_benchmark_family_spec@1`:
  - `schema`
  - `benchmark_family_spec_id`
  - `family_key`
  - `family_label`
  - `doctrinal_source_refs`
  - `capability_axes`
  - `baseline_regime_summary`
  - `perturbation_axis_posture`
  - `reliability_policy_summary`
  - `non_regression_policy_summary`
  - `subject_under_test_classes`
  - `benchmark_output_epistemic_postures`
  - `diagnostic_posture`
  - `implementation_posture`
- `adeu_benchmark_projection_spec@1`:
  - `schema`
  - `benchmark_projection_spec_id`
  - `benchmark_family_spec_ref`
  - `projection_key`
  - `projection_label`
  - `constraint_source_refs`
  - `target_capability_axes`
  - `target_subject_under_test_classes`
  - `hierarchical_trace_required`
  - `explicit_reintegration_trace_required`
  - `projection_validity_posture`
  - `interpretation_boundary_summary`
  - `declared_instance_contract_id`
  - `declared_gold_trace_contract_id`
  - `declared_run_trace_contract_id`
  - `declared_metrics_contract_id`
  - `declared_diagnostic_report_contract_id`
  - `projection_notes`
- `adeu_benchmark_execution_context@1`:
  - `schema`
  - `benchmark_execution_context_id`
  - `subject_under_test_class`
  - `subject_label`
  - `subject_version`
  - `prompt_wrapper_ref`
  - `tool_availability`
  - `context_budget_posture`
  - `determinism_posture`
  - `repo_snapshot_ref`
  - `orchestration_topology_ref`
  - `notes`
- `adeu_benchmark_validation_report@1`:
  - `schema`
  - `benchmark_validation_report_id`
  - `benchmark_projection_spec_ref`
  - `validation_label`
  - `validation_scope`
  - `scorer_determinism_posture`
  - `validation_case_results`
  - `all_expected_diagnostics_matched`
  - `benchmark_limitations`

## Acceptance

Accept `V46-A` when:

- `packages/adeu_benchmarking` is the only active implementation package for the slice
- four released starter contracts export and mirror deterministically:
  - `adeu_benchmark_family_spec@1`
  - `adeu_benchmark_projection_spec@1`
  - `adeu_benchmark_execution_context@1`
  - `adeu_benchmark_validation_report@1`
- released `V44` remains a constraining upstream doctrinal source only and is not
  silently redefined inside benchmark substrate artifacts
- benchmark family and projection specs make benchmark purpose, capability axes,
  reliability posture, and interpretation boundaries explicit without promoting
  benchmark outputs into operational authority
- projection specs declare downstream procedural-depth contract ids explicitly without
  claiming those contracts already ship in `V46-A`
- execution-context artifacts require explicit subject identity, determinism posture,
  and repo snapshot identity
- validation reports remain deterministic, fixture-scoped, and benchmark-self-validating
- positive validation coverage exercises at least:
  - `clean_success`
  - `horizontal_plan_spine`
  - `vertical_active_step_compilation`
  - `reintegration`
- no released procedural-depth instance, gold-trace, run-trace, metrics, or
  diagnostic-report contracts appear in the `V46-A` package lane
- targeted tests cover deterministic ids, canonical ordering, schema export replay,
  validation-report derivation, and reject posture.

Do not accept `V46-A` if:

- the slice silently promotes the imported benchmark bundle into live authority
- the starter projection contract claims downstream artifact families are already
  released on `main`
- benchmark validation case refs masquerade as released run-trace contracts before
  `V46-B`
- benchmark scoring, leaderboards, rankings, routing doctrine, or training entitlement
  appear in the released package surface
- root `spec/` mirrors are claimed in docs but missing from the released package lane
- the package ships procedural-depth-specific artifacts in the `V46-A` starter slice.

## Local Gate

- run `make arc-start-check ARC=136`
