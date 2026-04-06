# Locked Continuation vNext+139

Status: `V46-D` implementation contract.

## V139 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v46d_cross_subject_comparison_contract@1",
  "target_arc": "vNext+139",
  "target_path": "V46-D",
  "target_scope": "bounded_repo_owned_cross_subject_comparison_first_widening_over_released_v46a_v46b_v46c_procedural_depth_stack_with_one_deterministic_subject_pair_prior_to_broader_projection_library_or_downstream_consumer_widening",
  "implementation_packages": [
    "adeu_benchmarking"
  ],
  "governing_released_stack": "V46A_benchmark_substrate_plus_V46B_procedural_depth_baseline_plus_V46C_perturbation_non_regression_on_main",
  "selected_owner_surface": "packages/adeu_benchmarking",
  "selected_schema_ids": [
    "adeu_benchmark_subject_record@1",
    "adeu_cross_subject_comparison_case@1",
    "adeu_cross_subject_comparison_report@1",
    "adeu_cross_subject_comparison_validation_report@1"
  ],
  "consumed_released_schema_ids": [
    "adeu_benchmark_family_spec@1",
    "adeu_benchmark_projection_spec@1",
    "adeu_benchmark_execution_context@1",
    "adeu_procedural_depth_instance@1",
    "adeu_procedural_depth_run_trace@1",
    "adeu_procedural_depth_metrics@1",
    "adeu_procedural_depth_diagnostic_report@1",
    "adeu_procedural_depth_non_regression_report@1",
    "adeu_procedural_depth_benchmark_validation_report@1"
  ],
  "starter_comparison_mode": "one_deterministic_subject_pair_over_released_procedural_depth_stack_only",
  "starter_subject_class_subset_frozen": true,
  "same_projection_spec_required": true,
  "subject_specific_execution_context_refs_required": true,
  "execution_context_compatibility_law_frozen": true,
  "same_baseline_instance_required": true,
  "same_perturbation_bundle_required": true,
  "explicit_perturbation_bundle_anchor_required": true,
  "comparison_surface_vocabulary_frozen": true,
  "comparison_status_vocabulary_frozen": true,
  "per_surface_comparison_mapping_frozen": true,
  "descriptive_not_ranking_required": true,
  "per_subject_evidence_refs_required": true,
  "per_case_validation_structure_required": true,
  "starter_comparison_context_frozen_to_deterministic_fixed_context": true,
  "projection_library_widening_deferred_inside_v46d": true,
  "downstream_consumer_seam_deferred_to_v46e": true,
  "root_spec_mirror_required": true,
  "closeout_artifacts_required": [
    "artifacts/quality_dashboard_v139_closeout.json",
    "artifacts/stop_gate/metrics_v139_closeout.json",
    "artifacts/stop_gate/report_v139_closeout.md"
  ]
}
```

## Objective

Release the bounded `V46-D` cross-subject comparison starter seam by keeping
`packages/adeu_benchmarking` as the only active implementation package while consuming
the released `V46-A` substrate, the released `V46-B` procedural-depth baseline stack,
and the released `V46-C` perturbation/non-regression stack as-is.

This slice should release exactly four new repo-owned contracts:

- `adeu_benchmark_subject_record@1`
- `adeu_cross_subject_comparison_case@1`
- `adeu_cross_subject_comparison_report@1`
- `adeu_cross_subject_comparison_validation_report@1`

This slice is the first cross-subject comparison lane. It is not yet:

- a broad benchmark-projection-library release;
- a leaderboard or ranking lane;
- a routing, role-fit, or training-consumer lane;
- a stochastic or variance-tolerant comparison lane.

## Required Deliverables

The first `V46-D` release should add exactly these live implementation surfaces:

- `packages/adeu_benchmarking/src/adeu_benchmarking/models.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/procedural_depth.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/export_schema.py`
- `packages/adeu_benchmarking/src/adeu_benchmarking/__init__.py`
- package schema exports under:
  - `packages/adeu_benchmarking/schema/`
- root schema mirrors under:
  - `spec/`
- targeted tests under:
  - `packages/adeu_benchmarking/tests/`
- deterministic committed fixtures under:
  - `packages/adeu_benchmarking/tests/fixtures/v46d/`

This slice should not add:

- new benchmark projections outside the released Procedural Depth projection;
- broad multi-subject comparison matrices or ranking surfaces;
- API or web consumer surfaces;
- downstream routing, role-fit, model-promotion, or training semantics;
- a second package owner surface.

## Frozen Implementation Decisions

1. Ownership and relation to released `V46-A` / `V46-B` / `V46-C`

- `packages/adeu_benchmarking` remains the only active implementation package for
  `V46-D`.
- released `V46-A` family/projection/execution-context artifacts remain the only
  required family-level upstream substrate.
- released `V46-B` run-trace, metrics, and diagnostic-report artifacts remain the only
  required baseline comparison surfaces.
- released `V46-C` non-regression and benchmark-validation artifacts remain the only
  required perturbation comparison surfaces.
- `V46-D` may widen comparison posture only:
  - it may not fork the released `V46-B` or `V46-C` schema ids
  - it may not reopen the released `V46-A` substrate doctrine
  - it may not widen into `V46-E` downstream consumer seams

2. Subject-record posture

- admit exactly one new subject-record contract:
  - `adeu_benchmark_subject_record@1`
- each subject-record artifact must carry:
  - `schema`
  - `benchmark_subject_record_id`
  - `subject_class`
  - `subject_label`
  - `subject_identity_ref`
  - `benchmark_family_spec_ref`
  - `benchmark_projection_spec_ref`
  - `benchmark_execution_context_ref`
  - `perturbation_bundle_ref`
  - ordered `perturbation_case_refs`
  - `baseline_instance_ref`
  - `baseline_run_trace_ref`
  - `baseline_metric_ref`
  - `baseline_diagnostic_report_ref`
  - `perturbation_non_regression_report_ref`
  - `perturbation_benchmark_validation_report_ref`
  - `notes`
- the starter slice must freeze `subject_class` to:
  - `base_model`
  - `prompted_model`
- each subject record in the starter slice must bind to:
  - the same released benchmark family spec
  - the same released benchmark projection spec
  - the same released procedural-depth baseline instance
  - the same released perturbation bundle
- the starter subject pair must use subject-specific execution-context refs rather than
  a single shared execution-context artifact:
  - execution-context refs may differ on:
    - `subject_under_test_class`
    - `subject_label`
    - `subject_version`
    - `prompt_wrapper_ref`
  - execution-context refs must match exactly on:
    - `repo_snapshot_ref`
    - `tool_availability`
    - `context_budget_posture`
    - `determinism_posture`
- `perturbation_bundle_ref` and ordered `perturbation_case_refs` must anchor the same
  released perturbation bundle explicitly:
  - they must match the ordered evaluated-case refs carried by both subject-side
    non-regression and validation reports

3. Comparison-case posture

- admit exactly one new comparison-case contract:
  - `adeu_cross_subject_comparison_case@1`
- each comparison-case artifact must carry:
  - `schema`
  - `cross_subject_comparison_case_id`
  - `comparison_label`
  - `left_subject_ref`
  - `right_subject_ref`
  - `benchmark_family_spec_ref`
  - `benchmark_projection_spec_ref`
  - `baseline_instance_ref`
  - ordered `required_execution_context_compatibility_fields`
  - ordered `perturbation_case_refs`
  - ordered `required_comparison_surfaces`
  - `notes`
- `required_execution_context_compatibility_fields` in the starter slice must remain
  exactly:
  - `repo_snapshot_ref`
  - `tool_availability`
  - `context_budget_posture`
  - `determinism_posture`
- `required_comparison_surfaces` in the starter slice must remain exactly:
  - `baseline_structural_fidelity`
  - `perturbation_non_regression`
  - `perturbation_validation`
- the starter slice must remain exactly one deterministic subject pair over one
  released Procedural Depth bundle only:
  - no multi-pair comparison matrix
  - no cross-projection comparison

4. Comparison-report posture

- admit exactly one new comparison-report contract:
  - `adeu_cross_subject_comparison_report@1`
- each comparison-report artifact must carry:
  - `schema`
  - `cross_subject_comparison_report_id`
  - `comparison_case_ref`
  - `comparison_status`
  - ordered `subject_summaries`
  - ordered `field_comparisons`
  - ordered `supporting_artifact_refs`
  - `comparison_summary`
  - `notes`
- `comparison_status` in the starter slice must remain exactly:
  - `comparison_ready_clean`
  - `comparison_insufficient`
  - `comparison_incompatible`
- each `subject_summaries` entry must carry:
  - `subject_record_ref`
  - `baseline_metric_ref`
  - `baseline_diagnostic_report_ref`
  - `perturbation_non_regression_report_ref`
  - `perturbation_benchmark_validation_report_ref`
- each `field_comparisons` entry must carry:
  - `comparison_surface`
  - `left_ref`
  - `right_ref`
  - `match_status`
  - `difference_summary`
- `match_status` in the starter slice must remain exactly:
  - `exact_match`
  - `different_but_comparable`
  - `insufficient_evidence`
- the starter per-surface comparison law must remain exactly:
  - `baseline_structural_fidelity` compares only the released baseline
    Procedural Depth stack:
    - `plan_spine_fidelity`
    - `active_step_compilation_fidelity`
    - `reintegration_fidelity`
    - `dominant_failure_family`
    - bound baseline `terminal_trace_status`
  - `baseline_structural_fidelity = exact_match` only when all five released fields
    match exactly across the subject pair
  - `baseline_structural_fidelity = different_but_comparable` only when context
    compatibility and shared baseline-instance law hold and at least one of those five
    released fields differs
  - `baseline_structural_fidelity = insufficient_evidence` when required baseline
    metric or run-trace refs are missing, invalid, or context compatibility fails
  - `perturbation_non_regression` compares only the released non-regression report
    fields:
    - `evaluation_context_posture`
    - `replay_count`
    - `regression_detected`
    - ordered evaluated-case tuples of
      `perturbation_case_ref + regression_detected`
  - `perturbation_non_regression = exact_match` only when those released fields and
    tuples match exactly across the subject pair
  - `perturbation_non_regression = different_but_comparable` only when the ordered
    perturbation bundle and deterministic context remain shared but one or more of
    those released fields differs
  - `perturbation_non_regression = insufficient_evidence` when required reports are
    missing, invalid, or the ordered perturbation bundle anchor does not match
  - `perturbation_validation` compares only the released validation report fields:
    - `evaluation_context_posture`
    - `replay_count`
    - `deterministic_replay_confirmed`
    - ordered validation-case tuples of
      `perturbation_case_ref + observed_dominant_failure_family + observed_terminal_trace_status + deterministic_replay_confirmed`
  - `perturbation_validation = exact_match` only when those released fields and tuples
    match exactly across the subject pair
  - `perturbation_validation = different_but_comparable` only when the ordered
    perturbation bundle and deterministic context remain shared but one or more of
    those released fields differs
  - `perturbation_validation = insufficient_evidence` when required reports are
    missing, invalid, or the ordered perturbation bundle anchor does not match
- the starter comparison report must remain descriptive rather than ranking:
  - it may summarize sameness and difference across released artifacts
  - it may not emit leaderboard position, score ordering, or promotional subject
    selection

5. Comparison-validation posture

- admit exactly one new validation-report contract:
  - `adeu_cross_subject_comparison_validation_report@1`
- each comparison-validation artifact must carry:
  - `schema`
  - `cross_subject_comparison_validation_report_id`
  - `comparison_case_ref`
  - `deterministic_comparison_confirmed`
  - `validation_status`
  - ordered `validation_results`
  - ordered `limitations`
- `validation_status` in the starter slice must remain exactly:
  - `validation_ready_clean`
  - `validation_insufficient`
  - `validation_incompatible`
- each `validation_results` entry must carry:
  - `comparison_surface`
  - `left_ref`
  - `right_ref`
  - `comparison_status`
  - `deterministic_comparison_confirmed`
- the starter comparison-validation lane remains deterministic only:
  - `deterministic_fixed_context` only
  - no stochastic tolerance
  - no confidence interval or ranking doctrine

## Bounded Starter Vocabularies

The first `V46-D` release should freeze:

- `subject_class`:
  - `base_model`
  - `prompted_model`
- `required_comparison_surfaces`:
  - `baseline_structural_fidelity`
  - `perturbation_non_regression`
  - `perturbation_validation`
- `comparison_status`:
  - `comparison_ready_clean`
  - `comparison_insufficient`
  - `comparison_incompatible`
- `match_status`:
  - `exact_match`
  - `different_but_comparable`
  - `insufficient_evidence`
- `validation_status`:
  - `validation_ready_clean`
  - `validation_insufficient`
  - `validation_incompatible`

## Fixture And Test Expectations

The committed `v46d` fixture/test set should include at minimum:

- one positive reference subject-record pair:
  - same released baseline instance
  - same released perturbation bundle
  - subject-specific but context-compatible execution contexts
  - lawful `base_model` vs `prompted_model` starter pair
- one positive comparison report fixture:
  - `comparison_ready_clean`
  - descriptive per-subject summaries
  - explicit field-level sameness and difference refs
- one positive comparison-validation fixture:
  - deterministic comparison confirmed over the released starter pair
- reject fixtures for:
  - mismatched projection spec refs
  - incompatible execution-context compatibility fields
  - mismatched perturbation bundle refs or ordered perturbation case refs
  - unsupported subject class

## Acceptance

Accept `V46-D` when:

- the four new cross-subject comparison contracts validate and export cleanly;
- committed `v46d` fixtures replay deterministically;
- the starter comparison pair stays bound to the same released Procedural Depth stack;
- comparison reports remain descriptive and non-promotional;
- comparison-validation stays deterministic and fail-closed on incompatibility;
- root `spec/` mirrors match the authoritative package schema exports;
- targeted tests cover both positive comparison fixtures and reject fixtures.

Do not accept `V46-D` if:

- the starter slice emits leaderboard, ranking, or subject-promotion semantics;
- the implementation forks released `V46-B` or `V46-C` schema ids or scorer law;
- comparison reports hide per-subject evidence behind parallel top-level arrays only;
- stochastic tolerance or confidence-floor doctrine appears in the starter lane;
- the slice widens into additional benchmark projections instead of staying
  comparison-first.

## Local Gate

- run `make arc-start-check ARC=139`
