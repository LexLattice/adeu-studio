# Locked Continuation vNext+138

Status: `V46-C` implementation contract.

## V138 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v46c_procedural_depth_perturbation_contract@1",
  "target_arc": "vNext+138",
  "target_path": "V46-C",
  "target_scope": "bounded_repo_owned_procedural_depth_perturbation_and_non_regression_widening_over_released_v46a_v46b_stack_with_one_small_deterministic_perturbation_bundle_prior_to_cross_subject_or_consumer_widening",
  "implementation_packages": [
    "adeu_benchmarking"
  ],
  "governing_released_stack": "V46A_benchmark_substrate_and_V46B_procedural_depth_baseline_on_main",
  "selected_owner_surface": "packages/adeu_benchmarking",
  "selected_schema_ids": [
    "adeu_procedural_depth_perturbation_case@1",
    "adeu_procedural_depth_failure_topology@1",
    "adeu_procedural_depth_non_regression_report@1",
    "adeu_procedural_depth_benchmark_validation_report@1"
  ],
  "consumed_released_schema_ids": [
    "adeu_benchmark_family_spec@1",
    "adeu_benchmark_projection_spec@1",
    "adeu_benchmark_execution_context@1",
    "adeu_benchmark_validation_report@1",
    "adeu_procedural_depth_instance@1",
    "adeu_procedural_depth_gold_trace@1",
    "adeu_procedural_depth_run_trace@1",
    "adeu_procedural_depth_metrics@1",
    "adeu_procedural_depth_diagnostic_report@1"
  ],
  "starter_perturbation_bundle_mode": "one_small_deterministic_bundle_over_released_hierarchical_3x3_baseline_only",
  "released_v46b_run_metrics_and_diagnostic_contracts_reused_directly": true,
  "operational_perturbation_overlay_required": true,
  "starter_perturbation_kind_vocabulary_frozen": true,
  "starter_replay_count_frozen": true,
  "starter_non_regression_thresholds_frozen": true,
  "per_case_per_replay_aggregation_required": true,
  "released_v46b_dominant_family_vocabulary_reused_exactly": true,
  "released_v46b_terminal_trace_status_vocabulary_reused_exactly": true,
  "starter_evaluation_context_frozen_to_deterministic_fixed_context": true,
  "failure_topology_aggregation_required": true,
  "cross_subject_comparison_deferred_to_v46d": true,
  "downstream_consumer_seam_deferred_to_v46e": true,
  "root_spec_mirror_required": true,
  "closeout_artifacts_required": [
    "artifacts/quality_dashboard_v138_closeout.json",
    "artifacts/stop_gate/metrics_v138_closeout.json",
    "artifacts/stop_gate/report_v138_closeout.md"
  ]
}
```

## Objective

Release the bounded `V46-C` Procedural Depth perturbation and non-regression seam by
keeping `packages/adeu_benchmarking` as the only active implementation package while
consuming the released `V46-A` substrate and the released `V46-B` baseline
procedural-depth stack as-is.

This slice should release exactly four new repo-owned contracts:

- `adeu_procedural_depth_perturbation_case@1`
- `adeu_procedural_depth_failure_topology@1`
- `adeu_procedural_depth_non_regression_report@1`
- `adeu_procedural_depth_benchmark_validation_report@1`

This slice is the first perturbation and repeated-run widening lane. It is not yet:

- a benchmark-library widening lane;
- a cross-subject comparison lane;
- a ranking or leaderboard lane;
- a downstream routing/model/role/training consumer lane.

## Required Deliverables

The first `V46-C` release should add exactly these live implementation surfaces:

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
  - `packages/adeu_benchmarking/tests/fixtures/v46c/`

This slice should not add:

- new benchmark-substrate forks;
- cross-subject comparison or ranking artifacts;
- broader projection-library artifacts outside Procedural Depth Fidelity;
- API or web consumer surfaces;
- downstream operational promotion semantics over benchmark outputs.

## Frozen Implementation Decisions

1. Ownership and relation to released `V46-A` / `V46-B`

- `packages/adeu_benchmarking` remains the only active implementation package for
  `V46-C`.
- released `V46-A` family/projection/execution-context artifacts remain the only
  required family-level upstream substrate.
- released `V46-B` instance, gold trace, run trace, metrics, and diagnostic report
  remain the only required baseline projection stack.
- `V46-C` may widen perturbation and non-regression semantics only:
  - it may not fork the released `V46-B` baseline scorer or baseline schema ids
  - it may not reopen the released `V46-A` substrate doctrine
  - it may not widen into `V46-D` cross-subject comparison or `V46-E` consumer seams

2. Perturbation-case posture

- admit exactly one new perturbation-case contract:
  - `adeu_procedural_depth_perturbation_case@1`
- each perturbation-case artifact must carry:
  - `schema`
  - `procedural_depth_perturbation_case_id`
  - `baseline_instance_ref`
  - `perturbation_kind`
  - `perturbation_label`
  - ordered `perturbation_overlay_events`
  - optional `output_summary_override`
  - `expected_dominant_failure_family`
  - `expected_terminal_trace_status`
  - `notes`
- the starter slice must remain exactly one small perturbation bundle over the
  released `hierarchical_3x3` baseline only.
- `perturbation_kind` in the starter slice must remain exactly:
  - `branch_shift`
  - `delayed_constraint`
  - `paraphrase_preserving`
- each perturbation case must remain operational rather than label-only:
  - `perturbation_overlay_events` must define the bounded transformed observed event
    sequence that will be materialized into repeated starter run traces
  - `output_summary_override` may carry the bounded text-level paraphrase surface when
    selected
- the perturbation case must not embed a second instance or second gold-trace family:
  - released `V46-B` baseline refs remain authoritative
- `expected_dominant_failure_family` must reuse exactly the released `V46-B`
  dominant-family vocabulary:
  - `clean_success`
  - `horizontal_plan_spine`
  - `vertical_active_step_compilation`
  - `reintegration`
  - `mixed`
- `clean_success` remains the only starter non-failure sentinel in that reused field.
- `expected_terminal_trace_status` must reuse exactly the released `V46-B`
  terminal-status vocabulary:
  - `completed_clean`
  - `completed_with_structural_break`

3. Replay and non-regression posture

- perturbation cases in the starter slice must be evaluated by replaying them through
  the released `adeu_procedural_depth_run_trace@1`,
  `adeu_procedural_depth_metrics@1`, and
  `adeu_procedural_depth_diagnostic_report@1` contracts only.
- the starter replay count must remain exactly:
  - `3`
- the starter execution-context posture must remain exactly:
  - `deterministic_fixed_context`
- starter non-regression posture must remain exact and bounded:
  - `regression_detected = false` only when all three replays for one perturbation
    case match exactly on:
    - materialized run-trace id
    - materialized metrics id
    - materialized diagnostic-report id
    - observed dominant failure family
    - observed terminal trace status
  - `regression_detected = true` when any one of those exact replay subjects drifts
    across the three starter replays for one perturbation case
  - no stochastic tolerance, confidence interval, or variance-floor doctrine is
    selected in the starter lane

4. Failure-topology posture

- admit exactly one new failure-topology contract:
  - `adeu_procedural_depth_failure_topology@1`
- each failure-topology artifact must carry:
  - `schema`
  - `procedural_depth_failure_topology_id`
  - ordered `evaluated_cases`
  - `topology_summary`
  - `notes`
- each `evaluated_cases` entry must carry:
  - `perturbation_case_ref`
  - `observed_dominant_failure_family`
  - ordered `supporting_replay_refs`
- each `supporting_replay_refs` entry must carry:
  - `replay_index`
  - `run_trace_ref`
- the starter failure-topology artifact remains an aggregation over the bounded
  perturbation bundle only:
  - no cross-subject aggregation
  - no benchmark-library-wide topology

5. Non-regression-report posture

- admit exactly one new non-regression contract:
  - `adeu_procedural_depth_non_regression_report@1`
- each non-regression artifact must carry:
  - `schema`
  - `procedural_depth_non_regression_report_id`
  - `baseline_instance_ref`
  - `replay_count`
  - `regression_detected`
  - ordered `evaluated_cases`
  - `report_summary`
  - `notes`
- each `evaluated_cases` entry must carry:
  - `perturbation_case_ref`
  - `replay_indexes`
  - `regression_detected`
  - ordered `supporting_metric_refs`
- each `supporting_metric_refs` entry must carry:
  - `replay_index`
  - `metric_ref`
- `regression_detected` in the starter slice must remain exact and bounded:
  - `false` when all repeated replays stay deterministic under the frozen starter law
  - `true` when deterministic replay or starter thresholds are violated

6. Benchmark-validation-report posture

- admit exactly one new benchmark-validation contract:
  - `adeu_procedural_depth_benchmark_validation_report@1`
- each benchmark-validation artifact must carry:
  - `schema`
  - `procedural_depth_benchmark_validation_report_id`
  - `replay_count`
  - `deterministic_replay_confirmed`
  - ordered `validation_case_results`
  - ordered `limitations`
- each `validation_case_results` entry must carry:
  - `perturbation_case_ref`
  - `expected_dominant_failure_family`
  - `observed_dominant_failure_family`
  - `expected_terminal_trace_status`
  - `observed_terminal_trace_status`
  - `deterministic_replay_confirmed`
  - ordered `replay_results`
- each `replay_results` entry must carry:
  - `replay_index`
  - `run_trace_ref`
  - `metric_ref`
  - `diagnostic_report_ref`
- the starter validation lane remains bundle-scoped and deterministic only:
  - no cross-subject confidence claims
  - no promotion semantics

## Bounded Starter Vocabularies

The first `V46-C` release should freeze:

- `evaluation_context_posture`:
  - `deterministic_fixed_context`
- `perturbation_kind`:
  - `branch_shift`
  - `delayed_constraint`
  - `paraphrase_preserving`
- `expected_terminal_trace_status`:
  - `completed_clean`
  - `completed_with_structural_break`
- `dominant_failure_family`:
  - `clean_success`
  - `horizontal_plan_spine`
  - `vertical_active_step_compilation`
  - `reintegration`
  - `mixed`
- `regression_detected`:
  - `true`
  - `false`
- `deterministic_replay_confirmed`:
  - `true`
  - `false`

## Selected Schema Anchors

The first `V46-C` release should freeze at least these anchors:

- `adeu_procedural_depth_perturbation_case@1`:
  - `schema`
  - `procedural_depth_perturbation_case_id`
  - `baseline_instance_ref`
  - `perturbation_kind`
  - `perturbation_label`
  - `perturbation_overlay_events`
  - `output_summary_override`
  - `expected_dominant_failure_family`
  - `expected_terminal_trace_status`
  - `notes`
- `adeu_procedural_depth_failure_topology@1`:
  - `schema`
  - `procedural_depth_failure_topology_id`
  - `evaluated_cases`
  - `topology_summary`
  - `notes`
- `adeu_procedural_depth_non_regression_report@1`:
  - `schema`
  - `procedural_depth_non_regression_report_id`
  - `baseline_instance_ref`
  - `replay_count`
  - `regression_detected`
  - `evaluated_cases`
  - `report_summary`
  - `notes`
- `adeu_procedural_depth_benchmark_validation_report@1`:
  - `schema`
  - `procedural_depth_benchmark_validation_report_id`
  - `replay_count`
  - `deterministic_replay_confirmed`
  - `validation_case_results`
  - `limitations`

## Acceptance

Accept `V46-C` when:

- `packages/adeu_benchmarking` remains the only active implementation package for the
  slice
- four new procedural-depth perturbation/non-regression contracts export and mirror
  deterministically
- the released `V46-A` substrate and released `V46-B` baseline stack are consumed
  without reopening doctrine or forking baseline schema ids
- perturbation cases remain bounded to the starter perturbation bundle over the
  released `hierarchical_3x3` baseline
- perturbation cases are operational and materializable:
  - starter overlays define the transformed observed event sequence directly
- released `V46-B` run/metrics/diagnostic contracts are reused directly for repeated
  replay evidence
- starter evaluation remains `deterministic_fixed_context` only
- repeated-run drift is evaluated against the frozen starter exact-match subjects:
  - run-trace id
  - metrics id
  - diagnostic-report id
  - dominant failure family
  - terminal trace status
- aggregation artifacts carry per-case and per-replay structure rather than parallel
  top-level arrays
- positive fixtures exercise every frozen starter perturbation kind
- repeated replay coverage exercises both:
  - stable non-regression
  - detected regression
- no cross-subject comparison or downstream consumer surface ships in this slice
- targeted tests cover perturbation-case validation, replay aggregation, failure
  topology derivation, non-regression reporting, and benchmark-validation reporting

Do not accept `V46-C` if:

- the slice forks released `V46-B` baseline contracts instead of consuming them
- the slice widens into `V46-D` cross-subject comparison or projection-library seams
- the slice widens into `V46-E` downstream consumer promotion
- perturbation semantics are widened beyond the frozen starter bundle before the
  starter lane is accepted
