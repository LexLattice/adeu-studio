# Locked Continuation vNext+137

Status: `V46-B` implementation contract.

## V137 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v46b_procedural_depth_projection_contract@1",
  "target_arc": "vNext+137",
  "target_path": "V46-B",
  "target_scope": "bounded_repo_owned_first_concrete_procedural_depth_fidelity_projection_over_released_v46a_benchmark_substrate_with_one_tiny_deterministic_hierarchical_reference_chain_prior_to_perturbation_non_regression_cross_subject_or_consumer_widening",
  "implementation_packages": [
    "adeu_benchmarking"
  ],
  "governing_released_stack": "V46A_benchmark_substrate_on_main",
  "governing_stack_consumption_mode": "released_benchmark_family_projection_and_execution_context_substrate_plus_first_concrete_procedural_depth_projection_only_no_perturbation_non_regression_cross_subject_or_consumer_widening",
  "selected_schema_ids": [
    "adeu_procedural_depth_instance@1",
    "adeu_procedural_depth_gold_trace@1",
    "adeu_procedural_depth_run_trace@1",
    "adeu_procedural_depth_metrics@1",
    "adeu_procedural_depth_diagnostic_report@1"
  ],
  "selected_owner_surface": "packages/adeu_benchmarking",
  "consumed_released_schema_ids": [
    "adeu_benchmark_family_spec@1",
    "adeu_benchmark_projection_spec@1",
    "adeu_benchmark_execution_context@1"
  ],
  "starter_reference_chain_mode": "tiny_hierarchical_three_by_three_reference_chain_only",
  "declared_projection_contract_ids_must_bind_exactly": true,
  "bounded_repo_snapshot_required": true,
  "starter_terminal_trace_status_vocabulary_frozen": true,
  "starter_component_fidelity_value_domain_frozen": true,
  "starter_dominant_family_mapping_frozen": true,
  "trace_qualified_supporting_event_refs_required": true,
  "gold_trace_deterministically_derived_from_instance_required": true,
  "run_trace_scored_against_gold_required": true,
  "imported_materialization_bug_fix_required": true,
  "diagnostic_surface_non_promotional_required": true,
  "perturbation_and_non_regression_deferred_to_v46c": true,
  "cross_subject_comparison_deferred_to_v46d": true,
  "downstream_consumer_seam_deferred_to_v46e": true,
  "root_spec_mirror_required": true,
  "closeout_artifacts_required": [
    "artifacts/quality_dashboard_v137_closeout.json",
    "artifacts/stop_gate/metrics_v137_closeout.json",
    "artifacts/stop_gate/report_v137_closeout.md"
  ]
}
```

## Objective

Release the bounded `V46-B` Procedural Depth Fidelity baseline seam by defining one
repo-owned concrete benchmark projection stack under `packages/adeu_benchmarking`,
consuming the released `V46-A` substrate as-is while shipping exactly five new
procedural-depth artifact contracts:

- `adeu_procedural_depth_instance@1`
- `adeu_procedural_depth_gold_trace@1`
- `adeu_procedural_depth_run_trace@1`
- `adeu_procedural_depth_metrics@1`
- `adeu_procedural_depth_diagnostic_report@1`

This slice is the first released concrete benchmark projection. It is not yet the
perturbation/non-regression lane, the cross-subject comparison lane, or any downstream
consumer/promotion lane.

This slice must make explicit:

- one owner package only:
  - `packages/adeu_benchmarking`
- one consumed released benchmark substrate only:
  - `adeu_benchmark_family_spec@1`
  - `adeu_benchmark_projection_spec@1`
  - `adeu_benchmark_execution_context@1`
- one bounded procedural-depth artifact stack only:
  - one canonical instance
  - one canonical gold trace
  - one canonical run trace contract family
  - one canonical metrics contract family
  - one canonical diagnostic-report contract family
- one bounded reference world only:
  - one tiny deterministic hierarchical `3x3` reference chain
  - one bounded repo snapshot
  - no benchmark-library widening
- one explicit structural split only:
  - `horizontal_plan_spine`
  - `vertical_active_step_compilation`
  - `reintegration`
  with `clean_success` and `mixed` preserved at the benchmark-diagnostic layer
- one explicit starter scoring law only:
  - trace events are structurally anchored and trace-qualified
  - component fidelities are exact boolean checks in the starter slice
  - dominant family is derived from that boolean component pattern and terminal status
- one deferred-consumer posture only:
  - `V46-C` may later widen perturbation and non-regression
  - `V46-D` may later widen projection-library and cross-subject comparison
  - `V46-E` may later consume benchmark outputs under separately governed downstream
    seams

## Required Deliverables

The first `V46-B` release should add exactly these live implementation surfaces:

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
  - `packages/adeu_benchmarking/tests/fixtures/v46b/`

This slice should not add:

- perturbation or non-regression report artifacts;
- broader benchmark-library artifacts;
- cross-subject comparison or ranking surfaces;
- API or web benchmark-consumer surfaces;
- routing, role-assignment, or training-promotion doctrine;
- a second package owner surface;
- freeform larger benchmark families beyond the tiny starter reference chain.

## Frozen Implementation Decisions

1. Ownership and relation to released `V46-A`

- `packages/adeu_benchmarking` remains the only active implementation package for
  `V46-B`.
- released `adeu_benchmark_family_spec@1`,
  `adeu_benchmark_projection_spec@1`, and `adeu_benchmark_execution_context@1`
  remain the only required upstream artifact contracts for the starter slice.
- `V46-B` must bind exactly to the released projection declaration from `V46-A`:
  - actual released procedural-depth schema ids must match the `declared_*_contract_id`
    fields carried by the released projection spec
- released `V44` remains doctrinal constraint context through the released `V46-A`
  substrate:
  - `V46-B` may reuse the released structural split
  - it may not reopen or redefine released `V44` law here
- the imported GPT Pro benchmarking bundle remains support-only shaping evidence and may
  not define live procedural-depth law by itself.

2. Procedural-depth instance posture

- admit exactly one released instance contract:
  - `adeu_procedural_depth_instance@1`
- each instance artifact must carry:
  - `schema`
  - `procedural_depth_instance_id`
  - `benchmark_projection_spec_ref`
  - `benchmark_execution_context_ref`
  - `instance_label`
  - `repo_snapshot_ref`
  - `reference_chain_key`
  - ordered `top_level_plan_spine`
  - ordered `step_specs`
  - `expected_terminal_posture`
  - `gold_trace_derivation_posture`
  - `notes`
- the starter slice must remain exactly one bounded reference-chain family:
  - `hierarchical_3x3`
- `top_level_plan_spine` and `step_specs` must encode a tiny hierarchical `3x3`
  reference chain only:
  - exactly three top-level plan-spine steps
  - exactly three child steps under one active parent step
  - no deeper recursive grandchildren
- instance identity must be computed only after canonical `step_specs` ordering and
  structural validation are complete:
  - the known imported materialization/id-ordering bug may not be carried into the live
    repo-owned implementation
- `gold_trace_derivation_posture` in the starter slice must remain exactly:
  - `deterministically_derived_from_instance`
- `expected_terminal_posture` in the starter slice must remain exactly:
  - `complete_after_required_return`

3. Gold-trace posture

- admit exactly one released gold-trace contract:
  - `adeu_procedural_depth_gold_trace@1`
- each gold-trace artifact must carry:
  - `schema`
  - `procedural_depth_gold_trace_id`
  - `procedural_depth_instance_ref`
  - ordered `gold_events`
  - `terminal_trace_status`
  - `derivation_notes`
- each gold event in the starter slice must carry:
  - `event_index`
  - `event_kind`
  - `step_ref`
  - `step_role`
  - optional `parent_step_ref`
  - optional `return_target_step_ref`
- `gold_events` in the starter slice must use only:
  - `activate`
  - `complete`
  - `return`
- `step_role` in the starter slice must remain exactly:
  - `top_level`
  - `active_parent`
  - `child`
- `terminal_trace_status` in the starter slice must remain exactly:
  - `completed_clean`
  - `completed_with_structural_break`
- the gold trace must be deterministically derivable from the released instance only:
  - no alternate gold-trace families are selected here
  - no hidden scorer heuristics are selected here

4. Run-trace posture

- admit exactly one released run-trace contract:
  - `adeu_procedural_depth_run_trace@1`
- each run-trace artifact must carry:
  - `schema`
  - `procedural_depth_run_trace_id`
  - `procedural_depth_instance_ref`
  - ordered `observed_events`
  - `terminal_trace_status`
  - `observed_output_summary`
  - `trace_notes`
- each observed event in the starter slice must carry:
  - `event_index`
  - `event_kind`
  - `step_ref`
  - `step_role`
  - optional `parent_step_ref`
  - optional `return_target_step_ref`
- `observed_events` in the starter slice must use only:
  - `activate`
  - `complete`
  - `return`
- run traces in the starter slice must stay bound to the same released instance and
  repo snapshot as the gold trace they are scored against.
- `completed_invalid_early_closure` is not a lawful scored starter terminal status in
  `V46-B`:
  - invalid early closure remains reject-only in the starter slice

5. Metrics posture

- admit exactly one released metrics contract:
  - `adeu_procedural_depth_metrics@1`
- each metrics artifact must carry:
  - `schema`
  - `procedural_depth_metrics_id`
  - `procedural_depth_run_trace_ref`
  - `procedural_depth_gold_trace_ref`
  - `plan_spine_fidelity`
  - `active_step_compilation_fidelity`
  - `reintegration_fidelity`
  - `dominant_failure_family`
  - ordered `supporting_event_refs`
  - `scoring_notes`
- the starter slice may emit component fidelity values and dominant structural
  diagnosis only:
  - no one-number benchmark score
  - no ranking or promotion semantics
- starter component-fidelity value domain must remain exactly:
  - `true`
  - `false`
- starter component-fidelity derivation law must remain exactly:
  - `plan_spine_fidelity = true` only when every required top-level plan-spine event
    anchor from the gold trace is matched lawfully in the run trace
  - `active_step_compilation_fidelity = true` only when every required child-step
    activation/completion anchor under the active parent step is matched lawfully in
    the run trace
  - `reintegration_fidelity = true` only when every required return-to-parent anchor
    and post-return parent continuation anchor is matched lawfully in the run trace
- starter dominant-family mapping law must remain exactly:
  - `clean_success` only when:
    - `terminal_trace_status = completed_clean`
    - `plan_spine_fidelity = true`
    - `active_step_compilation_fidelity = true`
    - `reintegration_fidelity = true`
  - `horizontal_plan_spine` only when:
    - `terminal_trace_status = completed_with_structural_break`
    - `plan_spine_fidelity = false`
    - `active_step_compilation_fidelity = true`
    - `reintegration_fidelity = true`
  - `vertical_active_step_compilation` only when:
    - `terminal_trace_status = completed_with_structural_break`
    - `plan_spine_fidelity = true`
    - `active_step_compilation_fidelity = false`
    - `reintegration_fidelity = true`
  - `reintegration` only when:
    - `terminal_trace_status = completed_with_structural_break`
    - `plan_spine_fidelity = true`
    - `active_step_compilation_fidelity = true`
    - `reintegration_fidelity = false`
  - `mixed` only when:
    - `terminal_trace_status = completed_with_structural_break`
    - at least two component fidelities are `false`
- `dominant_failure_family` in the starter slice must remain exactly:
  - `clean_success`
  - `horizontal_plan_spine`
  - `vertical_active_step_compilation`
  - `reintegration`
  - `mixed`
- `clean_success` remains the only non-failure sentinel inside that starter field.
- each `supporting_event_ref` must be trace-qualified and carry:
  - `trace_role`
  - `trace_ref`
  - `event_index`
- `trace_role` in the starter slice must remain exactly:
  - `gold`
  - `run`

6. Diagnostic-report posture

- admit exactly one released diagnostic-report contract:
  - `adeu_procedural_depth_diagnostic_report@1`
- each diagnostic-report artifact must carry:
  - `schema`
  - `procedural_depth_diagnostic_report_id`
  - `procedural_depth_run_trace_ref`
  - `procedural_depth_metrics_ref`
  - `dominant_failure_family`
  - ordered `supporting_event_refs`
  - `benchmark_output_epistemic_posture`
  - ordered `limitations`
  - `diagnostic_summary`
- `benchmark_output_epistemic_posture` in the starter slice must remain exactly:
  - `inferred_interpretively`
- deterministic scoring basis remains carried by the bound metrics artifact and
  trace-qualified `supporting_event_refs`:
  - the report-level summary remains interpretive over that deterministic basis
- diagnostic reports remain diagnostic-only and non-promotional:
  - they may explain the bounded structural break pattern
  - they may not act as routing, ranking, or training authority

7. Ordering, hashing, and export law

- ids for all five released procedural-depth contracts must be deterministic and
  canonical
- `top_level_plan_spine`, `step_specs`, `gold_events`, `observed_events`,
  `supporting_event_refs`, `scoring_notes`, and `limitations` must be ordered
  deterministically
- `gold_events` and `observed_events` ordering must follow event index ascending
- `supporting_event_refs` ordering must follow first supporting occurrence in
  trace-event order across gold first, then run
- authoritative package-local schemas and root `spec/` mirrors must export
  deterministically from the same released models
- starter root `spec/` mirrors are required and may not be omitted in `V46-B`.

8. Fixture posture

- commit only deterministic local fixtures
- include at least:
  - one reference procedural-depth instance fixture
  - one reference procedural-depth gold-trace fixture
  - one reference clean-success run-trace fixture
  - one reference clean-success metrics fixture
  - one reference clean-success diagnostic-report fixture
  - positive degraded reference fixtures for at least:
    - `horizontal_plan_spine`
    - `vertical_active_step_compilation`
    - `reintegration`
    - `mixed`
  - one compact `V46-B` scoring matrix fixture showing:
    - run-trace ref
    - dominant failure family
    - component fidelities
    - supporting event refs
  - one reject fixture for a run trace whose instance ref does not match the bound gold
    trace and metrics stack
  - one reject fixture for unsupported event vocabulary or non-canonical step ordering
  - one reject fixture for invalid early closure terminal status in the starter scored
    slice
- keep the starter reference world tiny, deterministic, and repo-snapshot-bound only:
  - no perturbation bundle
  - no repeated-run non-regression bundle
  - no cross-subject comparison bundle

## Bounded Starter Vocabularies

The first `V46-B` release should freeze:

- `reference_chain_key`:
  - `hierarchical_3x3`
- `event_kind`:
  - `activate`
  - `complete`
  - `return`
- `step_role`:
  - `top_level`
  - `active_parent`
  - `child`
- `gold_trace_derivation_posture`:
  - `deterministically_derived_from_instance`
- `expected_terminal_posture`:
  - `complete_after_required_return`
- `terminal_trace_status`:
  - `completed_clean`
  - `completed_with_structural_break`
- `trace_role`:
  - `gold`
  - `run`
- `dominant_failure_family`:
  - `clean_success`
  - `horizontal_plan_spine`
  - `vertical_active_step_compilation`
  - `reintegration`
  - `mixed`
- `component_fidelity`:
  - `true`
  - `false`
- `benchmark_output_epistemic_posture`:
  - `inferred_interpretively`

## Selected Schema Anchors

The first `V46-B` release should freeze at least these anchors:

- `adeu_procedural_depth_instance@1`:
  - `schema`
  - `procedural_depth_instance_id`
  - `benchmark_projection_spec_ref`
  - `benchmark_execution_context_ref`
  - `instance_label`
  - `repo_snapshot_ref`
  - `reference_chain_key`
  - `top_level_plan_spine`
  - `step_specs`
  - `expected_terminal_posture`
  - `gold_trace_derivation_posture`
  - `notes`
- `adeu_procedural_depth_gold_trace@1`:
  - `schema`
  - `procedural_depth_gold_trace_id`
  - `procedural_depth_instance_ref`
  - `gold_events`
  - `terminal_trace_status`
  - `derivation_notes`
- `adeu_procedural_depth_run_trace@1`:
  - `schema`
  - `procedural_depth_run_trace_id`
  - `procedural_depth_instance_ref`
  - `observed_events`
  - `terminal_trace_status`
  - `observed_output_summary`
  - `trace_notes`
- `adeu_procedural_depth_metrics@1`:
  - `schema`
  - `procedural_depth_metrics_id`
  - `procedural_depth_run_trace_ref`
  - `procedural_depth_gold_trace_ref`
  - `plan_spine_fidelity`
  - `active_step_compilation_fidelity`
  - `reintegration_fidelity`
  - `dominant_failure_family`
  - `supporting_event_refs`
  - `scoring_notes`
- `adeu_procedural_depth_diagnostic_report@1`:
  - `schema`
  - `procedural_depth_diagnostic_report_id`
  - `procedural_depth_run_trace_ref`
  - `procedural_depth_metrics_ref`
  - `dominant_failure_family`
  - `supporting_event_refs`
  - `benchmark_output_epistemic_posture`
  - `limitations`
  - `diagnostic_summary`

## Acceptance

Accept `V46-B` when:

- `packages/adeu_benchmarking` remains the only active implementation package for the
  slice
- five released procedural-depth contracts export and mirror deterministically:
  - `adeu_procedural_depth_instance@1`
  - `adeu_procedural_depth_gold_trace@1`
  - `adeu_procedural_depth_run_trace@1`
  - `adeu_procedural_depth_metrics@1`
  - `adeu_procedural_depth_diagnostic_report@1`
- released `V46-A` family/projection/execution-context artifacts are consumed without
  reopening substrate doctrine
- actual released procedural-depth schema ids bind exactly to the declaration-only ids
  named by the released projection spec
- the starter reference world remains one tiny deterministic hierarchical `3x3`
  reference chain only
- gold traces derive deterministically from the released instance and run traces score
  deterministically against the gold trace
- gold/run event objects are structurally rich enough to support the released
  structural split:
  - `event_index`
  - `step_ref`
  - `step_role`
  - optional parent/return targeting where relevant
- `supporting_event_refs` remain trace-qualified across gold/run evidence
- metrics and diagnostic reports make the `horizontal_plan_spine`,
  `vertical_active_step_compilation`, `reintegration`, `mixed`, and `clean_success`
  outcomes explicit without collapsing them into one-number benchmark ranking posture
- component fidelity derivation and dominant-family mapping remain frozen to the
  starter boolean scoring law
- positive starter fixtures exercise:
  - `clean_success`
  - `horizontal_plan_spine`
  - `vertical_active_step_compilation`
  - `reintegration`
  - `mixed`
- the imported materialization/id-ordering bug is not carried into the live instance
  materialization path
- targeted tests cover deterministic ids, canonical ordering, gold-trace derivation,
  run-trace validation, metrics/diagnostic derivation, and reject posture.

Do not accept `V46-B` if:

- the slice widens into perturbation or non-regression families that belong to `V46-C`
- the slice widens into cross-subject comparison or benchmark-library release that
  belongs to `V46-D`
- the slice promotes diagnostic outputs into routing, ranking, or training authority
- actual released schema ids drift from the ids already declared in the released
  `V46-A` projection spec
- instance materialization computes ids before canonical ordering/validation
- scored starter traces admit invalid early closure as a lawful terminal status
- the starter reference chain widens beyond the tiny hierarchical `3x3` bound.

## Local Gate

- run `make arc-start-check ARC=137`
