# Draft ADEU Operator Projection V74B Implementation Mapping v0

Status: support note for the planned `V74-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V74-B`
should add typed adjudication case views, model-output comparison projections,
and exception visibility after `V74-A` has closed.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v64.md`
- `docs/ARCHITECTURE_ADEU_OPERATOR_PROJECTION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74A_IMPLEMENTATION_MAPPING_v0.md`

## Workflow Posture

This `V74-B` support spec remains below lock authority until `V74-A` has merged
and lean-closed, and a future canonical starter trio selects `V74-B`.

`V74-B` should extend released `V74-A` case-view, projection-source, and
guardrail rows. It should not create a parallel projection universe.

`V74-B` may project typed adjudication and model-output comparison state. It
must not perform new evidence classification, ratification, product selection,
benchmark ranking, runtime permission, dispatch, or release.

## Candidate New Surfaces

`V74-B` should select:

- `repo_typed_adjudication_case_view@1`
- `repo_model_output_comparison_projection@1`
- `repo_projection_exception_visibility_register@1`

These surfaces should make conceptual-diff and model-output comparison results
legible while preserving source, evidence, authority, outcome, and exception
boundaries.

## Typed Adjudication Case View

The typed adjudication case view should record:

- `typed_case_ref`
- `source_case_view_refs`
- `candidate_refs`
- `conceptual_diff_refs`
- `review_classification_refs`
- `ratification_refs`
- `outcome_recommendation_refs`
- `comparison_projection_refs`
- `exception_refs`
- `typed_case_posture`
- `odeu_lanes`
- `guardrail_refs`
- `limitation_note`

Minimum typed case posture:

- `projection_ready`
- `blocked_by_missing_conceptual_diff_source`
- `blocked_by_missing_review_source`
- `blocked_by_unresolved_exception`
- `future_family_only`
- `rejected_out_of_scope`

The typed adjudication case view may summarize what each source contributed. It
must not declare the source correct, adopted, productized, or released.

## Model-Output Comparison Projection

The comparison projection should record:

- `comparison_projection_ref`
- `typed_case_ref`
- `prompt_source_refs`
- `model_output_refs`
- `model_output_source_rows`
- `adjudicator_schema_refs`
- `comparison_axis_rows`
- `contradiction_refs`
- `complementarity_refs`
- `exception_refs`
- `comparison_projection_posture`
- `non_benchmark_guardrail`
- `limitation_note`

Minimum comparison axis kind:

- `source_binding`
- `authority_boundary_preservation`
- `odeu_lane_separation`
- `evidence_classification_fit`
- `ratification_boundary_fit`
- `implementation_safety`
- `utility_next_slice_fit`
- `conceptual_completeness`
- `operator_legibility`

Minimum comparison projection posture:

- `projection_ready`
- `blocked_by_missing_prompt_source`
- `blocked_by_missing_model_output_source`
- `blocked_by_missing_adjudicator_schema`
- `blocked_by_unresolved_conflict`
- `future_family_only`
- `rejected_out_of_scope`

Comparison projection is not benchmark truth. It can show that one output
preserved an authority boundary better on a bounded substrate, but it cannot
rank models globally or select a model for future work.

`comparison_axis_rows` should be structured rows, not a loose narrative list:

- `axis_ref`
- `axis_kind`
- `bounded_claim_horizon`
- `axis_source_refs`
- `observed_difference_posture`
- `contradiction_refs`
- `complementarity_refs`
- `exception_refs`
- `confidence_posture`
- `non_benchmark_guardrail`
- `limitation_note`

Minimum observed difference posture:

- `variant_a_stronger_on_axis`
- `variant_b_stronger_on_axis`
- `variants_complementary_on_axis`
- `variants_conflict_on_axis`
- `no_material_difference_observed`
- `axis_unchecked`
- `axis_blocked_by_missing_source`

Each model output source should carry provenance rows sufficient to fix the
comparison horizon without turning the comparison into a benchmark:

- `model_output_ref`
- `prompt_source_ref`
- `model_identity_ref`
- `output_capture_ref`
- `run_context_ref`
- `source_presence_posture`
- `limitation_note`

## Exception Visibility Register

The exception visibility register should record:

- `exception_ref`
- `case_view_refs`
- `typed_case_refs`
- `comparison_projection_refs`
- `candidate_refs`
- `exception_kind`
- `source_refs`
- `visible_decision_state`
- `blocking_posture`
- `required_next_surface`
- `limitation_note`

Minimum exception kind:

- `source_missing`
- `source_stale`
- `authority_boundary_blocker`
- `unresolved_dissent`
- `unresolved_regression`
- `review_conflict`
- `evidence_gap`
- `product_authority_missing`
- `runtime_authority_missing`
- `dispatch_authority_missing`
- `comparison_axis_unchecked`
- `model_output_provenance_gap`

Minimum blocking posture:

- `blocking`
- `warning_only`
- `carried_forward`
- `not_applicable`
- `unknown_needs_review`

Minimum required next surface:

- `v74c_visibility_contract`
- `v75_dispatch_review`
- `future_product_review`
- `future_ratification_or_policy_review`
- `future_family_review`
- `deferred_no_selection`

Exceptions must remain visible. A later case view may choose an operator-friendly
ordering, but it cannot omit blockers, dissent, regressions, source gaps, or
authority gaps from the typed substrate. `V74-B` may classify a row as blocking,
warning-only, carried forward, or not applicable; it must not mark exceptions
resolved.

## Mandatory Reject Cases

`V74-B` should reject:

- typed adjudication case without source `V74-A` case refs;
- typed case that treats conceptual-diff support docs as released schema;
- comparison projection without prompt or model-output source refs;
- comparison projection without model-output provenance rows;
- comparison projection that ranks a model globally;
- comparison axis row without source evidence;
- comparison axis row without bounded claim horizon or non-benchmark guardrail;
- product wedge projected as product authorization;
- exception register that omits a known source gap, dissent, regression, or
  authority blocker;
- exception marked resolved by `V74-B`;
- typed case that creates new ratification or outcome verdicts;
- comparison projection that authorizes implementation, release, product,
  runtime, dispatch, or external contest participation.

## Expected First Fixture

The first `V74-B` reference fixture should include:

- one typed adjudication case sourced from the conceptual-diff / product-wedge
  support lineage and released `V74-A` projection case;
- one model-output comparison projection with bounded axes and non-benchmark
  guardrail;
- one exception visibility register row for product authority missing;
- one exception visibility register row for model-output provenance or
  comparison-axis limitation;
- zero ratification, product, runtime, dispatch, release, or benchmark
  selection authority.

## Stop Gate Expectations

The future `V74-B` stop gate should require:

- schema exports for all three `V74-B` surfaces;
- reference and reject fixture validation;
- package export tests;
- rejection of model benchmark laundering and product-authority laundering;
- closeout evidence that `V74-B` only projects typed adjudication and
  comparison state.
