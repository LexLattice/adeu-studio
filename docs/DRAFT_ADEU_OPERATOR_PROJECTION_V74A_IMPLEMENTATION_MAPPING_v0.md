# Draft ADEU Operator Projection V74A Implementation Mapping v0

Status: support note for the planned `V74-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V74-A`
should add operator projection case-view rows, projection source indexing, and
non-authority guardrails after `V73` has closed.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v64.md`
- `docs/ARCHITECTURE_ADEU_OPERATOR_PROJECTION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_COMBINED_DOGFOOD_TEST_v0.md`

## Workflow Posture

This `V74-A` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not an active implementation lock.

When `V74-A` becomes active, it should receive its own canonical starter trio
after review patches are integrated. It should consume released `V73-C`
self-improvement outcome ledger, operator-cognition outcome signal,
promotion/demotion recommendation, and family closeout alignment rows as
source-bound substrate.

The active `V74-A` implementation may add its own schema, model, validator,
fixture, and test files under the future lock. That is distinct from product
workbench or operator command implementation. `V74-A` must not record
ratification, product authorization, release, runtime permission, dispatch, or
external contest authority.

## Candidate New Surfaces

`V74-A` should select:

- `repo_operator_projection_case_view@1`
- `repo_operator_projection_source_index@1`
- `repo_operator_projection_non_authority_guardrail@1`

These surfaces should translate released `V73-C` recommendation and ledger
substrate into bounded operator projection posture without building a live UI.

## Source Binding

`V74-A` should define explicit projection source rows over:

- `artifacts/agent_harness/v205/evidence_inputs/v73_family_closeout_alignment_v205.json`
- `artifacts/agent_harness/v205/evidence_inputs/v73c_candidate_outcome_closeout_evidence_v205.json`
- `apps/api/fixtures/repo_description/vnext_plus205/repo_self_improvement_outcome_ledger_v205_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus205/repo_operator_cognition_outcome_signal_v205_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus205/repo_outcome_promotion_demotion_recommendation_v205_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus205/repo_outcome_review_family_closeout_alignment_v205_reference.json`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_COMBINED_DOGFOOD_TEST_v0.json`
- `docs/support/arc_series_mapping/DRAFT_ADEU_TYPED_ADJUDICATION_PRODUCT_WEDGE_v0.md`

Absence should be represented as source posture, not as prose memory.

## Projection Source Index

The source index should record:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `projection_source_role`
- `limitation_note`

Minimum projection source role:

- `primary_projection_source`
- `outcome_ledger_source`
- `operator_signal_source`
- `recommendation_source`
- `family_closeout_source`
- `dogfood_source`
- `review_source`
- `ratification_source`
- `integration_source`
- `conceptual_diff_source`
- `product_wedge_source`
- `prompt_source`
- `model_output_source`
- `adjudicator_schema_source`
- `absence_marker`

Every case-view row, recommendation ref, ledger ref, operator-signal ref, and
guardrail row should resolve through concrete source rows or explicit absence
rows.

## Operator Projection Case View

The case view should record:

- `case_view_ref`
- `candidate_ref`
- `projection_case_kind`
- `projection_posture`
- `visible_decision_state`
- `projection_horizon`
- `visible_authority_state`
- `source_refs`
- `ledger_refs`
- `operator_signal_refs`
- `recommendation_refs`
- `family_closeout_refs`
- `exception_refs`
- `visible_blocker_rows`
- `odeu_lanes`
- `guardrail_refs`
- `limitation_note`

Minimum projection case kind:

- `self_improvement_outcome_case`
- `candidate_decision_case`
- `operator_cognition_signal_case`
- `typed_adjudication_case`
- `model_output_comparison_case`
- `product_pressure_case`
- `future_family_case`

Minimum projection posture:

- `eligible_for_operator_projection`
- `blocked_by_missing_source`
- `blocked_by_unresolved_regression`
- `blocked_by_unresolved_dissent`
- `blocked_by_authority_boundary`
- `future_family_only`
- `rejected_out_of_scope`

Minimum visible decision state:

- `ready_for_human_review`
- `blocked_pending_evidence`
- `blocked_pending_authority`
- `blocked_pending_dissent_resolution`
- `recommended_for_later_review`
- `recommended_more_evidence`
- `deferred_to_future_family`
- `rejected_out_of_scope`

Minimum projection horizon:

- `human_review_visibility`
- `later_ratification_review_request`
- `later_product_review_request`
- `later_dispatch_review_request`
- `future_family_visibility_only`

Minimum visible authority state:

- `no_authority_granted`
- `ratification_required`
- `product_authority_missing`
- `runtime_authority_missing`
- `dispatch_authority_missing`
- `release_authority_missing`

Visible decision state answers what the operator can see. Projection horizon
and visible authority state answer what, if anything, later review could do and
which authority is still absent. `ready_for_human_review` is not permission to
act.

## Visible Blocker Rows

`V74-A` should embed minimal visible blocker / exception-summary rows in the
case-view payload:

- `blocker_ref`
- `candidate_ref`
- `case_view_refs`
- `blocker_kind`
- `source_refs`
- `blocking_posture`
- `visible_decision_state`
- `required_next_surface`
- `limitation_note`

Minimum blocker kind:

- `source_gap`
- `unresolved_regression`
- `unresolved_dissent`
- `authority_boundary_gap`
- `product_authority_gap`
- `runtime_authority_gap`
- `dispatch_authority_gap`
- `release_authority_gap`
- `model_output_provenance_gap`
- `comparison_axis_gap`

Minimum blocking posture:

- `blocking`
- `warning_only`
- `carried_forward`
- `not_applicable`
- `unknown_needs_review`

These rows do not replace the later `V74-B`
`repo_projection_exception_visibility_register@1`. They make blocker
visibility machine-checkable before that later register exists.

Conditional validation:

- if `projection_posture = eligible_for_operator_projection`, then source refs,
  recommendation refs or ledger refs, and guardrail refs must be non-empty;
- if `projection_posture` is blocked, then source rows or exception refs must
  identify the blocker;
- if `projection_case_kind = product_pressure_case`, then visible state must not
  imply product authorization and visible authority state must be
  `product_authority_missing` unless the case is rejected or out of scope;
- if `projection_case_kind = model_output_comparison_case`, then visible state
  must not imply benchmark truth or model superiority;
- if visible state is ready for human review, then forbidden projection
  authority must still be non-empty in referenced guardrails.

## Non-Authority Guardrail

The guardrail should record:

- `guardrail_ref`
- `case_view_refs`
- `candidate_refs`
- `forbidden_projection_authorities`
- `required_later_authority`
- `operator_action_posture`
- `non_authority_statement`
- `limitation_note`

Minimum forbidden projection authority:

- `ratification_authority`
- `adoption_authority`
- `implementation_authority`
- `commit_release_authority`
- `merge_authority`
- `released_truth`
- `product_authorization`
- `runtime_permission`
- `dispatch_authority`
- `external_contest_authority`

Minimum operator action posture:

- `inspect_only`
- `acknowledge_only`
- `request_later_review_only`
- `annotate_source_gap_only`
- `export_support_report_only`
- `no_operator_action_selected`

Minimum required later authority:

- `human_ratification_required`
- `maintainer_release_authority_required`
- `product_authority_required`
- `runtime_authority_required`
- `dispatch_authority_required`
- `external_contest_authority_required`
- `none_selected_here`

`V74-A` may make state visible. It must not make the visible state authoritative.

## Mandatory Reject Cases

`V74-A` should reject:

- case view with unknown candidate ref;
- case view without source refs;
- source row with missing concrete source and no absence posture;
- recommendation, ledger, operator-signal, or family-closeout refs that do not
  resolve through the source index;
- product-pressure case marked as product-authorized;
- product-pressure case without product-authority-missing posture unless
  rejected or out of scope;
- model-output comparison case marked as benchmark truth or model-selected;
- operator action posture that implies implementation, release, runtime,
  dispatch, or external contest participation;
- case view with empty guardrail refs;
- guardrail with empty forbidden projection authority;
- transcript or operator turn treated as truth or authority;
- hidden regression, dissent, blocker, or source gap omitted from visible state
  or visible blocker rows;
- projection row that claims `V75` dispatch, product launch, release, or
  recursive self-approval.

## Expected First Fixture

The first reference fixture should include:

- one projection case for
  `candidate:internal:self_evidencing_workflow_type_emergence` sourced from
  released `V73-C` recommendation and ledger rows;
- one product-pressure case for
  `candidate:internal:typed_adjudication_product_wedge` that is visible as
  future-family pressure but not product-authorized;
- one source index with concrete `V73-C` and dogfood refs;
- one non-authority guardrail shared by the visible cases;
- zero live UI, command, runtime, product, dispatch, release, or external
  contest surfaces.

## Stop Gate Expectations

The future `vNext+206` stop gate should require:

- schema exports for all three `V74-A` surfaces;
- reference and reject fixture validation;
- package export tests;
- rejection of product / release / runtime / dispatch / authority laundering;
- closeout evidence that the slice remains projection-only.
