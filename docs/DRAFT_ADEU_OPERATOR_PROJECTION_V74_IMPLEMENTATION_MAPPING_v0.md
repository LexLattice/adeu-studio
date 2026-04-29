# Draft ADEU Operator Projection V74 Implementation Mapping v0

Status: support / implementation mapping record for planned `V74`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`V74` family into likely package, schema, validator, fixture, and evidence work
so the family can be reviewed before the first active slice lock is drafted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v64.md`
- `docs/ARCHITECTURE_ADEU_OPERATOR_PROJECTION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_OUTCOME_REVIEW_V73_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74C_IMPLEMENTATION_MAPPING_v0.md`

## 1. Family Intent

`V74` should add operator projection and typed case-view records without turning
projection into:

- ratification or adoption;
- implementation authority;
- commit / PR / merge / release authority;
- released truth;
- product authorization;
- runtime permission;
- dispatch or execution widening;
- external contest participation.

The implementation target is a typed operator-projection family that can
represent:

- source-bound operator case views over released `V73-C` ledger /
  operator-signal / recommendation rows;
- projection source rows and explicit source absence posture;
- non-authority guardrails for projected decisions;
- typed adjudication case views;
- model-output comparison projections;
- exception visibility;
- decision visibility contracts;
- ratification-review workbench projection rows;
- post-projection handoff rows without performing `V75`;
- family closeout alignment without selecting product, runtime, dispatch, or
  external contest participation.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_repo_description`
  - models, enums, canonicalization helpers, validators, and schemas for
    repo-grounded operator projection records
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/repo_description/vnext_plus206/`
  - reference and reject fixtures for the first bounded slice

This package choice is conservative: `V74` still describes repo/corpus metadata
and projection state. If a later slice tries to become a live frontend, product
workbench, command surface, runtime evaluator, dispatch loop, or release
automation, that work should split away instead of expanding
`adeu_repo_description` by implication.

The proposed `repo_*` schemas are repo-description operator-projection
surfaces, not live UI, product, runtime, dispatch, or ARC challenge artifacts.

Expected starter implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/operator_projection.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/tests/test_operator_projection_v74a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Expected starter schema files:

- `packages/adeu_repo_description/schema/repo_operator_projection_case_view.v1.json`
- `packages/adeu_repo_description/schema/repo_operator_projection_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_operator_projection_non_authority_guardrail.v1.json`

Expected later schema files:

- `packages/adeu_repo_description/schema/repo_typed_adjudication_case_view.v1.json`
- `packages/adeu_repo_description/schema/repo_model_output_comparison_projection.v1.json`
- `packages/adeu_repo_description/schema/repo_projection_exception_visibility_register.v1.json`
- `packages/adeu_repo_description/schema/repo_decision_visibility_contract.v1.json`
- `packages/adeu_repo_description/schema/repo_ratification_review_workbench_projection.v1.json`
- `packages/adeu_repo_description/schema/repo_post_projection_handoff.v1.json`
- `packages/adeu_repo_description/schema/repo_operator_projection_family_closeout_alignment.v1.json`

Expected mirror schema files:

- `spec/repo_operator_projection_case_view.schema.json`
- `spec/repo_operator_projection_source_index.schema.json`
- `spec/repo_operator_projection_non_authority_guardrail.schema.json`
- `spec/repo_typed_adjudication_case_view.schema.json`
- `spec/repo_model_output_comparison_projection.schema.json`
- `spec/repo_projection_exception_visibility_register.schema.json`
- `spec/repo_decision_visibility_contract.schema.json`
- `spec/repo_ratification_review_workbench_projection.schema.json`
- `spec/repo_post_projection_handoff.schema.json`
- `spec/repo_operator_projection_family_closeout_alignment.schema.json`

## 3. Candidate `V74` Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `repo_operator_projection_case_view@1` | `V74-A` | top-level operator case-view rows over released `V73-C` substrate |
| `repo_operator_projection_source_index@1` | `V74-A` | source rows for projection, absence posture, and source roles |
| `repo_operator_projection_non_authority_guardrail@1` | `V74-A` | non-ratification, non-product, non-release, non-runtime, and non-dispatch guardrails |
| `repo_typed_adjudication_case_view@1` | `V74-B` | typed adjudication case projection over conceptual diff / review lineage |
| `repo_model_output_comparison_projection@1` | `V74-B` | model-output comparison projection without benchmark authority |
| `repo_projection_exception_visibility_register@1` | `V74-B` | blocker, dissent, source-gap, regression, and authority exception rows |
| `repo_decision_visibility_contract@1` | `V74-C` | visible decision states and hidden/non-derivable field constraints |
| `repo_ratification_review_workbench_projection@1` | `V74-C` | projected ratification-review actions without ratification or execution authority |
| `repo_post_projection_handoff@1` | `V74-C` | handoff request rows for later family review such as `V75` |
| `repo_operator_projection_family_closeout_alignment@1` | `V74-C` | family closeout alignment without product, runtime, dispatch, or release authority |

`V74-A` should ship only starter shapes, validators, schema exports, and
reference/reject fixtures. It should not implement a live UI or workbench.

## 4. Source Classes

The family should consume concrete source refs from:

- `V68` cartography family closeout:
  - `docs/DRAFT_ADEU_ARC_SERIES_CARTOGRAPHY_V68_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v190/evidence_inputs/v68_family_closeout_alignment_v190.json`
- `V69` candidate-intake family closeout:
  - `docs/DRAFT_ADEU_RECURSIVE_CANDIDATE_INTAKE_V69_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v193/evidence_inputs/v69_family_closeout_alignment_v193.json`
- `V70` review-classification family closeout:
  - `docs/DRAFT_ADEU_CANDIDATE_REVIEW_CLASSIFICATION_V70_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v196/evidence_inputs/v70_family_closeout_alignment_v196.json`
- `V71` ratification-review family closeout:
  - `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v199/evidence_inputs/v71_family_closeout_alignment_v199.json`
- `V72` contained integration-review family closeout:
  - `docs/DRAFT_ADEU_CONTAINED_INTEGRATION_REVIEW_V72_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v202/evidence_inputs/v72_family_closeout_alignment_v202.json`
- `V73` outcome-review family closeout:
  - `docs/DRAFT_ADEU_CANDIDATE_OUTCOME_REVIEW_V73_FAMILY_CLOSEOUT_v0.md`
  - `artifacts/agent_harness/v205/evidence_inputs/v73_family_closeout_alignment_v205.json`
  - `artifacts/agent_harness/v205/evidence_inputs/v73c_candidate_outcome_closeout_evidence_v205.json`
- `V73` operator-projection source substrate:
  - `apps/api/fixtures/repo_description/vnext_plus205/repo_self_improvement_outcome_ledger_v205_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus205/repo_operator_cognition_outcome_signal_v205_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus205/repo_outcome_promotion_demotion_recommendation_v205_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus205/repo_outcome_review_family_closeout_alignment_v205_reference.json`
- support lineage:
  - `docs/DRAFT_ARC_SERIES_MULTI_LAYER_MAPPING_v2.md`
  - `docs/support/arc_series_mapping/DRAFT_ADEU_TYPED_ADJUDICATION_PRODUCT_WEDGE_v0.md`
  - `docs/support/arc_series_mapping/DRAFT_ARC_SERIES_REASONING_RECURSION_LOOP_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_COMBINED_DOGFOOD_TEST_v0.json`

Globs are discovery instructions, not evidence sources. Only observed concrete
files may become projection source rows.

If any expected source is missing when the active starter lock is drafted, the
absence should be represented as an explicit source row. The reference fixture
should not reconstruct projection state from planning prose.

## 5. Required Starter Enumerations

Projection case kind:

- `self_improvement_outcome_case`
- `candidate_decision_case`
- `operator_cognition_signal_case`
- `typed_adjudication_case`
- `model_output_comparison_case`
- `product_pressure_case`
- `future_family_case`

Projection posture:

- `eligible_for_operator_projection`
- `blocked_by_missing_source`
- `blocked_by_unresolved_regression`
- `blocked_by_unresolved_dissent`
- `blocked_by_authority_boundary`
- `future_family_only`
- `rejected_out_of_scope`

Visible decision state:

- `ready_for_human_review`
- `blocked_pending_evidence`
- `blocked_pending_authority`
- `blocked_pending_dissent_resolution`
- `recommended_for_later_review`
- `recommended_more_evidence`
- `deferred_to_future_family`
- `rejected_out_of_scope`

Projection source role:

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

Forbidden projection authority:

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

## 6. Shared Row Vocabulary

Minimum projection source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `projection_source_role`
- `limitation_note`

Minimum case-view row fields:

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

Minimum projection guardrail row fields:

- `guardrail_ref`
- `case_view_refs`
- `candidate_refs`
- `forbidden_projection_authorities`
- `required_later_authority`
- `operator_action_posture`
- `non_authority_statement`
- `limitation_note`

The same row vocabulary should be extended by later slices rather than
recreated in parallel.

Minimum visible blocker row fields embedded in the `V74-A` case-view payload:

- `blocker_ref`
- `candidate_ref`
- `case_view_refs`
- `blocker_kind`
- `source_refs`
- `blocking_posture`
- `visible_decision_state`
- `required_next_surface`
- `limitation_note`

`V74-A` blocker rows are summaries. `V74-B` may refine them into
`repo_projection_exception_visibility_register@1`, but it should not create the
first machine-checkable exception substrate from scratch.

Minimum comparison axis row fields for `V74-B`:

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

Minimum model-output provenance row fields for `V74-B`:

- `model_output_ref`
- `prompt_source_ref`
- `model_identity_ref`
- `output_capture_ref`
- `run_context_ref`
- `source_presence_posture`
- `limitation_note`

## 7. Fixture Strategy

The first `V74-A` reference fixture should remain deliberately partial:

- one `self_improvement_outcome_case` over the released `V73-C`
  recommendation for `candidate:internal:self_evidencing_workflow_type_emergence`;
- one `product_pressure_case` for
  `candidate:internal:typed_adjudication_product_wedge` that remains
  future-family-only or blocked pending product authority;
- one source index containing concrete `V73-C`, dogfood, and support sources;
- one guardrail row forbidding ratification, adoption, product, release,
  runtime, dispatch, and external contest authority;
- zero live UI, command, product, or dispatch surfaces.

Reject fixtures should cover:

- projection case without source refs;
- projection from a missing expected source without absence posture;
- operator projection case treated as ratification;
- product-pressure case treated as product authorization;
- model-output comparison case treated as benchmark truth;
- hidden regression or dissent omitted from visible state;
- visible decision state that contradicts source recommendation posture;
- case view with empty forbidden authority list;
- operator action posture that implies execution or dispatch;
- product-pressure case without `product_authority_required` or equivalent
  later-authority posture unless rejected or out of scope;
- transcript or operator turn treated as source truth.

## 8. Implementation Boundaries

`V74-A` may add Python schema/model/validator/test/fixture files under the
future active lock. That is different from building an operator UI or product
surface.

`V74-B` may project typed adjudication and model comparison records. It must not
perform new evidence classification, ratification, model benchmark selection,
or product authorization.

`V74-C` may define visibility contracts, workbench projection rows, and
post-projection handoff rows. It must not perform `V75` dispatch, runtime
permission, product launch, release, or external contest participation.

## 9. Expected Family Closeout

The final family closeout should record:

- the closed `V74-A` / `V74-B` / `V74-C` slice ladder;
- instantiated operator-projection schema surfaces;
- concrete source rows consumed from `V68` through `V73`;
- visible decision-state and exception posture;
- non-authority guardrails;
- whether a later `V75` dispatch-review family is ready to draft.

The closeout must not claim that `V75`, product authorization, release,
runtime permission, or external contest participation has occurred.
