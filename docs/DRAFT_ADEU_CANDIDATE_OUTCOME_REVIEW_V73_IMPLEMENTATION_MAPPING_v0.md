# Draft ADEU Candidate Outcome Review V73 Implementation Mapping v0

Status: support / implementation mapping record for planned `V73`.

Authority layer: support.

This note does not authorize implementation by itself. It maps the planned
`V73` family into likely package, schema, validator, fixture, and evidence work
so the family can be reviewed before the first active slice lock is drafted.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v63.md`
- `docs/ARCHITECTURE_ADEU_CANDIDATE_OUTCOME_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CONTAINED_INTEGRATION_REVIEW_V72_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_OUTCOME_REVIEW_V73A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_OUTCOME_REVIEW_V73B_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_OUTCOME_REVIEW_V73C_IMPLEMENTATION_MAPPING_v0.md`

## 1. Family Intent

`V73` should add candidate outcome review without turning outcome review into:

- autonomous adoption or self-approval;
- commit / PR / merge / release authority;
- product projection;
- runtime permission;
- dispatch or execution widening;
- external contest participation.

The implementation target is a typed candidate outcome-review family that can
represent:

- source-bound outcome-review entries over released `V72-C` handoff rows;
- outcome evidence sources and horizon boundaries;
- observed benefit, harm, mixed, neutral, or inconclusive outcomes;
- regression and blocker posture;
- tool-fitness drift;
- self-improvement outcome ledger rows;
- operator-cognition outcome signals;
- promotion / demotion / repeat / more-evidence recommendations;
- family closeout alignment without selecting `V74` or `V75`.

## 2. Package Ownership

Expected primary ownership:

- `packages/adeu_repo_description`
  - models, enums, canonicalization helpers, validators, and schemas for
    repo-grounded candidate outcome review
- `spec/`
  - mirrored exported schemas if repo policy continues mirror parity
- `apps/api/fixtures/repo_description/vnext_plus203/`
  - reference and reject fixtures for the first bounded slice

This package choice is conservative: `V73` still describes repo/corpus metadata
and outcome-review state. If a later slice tries to become a product workbench,
runtime evaluator, live dispatch loop, or release automation, that work should
split away instead of expanding `adeu_repo_description` by implication.

The proposed `repo_*` schemas are repo-description candidate outcome-review
surfaces, not live release, product, runtime, dispatch, or ARC challenge
artifacts.

Expected starter implementation surfaces:

- `packages/adeu_repo_description/src/adeu_repo_description/candidate_outcome_review.py`
- `packages/adeu_repo_description/src/adeu_repo_description/__init__.py`
- `packages/adeu_repo_description/src/adeu_repo_description/export_schema.py`
- `packages/adeu_repo_description/tests/test_candidate_outcome_review_v73a.py`
- `packages/adeu_repo_description/tests/test_repo_description_export_schema.py`

Expected starter schema files:

- `packages/adeu_repo_description/schema/repo_candidate_outcome_review_entry.v1.json`
- `packages/adeu_repo_description/schema/repo_outcome_evidence_source_index.v1.json`
- `packages/adeu_repo_description/schema/repo_outcome_review_boundary_guardrail.v1.json`

Expected later schema files:

- `packages/adeu_repo_description/schema/repo_candidate_outcome_observation_record.v1.json`
- `packages/adeu_repo_description/schema/repo_outcome_regression_register.v1.json`
- `packages/adeu_repo_description/schema/repo_tool_fitness_drift_register.v1.json`
- `packages/adeu_repo_description/schema/repo_self_improvement_outcome_ledger.v1.json`
- `packages/adeu_repo_description/schema/repo_operator_cognition_outcome_signal.v1.json`
- `packages/adeu_repo_description/schema/repo_outcome_promotion_demotion_recommendation.v1.json`
- `packages/adeu_repo_description/schema/repo_outcome_review_family_closeout_alignment.v1.json`

Expected mirror schema files:

- `spec/repo_candidate_outcome_review_entry.schema.json`
- `spec/repo_outcome_evidence_source_index.schema.json`
- `spec/repo_outcome_review_boundary_guardrail.schema.json`
- `spec/repo_candidate_outcome_observation_record.schema.json`
- `spec/repo_outcome_regression_register.schema.json`
- `spec/repo_tool_fitness_drift_register.schema.json`
- `spec/repo_self_improvement_outcome_ledger.schema.json`
- `spec/repo_operator_cognition_outcome_signal.schema.json`
- `spec/repo_outcome_promotion_demotion_recommendation.schema.json`
- `spec/repo_outcome_review_family_closeout_alignment.schema.json`

## 3. Candidate `V73` Artifact Set

| Artifact | Likely slice | Role |
|---|---|---|
| `repo_candidate_outcome_review_entry@1` | `V73-A` | top-level outcome-review entry rows over released `V72-C` handoffs |
| `repo_outcome_evidence_source_index@1` | `V73-A` | baseline / intervention / evaluation / trial / effect / rollback / authority source rows |
| `repo_outcome_review_boundary_guardrail@1` | `V73-A` | non-promotion, non-release, non-product, non-runtime, and non-dispatch guardrail rows |
| `repo_candidate_outcome_observation_record@1` | `V73-B` | observed outcome rows over selected entries |
| `repo_outcome_regression_register@1` | `V73-B` | regression, blocker, and negative-control rows |
| `repo_tool_fitness_drift_register@1` | `V73-B` | tool usefulness, staleness, and applicability-drift rows |
| `repo_self_improvement_outcome_ledger@1` | `V73-C` | longitudinal outcome ledger rows |
| `repo_operator_cognition_outcome_signal@1` | `V73-C` | operator-cognition and workflow-residue outcome signals |
| `repo_outcome_promotion_demotion_recommendation@1` | `V73-C` | recommendation rows without adoption authority |
| `repo_outcome_review_family_closeout_alignment@1` | `V73-C` | family closeout alignment without selecting `V74` or `V75` |

`V73-A` should ship only starter shapes, validators, schema exports, and
reference/reject fixtures. It should not classify outcomes.

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
  - `artifacts/agent_harness/v202/evidence_inputs/v72c_contained_integration_closeout_evidence_v202.json`
- `V72` outcome-review handoff substrate:
  - `apps/api/fixtures/repo_description/vnext_plus202/repo_commit_release_authority_posture_v202_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus202/repo_post_integration_outcome_review_handoff_v202_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus202/repo_contained_integration_family_closeout_alignment_v202_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus201/repo_contained_integration_trial_record_v201_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus201/repo_integration_effect_surface_register_v201_reference.json`
  - `apps/api/fixtures/repo_description/vnext_plus201/repo_integration_rollback_readiness_v201_reference.json`
- support dogfood:
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_COMBINED_DOGFOOD_TEST_v0.md`
  - `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_COMBINED_DOGFOOD_TEST_v0.json`

Globs are discovery instructions, not evidence sources. Only observed concrete
files may become outcome source rows.

If any expected source is missing when the active starter lock is drafted, the
absence should be represented as an explicit source row. The reference fixture
should not reconstruct outcome state from planning prose.

## 5. Required Starter Enumerations

Outcome-review entry posture:

- `eligible_for_outcome_review`
- `blocked_by_missing_trial_evidence`
- `blocked_by_rollback_gap`
- `blocked_by_effect_gap`
- `blocked_by_authority_boundary`
- `future_family_only`
- `rejected_out_of_scope`

Outcome evidence kind:

- `baseline_evidence`
- `intervention_evidence`
- `evaluation_evidence`
- `trial_evidence`
- `effect_evidence`
- `rollback_evidence`
- `authority_posture_evidence`
- `dogfood_evidence`
- `operator_cognition_evidence`
- `tool_run_evidence`
- `absence_evidence`

Outcome evidence role:

- `primary_outcome_evidence`
- `auxiliary_trial_context`
- `auxiliary_effect_context`
- `auxiliary_rollback_context`
- `authority_boundary_context`
- `absence_marker`

Outcome horizon kind:

- `baseline`
- `intervention`
- `evaluation`

Horizon coverage posture:

- `covered`
- `partially_covered`
- `missing_expected_source`
- `not_applicable`
- `future_family_only`

Boundary guardrail posture:

- `no_promotion_authority`
- `no_demotion_authority`
- `no_release_authority`
- `no_product_authorization`
- `no_runtime_permission`
- `no_dispatch_authority`
- `no_external_contest_authority`

Boundary required later authority:

- `human_ratification_required`
- `maintainer_release_authority_required`
- `product_authority_required`
- `runtime_authority_required`
- `dispatch_authority_required`
- `external_contest_authority_required`
- `none_selected_here`

## 6. Shared Row Vocabulary

Minimum outcome source row fields:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `outcome_evidence_kind`
- `horizon_refs`
- `evidence_role`
- `limitation_note`

Minimum outcome horizon row fields:

- `horizon_ref`
- `candidate_ref`
- `horizon_kind`
- `covered_surface_refs`
- `source_refs`
- `coverage_posture`
- `limitation_note`

Minimum outcome-review entry row fields:

- `entry_ref`
- `candidate_ref`
- `source_handoff_refs`
- `trial_refs`
- `effect_refs`
- `rollback_refs`
- `authority_posture_refs`
- `outcome_source_refs`
- `baseline_horizon_ref`
- `intervention_horizon_ref`
- `evaluation_horizon_ref`
- `blocking_trial_gap_refs`
- `blocking_effect_gap_refs`
- `blocking_rollback_gap_refs`
- `blocking_authority_boundary_refs`
- `entry_posture`
- `odeu_lanes`
- `guardrail_refs`
- `limitation_note`

Minimum boundary guardrail row fields:

- `guardrail_ref`
- `candidate_ref`
- `entry_refs`
- `forbidden_downstream_roles`
- `boundary_posture`
- `required_later_authority`
- `limitation_note`

## 7. Cross-Surface Validation Expectations

Starter validators should enforce:

- every outcome-review entry references a known released `V72-C` handoff row;
- only `ready_for_v73_review` handoff rows can become
  `eligible_for_outcome_review`;
- every trial / effect / rollback / authority ref resolves through released
  `V72-B` or `V72-C` fixture substrate;
- source absence is represented as source rows, not empty memory;
- eligible entries reference exactly one baseline, one intervention, and one
  evaluation horizon row;
- outcome evidence kind remains separate from evidence role, so trial, effect,
  rollback, and authority sources can be context without becoming outcome
  success;
- blocked entries carry machine-checkable blocker refs or explicit absence
  evidence rows;
- `odeu_lanes` is sorted, unique, and non-empty;
- every entry has non-empty guardrail refs;
- guardrails include promotion, release, product, runtime, dispatch, and
  external-contest prohibitions;
- no starter row includes outcome verdict, regression verdict, tool-fitness
  verdict, promotion, demotion, adoption, or product projection language.

## 8. Family Closeout Expectation

The family should close only after `V73-C` proves that entry, observation,
regression, tool drift, ledger, operator-cognition signal, and recommendation
rows remain distinct. `V74` remains responsible for operator/product projection.
`V75` remains responsible for any later dispatch widening.
