# Draft ADEU Candidate Outcome Review V73A Implementation Mapping v0

Status: support note for the planned `V73-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V73-A`
should add outcome-review entry, outcome evidence source indexing, and boundary
guardrails after `V72` has closed.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v63.md`
- `docs/ARCHITECTURE_ADEU_CANDIDATE_OUTCOME_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_OUTCOME_REVIEW_V73_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_COMBINED_DOGFOOD_TEST_v0.md`

## Workflow Posture

This `V73-A` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not an active implementation lock.

When `V73-A` becomes active, it should receive its own canonical starter trio
after review patches are integrated. It should consume released `V72-C`
authority-posture, post-integration handoff, and family closeout alignment rows
as source-bound substrate.

The active `V73-A` implementation may add its own schema, model, validator,
fixture, and test files under the future lock. That is distinct from candidate
outcome judgment. `V73-A` must not record outcome success, regression, tool
fitness, promotion, demotion, release, product, runtime, or dispatch authority.

## Candidate New Surfaces

`V73-A` should select:

- `repo_candidate_outcome_review_entry@1`
- `repo_outcome_evidence_source_index@1`
- `repo_outcome_review_boundary_guardrail@1`

These surfaces should translate released `V72-C` ready handoffs into bounded
outcome-review entry posture without judging the outcome.

## Source Binding

`V73-A` should define explicit outcome source rows over:

- `artifacts/agent_harness/v202/evidence_inputs/v72_family_closeout_alignment_v202.json`
- `artifacts/agent_harness/v202/evidence_inputs/v72c_contained_integration_closeout_evidence_v202.json`
- `apps/api/fixtures/repo_description/vnext_plus202/repo_commit_release_authority_posture_v202_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus202/repo_post_integration_outcome_review_handoff_v202_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus202/repo_contained_integration_family_closeout_alignment_v202_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus201/repo_contained_integration_trial_record_v201_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus201/repo_integration_effect_surface_register_v201_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus201/repo_integration_rollback_readiness_v201_reference.json`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_COMBINED_DOGFOOD_TEST_v0.json`

Absence should be represented as source posture, not as prose memory.

## Outcome Evidence Source Index

The evidence source index should record:

- `source_ref`
- `candidate_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `outcome_evidence_kind`
- `horizon_refs`
- `evidence_role`
- `limitation_note`

Minimum outcome evidence kind:

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

Minimum evidence role:

- `primary_outcome_evidence`
- `auxiliary_trial_context`
- `auxiliary_effect_context`
- `auxiliary_rollback_context`
- `authority_boundary_context`
- `absence_marker`

Trial, effect, rollback, and authority-posture evidence may be relevant to
outcome review, but none of them is sufficient by itself as outcome success.

## Outcome Horizon Rows

`V73-A` should make baseline, intervention, and evaluation horizons
first-class rows inside the starter payload:

- `horizon_ref`
- `candidate_ref`
- `horizon_kind`
- `covered_surface_refs`
- `source_refs`
- `coverage_posture`
- `limitation_note`

Minimum `horizon_kind`:

- `baseline`
- `intervention`
- `evaluation`

Minimum `coverage_posture`:

- `covered`
- `partially_covered`
- `missing_expected_source`
- `not_applicable`
- `future_family_only`

Every eligible outcome-review entry should reference one baseline horizon, one
intervention horizon, and one evaluation horizon. Missing baseline or
evaluation material should be represented through explicit absence evidence
rows and horizon coverage posture, not source-free notes.

## Outcome Review Entry

The outcome review entry should record:

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

Minimum entry postures:

- `eligible_for_outcome_review`
- `blocked_by_missing_trial_evidence`
- `blocked_by_rollback_gap`
- `blocked_by_effect_gap`
- `blocked_by_authority_boundary`
- `future_family_only`
- `rejected_out_of_scope`

Only rows with released `V72-C` handoff posture `ready_for_v73_review` may be
eligible for outcome review.

Conditional validation:

- if `entry_posture = eligible_for_outcome_review`, then source handoff refs,
  trial refs, effect refs, rollback refs, authority-posture refs,
  outcome-source refs, baseline / intervention / evaluation horizon refs, and
  guardrail refs must be non-empty;
- if `entry_posture` is blocked, then blocker refs or explicit absence
  evidence rows must identify the blocker;
- if `entry_posture = future_family_only`, then the entry must not carry a
  positive outcome-review horizon.

## Boundary Guardrail

The guardrail should record:

- `guardrail_ref`
- `candidate_ref`
- `entry_refs`
- `forbidden_downstream_roles`
- `boundary_posture`
- `required_later_authority`
- `limitation_note`

Minimum forbidden downstream roles:

- `promotion_authority`
- `demotion_authority`
- `adoption_authority`
- `commit_release_authority`
- `merge_authority`
- `released_truth`
- `product_authorization`
- `runtime_permission`
- `dispatch_authority`
- `external_contest_authority`

Minimum required later authority posture:

- `human_ratification_required`
- `maintainer_release_authority_required`
- `product_authority_required`
- `runtime_authority_required`
- `dispatch_authority_required`
- `external_contest_authority_required`
- `none_selected_here`

`V73-A` may open an outcome-review entry. It must not judge or recommend the
outcome.

## Mandatory Reject Cases

`V73-A` should reject:

- outcome-review entry with no released `V72-C` handoff refs;
- outcome-review entry for candidate absent from `V72-C`;
- outcome-review entry for a handoff that is not `ready_for_v73_review`;
- conceptual-diff candidate blocked by dissent treated as outcome-ready;
- typed-adjudication product wedge routed to outcome review as integrated
  product work;
- source-free missing baseline or evaluation evidence;
- eligible outcome-review entry without baseline / intervention / evaluation
  horizon rows;
- trial evidence treated as outcome success;
- effect evidence treated as outcome benefit without evaluation horizon;
- rollback posture treated as outcome success;
- guardrail with empty forbidden downstream roles;
- entry claiming promotion, demotion, adoption, release, product, runtime, or
  dispatch authority.

## Expected Fixture Coverage

Recommended fixture names:

- `repo_candidate_outcome_review_entry_v203_reference.json`
- `repo_outcome_evidence_source_index_v203_reference.json`
- `repo_outcome_review_boundary_guardrail_v203_reference.json`
- `repo_candidate_outcome_v203_reject_unknown_v72c_handoff.json`
- `repo_candidate_outcome_v203_reject_non_ready_handoff.json`
- `repo_candidate_outcome_v203_reject_product_wedge_to_outcome_review.json`
- `repo_candidate_outcome_v203_reject_conceptual_diff_dissent_as_ready.json`
- `repo_candidate_outcome_v203_reject_missing_baseline_source_free.json`
- `repo_candidate_outcome_v203_reject_eligible_entry_without_horizons.json`
- `repo_candidate_outcome_v203_reject_trial_as_outcome_success.json`
- `repo_candidate_outcome_v203_reject_effect_as_benefit_without_horizon.json`
- `repo_candidate_outcome_v203_reject_guardrail_allows_promotion.json`
- `repo_candidate_outcome_v203_reject_entry_claims_release.json`

The future `vNext+203` number is provisional until the active starter lock is
drafted.

## Closeout Expectation

`V73-A` should leave the repo with source-bound outcome-review entry substrate
for exactly the candidates admitted by released `V72-C` handoffs. It should not
leave the repo with outcome judgment, promotion, release, product, runtime, or
dispatch authority.
