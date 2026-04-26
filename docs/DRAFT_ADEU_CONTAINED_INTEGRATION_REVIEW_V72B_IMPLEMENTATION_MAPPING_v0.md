# Draft ADEU Contained Integration Review V72B Implementation Mapping v0

Status: support note for the planned `V72-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V72-B`
should add contained trial, effect-surface, and rollback-readiness records after
`V72-A` has shipped.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v62.md`
- `docs/ARCHITECTURE_ADEU_CONTAINED_INTEGRATION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CONTAINED_INTEGRATION_REVIEW_V72_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CONTAINED_INTEGRATION_REVIEW_V72A_IMPLEMENTATION_MAPPING_v0.md`

## Workflow Posture

This `V72-B` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not an active implementation lock.

When `V72-B` becomes active, it should receive its own canonical starter trio
after `V72-A` is merged and lean-closed. It should consume released `V72-A`
containment-plan, target-boundary, and non-release-guardrail rows.

## Candidate New Surfaces

`V72-B` should select:

- `repo_contained_integration_trial_record@1`
- `repo_integration_effect_surface_register@1`
- `repo_integration_rollback_readiness@1`

These surfaces should extend `V72-A` rows rather than creating a parallel
integration universe.

## Trial Record

The trial record should record:

- `trial_ref`
- `candidate_ref`
- `plan_refs`
- `target_boundary_refs`
- `trial_posture`
- `trial_diff_posture`
- `active_lock_refs`
- `trial_evidence_refs`
- `observed_effect_refs`
- `rollback_readiness_refs`
- `non_release_guardrail_refs`
- `limitation_note`

Minimum trial posture:

- `planned_not_executed`
- `dry_run_recorded`
- `local_trial_recorded`
- `trial_blocked`
- `trial_reverted`
- `trial_ready_for_outcome_review`

`local_trial_recorded` is not accepted repository truth. It is a record that a
bounded trial happened inside the active lock scope.

Minimum trial diff posture:

- `no_diff_recorded`
- `proposed_diff_recorded`
- `local_diff_observed`
- `diff_reverted`
- `diff_accepted_for_review_only`
- `diff_rejected`
- `diff_requires_later_authority`

`diff_accepted_for_review_only` is not commit, merge, release, or product
authority.

## Effect Surface Register

The effect surface register should record:

- `effect_ref`
- `candidate_ref`
- `trial_refs`
- `target_boundary_refs`
- `effect_surface_kind`
- `effect_posture`
- `observed_artifact_refs`
- `test_refs`
- `limitation_note`

Minimum effect surface kind:

- `docs_effect`
- `schema_effect`
- `validator_effect`
- `fixture_effect`
- `test_effect`
- `workflow_effect`
- `package_effect`
- `unknown_effect`

Minimum effect posture:

- `no_effect_observed`
- `effect_expected_not_checked`
- `effect_observed`
- `effect_blocked`
- `effect_reverted`
- `effect_requires_later_review`

## Rollback Readiness

The rollback readiness surface should record:

- `rollback_ref`
- `candidate_ref`
- `trial_refs`
- `effect_refs`
- `rollback_posture`
- `rollback_evidence_refs`
- `required_before_next_surface`
- `limitation_note`

Minimum rollback posture:

- `rollback_not_required_for_docs_only`
- `rollback_plan_required`
- `rollback_plan_present`
- `rollback_verified`
- `rollback_blocked`
- `rollback_not_applicable`

Rollback readiness must not be inferred from confidence prose. It must point to
explicit evidence or carry an explicit blocked / required posture.

## Mandatory Reject Cases

`V72-B` should reject:

- trial row with unknown `V72-A` plan refs;
- trial row whose candidate differs from referenced plan rows;
- local trial recorded without target boundary refs;
- local trial recorded without active-lock/source refs, trial evidence refs, or
  non-release guardrail refs;
- trial marked ready for outcome review while rollback is blocked;
- trial marked ready for outcome review while effect gaps are neither carried
  forward nor explicitly absent;
- effect row with unknown trial refs;
- rollback row with unknown effect refs;
- rollback marked verified without rollback evidence refs;
- trial row claiming commit, merge, release, product, runtime, or dispatch
  authority;
- any `V72-B` row that performs `V73` outcome review.

## Expected Fixture Coverage

Recommended fixture names:

- `repo_contained_integration_trial_record_v201_reference.json`
- `repo_integration_effect_surface_register_v201_reference.json`
- `repo_integration_rollback_readiness_v201_reference.json`
- `repo_contained_integration_v201_reject_unknown_plan_ref.json`
- `repo_contained_integration_v201_reject_candidate_mismatch.json`
- `repo_contained_integration_v201_reject_trial_without_target_boundary.json`
- `repo_contained_integration_v201_reject_local_trial_without_active_lock_ref.json`
- `repo_contained_integration_v201_reject_diff_accepted_as_commit.json`
- `repo_contained_integration_v201_reject_ready_with_blocked_rollback.json`
- `repo_contained_integration_v201_reject_ready_with_uncarried_effect_gap.json`
- `repo_contained_integration_v201_reject_unknown_effect_ref.json`
- `repo_contained_integration_v201_reject_rollback_verified_without_evidence.json`
- `repo_contained_integration_v201_reject_trial_claims_release.json`

The future `vNext+201` number is provisional until the active starter lock is
drafted.

## Closeout Expectation

`V72-B` should leave the repo with trial, effect, and rollback readiness records
over released `V72-A` plans. It should not leave the repo with commit, merge,
release, product, runtime, dispatch, or outcome-review authority.
