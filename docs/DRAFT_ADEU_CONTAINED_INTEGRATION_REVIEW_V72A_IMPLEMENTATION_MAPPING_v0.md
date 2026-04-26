# Draft ADEU Contained Integration Review V72A Implementation Mapping v0

Status: support note for the planned `V72-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V72-A`
should add contained integration planning after `V71` has closed.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v62.md`
- `docs/ARCHITECTURE_ADEU_CONTAINED_INTEGRATION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CONTAINED_INTEGRATION_REVIEW_V72_IMPLEMENTATION_MAPPING_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_COMBINED_DOGFOOD_TEST_v0.md`
- `docs/support/arc_series_mapping/REVIEW_GPTPRO_CONTAINED_INTEGRATION_REVIEW_V72_PLANNING_v0.md`

## Workflow Posture

This `V72-A` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not an active implementation lock.

When `V72-A` becomes active, it should receive its own canonical starter trio
after review patches are integrated. It should consume released `V71-C`
amendment-scope, post-ratification handoff, and family closeout alignment rows
as source-bound substrate.

The active `V72-A` implementation may add its own schema, model, validator,
fixture, and test files under the future lock. That is distinct from candidate
contained-integration trial work. `V72-A` must not record a candidate trial,
local write, accepted diff, commit, merge, release, product, runtime, or
dispatch action.

## Candidate New Surfaces

`V72-A` should select:

- `repo_contained_integration_candidate_plan@1`
- `repo_integration_target_boundary@1`
- `repo_integration_non_release_guardrail@1`

These surfaces should translate released `V71-C` ready handoffs into bounded
integration planning posture without executing a trial or editing files.

## Source Binding

`V72-A` should define explicit integration source rows over:

- `artifacts/agent_harness/v199/evidence_inputs/v71_family_closeout_alignment_v199.json`
- `artifacts/agent_harness/v199/evidence_inputs/v71c_candidate_ratification_closeout_evidence_v199.json`
- `apps/api/fixtures/repo_description/vnext_plus199/repo_ratification_amendment_scope_boundary_v199_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus199/repo_post_ratification_handoff_v199_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus199/repo_candidate_ratification_family_closeout_alignment_v199_reference.json`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_COMBINED_DOGFOOD_TEST_v0.json`

Absence should be represented as source posture, not as prose memory.

Preferred starter shape: embed `integration_source_rows` inside
`repo_contained_integration_candidate_plan@1`. Target-boundary and guardrail
`source_refs` should resolve through those rows or through explicit absence
rows.

## Containment Plan

The containment plan should record:

- `integration_source_rows`
- `plan_ref`
- `candidate_ref`
- `source_handoff_refs`
- `ratification_refs`
- `amendment_scope_refs`
- `target_boundary_refs`
- `containment_plan_posture`
- `required_trial_posture`
- `rollback_requirement`
- `odeu_lanes`
- `guardrail_refs`
- `limitation_note`

Minimum required trial posture:

- `no_trial_selected_in_v72a`
- `dry_run_required_later`
- `local_trial_required_later`
- `trial_blocked_until_source_gap_resolved`
- `trial_blocked_until_dissent_resolved`
- `future_family_trial_only`

Minimum plan postures:

- `eligible_for_containment_planning`
- `blocked_by_dissent`
- `blocked_by_evidence_gap`
- `blocked_by_scope_boundary`
- `future_family_only`
- `rejected_out_of_scope`

Only rows with released `V71-C` handoff posture `ready_for_v72_review` may be
eligible for containment planning.

Conditional validation:

- if `containment_plan_posture = eligible_for_containment_planning`, then
  source handoff refs, ratification refs, amendment-scope refs, target-boundary
  refs, guardrail refs, and rollback requirement must be non-empty;
- if `containment_plan_posture` is blocked by dissent, evidence gap, or scope
  boundary, then blocker refs or `limitation_note` must identify the blocker
  and `required_trial_posture` must not imply a recorded trial;
- if `containment_plan_posture = future_family_only`, then target-boundary refs
  may only reference `no_target_boundary` / `target_absent` rows and
  `required_trial_posture` must be `future_family_trial_only` or
  `no_trial_selected_in_v72a`.

## Target Boundary

The target boundary should record:

- `target_boundary_ref`
- `candidate_ref`
- `target_boundary_kind`
- `target_resolution_kind`
- `target_refs`
- `target_posture`
- `allowed_change_kinds`
- `forbidden_change_kinds`
- `source_refs`
- `limitation_note`

Minimum boundary kinds:

- `docs_support_surface`
- `schema_surface`
- `validator_surface`
- `fixture_surface`
- `test_surface`
- `workflow_surface`
- `package_surface`
- `no_target_boundary`

Target refs must be concrete. Globs may appear only as discovery instructions in
derivation records, not as target evidence.

Minimum target resolution kinds:

- `concrete_file_ref`
- `concrete_schema_ref`
- `concrete_fixture_ref`
- `concrete_test_ref`
- `concrete_doc_ref`
- `bounded_package_surface_with_child_refs`
- `no_target_boundary`

If `target_boundary_kind = package_surface`, then
`target_resolution_kind = bounded_package_surface_with_child_refs` and
`target_refs` must include concrete child refs or an explicit limitation note.
If `target_boundary_kind != no_target_boundary`, then `target_refs` and
`forbidden_change_kinds` must be non-empty.

## Non-Release Guardrail

The guardrail should record:

- `guardrail_ref`
- `candidate_ref`
- `plan_refs`
- `forbidden_downstream_roles`
- `non_release_posture`
- `required_later_authority`
- `limitation_note`

Minimum forbidden downstream roles:

- `implementation_task`
- `commit_release_authority`
- `merge_authority`
- `released_truth`
- `product_authorization`
- `runtime_permission`
- `dispatch_authority`
- `external_contest_authority`

`V72-A` may plan a later trial surface. It must not perform the trial.

## Mandatory Reject Cases

`V72-A` should reject:

- containment plan with no released `V71-C` handoff refs;
- containment plan for candidate absent from `V71-C`;
- containment plan for a handoff that is not `ready_for_v72_review`;
- conceptual-diff candidate deferred with dissent treated as ready;
- typed-adjudication product wedge routed to contained integration;
- target boundary with a glob as target ref;
- package-surface target boundary without concrete child refs or explicit
  limitation;
- target boundary with no forbidden change kinds;
- guardrail with empty forbidden downstream roles;
- eligible containment plan with no rollback requirement;
- blocked containment plan with no blocker refs and no blocker limitation note;
- future-family-only plan with a concrete integration target;
- plan claiming trial execution, local write, commit, merge, release, product,
  runtime, or dispatch authority.

## Expected Fixture Coverage

Recommended fixture names:

- `repo_contained_integration_candidate_plan_v200_reference.json`
- `repo_integration_target_boundary_v200_reference.json`
- `repo_integration_non_release_guardrail_v200_reference.json`
- `repo_contained_integration_v200_reject_unknown_v71c_handoff.json`
- `repo_contained_integration_v200_reject_non_ready_handoff.json`
- `repo_contained_integration_v200_reject_product_wedge_to_integration.json`
- `repo_contained_integration_v200_reject_deferred_dissent_as_ready.json`
- `repo_contained_integration_v200_reject_glob_target_boundary.json`
- `repo_contained_integration_v200_reject_package_surface_without_child_refs.json`
- `repo_contained_integration_v200_reject_eligible_without_rollback_requirement.json`
- `repo_contained_integration_v200_reject_future_family_with_target_boundary.json`
- `repo_contained_integration_v200_reject_guardrail_allows_release.json`
- `repo_contained_integration_v200_reject_trial_executed_in_v72a.json`

The future `vNext+200` number is provisional until the active starter lock is
drafted.

## Closeout Expectation

`V72-A` should leave the repo with source-bound containment planning substrate
for exactly the candidates admitted by `V71-C`. It should not leave the repo
with trial execution, implementation, release, product, runtime, or dispatch
authority.
