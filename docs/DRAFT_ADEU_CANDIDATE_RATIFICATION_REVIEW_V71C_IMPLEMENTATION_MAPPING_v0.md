# Draft ADEU Candidate Ratification Review V71C Implementation Mapping v0

Status: support note for the planned `V71-C` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V71-C`
should harden amendment scope and prepare post-ratification handoff after
`V71-A` and `V71-B` have shipped.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v61.md`
- `docs/ARCHITECTURE_ADEU_CANDIDATE_RATIFICATION_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_CANDIDATE_RATIFICATION_REVIEW_V71B_IMPLEMENTATION_MAPPING_v0.md`

## Workflow Posture

This `V71-C` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not an active implementation lock.

When `V71-C` becomes active, it should receive its own canonical starter trio
after `V71-B` is merged and lean-closed. It should close the family only after
proving that ratification remains non-integrating and non-releasing.

## Candidate New Surfaces

`V71-C` should select:

- `repo_ratification_amendment_scope_boundary@1`
- `repo_post_ratification_handoff@1`

These surfaces should translate released `V71-B` outcomes into bounded later
review posture without changing their authority posture.

## Amendment Scope Boundary

The amendment scope boundary should record:

- `amendment_scope_ref`
- `candidate_ref`
- `ratification_refs`
- `settlement_refs`
- `allowed_amendment_scope`
- `forbidden_downstream_roles`
- `allowed_next_review_surfaces`
- `scope_limitation_note`
- `non_release_guardrail`

Minimum allowed amendment scope:

- `docs_or_support_only`
- `schema_review_candidate`
- `validator_review_candidate`
- `fixture_review_candidate`
- `workflow_review_candidate`
- `future_family_only`
- `no_amendment_scope`

An amendment scope is a boundary for later review. It is not permission to edit
files, integrate code, merge, release, productize, or dispatch.

## Post-Ratification Handoff

The post-ratification handoff should record:

- `handoff_ref`
- `candidate_ref`
- `ratification_refs`
- `amendment_scope_refs`
- `handoff_target`
- `handoff_posture`
- `required_next_surface`
- `carried_forward_dissent_refs`
- `carried_forward_gap_refs`
- `non_integration_guardrail`

Minimum handoff targets:

- `v72_contained_integration_review`
- `future_family_review`
- `deferred_no_selection`

Minimum handoff posture:

- `ready_for_v72_review`
- `blocked_by_scope_boundary`
- `blocked_by_dissent`
- `blocked_by_evidence_gap`
- `deferred_to_future_family`
- `rejected_out_of_scope`

The handoff target may request `V72` review. It must not perform `V72`
integration.

`required_next_surface` should be narrower than `handoff_target`. For example,
`handoff_target = v72_contained_integration_review` can pair with
`required_next_surface = v72_candidate_containment_planning`. This records the
next obligation without pretending `V71-C` already knows the implementation
slice.

## Family Closeout Alignment

`V71-C` should emit a family closeout alignment artifact analogous to the `V68`,
`V69`, and `V70` family closeout records. The alignment should list:

- closed slices;
- emitted surfaces;
- ratified candidates and their bounded horizon;
- rejected candidates;
- deferred candidates;
- future-family-routed candidates;
- amendment-scope boundaries;
- post-ratification handoff posture;
- non-authority guardrails;
- future families still unselected.

## Mandatory Reject Cases

`V71-C` should reject:

- amendment scope row with no ratification refs;
- post-ratification handoff with no ratification refs;
- rejected or deferred candidate routed to `V72` as ready;
- unresolved dissent omitted from handoff;
- amendment scope allowing implementation, merge, release, product, runtime, or
  dispatch;
- `v72_contained_integration_review` handoff without non-integration guardrail;
- `ready_for_v72_review` handoff with blocking dissent or evidence gaps;
- product wedge routed to `V72` integration;
- family closeout claiming implementation, release, product authorization, or
  dispatch.

## Expected Fixture Coverage

Recommended fixture names:

- `repo_ratification_amendment_scope_boundary_v199_reference.json`
- `repo_post_ratification_handoff_v199_reference.json`
- `repo_candidate_ratification_v199_reject_scope_without_ratification_ref.json`
- `repo_candidate_ratification_v199_reject_handoff_without_ratification_ref.json`
- `repo_candidate_ratification_v199_reject_rejected_candidate_to_v72.json`
- `repo_candidate_ratification_v199_reject_dissent_omitted.json`
- `repo_candidate_ratification_v199_reject_scope_allows_release.json`
- `repo_candidate_ratification_v199_reject_v72_integration_performed.json`
- `repo_candidate_ratification_v199_reject_product_wedge_to_v72.json`
- `repo_candidate_ratification_v199_reject_family_closeout_claims_release.json`

The future `vNext+199` number is provisional until the active starter lock is
drafted.

## Family Closeout Expectation

`V71-C` should leave the repo ready to draft `V72` with a typed set of ratified,
rejected, deferred, and future-family-routed candidates plus explicit amendment
scope. The closeout should make clear that `V71` produced ratification-review
machinery, not implementation or release.
