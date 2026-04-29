# Draft ADEU Operator Projection V74C Implementation Mapping v0

Status: support note for the planned `V74-C` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V74-C`
should add decision visibility contracts, ratification-review workbench projection,
post-projection handoff, and family closeout alignment after `V74-B` has
closed.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v64.md`
- `docs/ARCHITECTURE_ADEU_OPERATOR_PROJECTION_FAMILY_v0.md`
- `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74B_IMPLEMENTATION_MAPPING_v0.md`

## Workflow Posture

This `V74-C` support spec remains below lock authority until `V74-B` has merged
and lean-closed, and a future canonical starter trio selects `V74-C`.

`V74-C` should extend released `V74-A` and `V74-B` rows. It should not create a
parallel projection universe.

`V74-C` may define decision visibility, workbench projection, and handoff
posture. It must not implement a live product workbench, ratify a candidate,
execute a command, dispatch workers, open or update PRs, merge, release, or
authorize external contest participation.

## Candidate New Surfaces

`V74-C` should select:

- `repo_decision_visibility_contract@1`
- `repo_ratification_review_workbench_projection@1`
- `repo_post_projection_handoff@1`
- `repo_operator_projection_family_closeout_alignment@1`

These surfaces should make projected decision state contractually visible and
prepare later-family handoff without doing `V75`.

## Decision Visibility Contract

The decision visibility contract should record:

- `visibility_contract_ref`
- `case_view_refs`
- `typed_case_refs`
- `exception_refs`
- `visible_decision_state`
- `visible_source_refs`
- `visible_exception_refs`
- `visibility_obligation_kinds`
- `non_derivable_authority_kinds`
- `operator_action_postures`
- `required_later_authority`
- `required_later_authority_rows`
- `contract_posture`
- `limitation_note`

Minimum contract posture:

- `visibility_contract_ready`
- `blocked_by_missing_case_view`
- `blocked_by_hidden_required_exception`
- `blocked_by_authority_boundary`
- `future_family_only`
- `rejected_out_of_scope`

Minimum visibility obligation kind:

- `no_hidden_source_status`
- `no_hidden_authority_boundary`
- `no_hidden_regression`
- `no_hidden_dissent`
- `no_hidden_product_authority_gap`
- `no_hidden_runtime_or_dispatch_gap`

Minimum non-derivable authority kind:

- `release_truth`
- `product_selection`
- `runtime_permission`
- `dispatch_authority`

Minimum required later authority row:

- `authority_requirement_ref`
- `authority_kind`
- `authority_source_refs`
- `source_presence_posture`
- `required_before_action`
- `limitation_note`

The contract should make visible what is visible, what must not be hidden, and
what cannot be derived from the projection.

## Ratification Review Workbench Projection

The ratification review workbench projection should record:

- `workbench_projection_ref`
- `visibility_contract_refs`
- `case_view_refs`
- `candidate_refs`
- `ratification_refs`
- `recommendation_refs`
- `exception_refs`
- `permitted_operator_action_postures`
- `forbidden_operator_action_postures`
- `required_later_authority`
- `required_later_authority_rows`
- `workbench_projection_posture`
- `limitation_note`

Minimum workbench projection posture:

- `projection_ready_for_operator_review`
- `blocked_by_missing_visibility_contract`
- `blocked_by_unresolved_exception`
- `blocked_by_authority_boundary`
- `future_family_only`
- `rejected_out_of_scope`

Permitted operator action postures should remain limited to review and
visibility actions:

- `inspect_only`
- `acknowledge_only`
- `request_later_review_only`
- `annotate_source_gap_only`
- `export_support_report_only`
- `no_operator_action_selected`

Forbidden operator action postures should include:

- `ratify_now`
- `adopt_now`
- `implement_now`
- `commit_now`
- `merge_now`
- `release_now`
- `authorize_product_now`
- `grant_runtime_permission_now`
- `dispatch_now`
- `enter_external_contest_now`

The workbench projection may show that later ratification or dispatch review is
needed. It cannot perform that review.

## Post-Projection Handoff

The handoff should record:

- `handoff_ref`
- `visibility_contract_refs`
- `workbench_projection_refs`
- `candidate_refs`
- `handoff_target`
- `handoff_posture`
- `carried_exception_refs`
- `required_later_authority`
- `non_dispatch_guardrail`
- `limitation_note`

Minimum handoff target:

- `v75_dispatch_review`
- `future_product_review`
- `future_ratification_or_policy_review`
- `future_family_review`
- `deferred_no_selection`

Minimum handoff posture:

- `ready_for_later_review`
- `blocked_by_unresolved_exception`
- `blocked_by_authority_boundary`
- `deferred_to_future_family`
- `rejected_out_of_scope`

`handoff_target = v75_dispatch_review` is only a request for later review. It
is not dispatch, worker assignment, runtime permission, or execution.

Hard `V75` handoff invariant:

- if `handoff_target = v75_dispatch_review`, then `non_dispatch_guardrail` must
  be non-empty;
- if `handoff_target = v75_dispatch_review`, then required later authority must
  include a dispatch authority requirement;
- if carried exception refs include blocking exceptions, then
  `handoff_posture` must not be `ready_for_later_review`.

## Family Closeout Alignment

The family closeout alignment should record:

- `family`
- `closed_by_arc`
- `closed_slice_ladder`
- `shipped_record_shapes`
- `consumed_source_families`
- `future_family_authority`
- `unselected_future_surfaces`
- `operator_projection_authority_boundary`
- `limitation_note`

The family closeout may say that `V74` is closed as operator projection. It
must not say that product, runtime, dispatch, release, or external contest
authority has been granted.

## Mandatory Reject Cases

`V74-C` should reject:

- visibility contract without released `V74-A` case refs;
- visibility contract that hides known source status, authority boundary,
  dissent, regression, or product/runtime/dispatch authority gap;
- visibility contract that mixes visibility obligations with non-derivable
  authority states in one untyped list;
- visibility contract with free-floating later-authority claims that do not
  resolve through authority requirement rows;
- workbench projection without a visibility contract;
- workbench projection that permits ratify, adopt, implement, commit, merge,
  release, product authorization, runtime permission, dispatch, or external
  contest action;
- post-projection handoff that performs `V75` dispatch rather than requesting
  later review;
- `V75` handoff without non-dispatch guardrail or dispatch authority
  requirement;
- handoff with unresolved exceptions marked ready without carrying them
  forward;
- product wedge projected as product-selected;
- family closeout claiming product launch, release, runtime permission,
  dispatch, or external contest participation;
- family closeout that creates a new `DRAFT_NEXT_ARC_OPTIONS_v*` precedent for
  sub-lanes.

## Expected First Fixture

The first `V74-C` reference fixture should include:

- one decision visibility contract over released `V74-A` / `V74-B` case rows;
- one ratification-review workbench projection that permits inspect / request-later-
  review actions only;
- one post-projection handoff requesting future `V75` review or deferred future
  review without dispatch;
- one family closeout alignment row listing `V74-A`, `V74-B`, and `V74-C`;
- zero product launch, runtime permission, dispatch, release, external contest,
  or ratification action.

## Stop Gate Expectations

The future `V74-C` stop gate should require:

- schema exports for all `V74-C` surfaces;
- reference and reject fixture validation;
- package export tests;
- closeout consistency and semantic closeout lint;
- rejection of hidden decision-state, operator-action authority laundering, and
  dispatch laundering;
- closeout evidence that the family is closed as projection only.
