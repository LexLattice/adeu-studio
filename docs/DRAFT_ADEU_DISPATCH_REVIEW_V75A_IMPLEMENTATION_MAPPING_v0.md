# Draft ADEU Dispatch Review V75A Implementation Mapping v0

Status: support note for the planned `V75-A` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V75-A`
should add dispatch-review request rows, dispatch source indexing, and
non-execution guardrails after `V74` has closed.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v65.md`
- `docs/ARCHITECTURE_ADEU_DISPATCH_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_COMBINED_DOGFOOD_TEST_v0.md`

## Workflow Posture

This `V75-A` support spec is part of the early `A` / `B` / `C` support-spec
bundle for joint review. It is not an active implementation lock.

When `V75-A` becomes active, it should receive its own canonical starter trio
after review patches are integrated. It should consume released `V74-C`
decision visibility contract, ratification-review workbench projection,
post-projection handoff, and family closeout alignment rows as source-bound
substrate.

The active `V75-A` implementation may add its own schema, model, validator,
fixture, and test files under the future lock. That is distinct from worker
assignment, command execution, runtime permission, product authorization,
release, or external contest implementation.

## Candidate New Surfaces

`V75-A` should select:

- `repo_dispatch_review_request@1`
- `repo_dispatch_source_index@1`
- `repo_dispatch_non_execution_guardrail@1`

These surfaces should translate released `V74-C` post-projection handoff and
visibility substrate into bounded dispatch-review posture without executing
dispatch.

## Source Binding

`V75-A` should define explicit dispatch source rows over:

- `artifacts/agent_harness/v208/evidence_inputs/v74_family_closeout_alignment_v208.json`
- `artifacts/agent_harness/v208/evidence_inputs/v74c_operator_projection_closeout_evidence_v208.json`
- `apps/api/fixtures/repo_description/vnext_plus208/repo_decision_visibility_contract_v208_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus208/repo_ratification_review_workbench_projection_v208_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus208/repo_post_projection_handoff_v208_reference.json`
- `apps/api/fixtures/repo_description/vnext_plus208/repo_operator_projection_family_closeout_alignment_v208_reference.json`
- `docs/DRAFT_ADEU_OPERATOR_PROJECTION_V74_FAMILY_CLOSEOUT_v0.md`
- `docs/support/arc_series_mapping/V68_V69_V70_V71_V72_V73_V74_COMBINED_DOGFOOD_TEST_v0.json`
- `docs/DRAFT_MULTI_ARC_ROADMAP_POST_V74_v0.md`

Absence should be represented as source posture, not as prose memory.

## Dispatch Source Index

The source index should record:

- `source_ref`
- `source_kind`
- `authority_layer`
- `source_status`
- `source_presence_posture`
- `dispatch_source_role`
- `source_horizon`
- `limitation_note`

Minimum dispatch source role:

- `v74_post_projection_handoff_source`
- `visibility_contract_source`
- `workbench_projection_source`
- `exception_visibility_source`
- `required_later_authority_source`
- `non_dispatch_guardrail_source`
- `combined_dogfood_source`
- `family_closeout_source`
- `absence_marker`

Every dispatch-review request, handoff ref, visibility contract ref, workbench
projection ref, carried upstream exception ref, required later-authority ref,
and guardrail row should resolve through concrete source rows or explicit
absence rows.

Roadmap and support-review sources may contextualize `V75-A`, but they cannot
make a dispatch-review request eligible by themselves. Eligibility requires
concrete released `V74-C` substrate:

- at least one source row with
  `dispatch_source_role = v74_post_projection_handoff_source`;
- at least one source row with
  `dispatch_source_role = visibility_contract_source`;
- at least one source row with
  `dispatch_source_role = workbench_projection_source`.

## Dispatch-Review Request

The request should record:

- `dispatch_request_ref`
- `candidate_ref`
- `case_view_refs`
- `visibility_contract_refs`
- `workbench_projection_refs`
- `post_projection_handoff_refs`
- `required_later_authority_refs`
- `required_later_authority_rows`
- `carried_upstream_exception_refs`
- `carried_exception_origin`
- `dispatch_review_posture`
- `requested_orchestration_horizon`
- `odeu_lanes`
- `guardrail_refs`
- `limitation_note`

Minimum dispatch-review posture:

- `eligible_for_dispatch_review`
- `blocked_by_missing_projection_source`
- `blocked_by_unresolved_exception`
- `blocked_by_required_later_authority`
- `blocked_by_product_authority_gap`
- `blocked_by_runtime_authority_gap`
- `blocked_by_external_branch_boundary`
- `future_family_only`
- `rejected_out_of_scope`

Minimum requested orchestration horizon:

- `review_only_no_assignment`
- `role_planning_later`
- `multi_worker_planning_later`
- `tool_applicability_review_later`
- `reconciliation_planning_later`
- `runtime_permission_review_later`
- `product_review_later`
- `external_branch_review_later`
- `future_family_only`

Minimum carried exception origin:

- `v74_exception_visibility`
- `v74_visibility_contract`
- `v74_post_projection_handoff`
- `absence_marker`

`carried_upstream_exception_refs` point to upstream visible exceptions or
exception-carrying rows from `V74-C`. Native dispatch exceptions are introduced
later by `V75-B`; `V75-A` must not pretend the `V75-B` exception register
already exists.

Required later-authority rows should record:

- `authority_requirement_ref`
- `candidate_ref`
- `authority_kind`
- `required_before_surface`
- `source_refs`
- `source_presence_posture`
- `authority_gap_posture`
- `limitation_note`

Minimum authority kind:

- `runtime_permission`
- `product_authorization`
- `release_authority`
- `external_branch_activation`
- `dispatch_execution_authority`
- `human_or_maintainer_review`
- `recursive_policy_authority`

`eligible_for_dispatch_review` means eligible for later review, not eligible
for dispatch execution.

Conditional validation:

- if `dispatch_review_posture = eligible_for_dispatch_review`, then
  post-projection handoff refs, visibility contract refs, workbench projection
  refs, source refs, and guardrail refs must be non-empty;
- if `dispatch_review_posture` is blocked, then carried exception refs,
  required later authority refs, source rows, or limitation note must identify
  the blocker;
- if carried exceptions include product, runtime, release, or external branch
  authority gaps, then request posture must be blocked or future-family-only
  unless a later selected family handles that gap;
- if requested horizon includes runtime, product, or external branch review,
  the request must carry a required-later-authority ref for that horizon;
- support or roadmap sources may not be the only eligibility sources;
- no `V75-A` request may include worker assignment refs, command refs, PR refs,
  merge refs, release refs, product authorization refs, or external submission
  refs.

## Non-Execution Guardrail

The guardrail should record:

- `guardrail_ref`
- `candidate_ref`
- `dispatch_request_refs`
- `forbidden_action_kinds`
- `allowed_next_review_surfaces`
- `non_execution_guardrail`
- `limitation_note`

Minimum forbidden action kind:

- `assign_worker_now`
- `run_command_now`
- `open_pr_now`
- `commit_now`
- `merge_now`
- `release_now`
- `authorize_product_now`
- `grant_runtime_permission_now`
- `enter_external_contest_now`
- `self_approve_now`

Minimum allowed next review surface:

- `v75b_orchestration_planning_review`
- `future_runtime_permission_review`
- `future_product_review`
- `future_external_branch_review`
- `future_experiment_review`
- `future_family_review`
- `deferred_no_selection`

`V75-A` may make dispatch-review pressure visible. It must not make the
pressure executable.

## Mandatory Reject Cases

`V75-A` should reject:

- dispatch request with unknown candidate ref;
- dispatch request without concrete source refs or explicit absence rows;
- dispatch request without released `V74-C` post-projection handoff refs;
- dispatch request that assigns workers;
- dispatch request that carries a command to run;
- dispatch request that treats a workbench action as authorization;
- dispatch request that routes product pressure into dispatch without
  product-authority blocker;
- dispatch request that routes runtime command pressure without runtime
  authority blocker;
- dispatch request that routes external contest pressure without `V43` branch
  posture;
- guardrail with empty forbidden action kinds;
- guardrail that omits non-execution statement;
- transcript, operator desire, or model suggestion treated as dispatch source
  truth;
- request that claims runtime permission, product authorization, release,
  external contest participation, or recursive policy amendment.

## Expected First Fixture

The first reference fixture should include:

- one dispatch source index with concrete `V74-C` fixture, closeout, and dogfood
  refs;
- one dispatch-review request for the self-evidencing workflow-type emergence
  candidate sourced from released `V74-C` handoff rows;
- one blocked or future-family-only product or runtime pressure row proving
  dispatch-adjacent pressure remains visible without becoming eligible;
- one non-execution guardrail shared by the request;
- zero worker assignment, command, runtime, product, release, external contest,
  or recursive policy amendment rows.

## Stop Gate Expectations

The future `vNext+209` stop gate should require:

- schema exports for all three `V75-A` surfaces;
- reference and reject fixture validation;
- package export tests;
- rejection of dispatch / runtime / product / release / external authority
  laundering;
- closeout evidence that the slice remains dispatch-review-only.
