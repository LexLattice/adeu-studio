# Draft ADEU Dispatch Review V75B Implementation Mapping v0

Status: support note for the planned `V75-B` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V75-B`
should add worker role capacity profiles, multi-worker assignment plans, worker
IO contracts, worker tool-applicability matrix rows, and dispatch exception
registers after `V75-A` has closed.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v65.md`
- `docs/ARCHITECTURE_ADEU_DISPATCH_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75A_IMPLEMENTATION_MAPPING_v0.md`

## Workflow Posture

This `V75-B` support spec remains below lock authority until `V75-A` has
merged and lean-closed, and a future canonical starter trio selects `V75-B`.

`V75-B` should extend released `V75-A` dispatch-review request, dispatch source
index, and non-execution guardrail rows. It should not create a parallel
dispatch universe.

`V75-B` may plan worker / role / tool / IO posture. It must not assign
workers, run commands, open PRs, grant runtime permission, authorize products,
enter external contests, merge, release, or treat worker output as truth.

## Candidate New Surfaces

`V75-B` should select:

- `repo_worker_role_capacity_profile@1`
- `repo_multi_worker_assignment_plan@1`
- `repo_worker_io_contract@1`
- `repo_worker_tool_applicability_matrix@1`
- `repo_dispatch_exception_register@1`

These surfaces should describe orchestration planning without executing the
plan.

## Worker Role Capacity Profile

The role profile should record:

- `worker_role_ref`
- `role_kind`
- `capability_horizon`
- `allowed_input_kinds`
- `expected_output_kinds`
- `allowed_tool_ids`
- `tool_use_posture`
- `forbidden_action_kinds`
- `authority_boundary_refs`
- `limitation_note`

Minimum role kind:

- `source_index_worker`
- `evidence_review_worker`
- `adversarial_review_worker`
- `schema_validation_worker`
- `tool_run_worker`
- `reconciliation_worker`
- `operator_projection_worker`
- `external_branch_review_worker`

A worker role is a capability profile, not a worker authority grant.
`allowed_tool_ids` is an applicability cue, not permission to run tools.

Minimum tool-use posture:

- `applicability_record_only`
- `tool_use_requires_later_runtime_permission`
- `tool_use_not_authorized_by_v75`

## Multi-Worker Assignment Plan

The assignment plan should record:

- `assignment_plan_ref`
- `dispatch_request_refs`
- `worker_role_refs`
- `io_contract_refs`
- `tool_applicability_refs`
- `exception_refs`
- `assignment_plan_posture`
- `assignment_execution_posture`
- `non_execution_guardrail_refs`
- `limitation_note`

Minimum assignment plan posture:

- `plan_ready_for_review`
- `blocked_by_missing_role_profile`
- `blocked_by_missing_io_contract`
- `blocked_by_tool_applicability_gap`
- `blocked_by_unresolved_exception`
- `blocked_by_later_authority`
- `future_family_only`
- `rejected_out_of_scope`

`plan_ready_for_review` means ready for later review of the plan, not ready to
dispatch workers.

Minimum assignment execution posture:

- `no_execution_authorized`
- `review_plan_only`
- `blocked_pending_later_authority`

Reference rows should use `assignment_execution_posture =
no_execution_authorized`.

## Worker IO Contract

The IO contract should record:

- `io_contract_ref`
- `worker_role_refs`
- `input_source_refs`
- `input_claim_horizon`
- `expected_output_kind`
- `output_schema_ref`
- `output_authority_posture`
- `non_truth_guardrail`
- `limitation_note`

Minimum output authority posture:

- `output_for_review_only`
- `output_requires_reconciliation`
- `output_requires_adversarial_review`
- `output_requires_human_ratification`
- `output_not_truth`

An output contract can say what output shape would be expected. It cannot make
future output true, adopted, ratified, integrated, or released.

## Worker Tool Applicability Matrix

The tool matrix should record:

- `tool_matrix_ref`
- `worker_role_refs`
- `tool_id`
- `target_claim_refs`
- `target_namespace_kind`
- `claim_horizon`
- `applicability_posture`
- `observed_or_required_result_refs`
- `limitation_note`

Minimum applicability posture:

- `applicable_for_target_horizon`
- `blocked_by_missing_source`
- `blocked_by_missing_tool_evidence`
- `not_applicable_for_target_horizon`
- `requires_negative_control`
- `requires_human_review`
- `unknown_needs_review`

Tool applicability remains target-bound and horizon-bound. A tool pass must not
expand dispatch scope.

## Dispatch Exception Register

The exception register should record:

- `dispatch_exception_ref`
- `dispatch_request_refs`
- `assignment_plan_refs`
- `worker_role_refs`
- `io_contract_refs`
- `tool_matrix_refs`
- `exception_kind`
- `source_refs`
- `blocking_posture`
- `required_next_surface`
- `limitation_note`

Minimum exception kind:

- `missing_dispatch_source`
- `unresolved_projection_exception`
- `missing_role_profile`
- `missing_io_contract`
- `tool_applicability_gap`
- `required_later_authority_missing`
- `product_authority_gap`
- `runtime_authority_gap`
- `external_branch_boundary_gap`
- `worker_output_truth_gap`
- `unknown_needs_review`

Exceptions must remain visible. `V75-B` may classify a row as blocking,
warning-only, carried forward, or not applicable; it must not mark exceptions
resolved.

## Conditional Validation

`V75-B` validators should enforce:

- every assignment plan references released `V75-A` dispatch request rows;
- every assignment plan references non-execution guardrails;
- every worker role profile has forbidden action kinds;
- every worker role profile with `allowed_tool_ids` has `tool_use_posture`
  that keeps tool use non-executing;
- every IO contract has a non-truth guardrail;
- every tool matrix row is target-bound and horizon-bound;
- every assignment plan has `assignment_execution_posture =
  no_execution_authorized`;
- upstream exceptions are carried into the exception register or explicitly
  marked not applicable with source evidence;
- if `role_kind = external_branch_review_worker`, assignment plan posture must
  be blocked by later authority or future-family-only unless `V43` branch
  posture source refs are present;
- external contest work remains blocked unless `V43` branch posture exists;
- runtime command pressure remains blocked unless future runtime permission
  review is selected.

## Mandatory Reject Cases

`V75-B` should reject:

- assignment plan without released `V75-A` dispatch request refs;
- assignment plan treated as execution;
- role profile treated as permission;
- worker IO output treated as truth;
- tool applicability treated as global;
- assignment plan missing exception refs when upstream exceptions exist;
- plan missing required later authority refs;
- plan that assigns external contest work without `V43` branch posture;
- plan that includes command execution, PR creation, commit, merge, release, or
  product authorization;
- exception register that omits known source, authority, product, runtime, or
  external branch gaps;
- exception row marked resolved by `V75-B`.

## Expected First Fixture

The first `V75-B` reference fixture should include:

- one worker role capacity profile for a review-only role;
- one IO contract that marks output as review-only and not truth;
- one tool applicability row scoped to a bounded claim horizon;
- one assignment plan referencing released `V75-A` request and guardrail rows;
- one dispatch exception register carrying at least one authority or exception
  blocker forward;
- zero worker execution, command, runtime permission, product authorization,
  release, or external contest rows.

## Stop Gate Expectations

The future `V75-B` stop gate should require:

- schema exports for all `V75-B` surfaces;
- reference and reject fixture validation;
- package export tests;
- rejection of assignment-as-execution, role-as-permission, output-as-truth, and
  tool-as-global-scope laundering;
- closeout evidence that the slice remains orchestration planning only.
