# Draft ADEU Dispatch Review V75C Implementation Mapping v0

Status: support note for the planned `V75-C` implementation pass.

Authority layer: support only.

This note does not authorize implementation by itself. It records how `V75-C`
should add worker-output reconciliation plans, dispatch reconciliation
contracts, post-dispatch-review handoff rows, and family closeout alignment
after `V75-B` has closed.

Read together with:

- `docs/DRAFT_NEXT_ARC_OPTIONS_v65.md`
- `docs/ARCHITECTURE_ADEU_DISPATCH_REVIEW_FAMILY_v0.md`
- `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75A_IMPLEMENTATION_MAPPING_v0.md`
- `docs/DRAFT_ADEU_DISPATCH_REVIEW_V75B_IMPLEMENTATION_MAPPING_v0.md`

## Workflow Posture

This `V75-C` support spec remains below lock authority until `V75-B` has
merged and lean-closed, and a future canonical starter trio selects `V75-C`.

`V75-C` should extend released `V75-A` and `V75-B` rows. It should not create a
parallel dispatch universe.

`V75-C` may define reconciliation posture and later-review handoff. It must not
execute dispatch, claim that dispatch execution occurred, treat worker output
as truth, grant runtime permission, authorize product work, open or update PRs,
merge, release, or enter external contests.

## Candidate New Surfaces

`V75-C` should select:

- `repo_worker_output_reconciliation_plan@1`
- `repo_dispatch_reconciliation_contract@1`
- `repo_post_dispatch_review_handoff@1`
- `repo_dispatch_review_family_closeout_alignment@1`

These surfaces should prepare reconciliation and later-family handoff without
doing runtime dispatch.

## Worker Output Reconciliation Plan

The reconciliation plan should record:

- `reconciliation_plan_ref`
- `dispatch_request_refs`
- `assignment_plan_refs`
- `io_contract_refs`
- `projected_output_slot_refs`
- `observed_worker_output_refs`
- `output_presence_posture`
- `dispatch_execution_posture`
- `relation_rows`
- `exception_refs`
- `non_truth_guardrail`
- `limitation_note`

Minimum output presence posture:

- `projected_not_observed`
- `observed_from_authorized_prior_run`
- `observed_from_support_artifact`
- `missing_expected_output`
- `not_applicable`

Minimum dispatch execution posture:

- `no_dispatch_executed_by_v75`

`projected_not_observed` should be the default posture when no later authority
has executed dispatch. Observed outputs must cite authorized prior runs or
support artifacts and still remain non-truth until later review.

Validation:

- if `output_presence_posture = projected_not_observed`, then
  `observed_worker_output_refs` must be empty and projected output slot refs
  must be non-empty or explicitly not applicable;
- if `output_presence_posture` is `observed_from_authorized_prior_run` or
  `observed_from_support_artifact`, then observed worker output refs must cite
  source refs and `dispatch_execution_posture` must still be
  `no_dispatch_executed_by_v75`.

## Relation Rows

Relation rows inside or beside the reconciliation plan should record:

- `relation_ref`
- `left_output_ref`
- `right_output_ref`
- `claim_horizon`
- `relation_kind`
- `source_refs`
- `authority_boundary_posture`
- `required_next_review_surface`
- `limitation_note`

Minimum relation kind:

- `conflict`
- `complementarity`
- `duplicate`
- `orthogonal`
- `unclear_relation`
- `single_output_no_relation`

Relation rows should make conflict and complementarity visible without
settling them as truth.

## Dispatch Reconciliation Contract

The contract should record:

- `contract_ref`
- `reconciliation_plan_refs`
- `required_review_roles`
- `required_authority_refs`
- `allowed_settlement_postures`
- `forbidden_inferences`
- `handoff_refs`
- `limitation_note`

Minimum forbidden inference:

- `worker_output_as_truth`
- `model_output_as_benchmark_truth`
- `tool_pass_as_scope_expansion`
- `assignment_plan_as_execution`
- `dispatch_review_as_runtime_permission`

The contract should state which later reviews or authorities are required
before worker outputs can be used for ratification, integration, product,
runtime, external, or release decisions.

## Post-Dispatch-Review Handoff

The handoff should record:

- `handoff_ref`
- `dispatch_request_refs`
- `assignment_plan_refs`
- `reconciliation_plan_refs`
- `reconciliation_contract_refs`
- `handoff_target`
- `handoff_subject_horizon`
- `handoff_posture`
- `carried_exception_refs`
- `required_later_authority_refs`
- `non_execution_guardrail`
- `limitation_note`

Minimum handoff target:

- `future_runtime_permission_review`
- `future_product_review`
- `future_external_branch_review`
- `future_outcome_review`
- `future_reconciliation_or_arbiter_review`
- `future_experiment_review`
- `future_family_review`
- `deferred_no_selection`

Minimum handoff subject horizon:

- `dispatch_review_process_outcome`
- `projected_orchestration_plan_review`
- `authorized_prior_worker_run_output`
- `future_runtime_execution_outcome`
- `product_review_pressure`
- `external_branch_review_pressure`
- `experiment_design_pressure`

Minimum handoff posture:

- `ready_for_later_review`
- `blocked_by_unresolved_exception`
- `blocked_by_required_later_authority`
- `blocked_by_output_truth_boundary`
- `deferred_to_future_family`
- `rejected_out_of_scope`

`post_dispatch_review` means after dispatch review, not after dispatch
execution.

Blocking-exception invariant:

- if carried exception refs contain any blocking exception, then
  `handoff_posture` must not be `ready_for_later_review` unless
  `handoff_target = future_reconciliation_or_arbiter_review` and the limitation
  note states that the blocker is being carried for settlement.

## Family Closeout Alignment

The family closeout alignment should record:

- `family`
- `closed_by_arc`
- `closed_slice_ladder`
- `shipped_record_shapes`
- `consumed_source_families`
- `future_family_authority`
- `unselected_future_surfaces`
- `dispatch_review_authority_boundary`
- `limitation_note`

The family closeout may say that `V75` is closed as dispatch review and
orchestration posture. It must not say that dispatch, runtime permission,
product authorization, external participation, release, benchmark truth, model
selection, or recursive policy authority has been granted.

## Conditional Validation

`V75-C` validators should enforce:

- every reconciliation plan references released `V75-A` request rows and
  released `V75-B` assignment / IO rows;
- every reconciliation plan carries `dispatch_execution_posture =
  no_dispatch_executed_by_v75`;
- observed output posture must cite authorized prior-run or support-artifact
  source refs;
- relation rows must have source refs or explicit absence posture;
- contracts must carry forbidden inferences;
- handoff rows must carry unresolved exceptions forward;
- future outcome review targets must include `handoff_subject_horizon` so they
  cannot imply hidden dispatch execution inside `V75`;
- runtime, product, external, release, and experiment handoffs remain review
  requests only.

## Mandatory Reject Cases

`V75-C` should reject:

- reconciliation row that treats worker output as truth;
- reconciliation row that claims `V75` executed dispatch;
- relation row without source refs or explicit absence posture;
- contract without forbidden inferences;
- post-dispatch-review handoff that claims dispatch execution occurred;
- handoff marked ready while carrying blocking exceptions outside explicit
  reconciliation / arbiter settlement;
- handoff to runtime execution while blocking exceptions remain;
- handoff to product authorization without product authority;
- handoff to external contest participation without `V43` branch activation;
- family closeout claiming runtime permission, product launch, release,
  dispatch execution, external contest participation, benchmark truth, model
  selection, or recursive policy amendment;
- family closeout that creates a new `DRAFT_NEXT_ARC_OPTIONS_v*` precedent for
  sub-lanes.

## Expected First Fixture

The first `V75-C` reference fixture should include:

- one worker-output reconciliation plan over released `V75-A` / `V75-B` rows
  with `output_presence_posture = projected_not_observed`;
- one dispatch reconciliation contract with forbidden inferences;
- one post-dispatch-review handoff that requests later review without dispatch
  execution;
- one family closeout alignment row listing `V75-A`, `V75-B`, and `V75-C`;
- zero command execution, runtime permission, product authorization, external
  contest, release, benchmark truth, model selection, or recursive policy
  amendment rows.

## Stop Gate Expectations

The future `V75-C` stop gate should require:

- schema exports for all `V75-C` surfaces;
- reference and reject fixture validation;
- package export tests;
- closeout consistency and semantic closeout lint;
- rejection of worker-output-as-truth, post-dispatch-as-execution, runtime,
  product, external, release, and recursive-policy laundering;
- closeout evidence that the family is closed as dispatch review only.
