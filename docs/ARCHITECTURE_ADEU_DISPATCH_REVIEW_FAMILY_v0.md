# Architecture ADEU Dispatch Review Family v0

Status: architecture / decomposition record for planned `V75`.

Authority layer: architecture / decomposition.

This note does not authorize implementation by itself. It records the intended
family shape for `V75` downstream of closed `V68` cartography, closed `V69`
candidate intake, closed `V70` candidate review classification, closed `V71`
candidate ratification review, closed `V72` contained integration review,
closed `V73` candidate outcome review, and closed `V74` operator projection.

## 1. Family Thesis

`V75` is the dispatch-review and multi-worker orchestration-posture family.

It should make the repo able to represent dispatch pressure emitted by
operator-projection handoffs in a governed way, without confusing review,
assignment planning, IO contracts, tool applicability, or reconciliation
posture with execution authority.

`V75` may say:

- this projected case has a dispatch-review request;
- these sources, visibility contracts, workbench projections, handoffs,
  exceptions, and required later authority rows justify or block review;
- this request is eligible, blocked, future-family-only, or rejected out of
  scope;
- these worker roles, IO contracts, tools, and exceptions would matter if a
  later authority selected orchestration;
- these projected or later-observed worker outputs require reconciliation;
- this later review should go to runtime permission, product review, external
  branch review, outcome review, or future-family review.

`V75` must not say:

- a dispatch-review request is dispatch;
- a worker role profile is a worker authority grant;
- an assignment plan is worker execution;
- a tool pass expands scope globally;
- worker output is truth;
- an operator click or workbench action authorizes dispatch;
- runtime permission, product authorization, release, external contest
  participation, global model selection, benchmark truth, or recursive policy
  amendment has occurred.

## 2. Relationship To `V68` Through `V74`

`V68` provides the map substrate:

- source rows and authority layers;
- family / slice / arc namespace disambiguation;
- support lineage;
- evidence surface indexing;
- tool applicability boundaries.

`V69` provides candidate substrate:

- source-bound candidate rows;
- source registers and source absence posture;
- non-adoption guardrails;
- operator-ingress bindings;
- recursive workflow residue reports.

`V70` provides review substrate:

- evidence source index;
- claim and classification rows;
- adversarial review matrix;
- conflict / complementarity register;
- review gap scan;
- pre-ratification handoff rows.

`V71` provides ratification substrate:

- ratification requests;
- authority profiles;
- settlement records;
- ratification / rejection / deferral records;
- dissent register rows;
- amendment-scope boundaries;
- post-ratification handoff rows.

`V72` provides contained integration substrate:

- containment plans;
- target boundaries;
- non-release guardrails;
- contained trial records;
- effect-surface registers;
- rollback readiness;
- commit / PR / merge / release authority posture;
- post-integration outcome-review handoff rows.

`V73` provides outcome-review substrate:

- outcome-review entries;
- outcome evidence source rows and horizons;
- outcome observations;
- regression and tool-fitness drift rows;
- self-improvement outcome ledger rows;
- operator-cognition outcome signals;
- promotion / demotion / more-evidence recommendations.

`V74` provides operator-projection substrate:

- operator projection case views;
- typed adjudication case views;
- model-output comparison projections;
- exception visibility rows;
- decision visibility contracts;
- ratification-review workbench projections;
- post-projection handoff rows;
- family closeout alignment rows.

`V75` consumes those substrates. It should not weaken them by treating
cartography as authority, intake as adoption, classification as ratification,
ratification as implementation, contained trial posture as outcome success,
outcome recommendation as operator authority, or operator projection as
dispatch authority.

## 3. Core Separations

| Lane | Question | Forbidden collapse |
|---|---|---|
| Dispatch-review entry | Which projected case can be reviewed for dispatch pressure? | Treating review request as dispatch |
| Source binding | Which released `V74-C` rows justify or block the request? | Reconstructing from prose memory or operator desire |
| Non-execution guardrail | Which actions are explicitly forbidden here? | Treating guardrails as optional commentary |
| Worker role profile | Which role capability would be needed later? | Treating role profile as permission |
| Assignment planning | Which roles, IO contracts, tools, and exceptions would matter? | Treating assignment plan as worker execution |
| IO contract | What input / output contract would constrain a worker? | Treating output as truth |
| Tool applicability | Which tool applies to which claim horizon? | Treating tool pass as global scope expansion |
| Reconciliation | How should projected or observed outputs relate? | Treating worker output or majority agreement as correctness |
| Handoff | Which later review surface is requested? | Performing runtime, product, external, or outcome review inside `V75` |

## 4. ODEU Dispatch Posture

Dispatch review should preserve ODEU lane information with an `odeu_lanes`
field. The field should be a sorted, non-empty list even when the row is
single-lane.

Minimum lane values:

- `ontological`
- `deontic`
- `epistemic`
- `utility`

Dispatch review is usually deontic and utility-bearing because it asks whether
later action review is allowed or useful. It is epistemic when it carries source
and exception evidence, and ontological when it identifies cases, workers,
outputs, and target claim horizons.

## 5. Dispatch Vocabulary

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

Eligibility source invariant:

- `eligible_for_dispatch_review` must cite concrete released `V74-C` substrate;
- at least one source row must have
  `dispatch_source_role = v74_post_projection_handoff_source`;
- at least one source row must have
  `dispatch_source_role = visibility_contract_source`;
- at least one source row must have
  `dispatch_source_role = workbench_projection_source`;
- roadmap, architecture, planning, or support-review sources may contextualize
  the family, but they may not be the only eligibility sources.

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

Minimum carried exception origin:

- `v74_exception_visibility`
- `v74_visibility_contract`
- `v74_post_projection_handoff`
- `absence_marker`

Minimum required later-authority row fields:

- `authority_requirement_ref`
- `candidate_ref`
- `authority_kind`
- `required_before_surface`
- `source_refs`
- `source_presence_posture`
- `authority_gap_posture`
- `limitation_note`

Minimum required later-authority kind:

- `runtime_permission`
- `product_authorization`
- `release_authority`
- `external_branch_activation`
- `dispatch_execution_authority`
- `human_or_maintainer_review`
- `recursive_policy_authority`

Minimum worker role kind:

- `source_index_worker`
- `evidence_review_worker`
- `adversarial_review_worker`
- `schema_validation_worker`
- `tool_run_worker`
- `reconciliation_worker`
- `operator_projection_worker`
- `external_branch_review_worker`

Minimum assignment plan posture:

- `plan_ready_for_review`
- `blocked_by_missing_role_profile`
- `blocked_by_missing_io_contract`
- `blocked_by_tool_applicability_gap`
- `blocked_by_unresolved_exception`
- `blocked_by_later_authority`
- `future_family_only`
- `rejected_out_of_scope`

Minimum assignment execution posture:

- `no_execution_authorized`
- `review_plan_only`
- `blocked_pending_later_authority`

Minimum worker-output authority posture:

- `output_for_review_only`
- `output_requires_reconciliation`
- `output_requires_adversarial_review`
- `output_requires_human_ratification`
- `output_not_truth`

Minimum tool-use posture:

- `applicability_record_only`
- `tool_use_requires_later_runtime_permission`
- `tool_use_not_authorized_by_v75`

Minimum output presence posture:

- `projected_not_observed`
- `observed_from_authorized_prior_run`
- `observed_from_support_artifact`
- `missing_expected_output`
- `not_applicable`

Worker-output reference split:

- projected output slots should be represented separately from observed worker
  outputs;
- `projected_output_slot_refs` names expected output slots that have not been
  observed;
- `observed_worker_output_refs` names outputs only when they are sourced from
  an authorized prior run or support artifact;
- if `output_presence_posture = projected_not_observed`, observed worker output
  refs must be empty.

Minimum dispatch execution posture:

- `no_dispatch_executed_by_v75`

Minimum relation kind:

- `conflict`
- `complementarity`
- `duplicate`
- `orthogonal`
- `unclear_relation`
- `single_output_no_relation`

Minimum forbidden inference:

- `worker_output_as_truth`
- `model_output_as_benchmark_truth`
- `tool_pass_as_scope_expansion`
- `assignment_plan_as_execution`
- `dispatch_review_as_runtime_permission`

Minimum handoff subject horizon:

- `dispatch_review_process_outcome`
- `projected_orchestration_plan_review`
- `authorized_prior_worker_run_output`
- `future_runtime_execution_outcome`
- `product_review_pressure`
- `external_branch_review_pressure`
- `experiment_design_pressure`

## 6. Family Surface Plan

`V75-A` should introduce:

- `repo_dispatch_review_request@1`
- `repo_dispatch_source_index@1`
- `repo_dispatch_non_execution_guardrail@1`

`V75-B` should introduce:

- `repo_worker_role_capacity_profile@1`
- `repo_multi_worker_assignment_plan@1`
- `repo_worker_io_contract@1`
- `repo_worker_tool_applicability_matrix@1`
- `repo_dispatch_exception_register@1`

`V75-C` should introduce:

- `repo_worker_output_reconciliation_plan@1`
- `repo_dispatch_reconciliation_contract@1`
- `repo_post_dispatch_review_handoff@1`
- `repo_dispatch_review_family_closeout_alignment@1`

The `V75-C` names deliberately use `post_dispatch_review`, not
`post_dispatch_outcome`, because `V75` does not execute dispatch.

## 7. Negative Laws

`V75` should preserve these negative laws:

- source-free dispatch pressure is invalid;
- dispatch-review request is not dispatch;
- worker role profile is not permission;
- assignment plan is not execution;
- IO output is not truth;
- tool applicability is not global scope;
- worker-output reconciliation is not ratification;
- model-output comparison is not benchmark truth;
- product pressure is not product authorization;
- runtime command pressure is not runtime permission;
- external branch pressure is not external contest participation;
- family closeout is not release authority;
- self-improvement recommendation is not recursive policy amendment.
