# Architecture ADEU Runtime Permission Effect Envelope Family v0

Status: architecture / decomposition record for planned `V77`.

Authority layer: architecture / decomposition.

This note does not authorize implementation by itself. It records the intended
family shape for `V77` downstream of closed `V68` cartography, closed `V69`
candidate intake, closed `V70` review classification, closed `V71`
ratification review, closed `V72` contained integration review, closed `V73`
outcome review, closed `V74` operator projection, closed `V75` dispatch review,
and closed `V76` reconciliation / arbiter review.

## 1. Family Thesis

`V77` is the runtime-permission review and action-effect envelope family.

It should make runtime-action pressure reviewable by typing permission
requests, source posture, command preflight conditions, target/effect
boundaries, telemetry requirements, rollback requirements, authority posture,
and later handoff state. It must not execute commands, grant runtime
permission, assign workers, dispatch workers, productize, activate external
branches, release, or amend policy.

`V77` may say:

- this candidate or handoff requests runtime-permission review;
- this request is blocked, deferred, future-family-only, or ready for later
  review;
- this command intent, if any, has a bounded preflight contract;
- this action-effect envelope identifies allowed and forbidden effect
  surfaces for later review;
- this telemetry evidence would be required before any later execution review;
- this rollback contract would be required before any later execution review;
- this human, maintainer, policy, runtime, product, external, or release
  authority is missing or required later.

`V77` must not say:

- a command may run now;
- a tool may be invoked now;
- runtime permission is granted;
- worker assignment or dispatch has happened;
- product authorization has happened;
- external contest or branch activation has happened;
- PR, commit, merge, release, or released truth has happened;
- relation settlement, claim truth, benchmark truth, model selection,
  living-memory authority, or recursive policy amendment has happened.

## 2. Relationship To `V68` Through `V76`

`V68` provides source / authority cartography and namespace disambiguation.

`V69` provides source-bound candidate identity and non-adoption guardrails.

`V70` provides claim, evidence, adversarial-review, conflict, complementarity,
gap, and pre-ratification substrate.

`V71` provides request, authority profile, settlement, ratification review,
dissent, amendment-scope, and post-ratification substrate.

`V72` provides containment, target-boundary, trial, effect, rollback, and
commit / PR / merge / release authority posture substrate.

`V73` provides outcome, regression, tool-fitness, self-improvement ledger,
operator-cognition signal, and recommendation substrate.

`V74` provides operator projection, typed case view, model-output comparison,
exception visibility, decision visibility contract, workbench projection, and
post-projection handoff substrate.

`V75` provides dispatch-review request, worker-role / assignment / IO /
tool-applicability planning, exception registers, projected worker-output
slots, relation rows, reconciliation contracts, post-dispatch-review handoffs,
and dispatch-review family closeout alignment.

`V76` provides reconciliation claim maps, relation registers, dissent
registers, arbiter authority profiles, settlement requests, adversarial
relation reviews, gap scans, summaries, post-reconciliation handoffs, and
family closeout alignment.

`V77` consumes those substrates. It should not weaken them by treating
cartography as authority, intake as adoption, review classification as
ratification, ratification review as implementation, contained trial posture
as runtime permission, outcome recommendation as self-approval, operator
projection as authority, dispatch review as execution, or reconciliation
review as truth settlement.

## 3. Core Separations

| Lane | Question | Forbidden collapse |
|---|---|---|
| Runtime review request | What source-bound pressure asks for runtime review? | Treating request as permission |
| Runtime source index | What concrete source or absence posture supports the request? | Treating support roadmap as eligibility source |
| Non-execution guardrail | What must remain impossible in this family? | Treating visibility as authorization |
| Command preflight | What would need checking before any later command review? | Treating preflight as command execution |
| Action-effect envelope | What effects are in or out of a later review horizon? | Treating envelope as accepted effect |
| Telemetry requirement | What evidence would be needed to observe an action later? | Treating missing telemetry as success |
| Rollback contract | What rollback posture would be required later? | Treating rollback intent as rollback verified |
| Authority posture | Which later authority is missing or required? | Treating authority posture as authority grant |
| Summary / handoff | What later surface should receive the state? | Performing runtime, product, external, release, or policy work inside `V77` |

## 4. ODEU Runtime Posture

Runtime-permission records should preserve ODEU lane information with an
`odeu_lanes` field where useful. The field should be a sorted, non-empty list
even when the row is single-lane.

Minimum lane values:

- `ontological`
- `deontic`
- `epistemic`
- `utility`

`V77` is ontological when it identifies requests, command intents, target
boundaries, effect surfaces, telemetry surfaces, rollback refs, and authority
requirements. It is epistemic when it tracks source coverage, preflight
checks, telemetry requirements, evidence gaps, and rollback evidence. It is
deontic when it preserves non-execution, non-product, non-external, non-release,
and non-policy boundaries. It is utility-bearing when it recommends the next
review surface.

## 5. Runtime Permission Vocabulary

Minimum runtime source role:

- `v76_summary_source`
- `v76_post_reconciliation_handoff_source`
- `v76_family_closeout_source`
- `v72_effect_surface_source`
- `v72_rollback_source`
- `combined_dogfood_source`
- `support_roadmap_context`
- `absence_marker`

Support roadmap sources may contextualize `V77`; they cannot by themselves
make a runtime-permission review request eligible.

Minimum runtime request posture:

- `eligible_for_runtime_permission_review`
- `blocked_by_missing_source`
- `blocked_by_missing_authority`
- `blocked_by_non_runtime_handoff`
- `blocked_by_product_authority_gap`
- `blocked_by_external_branch_gap`
- `future_family_only`
- `rejected_out_of_scope`

Minimum permission horizon:

- `command_preflight_review`
- `local_tool_invocation_review`
- `bounded_runtime_action_review`
- `effect_telemetry_review`
- `rollback_readiness_review`
- `future_product_runtime_review`
- `future_external_branch_runtime_review`
- `future_family_review`

Minimum command intent kind:

- `no_command_intent_recorded`
- `shell_command_pressure`
- `python_tool_pressure`
- `repo_script_pressure`
- `api_call_pressure`
- `external_tool_pressure`
- `future_family_only`

Minimum command execution posture:

- `no_execution_authorized`
- `execution_requires_later_authority`
- `execution_forbidden_by_this_family`

Reference and starter rows should use `no_execution_authorized` unless a later
family explicitly selects a stronger runtime authority surface. `V77` itself
must not emit an execution-authorized row.

Minimum effect envelope posture:

- `effect_envelope_for_review_only`
- `effect_envelope_blocked_by_missing_target`
- `effect_envelope_blocked_by_missing_telemetry`
- `effect_envelope_blocked_by_missing_rollback`
- `effect_envelope_future_family_only`

Minimum target resolution kind:

- `concrete_file_ref`
- `concrete_schema_ref`
- `concrete_fixture_ref`
- `concrete_test_ref`
- `concrete_doc_ref`
- `concrete_script_ref`
- `bounded_package_surface_with_child_refs`
- `external_endpoint_ref`
- `no_target_boundary`

Globs may be discovery context only. They are not concrete target boundaries.

Minimum effect acceptance posture:

- `no_effect_accepted`
- `effect_requires_later_review`
- `effect_not_observed`
- `effect_observed_from_prior_authorized_artifact`

Minimum telemetry posture:

- `telemetry_required_later`
- `telemetry_source_present_for_prior_artifact`
- `telemetry_missing_expected_source`
- `telemetry_not_applicable`
- `telemetry_future_family_only`

Minimum rollback posture:

- `rollback_required_later`
- `rollback_source_present_for_prior_artifact`
- `rollback_missing_expected_source`
- `rollback_blocked`
- `rollback_not_applicable`
- `rollback_future_family_only`

## 6. Family Slices

`V77-A` should instantiate the starter request/source/guardrail layer:

- `repo_runtime_permission_review_request@1`
- `repo_runtime_permission_source_index@1`
- `repo_runtime_non_execution_guardrail@1`

`V77-B` should instantiate preflight and effect-envelope review:

- `repo_command_preflight_contract@1`
- `repo_action_effect_envelope@1`
- `repo_runtime_telemetry_requirement@1`
- `repo_runtime_rollback_contract@1`

`V77-C` should instantiate authority posture, summary, handoff, and closeout:

- `repo_runtime_permission_authority_posture@1`
- `repo_runtime_permission_review_summary@1`
- `repo_post_runtime_permission_review_handoff@1`
- `repo_runtime_permission_family_closeout_alignment@1`

## 7. Negative Laws

- Runtime permission review is not runtime permission.
- Command preflight is not command execution.
- Tool applicability is not tool-use permission.
- A command string is not permission to run it.
- A target boundary is not permission to change that target.
- An effect envelope is not accepted effect.
- Telemetry requirement is not observed telemetry.
- Rollback requirement is not rollback verification.
- Authority posture is not authority grant.
- A local command run outside the lock is not `V77` evidence by itself.
- Product pressure is not product authorization.
- External branch pressure is not external branch activation.
- Dispatch review is not dispatch execution.
- Reconciliation review is not truth settlement.
- A handoff is not later-family completion.

## 8. Package Boundary

The first implementation surface should remain in
`packages/adeu_repo_description` because `V77` is still repo-grounded review
metadata. If a later slice tries to become live command execution, runtime
permissioning, worker dispatch, product UI, external branch automation,
release automation, or a queryable living decision graph, that work should
split rather than expanding repo-description by implication.
