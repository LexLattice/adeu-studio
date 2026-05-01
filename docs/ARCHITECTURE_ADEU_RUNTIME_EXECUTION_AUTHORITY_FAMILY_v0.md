# Architecture ADEU Runtime Execution Authority Family v0

Status: architecture / decomposition record for planned `V78`.

Authority layer: architecture / decomposition.

This note does not authorize implementation by itself. It records the intended
family shape for `V78` downstream of closed `V68` cartography, closed `V69`
candidate intake, closed `V70` review classification, closed `V71`
ratification review, closed `V72` contained integration review, closed `V73`
outcome review, closed `V74` operator projection, closed `V75` dispatch review,
closed `V76` reconciliation / arbiter review, and closed `V77`
runtime-permission review.

## 1. Family Thesis

`V78` is the runtime execution authority and tool-use permission envelope
family.

It should make bounded runtime execution authority reviewable by typing
authority requests, source posture, authority decisions, tool-use permission
envelopes, command-scope authorization boundaries, exception registers,
readiness summaries, and pre-execution-review handoffs. It must not execute
commands, invoke tools, assign workers, dispatch workers, productize, activate
external branches, release, or amend policy.

`V78` may say:

- this candidate or handoff requests runtime execution authority review;
- this request is blocked, deferred, future-family-only, rejected, or ready for
  later authority decisioning;
- this source, lock, maintainer record, policy record, or absence marker bears
  on the authority horizon;
- this bounded authority decision grants, denies, defers, blocks, or rejects
  later execution review for a specified horizon;
- this tool-use permission envelope is bounded, denied, deferred, blocked, or
  future-family-only;
- this command-scope authorization boundary identifies the exact target,
  command-intent, telemetry, rollback, and authority constraints for a later
  execution-review surface;
- this pre-execution-review handoff requests a later family without performing
  that family.

`V78` must not say:

- a command ran;
- a tool was invoked;
- worker assignment or dispatch has happened;
- product authorization has happened;
- external contest or branch activation has happened;
- PR, commit, merge, release, or released truth has happened;
- relation settlement, claim truth, benchmark truth, model selection,
  living-memory authority, or recursive policy amendment has happened.

## 2. Relationship To `V68` Through `V77`

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

`V77` provides runtime-permission review requests, runtime source indexes,
non-execution guardrails, command preflight contracts, action-effect envelopes,
telemetry requirements, rollback contracts, authority posture, summaries,
post-runtime-permission-review handoffs, and family closeout alignment.

`V78` consumes those substrates. It should not weaken them by treating
cartography as authority, intake as adoption, review classification as
ratification, ratification review as implementation, contained trial posture
as runtime permission, outcome recommendation as self-approval, operator
projection as authority, dispatch review as execution, reconciliation review
as truth settlement, or runtime-permission review as runtime execution
authority.

## 3. Core Separations

| Lane | Question | Forbidden collapse |
|---|---|---|
| Authority request | What source-bound pressure asks for runtime execution authority? | Treating request as authority grant |
| Authority source index | What source, lock, maintainer record, policy record, or absence posture bears on authority? | Treating support context as authority source |
| Non-action guardrail | What must remain impossible in this family? | Treating authority visibility as action |
| Authority decision | Is bounded later execution review granted, denied, deferred, blocked, or rejected? | Treating a grant record as command execution |
| Tool-use permission envelope | Which tool use is bounded for later review? | Treating envelope as tool invocation |
| Command-scope authorization boundary | Which command intent / target / telemetry / rollback constraints are in scope? | Treating scope as a command run |
| Exception register | Which authority, source, product, external, telemetry, rollback, or target gaps remain? | Treating gaps as resolved by narration |
| Readiness / handoff | What later surface should receive the state? | Performing runtime execution, product, external, release, or policy work inside `V78` |

## 4. ODEU Runtime Authority Posture

Runtime execution authority records should preserve ODEU lane information with
an `odeu_lanes` field where useful. The field should be a sorted, non-empty
list even when the row is single-lane.

Minimum lane values:

- `ontological`
- `deontic`
- `epistemic`
- `utility`

`V78` is ontological when it identifies requests, authority sources, actors,
decision records, tool envelopes, command scopes, target boundaries, telemetry
refs, rollback refs, and handoff subjects. It is epistemic when it tracks
source coverage, authority evidence, exception state, telemetry sufficiency,
rollback sufficiency, and target-boundary evidence. It is deontic when it
preserves non-action, non-product, non-external, non-release, and non-policy
boundaries. It is utility-bearing when it recommends the next review surface.

## 5. Runtime Authority Vocabulary

Minimum runtime authority source role:

- `v77_authority_posture_source`
- `v77_runtime_summary_source`
- `v77_post_runtime_permission_review_handoff_source`
- `v77_family_closeout_source`
- `v77_command_preflight_source`
- `v77_effect_envelope_source`
- `v77_telemetry_requirement_source`
- `v77_rollback_contract_source`
- `combined_dogfood_source`
- `maintainer_authority_source`
- `policy_authority_source`
- `support_context`
- `absence_marker`

Support context may explain why `V78` exists; it cannot by itself make a
runtime execution authority request eligible.

Minimum authority request posture:

- `eligible_for_runtime_execution_authority_review`
- `blocked_by_missing_source`
- `blocked_by_missing_authority_source`
- `blocked_by_product_authority_gap`
- `blocked_by_external_branch_gap`
- `blocked_by_unbounded_command_scope`
- `blocked_by_missing_telemetry_requirement`
- `blocked_by_missing_rollback_requirement`
- `future_family_only`
- `rejected_out_of_scope`

Minimum requested authority horizon:

- `bounded_command_execution_review`
- `bounded_tool_invocation_review`
- `bounded_repo_script_execution_review`
- `bounded_api_call_execution_review`
- `telemetry_observation_review`
- `rollback_execution_review`
- `future_product_runtime_review`
- `future_external_branch_runtime_review`
- `future_family_review`

Minimum authority decision posture:

- `review_authority_granted_for_bounded_execution_surface`
- `review_authority_denied`
- `review_authority_deferred`
- `review_authority_blocked_by_missing_source`
- `review_authority_blocked_by_missing_scope`
- `review_authority_blocked_by_missing_telemetry`
- `review_authority_blocked_by_missing_rollback`
- `review_authority_future_family_only`
- `review_authority_rejected_out_of_scope`

An authority grant record may authorize only a later execution-review surface.
It must not assert that execution happened inside `V78`.

Minimum authorized surface kind:

- `later_execution_review_surface`
- `later_tool_invocation_review_surface`
- `later_telemetry_review_surface`
- `later_rollback_review_surface`
- `future_family_review_surface`

Minimum authority grant horizon:

- `later_execution_review_only`
- `later_tool_invocation_review_only`
- `later_runtime_review_only`
- `future_family_review_only`

Minimum execution authorization posture:

- `execution_not_authorized_by_v78`
- `execution_requires_later_family`
- `execution_forbidden_by_this_family`

Reference rows should use `execution_not_authorized_by_v78`.

Minimum execution posture:

- `no_execution_performed_by_v78`
- `execution_requires_later_family`
- `execution_forbidden_by_this_family`

Reference rows should use `no_execution_performed_by_v78`.

Minimum tool-use permission posture:

- `tool_use_permission_granted_for_later_execution_review`
- `tool_use_permission_denied`
- `tool_use_permission_deferred`
- `tool_use_permission_blocked_by_missing_authority`
- `tool_use_permission_future_family_only`
- `tool_use_not_applicable`

Minimum command-scope posture:

- `bounded_scope_authorized_for_later_execution_review`
- `scope_denied`
- `scope_deferred`
- `scope_blocked_by_missing_target`
- `scope_blocked_by_unbounded_target`
- `scope_blocked_by_missing_telemetry`
- `scope_blocked_by_missing_rollback`
- `scope_future_family_only`

Globs may be discovery context only. They are not command-scope authorization
boundaries.

## 6. Family Slices

`V78-A` should instantiate the starter request/source/guardrail layer:

- `repo_runtime_execution_authority_request@1`
- `repo_runtime_authority_source_index@1`
- `repo_runtime_authority_non_action_guardrail@1`

`V78-B` should instantiate authority decisions and permission envelopes:

- `repo_runtime_execution_authority_decision@1`
- `repo_tool_use_permission_envelope@1`
- `repo_command_scope_authorization_boundary@1`
- `repo_runtime_authority_exception_register@1`

`V78-C` should instantiate readiness, handoff, and closeout:

- `repo_runtime_authority_readiness_summary@1`
- `repo_pre_execution_authority_review_handoff@1`
- `repo_runtime_execution_authority_family_closeout_alignment@1`

## 7. Negative Laws

- Runtime execution authority request is not authority grant.
- Authority source visibility is not authority source sufficiency.
- Authority decision is not command execution.
- Tool-use permission envelope is not tool invocation.
- Command-scope authorization boundary is not command execution.
- Target scope is not permission to mutate target state.
- Telemetry requirement satisfaction must remain source-bound.
- Rollback requirement satisfaction must remain source-bound.
- Product pressure is not runtime authority.
- External branch pressure is not `V43` activation.
- Pre-execution-review handoff is not execution.
- A passing local command or tool run is not authority evidence unless a prior
  authorized source explicitly admits it.
- `V78` closeout is not `V79` selection.

## 8. Package Boundary

Expected implementation remains in `packages/adeu_repo_description` while the
surfaces are repo-grounded metadata, authority posture, schema exports, and
fixtures. If later work becomes a live runtime permission system, command
runner, tool invocation layer, worker dispatcher, product UI, external
automation layer, release automation layer, or graph query runtime, that work
should split instead of expanding repo-description by implication.
