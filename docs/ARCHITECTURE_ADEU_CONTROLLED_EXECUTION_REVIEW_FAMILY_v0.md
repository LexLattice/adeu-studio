# Architecture ADEU Controlled Execution Review Family v0

Status: architecture / decomposition note for planned `V79`.

Authority layer: architecture / decomposition.

This architecture note does not authorize implementation by itself. It defines
the intended family boundary for `V79` so starter locks can select bounded
implementation slices without turning controlled execution review into command
execution, tool invocation, dispatch, product authorization, external branch
activation, release, or recursive policy amendment.

## Family Thesis

`V79` should make controlled execution review legible before any later family
considers live command execution or tool invocation. It consumes the `V78`
runtime execution authority review substrate and emits review records about
whether a bounded run plan, tool-invocation plan, effect-monitoring contract,
and post-review handoff are sufficiently source-bound for later review.

`V79` may say:

- a controlled execution review request exists;
- a source or absence posture supports that request;
- an upstream `V78-C` handoff is eligible, blocked, deferred, or
  future-family-only;
- a later run plan would need concrete command, target, tool, effect,
  telemetry, rollback, authority, and operator-confirmation boundaries;
- exceptions block or warn against later review;
- a summary can hand off pressure to a later family.

`V79` must not say:

- a command was executed;
- a tool was invoked;
- a worker was assigned or dispatched;
- a target was mutated;
- an effect was accepted;
- telemetry was observed by `V79`;
- rollback was verified by `V79`;
- product, external branch, PR, commit, merge, release, benchmark, model,
  living-memory, or recursive policy authority exists;
- `V80` or any later family is selected.

## Source Stack Consumed

`V79` consumes:

- `V68` source / authority / namespace cartography;
- `V69` source-bound candidate identity;
- `V70` review classification and gap posture;
- `V71` ratification-review and authority-profile posture;
- `V72` containment, effect, rollback, and commit/release boundary posture;
- `V73` outcome and recommendation posture;
- `V74` operator projection and visibility posture;
- `V75` dispatch-review and worker-planning posture;
- `V76` reconciliation / arbiter and dissent posture;
- `V77` runtime-permission review, command preflight, telemetry, rollback, and
  authority posture;
- `V78` runtime execution authority review, tool-use permission envelope,
  command-scope boundary, exception, readiness, and handoff posture.

No upstream stage becomes execution authority by being consumed.

## Family Slices

### `V79-A`: Controlled Execution Review Intake

Starter surfaces:

- `repo_controlled_execution_review_request@1`
- `repo_controlled_execution_source_index@1`
- `repo_controlled_execution_non_execution_guardrail@1`

Purpose:

- admit source-bound controlled-execution review requests over released
  `V78-C` readiness / handoff / closeout substrate;
- distinguish eligibility sources from support context;
- preserve product, external, release, dispatch, and recursive-policy gaps;
- make non-execution guardrails explicit before run-plan vocabulary exists.

Forbidden:

- run plans;
- tool-invocation plans;
- effect-monitoring contracts;
- exception registers;
- readiness summaries;
- handoffs;
- command execution or tool invocation.

`V79-A` should represent later run-plan, tool-invocation, monitoring,
telemetry, rollback, and operator-confirmation pressure through requested
horizons and required postures rather than refs to future `V79-B` surfaces.
Every reference request should carry
`controlled_execution_action_posture =
no_controlled_execution_performed_by_v79`.

### `V79-B`: Run-Plan And Invocation-Plan Review

Later surfaces:

- `repo_execution_run_plan@1`
- `repo_tool_invocation_plan@1`
- `repo_execution_effect_monitoring_contract@1`
- `repo_controlled_execution_exception_register@1`

Purpose:

- represent bounded run plans without running them;
- represent bounded tool-invocation plans without invoking tools;
- bind effect monitoring, telemetry, rollback, operator confirmation, and
  authority refs to the planned horizon;
- keep blocking exceptions visible.

Forbidden:

- actual command execution;
- actual tool invocation;
- target mutation;
- observed-effect claims without prior authorized source artifacts;
- resolving blockers by prose;
- treating a plan as an action.

### `V79-C`: Controlled Execution Review Summary And Handoff

Later surfaces:

- `repo_controlled_execution_review_summary@1`
- `repo_post_controlled_execution_review_handoff@1`
- `repo_controlled_execution_review_family_closeout_alignment@1`

Purpose:

- summarize released `V79-A` request / source / guardrail rows and released
  `V79-B` plan / monitoring / exception rows;
- preserve blockers and nonblocking warnings;
- hand off later pressure without performing the target family;
- close `V79` as controlled execution review only.

Forbidden:

- execution completion;
- tool invocation completion;
- product, external, release, dispatch, or living-memory authority;
- selecting `V80` or any later family.

## Required Boundary Distinctions

`V79` must keep these distinctions machine-checkable:

- review request is not execution request;
- authority review is not execution authority;
- run plan is not command execution;
- tool-invocation plan is not tool invocation;
- target boundary is not target mutation authority;
- effect-monitoring contract is not observed effect;
- telemetry requirement is not telemetry success;
- rollback requirement is not rollback verification;
- operator confirmation requirement is not operator authorization;
- handoff is not target-family completion;
- product pressure is not product authorization;
- external pressure is not `V43` activation.
- support / dogfood context is not controlled-execution-review eligibility;
- operator confirmation requirement is not operator authorization.

## Negative Laws

- A passing local command output is not authority.
- A model suggestion is not authority.
- Operator desire is not authority.
- A `V78` decision is not command execution.
- A `V78` tool-use permission envelope is not tool invocation.
- A `V78` command-scope boundary is not target mutation authority.
- A run plan is not a run.
- A tool-invocation plan is not invocation.
- A monitoring contract is not effect evidence.
- A summary is not self-approval.
- A closeout is not next-family selection.

## Package Boundary

Primary implementation should remain in `packages/adeu_repo_description`
because `V79` is still repo/corpus review metadata, not a live command runner,
tool runtime, dispatcher, product UI, external automation layer, release
automation layer, or graph-query runtime.

If later work becomes live command execution, credentialed tool invocation,
worker dispatch, product UI, external branch automation, release automation,
or a persistent decision graph runtime, it should split away rather than
expanding repo-description by implication.
