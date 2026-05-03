# Architecture ADEU Work Packet Activation Review Family v0

Status: architecture / decomposition note for planned `V84`.

Authority layer: architecture / decomposition.

This architecture note does not authorize implementation by itself. It defines
the intended family boundary for `V84` so starter locks can select bounded
review slices without turning work-packet activation review into code edits,
runtime execution, PR creation, commit, merge, release, product authority, or
general artifact truth.

## Family Thesis

`V84` should institutionalize the step after semantic implementation-spec
projection and before implementation. `V83` made intent, semantic edges,
artifact obligations, drift posture, projection packets, quality gates, and
work-packet handoff pressure reviewable. `V84` should decide whether those
released packets are fit to become bounded later implementation locks or work
packet review packages.

The practical goal is not to write code yet. The practical goal is to make the
activation boundary explicit:

```text
V83 projection packet
  -> activation-review request
  -> scope / target / validation / exception review
  -> readiness summary
  -> later canonical implementation lock request
```

Controlling invariant:

```text
V84 may produce an implementation-lock review package, but it may not produce
an implementation work packet with execution authority.
```

`V84` may say:

- a released `V83-C` projection packet or handoff creates activation-review
  pressure;
- a work-packet activation-review request is source-bound and bounded;
- an activation package has a stable identity across request, scope, target,
  validation, exception, readiness, and handoff rows;
- an activation-review source index records projection packets, quality gates,
  implementation spec rows, semantic edge rows, artifact obligation rows,
  drift rows, support context, and explicit absence rows;
- generated/model/agent work-packet candidates exist as candidate-only rows
  with source, prompt/context, profile, projection, quality-gate, and reviewer
  provenance;
- a canonical later-lock requirement is typed and source-bound;
- a target surface is bounded enough for review or blocked by unresolved
  scope;
- a validation evidence plan exists for later review;
- a carried blocker, warning, authority gap, target gap, semantic drift, or
  generated-spec provenance gap prevents activation readiness;
- a later canonical implementation lock is required before work executes.

`V84` must not say:

- implementation happened;
- files may be edited because an activation request exists;
- a work packet has been activated or executed;
- commands may run;
- tools may be invoked;
- workers may be assigned or dispatched;
- a PR may be opened;
- a commit, merge, release, or product decision is authorized;
- a Morphic UX projection has become runtime UI work;
- a direct OAI harness spec has become provider runtime behavior;
- a projection packet proves code correctness;
- `V85` or any later family is selected.

## General Frame

`V83` answers:

```text
What does the intent require, and what implementation spec would preserve it?
```

`V84` answers:

```text
Is that implementation spec bounded enough to request a later implementation lock?
```

The distinction matters. A high-quality implementation spec can still be
unfit for activation review if its target surfaces are too broad, validation
evidence is missing, drift warnings are blocking, authority boundaries are
unresolved, or the requested work would cross runtime, product, release,
external, corpus, graph, or recursive-policy lines.

## Source Stack Consumed

`V84` consumes the full `V68` through `V83` substrate. Most importantly, it
consumes:

- `V83-A` source-bound semantic intent contracts, intent source indexes, and
  non-implementation guardrails;
- `V83-B` semantic edge decompositions, artifact obligation maps, and
  drift / ambiguity registers;
- `V83-C` implementation-spec projection packets, review checklists,
  implementation-spec quality gates, intent-to-work-packet handoffs, and
  family closeout alignment.

No upstream stage becomes implementation authority by being consumed.

## Family Slices

### `V84-A`: Activation-Review Request Intake

Starter surfaces:

- `repo_work_packet_activation_review_request@1`
- `repo_work_packet_activation_source_index@1`
- `repo_work_packet_activation_non_execution_guardrail@1`

Purpose:

- record source-bound activation-review requests over released `V83-C`
  projection / handoff / closeout substrate;
- index projection packets, quality gates, implementation spec rows, semantic
  edges, artifact obligations, drift rows, support sources, and absence rows;
- split request recordability from activation-review eligibility;
- preserve non-execution guardrails before scope contracts, target-surface
  boundaries, validation plans, readiness summaries, or handoffs exist.

Forbidden:

- work-packet scope contracts;
- target-surface boundary rows;
- validation evidence plans;
- activation exception registers;
- activation readiness summaries;
- post-activation-review handoffs;
- implementation, code edits, command execution, tool invocation, worker
  dispatch, PR creation, commit, merge, release, product authorization, graph
  authority, or `V85` selection.

### `V84-B`: Scope, Target, Validation, And Exception Review

Later surfaces:

- `repo_work_packet_scope_contract@1`
- `repo_implementation_target_surface_boundary@1`
- `repo_work_packet_validation_evidence_plan@1`
- `repo_work_packet_activation_exception_register@1`

Purpose:

- define bounded work-packet scope for review only;
- bind target surfaces to concrete files, schemas, fixtures, tests, docs, or
  other explicit artifacts;
- plan validation evidence against known semantic edges and artifact
  obligations;
- preserve blockers and warnings that prevent later implementation-lock
  readiness.

Forbidden:

- readiness summaries or final handoffs;
- treating scope contracts as permission to mutate targets;
- treating validation plans as test execution or semantic truth;
- implementing code or modifying runtime surfaces.

### `V84-C`: Activation Readiness And Handoff

Later surfaces:

- `repo_work_packet_activation_readiness_summary@1`
- `repo_post_work_packet_activation_review_handoff@1`
- `repo_work_packet_activation_family_closeout_alignment@1`

Purpose:

- summarize released `V84-A` and `V84-B` substrate;
- say whether a package is ready for later canonical implementation-lock
  review, warning-ready, blocked, future-family-only, or out of scope;
- hand off later implementation-lock pressure without executing work;
- close `V84` as work-packet activation review only.

Forbidden:

- activating or executing the work packet;
- opening a PR or committing code;
- running tests as implementation evidence;
- selecting `V85`;
- product, runtime, release, graph, or recursive-policy authority.

## Required Boundary Distinctions

`V84` must keep these distinctions machine-checkable:

- activation-review request is not work-packet activation;
- activation-review request is not activation authority;
- activation package identity is not execution authority;
- source-bound projection packet is not implementation authority;
- quality gate readiness is not permission to implement;
- target boundary is not permission to mutate target state;
- prospective write target is not write authority;
- read dependency, validation target, generated artifact target, forbidden
  target, and context-only target are distinct target roles;
- validation evidence plan is not executed validation;
- validation matrix coverage is not semantic truth;
- test plan is not semantic truth;
- operator confirmation requirement is not operator authorization;
- implementation-lock requirement is not an implementation lock;
- support context is not activation eligibility by itself;
- model/agent-generated spec provenance is not correctness;
- Morphic UX projection review is not runtime UI implementation;
- direct OAI harness review is not provider runtime behavior;
- handoff is not target-family completion.

## Negative Laws

- "Ready for later implementation review" is not "ready to implement now".
- "Scope is bounded" is not "target mutation is authorized".
- "A work packet exists" is not "a work packet may execute".
- "A projection packet passed a V83 quality gate" is not implementation truth.
- "A canonical lock requirement exists" is not "a canonical lock was created".
- "A validation plan exists" is not test execution.
- "Tests are listed" is not semantic preservation.
- "The operator wants it" is not canonical lock authority.
- "The model generated the work packet" is not activation authority.
- "The handoff target is implementation review" is not implementation.

## Expected Post-`V84` Pressure

`V84-C` may emit pressure toward a later family such as canonical
implementation-lock review, Morphic UX implementation review, direct OAI
harness implementation review, meta-orchestrator workflow activation review,
product review, or graph-memory review. `V84-C` must not select that family.
The next selector should decide based on released `V84-C` readiness summaries,
handoffs, blockers, and authority gaps.
