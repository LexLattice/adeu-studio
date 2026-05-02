# Architecture ADEU External Branch Activation Review Family v0

Status: architecture / decomposition note for planned `V80`.

Authority layer: architecture / decomposition.

This architecture note does not authorize implementation by itself. It defines
the intended family boundary for `V80` so starter locks can select bounded
implementation slices without turning external branch activation review into
external branch activation, external contest participation, external
submission, external tool invocation, product authorization, release, or
recursive policy amendment.

## Family Thesis

`V80` should make external-world / `V43` branch activation review legible
before any later family considers external contest participation, external
submission, external endpoint use, or external result claims. It consumes the
`V79` controlled execution review substrate and emits review records about
whether an external branch horizon has source-bound objective, data, tool,
submission, result-provenance, withdrawal, and authority posture.

`V80` may say:

- an external branch review request exists;
- a source or absence posture supports that request;
- a `V43` / external branch posture source exists or is missing;
- an external objective is recorded, eligible only for objective-only review,
  blocked, deferred, or out of scope;
- later review would need data boundary, tool boundary, submission authority,
  result provenance, withdrawal posture, and human / maintainer authority;
- exceptions block or warn against later external review;
- a summary can hand off pressure to a later family.

`V80` must not say:

- an external branch was activated;
- `V43` contest participation occurred;
- an external submission was made;
- an external endpoint or external tool was invoked for effect;
- external data was ingested or exported;
- an external result is true;
- command execution, tool invocation, dispatch, product, release, or external
  authority exists;
- `V81` or any later family is selected.

## Source Stack Consumed

`V80` consumes:

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
  command-scope boundary, exception, readiness, and handoff posture;
- `V79` controlled execution review, run-plan review, tool-invocation-plan
  review, effect-monitoring, exception, summary, and handoff posture.

No upstream stage becomes external activation authority by being consumed.

## Family Slices

### `V80-A`: External Branch Review Intake

Starter surfaces:

- `repo_external_branch_review_request@1`
- `repo_external_branch_source_index@1`
- `repo_external_branch_non_activation_guardrail@1`

Purpose:

- admit source-bound external branch review requests over released `V79-C`
  summary / handoff / closeout substrate;
- distinguish concrete `V43` / external branch posture from historical
  planning context and explicit absence rows;
- preserve product, runtime, release, dispatch, and recursive-policy gaps;
- make non-activation guardrails explicit before data, tool, submission, or
  result-provenance vocabulary exists.

Forbidden:

- external data boundary rows;
- external tool boundary rows;
- submission authority rows;
- result provenance contracts;
- withdrawal contracts;
- external branch exception registers;
- readiness summaries;
- handoffs;
- external activation, external submission, or external tool invocation.

### `V80-B`: External Boundary And Authority Review

Later surfaces:

- `repo_external_data_boundary@1`
- `repo_external_tool_boundary@1`
- `repo_external_submission_authority_review@1`
- `repo_external_result_provenance_contract@1`
- `repo_external_branch_exception_register@1`

Purpose:

- represent external data boundaries without ingesting or exporting data;
- represent external tool boundaries without invoking external tools;
- represent submission authority review without submitting;
- represent result provenance and withdrawal requirements without claiming
  external result truth or performing withdrawal;
- keep blocking exceptions visible.

Forbidden:

- actual external endpoint access for effect;
- external submission;
- external result truth;
- benchmark truth;
- product authorization;
- resolving blockers by prose;
- treating a boundary as an action.

Data-boundary rows should use `allowed_data_review_actions`, not
`allowed_data_actions`, so review actions cannot be mistaken for transfer,
ingest, export, mutation, or submission authority. Endpoint refs should carry
an explicit non-authorizing posture:

- `endpoint_identifier_only`
- `endpoint_access_requires_later_authority`
- `endpoint_access_forbidden_by_this_family`
- `endpoint_absent_or_unknown`

### `V80-C`: External Branch Review Summary And Handoff

Later surfaces:

- `repo_external_branch_readiness_summary@1`
- `repo_post_external_branch_review_handoff@1`
- `repo_external_branch_review_family_closeout_alignment@1`

Purpose:

- summarize released `V80-A` request / source / guardrail rows and released
  `V80-B` data / tool / submission / provenance / exception rows;
- preserve blockers and nonblocking warnings;
- hand off later pressure without performing the target family;
- close `V80` as external branch activation review only.

Forbidden:

- external activation completion;
- external submission completion;
- external result truth;
- product, release, runtime, dispatch, or living-memory authority;
- selecting `V81` or any later family.

Handoffs should distinguish authority review from participation or submission
review. The family should use separate targets for
`future_external_branch_activation_authority_review` and
`future_external_participation_or_submission_review`, and include
`handoff_external_authority_horizon` so later selectors can see whether the
emitted pressure concerns branch posture, data boundary, external tool access,
submission authority, result provenance, withdrawal authority, or external
participation.

## Required Boundary Distinctions

`V80` must keep these distinctions machine-checkable:

- branch review request is not branch activation;
- `V43` planning lineage is not `V43` activation authority;
- external objective is not external permission or current branch posture;
- historical branch planning context is not current branch posture;
- data boundary is not data ingestion or export;
- tool boundary is not tool invocation;
- submission authority review is not submission authority;
- result provenance contract is not result truth;
- withdrawal posture is not withdrawal action;
- handoff is not target-family completion;
- product pressure is not product authorization;
- controlled execution review is not external execution authority;
- support / dogfood context is not external-branch-review eligibility.

## Negative Laws

- A historical planning doc is not current external activation authority.
- A model suggestion is not external authority.
- Operator desire is not external authority.
- A URL or endpoint string is not permission to access an external system.
- A local command result is not external result evidence.
- A passing tool result is not submission authority.
- A data boundary is not data transfer.
- A tool boundary is not tool use.
- A submission authority review is not submission.
- A result provenance contract is not result truth.
- A closeout is not next-family selection.

## Package Boundary

Primary implementation should remain in `packages/adeu_repo_description`
because `V80` is still repo/corpus review metadata, not an external contest
runner, external data ingestion layer, credentialed external tool runtime,
product UI, release automation layer, or graph-query runtime.

If later work becomes external submission automation, credential handling,
live external tool invocation, product UI, release automation, or a persistent
decision graph runtime, it should split away rather than expanding
repo-description by implication.
