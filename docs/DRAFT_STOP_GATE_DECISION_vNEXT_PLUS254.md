# Draft Stop-Gate Decision vNext+254

Status: pre-start scaffold decision for `PB-TRIAL-0-A`.

Authority layer: planning / pre-lock scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS254.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold decision is scoped to `vNext+254` / `PB-TRIAL-0-A` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS254.md`.
- It does not authorize worker dispatch, command execution, candidate
  artifact snapshotting, local trial execution capture, lifecycle projection,
  local outcome audit, trial observation summary, remand decision, retry
  dispatch authority, official ProgramBench participation, official task
  execution, official runner integration, official evaluator integration,
  hidden-test handling, hidden-test inference, hidden-test equivalence,
  original source lookup, decompilation, internet lookup inside ProgramBench
  tasks, external repository lookup, benchmark submission, benchmark scoring,
  benchmark truth, model ranking, generated official submissions, official
  submission authority, unbounded command execution, target mutation outside
  released local artifacts, runtime transition, product authorization,
  graph-memory authority, recursive policy amendment, or future-family
  selection.

## Pre-Start Decision

Recommended scaffold decision:

- gate decision:
  - `PB_TRIAL_0A_STARTER_READY_FOR_IMPLEMENTATION_LOCK_REVIEW`
- rationale:
  - `PB-TRIAL-0` has been selected in planning as the next ProgramBench
    practical family after `PB-ATTEMPT-0`;
  - `PB-TRIAL-0-A` is the correct first slice because it remains non-executing
    and packages only docket, runbook, readiness, and guardrail surfaces;
  - the starter hardens the major review edge by treating prior
    `PB-ATTEMPT-0` result-review rows as lifecycle context only, not as the
    new trial outcome;
  - the starter requires runbook hash, input materialization policy, and
    sandbox witness requirements before later execution can be reviewed;
  - local execution remains deferred to `PB-TRIAL-0-B`.

## Required Exit Criteria For Later Closeout

The later closeout decision should require evidence that:

- `PB-TRIAL-0-A` shipped only trial docket, execution runbook, sandbox
  readiness review, and non-authority guardrail shapes;
- released `PB-ATTEMPT-0` lifecycle refs and family closeout alignment were
  required before validation;
- trial docket selected exactly one attempt lifecycle package;
- prior `PB-ATTEMPT-0` result-review rows stayed lifecycle context only and
  were not counted as trial outcome evidence;
- execution runbook included worker input packet hash, worker-visible context
  hash, runbook hash, trial input materialization policy ref, sandbox/budget
  refs, and sandbox witness requirement refs;
- sandbox readiness required network disabled, source lookup disabled,
  decompilation disabled, Docker socket absent, host secrets absent, bounded
  write scope, closed tool manifest, and run budget;
- readiness marked ready required every readiness row to map to a later B
  witness requirement;
- non-closed tool manifest could not validate as ready;
- no worker dispatch, command execution, candidate snapshot, lifecycle
  projection, outcome audit, retry authority, official benchmark authority, or
  future-family selection shipped.

## Recommended Verification

- docs-only starter bundle:
  - `make arc-start-check ARC=254`
- later implementation PR:
  - focused `PB-TRIAL-0-A` pytest
  - `make check`

