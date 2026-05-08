# Draft Stop-Gate Decision vNext+255

Status: pre-start scaffold decision for `PB-TRIAL-0-B`.

Authority layer: planning / pre-lock scaffold.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS255.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Decision Guardrail

- This scaffold decision is scoped to `vNext+255` / `PB-TRIAL-0-B` only.
- It does not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS255.md`.
- It does not authorize trial outcome audit, observation summary, remand
  decision, retry dispatch authority, official ProgramBench participation,
  official task execution, official runner integration, official evaluator
  integration, hidden-test handling, hidden-test inference, hidden-test
  equivalence, original source lookup, decompilation, internet lookup inside
  ProgramBench tasks, external repository lookup, benchmark submission,
  benchmark scoring, benchmark truth, model ranking, generated official
  submissions, official submission authority, unbounded command execution,
  target mutation outside released local sandbox/write scope, runtime
  transition, product authorization, graph-memory authority, recursive policy
  amendment, or future-family selection.

## Pre-Start Decision

Recommended scaffold decision:

- gate decision:
  - `PB_TRIAL_0B_STARTER_READY_FOR_IMPLEMENTATION_LOCK_REVIEW`
- rationale:
  - `PB-TRIAL-0-A` has closed on `main` as the non-executing docket/runbook/
    readiness seam;
  - `PB-TRIAL-0-B` is the correct next slice because it records the single
    local dispatch specimen and local evidence that A only planned;
  - the starter hardens the major execution edge by requiring released A
    readiness, B-lock dispatch authority, sandbox witness refs, exact input
    hashes, and forbidden-content screening before candidate snapshots;
  - outcome audit, observation summary, remand decision, family closeout, and
    retry authority remain deferred to `PB-TRIAL-0-C`.

## Required Exit Criteria For Later Closeout

The later closeout decision should require evidence that:

- `PB-TRIAL-0-B` shipped only worker dispatch record, execution capture,
  candidate artifact snapshot, and lifecycle projection shapes;
- released `PB-TRIAL-0-A` docket/runbook/readiness/guardrail refs were
  required before validation;
- dispatch records could not validate unless A readiness was ready;
- dispatch records required a `dispatch_authority_ref` tied to the B lock;
- exactly one dispatch specimen per trial docket was enforced;
- dispatch records were hash-bound to the A worker input packet, visible
  context, tool manifests, sandbox instance, sandbox attestation bundle, and
  input materialization;
- local execution capture required transcript/stdout/stderr hashes, bounded
  excerpts, exit/duration/timeout status, output capture policy, worker tool
  call manifest, sandbox witnesses, and forbidden-content screen verdict;
- candidate snapshots were blocked unless forbidden-content screening passed;
- candidate snapshots stayed inside released write scope and carried
  pre/post manifests, fs diff refs, snapshot manifest hash, and generated
  file hashes;
- lifecycle projection mapped to released `PB-ATTEMPT-0` lifecycle refs and
  could not define new evidence law;
- no C-slice artifacts, official benchmark authority, retry authority, model
  ranking, benchmark truth, or future-family selection shipped.

## Recommended Verification

- docs-only starter bundle:
  - `make arc-start-check ARC=255`
- later implementation PR:
  - focused `PB-TRIAL-0-B` pytest
  - `make check`
