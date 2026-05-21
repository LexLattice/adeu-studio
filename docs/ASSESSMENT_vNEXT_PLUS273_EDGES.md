# Assessment vNext+273 Edges

Status: starter edge assessment for `HOB-0-B`.

Authority layer: planning / starter gate.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS273_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: B Re-Decides Semantic Applicability

- Risk:
  closure planning could decide whether a parent applies instead of consuming
  A activation rows.
- Starter containment:
  B consumes released A records and validates catalog/hash continuity. It may
  compute closure over selected subtrees only.

### Edge 2: Closure Becomes Product Truth

- Risk:
  a closed subtree could be read as product behavior correctness.
- Starter containment:
  closure reports are broker-accounting artifacts only; probe execution,
  product behavior truth, ProgramBench integration, and score attribution are
  excluded.

### Edge 3: Probe Plan Becomes Observation

- Risk:
  planned probe rows could be written as if behavior was observed.
- Starter containment:
  probe matrix rows require `probe_authority_posture =
  plan_only_not_observed` and non-execution posture.

### Edge 4: Batch Contract Becomes Worker Dispatch

- Risk:
  implementation batch contracts could become permission to assign workers.
- Starter containment:
  batch contracts are planning records only and require
  `worker_dispatch_authority_posture = no_worker_dispatch_authority`.

### Edge 5: Parent Readiness Exceeds Weakest Child

- Risk:
  a parent could be marked gold-ready while a required child is scoped,
  blocked, deferred, or representative-only.
- Starter containment:
  weakest-child readiness rows are required, and parent closure cannot exceed
  the weakest required child.

### Edge 6: Representative-Only Closure Launders Partial Coverage

- Risk:
  representative coverage could be marked fixed or gold-ready.
- Starter containment:
  representative-only branches have distinct closure basis and cannot produce
  fixed/gold readiness.

### Edge 7: A Validation Blockers Are Ignored

- Risk:
  B could compute closure from a ledger that A already marked invalid.
- Starter containment:
  consumed A validation blockers force `blocked_by_A_validation` closure.

### Edge 8: Frontier Prioritization Hides Blockers

- Risk:
  prioritization could remove blocked/frontier rows from the next work set.
- Starter containment:
  next-frontier reports preserve source frontier refs, blocker refs, priority
  rows, and batchability rows separately.

### Edge 9: C Attribution Sneaks Into B

- Risk:
  B could attribute score/failure deltas or invalidate stale ledgers.
- Starter containment:
  delta attribution, stale-ledger invalidation, integration handoff, and family
  closeout remain deferred to `HOB-0-C`.

### Edge 10: Canonical Determinism Is Claimed But Not Tested

- Risk:
  row-order differences could change closure rows, frontier priorities, or
  hashes.
- Starter containment:
  the starter fixture set requires shuffled input order to preserve output
  order and canonical hashes.

## Current Judgment

`HOB-0-B` is safe to draft as the second slice if it stays limited to closure
reporting, frontier prioritization, plan-only probe matrices, bounded
implementation batch contracts, and operationalization reports over released
`HOB-0-A` artifacts.

The strongest implementation risks are observation leakage and dispatch
leakage. The first B PR should prove plan-only behavior with small deterministic
fixtures before any probe runner, worker orchestration, or delta-attribution
machinery is added.
