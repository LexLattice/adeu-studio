# Assessment vNext+159 Edges

Status: starter edge assessment for `V58-B` (April 15, 2026 UTC).

Authority layer: starter planning + lock draft only.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS159_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Hidden Cleanup Could Masquerade As Lawful Restoration-State Integration

- Risk:
  once the first live restoration path is added, the harness could still auto-clean up
  successfully and only later emit artifacts as commentary.
- Response:
  require explicit live restoration handoff and reintegration surfaces.
  - no hidden cleanup
  - no hidden compensators
  - no success-by-aftermath reasoning

### Edge 2: Original Ticket Authority Could Be Over-Read As Ambient Ongoing Restore Power

- Risk:
  because `V58-B` stays on the same lineage, the shipped ticket could be misread as if
  it authorizes all later restore acts automatically.
- Response:
  keep restoration a new live act with explicit bounded compensating-scope derivation.
  - original ticket is not ambient ongoing restoration authority
  - restoration must match the exact prior observed/restored lineage or fail closed

### Edge 3: Stale `V58-A` Admission State Could Be Reused For A New Restore Act

- Risk:
  the slice could call restoration a new live act in principle while still leaning on
  stale `V58-A` capability or approval posture in practice.
- Response:
  keep restoration-time admission fresh.
  - same-session and same-turn continuation only
  - restoration-time capability / approval posture must be re-snapshotted
  - mismatch or missing resnapshot fails closed

### Edge 4: Historical Lineage Refs Could Quietly Become Quasi-Ambient Entitlement

- Risk:
  required `action_ticket_ref` or prior reintegration refs could be over-read as if
  they already authorize current-turn restoration by reference alone.
- Response:
  keep those refs historical lineage inputs only.
  - they participate in bounded compensating-scope derivation
  - they never stand in for current-turn restoration witness or entitlement

### Edge 5: Restore-State Integration Could Widen Beyond The Exact `create_new` Exemplar

- Risk:
  the live harness could use one successful compensating restore as if it proved
  append-only restore integration or broader cleanup law.
- Response:
  freeze the selected path exactly:
  - `local_write`
  - `create_new`
  - compensating restore only
  - designated root `artifacts/agentic_de/v57/local_effect/`
  - target centered on `runtime/reference_patch_candidate.diff`
  - no broader class or restoration-family generalization by default

### Edge 6: Transcript / Event Stream / Prior Artifacts Could Be Mistaken For Current-Turn Restoration Witness

- Risk:
  observability echoes or prior fixtures/closeout evidence could be counted as if they
  were native current-turn restoration support.
- Response:
  keep transcript and event stream as observability only, keep prior artifacts as drift
  guards only, and require origin / dependence tags plus root-origin dedup for current
  turn support.

### Edge 7: Replay Could Be Generalized Into Arbitrary Re-Execution

- Risk:
  the word “replay” could drift from bounded recomputation / re-evaluation of the exact
  restoration event into broader re-execution power.
- Response:
  keep replay semantics narrow.
  - bounded recomputation and re-evaluation of the exact restoration event only
  - no arbitrary prior live-action re-execution
  - the replay-law proof surface stays inside the live restoration reintegration
    report rather than implying a separate replay authority surface

### Edge 8: Broader Repo Cleanup Surfaces Could Reappear Under Cover Of Restoration

- Risk:
  restore-state integration could quietly reuse broader cleanup helpers or destructive
  write modes beyond the selected target and sandbox.
- Response:
  keep the slice bound to the exact shipped `V58-A -> V57-B` path only.
  - same designated sandbox root
  - same target path
  - no broader cleanup semantics
  - no broader repo-authority write surface

### Edge 9: Hardening Could Be Smuggled In Early

- Risk:
  once restoration-state integration lands, the repo could start treating that evidence
  as if `V58-C` hardening or migration law had already shipped.
- Response:
  keep hardening explicitly deferred to later `V58-C`.
  - `V58-B` may emit restoration-state evidence only
  - it may not emit hardening or migration outputs in the same slice

### Edge 10: Execute / Dispatch / Product Boundaries Could Blur During Live Integration

- Risk:
  live harness work could be used to reintroduce `local_reversible_execute`, stronger
  execute, delegated/external dispatch, or product/UI authority under a different name.
- Response:
  keep `V58-B` grounded in externalized restoration-state evidence only and preserve
  existing ownership boundaries.
  - `V48` still owns delegated worker execution after any later lawful dispatch
  - no execute widening
  - no product/UI authority source

## Current Judgment

- `V58-B` is the right next slice because `V58-A` closed one bounded live harness bind
  path on `main`, and the next exact gap is explicit restoration-state integration over
  that same lineage.
- the starter should remain properly bounded:
  - existing-session-path-first
  - existing-lineage-first
  - restoration-state-artifact-first
  - exact-exemplar-first
  - non-append-only
  - non-dispatch
  - non-product
  - non-hidden-cognition-governing
- any next move after `V58-B` should depend on whether one exact restoration-state
  path can be integrated and reintegrated without hidden cleanup or authority drift,
  not on appetite for broader cleanup families or action classes.
