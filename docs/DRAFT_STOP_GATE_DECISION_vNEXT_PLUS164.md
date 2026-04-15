# Draft Stop-Gate Decision vNext+164

Status: proposed gate for `V60-A`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS164.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- starter seed intent is represented by one typed bounded artifact rather than raw
  transcript semantics;
- the shipped `V56` / `V57` / `V58` / `V59` lineage is consumed by default rather than
  reopened;
- one task charter packet compiles deterministically from the starter seed-intent
  record and frozen policy basis;
- one task residual packet remains derived and replayable rather than human-authored
  law;
- one loop-state ledger binds charter, residual, resident session, continuity region,
  and latest reintegration lineage without collapsing into transcript memory;
- one continuation decision record stays typed and replayable over the declared
  evidence chain;
- only `continue_to_governed_act` may descend into the shipped act ladder in this
  slice;
- `emit_governed_communication` remains posture-only and does not ship `V61` packet
  law or office binding;
- Python tests cover:
  - seed-intent validation
  - charter compilation
  - residual derivation
  - loop-state binding
  - continuation outcome replay
  - fail-closed non-chat-native ingress posture

## Do Not Accept If

- starter seed intent is compiled from raw transcript or generic chat memory;
- `TaskResidual` behaves like standing permission or stretched ticket authority;
- continuation decision is opaque or non-replayable;
- communication packet law, office binding, connector admission, or remote operator
  surfaces land under cover of `V60-A`;
- repo-bound writable authority, replay/resume widening, execute widening, or dispatch
  widening lands in this slice;
- `V56` ticket duration is widened beyond `single_step_local`;
- earlier hardening/advisory surfaces are over-read as live authority.

## Local Gate

- docs-only starter bundle validation:
  - `make arc-start-check ARC=164`
- implementation-phase local gate:
  - `make check`
