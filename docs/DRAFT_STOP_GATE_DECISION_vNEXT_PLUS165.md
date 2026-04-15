# Draft Stop-Gate Decision vNext+165

Status: proposed gate for `V60-B`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS165.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the shipped `V60-A` loop identity is consumed by default rather than reopened;
- the shipped `V60-A` loop-state ledger remains the canonical stable loop anchor in
  `V60-B`;
- one refreshed residual packet is derived replayably from prior continuation lineage
  plus one latest reintegrated act lineage;
- latest reintegrated act selection is explicit and fail-closed rather than
  summary-only;
- one refreshed continuation decision stays typed and replayable over the declared
  evidence chain;
- `reproposal_required` remains typed posture only and does not reopen raw transcript
  or seed-ingress law, and it does not act as implicit charter amendment;
- only `continue_to_governed_act` may descend into the shipped act ladder in this
  slice;
- `emit_governed_communication` remains posture-only and does not ship `V61` packet
  law or office binding;
- Python tests cover:
  - refresh derivation
  - refreshed continuation decision
  - fail-closed lineage mismatch
  - fail-closed reproposal posture without seed-law widening
  - fail-closed exact selected-path preservation

## Do Not Accept If

- `V60-B` recompiles or widens starter seed ingress;
- loop identity becomes ambiguous or is silently replaced under cover of refresh;
- latest reintegrated act selection is ambiguous, narrative-only, or not fail-closed;
- refreshed residual behaves like standing permission or stretched ticket authority;
- reproposal posture silently becomes raw transcript semantics or generic chat memory;
- communication packet law, office binding, connector admission, or remote operator
  surfaces land under cover of `V60-B`;
- repo-bound writable authority, replay/resume widening, execute widening, or
  dispatch widening land in this slice;
- `V56` ticket duration is widened beyond `single_step_local`.

## Local Gate

- docs-only starter bundle validation:
  - `make arc-start-check ARC=165`
- implementation-phase local gate:
  - `make check`
