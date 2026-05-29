# Draft Stop-Gate Decision vNext+280

Status: pre-start scaffold for `BRL-0-C`.

Authority layer: planning.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS280.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Pre-Start Decision

This scaffold selects `BRL-0-C` as the next bounded implementation candidate
inside the already selected `BRL-0` family, contingent on the starter lock in
`docs/LOCKED_CONTINUATION_vNEXT_PLUS280.md`.

The slice may consume released `BRL-0-A` and `BRL-0-B` records to implement
impact-cone sentinel selection, bounded no-regression certificates,
stale-lock reports, and integration handoff rows. It must not generate probes,
execute replay commands, update expected hashes, authorize HOB closure, grant
OTB transition legality, claim product truth, or claim official-eval readiness.

## Required Closeout Evidence Later

The eventual closeout decision must record:

- merged implementation PR and merge commit;
- implementation commits and package boundary;
- focused `BRL-0-C` tests and schema export verification;
- local gate used before PR / review updates;
- GitHub CI status;
- deterministic closeout artifacts;
- `BRL-0-C` edge assessment;
- explicit confirmation that product truth, HOB closure, OTB transition
  legality, and official-eval readiness remain forbidden promotions.
