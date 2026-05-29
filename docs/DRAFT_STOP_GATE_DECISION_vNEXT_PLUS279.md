# Draft Stop-Gate Decision vNext+279

Status: pre-start scaffold for `BRL-0-B`.

Authority layer: planning.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS279.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Pre-Start Decision

This scaffold selects `BRL-0-B` as the next bounded implementation candidate
inside the already selected `BRL-0` family, contingent on the starter lock in
`docs/LOCKED_CONTINUATION_vNEXT_PLUS279.md`.

The slice may consume released `BRL-0-A` records and implement replay execution,
canonical observation capture, regression diff, and suite-root hash report
surfaces. It must not select probes, update expected hashes, choose
impact-cone sentinels, issue no-regression certificates, or claim product /
official-eval readiness.

## Required Closeout Evidence Later

The eventual closeout decision must record:

- merged implementation PR and merge commit;
- implementation commits and package boundary;
- focused `BRL-0-B` tests and schema export verification;
- local gate used before PR / review updates;
- GitHub CI status;
- deterministic closeout artifacts;
- `BRL-0-B` edge assessment;
- explicit confirmation that `BRL-0-C` surfaces remain deferred.
