# Draft Stop-Gate Decision vNext+100

Status: proposed gate for `V45-C`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS100.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `repo_arc_dependency_register@1` schema validates and exports cleanly with
  authoritative/mirror parity;
- one deterministic entrypoint materializes the accepted dependency-register reference
  fixture from one bounded snapshot on repeated runs;
- outputs carry explicit snapshot identity/hash and explicit stale-snapshot posture;
- outputs carry immutable dependency-policy binding through explicit ref plus hash;
- open-arc entries carry typed identity/status/authority/readiness/blocker fields;
- dependency edges carry typed source/target/kind/strength/status fields;
- fail-closed rules reject:
  - dangling dependency edges;
  - duplicate arc or edge identities;
  - contradictory readiness posture with unresolved blockers;
  - cycles without explicit cycle posture;
  - scheduling or mutation entitlement laundering from diagnostics;
- Python tests cover schema/model validation, schema parity, deterministic replay, and
  rejection behavior.

## Do Not Accept If

- dependency outputs are used as automatic planning scheduler authority;
- dependency outputs are treated as mutation entitlement;
- `dependency_policy_ref` exists without immutable hash binding;
- snapshot-bound outputs are presented as current truth without freshness posture;
- the slice widens into symbol catalog, test-intent matrix, optimization register, or
  recursive-governance binding release.

## Local Gate

- run `make arc-start-check ARC=100`
