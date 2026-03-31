# Draft Stop-Gate Decision vNext+102

Status: proposed gate for `V45-C` corrective hardening (`100-bis`).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS102.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `repo_arc_dependency_register@2` schema validates and exports cleanly with
  authoritative/mirror parity;
- deterministic entrypoint(s) materialize the accepted corrective reference fixture from
  one bounded snapshot on repeated runs;
- outputs carry explicit source-set binding, source-set hash, extraction posture, and
  extraction method;
- entry and edge rows carry explicit derivation posture, derivation method, and source
  artifact refs;
- outputs carry explicit cycle posture, cycle detection scope, and pending-list posture;
- blocker-list projections reconcile exactly with the incoming unresolved hard-blocking
  dependency-edge subset for each blocked entry;
- fail-closed rules reject:
  - missing provenance anchors;
  - missing derivation posture or method;
  - `source_artifact_ref` outside the declared `source_set`;
  - blocker-list / dependency-edge inconsistency;
  - missing cycle posture or cycle detection scope;
  - undefined pending-list posture;
  - retained `supports_all_three_way_claim` or equivalent undefined vocabulary;
  - scheduling or mutation entitlement laundering;
- Python tests cover schema/model validation, schema parity, deterministic replay, and
  rejection behavior.

## Do Not Accept If

- the corrective slice silently rewrites released `repo_arc_dependency_register@1` in
  place rather than emitting a bounded corrective release posture;
- the artifact still blurs planning/open-arc dependency posture with the later
  `repo_dependency_graph` surface;
- the slice widens into symbol catalog release, code dependency-graph release,
  test-intent matrix release, optimization-register release, or recursive-governance
  binding.

## Local Gate

- run `make arc-start-check ARC=102`
