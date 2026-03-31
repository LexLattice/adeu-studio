# Draft Stop-Gate Decision vNext+101

Status: proposed gate for `V45-B`.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS101.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- canonical `repo_symbol_catalog@1` and `repo_dependency_graph@1` schemas validate and
  export cleanly with authoritative/mirror parity;
- deterministic entrypoint(s) materialize the accepted symbol-catalog and
  dependency-graph reference fixtures from one bounded snapshot on repeated runs;
- outputs carry explicit snapshot identity/hash, explicit source-set binding, and
  explicit stale-snapshot posture;
- symbol rows carry typed identity/module/qualname/kind/classification posture fields;
- dependency edges carry typed source/target/kind/posture fields;
- fail-closed rules reject:
  - dangling symbol or dependency targets;
  - duplicate symbol or edge identities;
  - missing source-set or snapshot binding;
  - missing dependency posture;
  - refactor or mutation entitlement laundering from descriptive diagnostics;
- Python tests cover schema/model validation, schema parity, deterministic replay, and
  rejection behavior.

## Do Not Accept If

- symbol or dependency outputs are used as automatic refactor authority;
- dependency outputs are treated as scheduling or mutation entitlement;
- snapshot-bound outputs are presented as current truth without freshness posture;
- the slice widens into test-intent matrix release, optimization-register release, or
  recursive-governance binding.

## Local Gate

- run `make arc-start-check ARC=101`
