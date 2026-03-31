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
- outputs carry explicit snapshot identity/hash, explicit source-set binding,
  `source_set_hash`, explicit extraction posture/method, and explicit stale-snapshot
  posture;
- symbol rows carry typed identity/module/qualname/kind/classification posture fields
  plus explicit source artifact refs;
- dependency edges carry typed endpoint-kind/source-target/kind/posture fields plus
  explicit derivation posture/method;
- accepted catalog and graph fixtures reconcile over one shared snapshot/source-set
  identity;
- fail-closed rules reject:
  - dangling symbol or dependency targets;
  - out-of-scope dependency endpoints lacking valid boundary typing;
  - duplicate symbol or edge identities;
  - mismatched snapshot/source-set identity across the paired artifacts;
  - missing source-set hash, extraction posture/method, or per-edge derivation
    posture/method;
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
