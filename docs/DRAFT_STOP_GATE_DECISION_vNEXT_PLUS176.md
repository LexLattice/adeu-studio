# Draft Stop-Gate Decision vNext+176

Status: proposed gate for `V64-A`.

Authority layer: planning scaffold only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS176.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "required_in_closeout": true,
  "all_passed": false
}
```

## Accept When

- the new `V64-A` writable-surface starter schemas validate and export cleanly;
- the lane handoff from closed `V63-C` is explicit via
  `agentic_de_lane_drift_record@1`;
- the selected writable surface remains explicit:
  - one declared subtree or file-set only
  - not all-repo authority;
- the consumed basis remains explicit:
  - shipped `V59` continuity lineage only
  - shipped `V60` continuation lineage only
  - shipped `V61` communication lineage only where relevant;
- surface widening remains distinct from mutation-semantics widening:
  - preserve the current `local_write` / `create_new` subset
  - do not widen append / overwrite / rename / delete semantics in `V64-A`;
- continuity region remains distinct from writable entitlement;
- communication lineage may contextualize write posture but does not become the
  writable lease or repo-surface authority;
- writable-surface membership remains canonical and fail-closed:
  - canonical normalized path membership required
  - explicit inclusion / exclusion basis required
  - symlink / alias / indirection surprises fail closed;
- per-target occupancy / admissibility remains required inside the selected
  surface;
- the implementation remains bounded to existing repo-owned packages plus one thin
  starter runner only;
- outputs remain non-equivalent to:
  - shell authority
  - execute authority
  - dispatch authority
  - delegated worker authority
  - remote operator law;
- tests cover:
  - continuity-vs-entitlement non-equivalence
  - communication-vs-entitlement non-equivalence
  - canonical path-membership and fail-closed path handling
  - per-target occupancy/admissibility requirement
  - preserved narrow write semantics only
  - no execute / dispatch / worker / all-repo drift

## Do Not Accept If

- `V64-A` widens writable surface and mutation semantics at the same time;
- continuity region is treated as writable entitlement;
- communication or remote-control lineage is treated as writable entitlement;
- the lease acts as blanket standing authority for every path in the selected
  surface;
- canonical path-membership and fail-closed alias/symlink handling are absent;
- `V64-A` is used to smuggle shell authority, execute authority, dispatch
  authority, delegated worker authority, or all-repo authority into the family.

## Local Gate

- run `make arc-start-check ARC=176`
- full Python lane is intentionally skipped at starter-draft time because this
  bundle is docs-only
