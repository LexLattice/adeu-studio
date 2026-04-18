# Assessment vNext+176 Edges

Status: pre-lock edge assessment for `V64-A`.

Authority layer: planning scaffold only.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS176_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Writable Surface Could Collapse Back Into Continuity Law

- Risk:
  continuity region or occupancy posture could be over-read as writable
  entitlement instead of context / persistence basis.
- Response:
  keep continuity and entitlement distinct.
  - continuity region is persistence/context law
  - writable-surface descriptor and lease are entitlement law
  - neither silently collapses into the other

### Edge 2: `V64-A` Could Widen Two Authority Axes At Once

- Risk:
  the starter slice could widen both surface scope and mutation semantics in one
  pass.
- Response:
  widen surface only in the starter slice.
  - keep one declared subtree or file-set only
  - preserve current `local_write` / `create_new` semantics only
  - defer broader mutation semantics to later `V64`

### Edge 3: Path Membership Could Be Laundered Through Aliases Or Indirection

- Risk:
  path strings, symlinks, aliases, or implicit descendants could let out-of-scope
  targets appear in-scope.
- Response:
  keep membership canonical and fail-closed.
  - canonical normalized path membership required
  - explicit inclusion / exclusion basis required
  - symlink / alias / indirection surprises fail closed

### Edge 4: The Lease Could Become Blanket Standing Authority Inside The Surface

- Risk:
  once a surface lease exists, later code or review could treat it as sufficient
  entitlement for every target path within that surface.
- Response:
  keep per-target admission explicit.
  - lease alone is not enough
  - per-target occupancy / admissibility basis remains required
  - missing or inconsistent target basis fails closed

### Edge 5: Communication Or Remote Lineage Could Drift Into Repo Entitlement

- Risk:
  communication approval lineage or closed remote-control posture could be
  over-read as repo-surface authority.
- Response:
  keep communication and remote posture contextual only here.
  - communication lineage may contextualize or justify write posture
  - communication lineage is not the writable lease
  - remote operator law remains outside `V64`

### Edge 6: `V64-A` Could Smuggle Shell / Execute / Dispatch / Worker Authority

- Risk:
  the first writable-surface slice could become a stealth shell, execute, dispatch,
  or worker-export foothold.
- Response:
  keep repo-surface authority path-local and lease-shaped only.
  - not shell authority
  - not execute authority
  - not dispatch authority
  - not delegated worker authority

## Current Judgment

- `V64-A` is the right next slice because `V59` already closed continuity over one
  exact path, while the repo still lacks first-class writable-surface authority
  over a selected subtree or file-set.
- the follow-on should stay properly bounded:
  - one selected writable surface only
  - one bounded write lease only
  - one repo-surface admission posture only
  - explicit `V59` / `V60` / `V61` basis consumption
  - surface widening only, not mutation-semantics widening
  - canonical path-membership and per-target admissibility
  - no shell / execute / dispatch / worker / all-repo widening
- if `V64-A` lands cleanly, later `V64` work should handle restoration and
  hardening over that same selected writable-surface lineage rather than broadening
  authority in place.
