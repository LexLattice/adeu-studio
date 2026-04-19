# Assessment vNext+177 Edges

Status: pre-lock edge assessment for `V64-B`.

Authority layer: planning scaffold only.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS177_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Restoration Could Reopen Surface Selection Or Lease Issuance

- Risk:
  a follow-on restoration slice could quietly behave like fresh surface-selection
  or fresh lease-issuance law instead of consuming shipped `V64-A` basis.
- Response:
  keep restoration downstream of shipped `V64-A`.
  - same selected writable surface only
  - same shipped lease only
  - restoration is not fresh entitlement by itself

### Edge 2: Restoration Could Drift Beyond The Exact Admitted Target

- Risk:
  once a writable surface exists, restoration could start acting over other
  in-surface paths or even outside the selected surface.
- Response:
  keep restoration exact and fail-closed.
  - same exact admitted target only
  - target membership basis remains explicit
  - target occupancy / admissibility basis remains explicit
  - non-admitted or out-of-surface targets fail closed
  - no blanket standing restoration authority

### Edge 3: Restoration Could Behave Like Fresh Target Admission

- Risk:
  a follow-on restoration seam could quietly re-admit a target rather than
  consume the shipped `V64-A` target-admission and concrete write-effect basis.
- Response:
  keep restoration downstream of shipped effect and target-admission law.
  - restoration is not fresh target admission by itself
  - shipped write-effect lineage remains explicit
  - missing or inconsistent target carry-through fails closed

### Edge 4: `V64-B` Could Widen Mutation Semantics Indirectly

- Risk:
  a restoration seam could smuggle append / overwrite / rename / delete semantics
  under the label of reintegration.
- Response:
  preserve the shipped `V64-A` write posture only.
  - same narrow `local_write` / `create_new` posture only
  - broader mutation semantics stay deferred

### Edge 5: Continuity Or Communication Basis Could Drift Into Fresh Repo Entitlement

- Risk:
  restoration review could overread shipped `V59` or `V61` lineage as if they
  minted fresh repo authority.
- Response:
  keep consumed basis contextual and bounded.
  - continuity remains continuity law
  - communication remains communication law
  - neither becomes fresh writable entitlement here

### Edge 6: Reintegration Could Become Broad Repo-Admin Law

- Risk:
  a reintegration report could be interpreted as approval for all-repo or
  multi-target authority rather than one bounded restoration lineage.
- Response:
  keep reintegration path-local and lineage-local only.
  - not all-repo authority
  - not shell authority
  - not execute authority
  - not dispatch authority
  - not delegated worker authority

## Current Judgment

- `V64-B` is the right next slice because `V64-A` already closed the first-class
  writable-surface descriptor / lease / admission seam on `main`, while the repo
  still lacks a typed restoration / reintegration path over that same shipped
  lineage.
- the follow-on should stay properly bounded:
  - one shipped `V64-A` surface lineage only
  - one exact admitted target only
  - one restoration record only
  - one reintegration report only
  - explicit `V59` / `V60` / `V61` basis consumption
  - no fresh surface selection or fresh lease issuance
  - no mutation-semantics widening
  - no all-repo / shell / execute / dispatch / worker widening
- if `V64-B` lands cleanly, later `V64` work should handle advisory writable-
  surface hardening in `V64-C` rather than broadening restoration authority in
  place.
