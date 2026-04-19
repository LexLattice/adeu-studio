# Assessment vNext+178 Edges

Status: pre-lock edge assessment for `V64-C`.

Authority layer: planning scaffold only.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS178_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Advisory Hardening Could Quietly Reopen `V64-A` Or `V64-B` Law

- Risk:
  the advisory layer could start replacing shipped writable-surface selection,
  lease, admission, restoration, or reintegration semantics instead of consuming
  them.
- Response:
  keep `V64-A` and `V64-B` authoritative.
  - shipped `V64-A` descriptor / lease / admission remain the only entitlement basis
  - shipped `V64-B` restoration / reintegration remain consumed-only
  - advisory output is not fresh writable entitlement by itself

### Edge 2: Advisory Output Could Become A Soft Repo Sovereign

- Risk:
  one favorable hardening recommendation could drift into apparent permission to
  select surfaces, issue leases, restore targets, or broaden repo authority.
- Response:
  keep advisory output non-entitling and non-sovereign.
  - advisory output is not surface selection
  - advisory output is not lease issuance
  - advisory output is not target admission
  - advisory output is not restoration authority
  - advisory output is not repo authority

### Edge 3: Narrative Review Could Replace Committed Evidence Basis

- Risk:
  reviewer interpretation or prose could silently outrank the committed shipped
  lineage that the hardening register is supposed to evaluate.
- Response:
  keep committed artifacts first-class and fail closed on drift.
  - committed lane artifacts outrank narrative interpretation
  - explicit evidence basis remains separate from recommendation
  - same evidence chain plus same frozen policy yields the same recommendation

### Edge 4: Optional Restoration Or Reintegration Basis Could Be Over-Read

- Risk:
  absent or mismatched optional upstream restoration / reintegration refs could
  be treated as if restoration-local evidence had been lawfully carried into the
  hardening register.
- Response:
  keep optional upstream basis explicit and fail-closed.
  - if both optional refs are `none`, no restoration-local overread
  - restoration ref may appear alone only for restoration-local evidence
  - reintegration ref may not appear without restoration ref
  - co-present refs must remain one shipped restoration chain
  - if present, they must match selected writable-surface and target posture
  - selected write-effect or restoration-kind summary stays explicit where present

### Edge 5: Advisory Basis Could Overread Non-Selected Write Semantics

- Risk:
  restoration-local evidence could be read as if append / overwrite / rename /
  delete were in play even though `V64` still preserves the narrow shipped
  write posture.
- Response:
  carry preserved write semantics directly in the evidence basis.
  - preserved write-semantics summary remains explicit
  - non-selected mutation semantics may not be inferred from restoration-local evidence

### Edge 6: One Writable Exemplar Could Be Over-Read As Broad Repo-Admin Law

- Risk:
  one shipped admitted writable path could be treated as if it proves broad
  repo-admin, all-repo, or all-surface authority law.
- Response:
  keep the advisory path exact and non-generalizing by default.
  - one admitted writable path only
  - not broad repo-admin law
  - not all-repo authority
  - not all-device or all-surface law

### Edge 7: Continuity Or Communication Lineage Could Drift Into Fresh Repo Entitlement

- Risk:
  shipped `V59` or `V61` lineage could be overread as if it minted writable
  entitlement rather than contextualizing the advisory posture.
- Response:
  keep consumed basis contextual and bounded.
  - continuity remains continuity law
  - communication remains communication law
  - neither becomes fresh writable entitlement here

### Edge 8: Advisory Register Could Quietly Swallow Shell / Execute / Dispatch / Worker Law

- Risk:
  once writable-surface hardening exists, later code or reviewers could overread
  it as a standing foothold for shell, execute, dispatch, or worker authority.
- Response:
  keep the advisory seam writable-lineage-local only.
  - not shell authority
  - not execute authority
  - not dispatch authority
  - not delegated worker authority
  - no advisory-to-live promotion

## Current Judgment

- `V64-C` is the right next slice because `V64-A` already closed the first-class
  writable-surface descriptor / lease / admission seam on `main`, `V64-B`
  already closed the restoration / reintegration seam on `main`, and the repo
  still lacks a typed advisory hardening path over that same shipped lineage.
- the follow-on should stay properly bounded:
  - one shipped `V64-A` / `V64-B` lineage only
  - one selected writable surface only
  - one exact admitted target only
  - one advisory hardening register only
  - explicit `V59` / `V60` / `V61` basis consumption
  - explicit evidence-vs-recommendation separation
  - explicit committed-artifact precedence and frozen-policy replayability anchor
  - explicit preserved write-semantics carry-through
  - no all-repo / shell / execute / dispatch / worker widening
- if `V64-C` lands cleanly, later work should move to `V65` rather than reopen
  `V64` with live authority widening.
