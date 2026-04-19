# Assessment vNext+177 Edges

Status: post-closeout edge assessment for `V64-B` (April 19, 2026 UTC).

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS177_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Restoration Could Reopen Surface Selection Or Lease Issuance

- Risk:
  a restoration follow-on could quietly behave like fresh surface-selection or
  fresh lease-issuance law instead of consuming shipped `V64-A` basis.
- Response:
  keep `V64-B` downstream of shipped `V64-A`.
  - same selected writable surface only
  - same shipped lease only
  - restoration is not fresh entitlement by itself
- Closeout Evidence:
  shipped checker/tests enforce exact shipped `V64-A` descriptor/lease/admission
  lineage and reject non-`V64-A` basis.

### Edge 2: Restoration Could Drift Beyond The Exact Admitted Target

- Risk:
  restoration could start acting over other in-surface paths or out-of-surface
  paths once a writable surface exists.
- Response:
  keep restoration exact and fail-closed.
  - same exact admitted target only
  - target membership basis remains explicit
  - target occupancy/admissibility basis remains explicit
  - non-admitted or out-of-surface targets fail closed
  - no blanket standing restoration authority
- Closeout Evidence:
  shipped checker/tests enforce exact shipped admitted target carry-through and
  reject target mismatch.

### Edge 3: Restoration Could Behave Like Fresh Target Admission

- Risk:
  `V64-B` could quietly re-admit a target rather than consume shipped `V64-A`
  target-admission and shipped `V59-A` write-effect lineage.
- Response:
  keep restoration downstream of shipped effect/admission law.
  - restoration is not fresh target admission by itself
  - shipped observed/conformance effect lineage remains explicit
  - missing or inconsistent basis fails closed
- Closeout Evidence:
  shipped checker/tests enforce exact shipped `V59-A` observed/conformance
  lineage and explicit non-fresh-admission posture in restoration summaries.

### Edge 4: Restoration Input Paths Could Launder Authority Through Alias Or Symlink

- Risk:
  lexically outside paths or symlink-root indirection could make out-of-scope
  inputs appear repo-local.
- Response:
  keep input-path posture canonical and fail-closed.
  - V64-B inputs must remain lexically inside repo root
  - symlink repo root is rejected
  - lexical alias paths fail closed
- Closeout Evidence:
  shipped checker/tests enforce lexical repo-local path checks and symlink-root
  rejection for `V64-B`.

### Edge 5: `V64-B` Could Widen Mutation Semantics Indirectly

- Risk:
  reintegration could smuggle `append`/`overwrite`/`rename`/`delete` semantics
  under a restoration label.
- Response:
  preserve shipped `V64-A` write posture only.
  - same narrow `local_write/create_new` posture only
  - broader mutation semantics remain deferred
- Closeout Evidence:
  shipped restoration summaries and checker/tests preserve
  `local_write/create_new` posture and explicit no-widening law.

### Edge 6: Reintegration Could Be Over-Read As Broad Repo-Admin Law

- Risk:
  one reintegration report could be interpreted as all-repo or multi-target
  standing authority.
- Response:
  keep reintegration path-local and lineage-local only.
  - not all-repo authority
  - not shell authority
  - not execute authority
  - not dispatch authority
  - not delegated worker authority
  - not connector or remote-operator law
- Closeout Evidence:
  shipped checker/tests and record summaries preserve explicit
  non-generalization/non-equivalence posture.

## Current Judgment

- `V64-B` was the right next slice because `V64-A` already closed first-class
  writable-surface descriptor/lease/admission law on `main`, while the repo still
  lacked a typed restoration/reintegration seam over that same shipped lineage.
- the shipped result remained properly bounded:
  - one shipped `V64-A` writable-surface lineage only
  - one exact admitted target only
  - one typed restoration record only
  - one typed reintegration report only
  - explicit shipped `V59-A` write-effect observation/conformance consumption
  - explicit shipped `V60`/`V61` lineage consumption
  - no fresh surface selection, lease issuance, or target admission
  - no mutation-semantics widening
  - no all-repo/shell/execute/dispatch/worker/connector/remote widening
- `V64-B` is now closed on `main`.
- the next same-family move should be `V64-C` hardening, not broader restoration
  authority in place.
