# Assessment vNext+178 Edges

Status: post-closeout edge assessment for `V64-C` (April 19, 2026 UTC).

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS178_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Advisory Hardening Could Quietly Reopen `V64-A` Or `V64-B` Law

- Risk:
  the advisory layer could start replacing shipped writable-surface selection,
  lease, admission, restoration, or reintegration semantics instead of
  consuming them.
- Response:
  keep `V64-A` and `V64-B` authoritative.
  - shipped `V64-A` descriptor / lease / admission remain the only entitlement basis
  - shipped `V64-B` restoration / reintegration remain consumed-only
  - advisory output is not fresh writable entitlement by itself
- Closeout Evidence:
  shipped checker/tests enforce exact shipped `V64-A` / `V64-B` lineage and
  reject mismatched entitlement or restoration-chain basis.

### Edge 2: Advisory Output Could Become A Soft Repo Sovereign

- Risk:
  one favorable hardening recommendation could drift into apparent permission to
  select surfaces, issue leases, admit targets, restore targets, or broaden
  repo authority.
- Response:
  keep advisory output non-entitling and non-sovereign.
  - advisory output is not surface selection
  - advisory output is not lease issuance
  - advisory output is not target admission
  - advisory output is not restoration authority
  - advisory output is not repo authority
- Closeout Evidence:
  shipped register/checker/tests preserve bounded advisory outcome allowlists
  and explicit non-equivalence to live writable authority.

### Edge 3: Narrative Review Could Replace Committed Evidence Basis

- Risk:
  reviewer interpretation or prose could silently outrank the committed shipped
  lineage that the hardening register is supposed to evaluate.
- Response:
  keep committed artifacts first-class and fail closed on drift.
  - committed lane artifacts outrank narrative interpretation
  - explicit evidence basis remains separate from recommendation
  - same evidence chain plus same frozen policy yields the same recommendation
- Closeout Evidence:
  shipped checker/tests preserve committed-artifact precedence, explicit
  evidence-vs-recommendation separation, and replayable same-input outputs.

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
- Closeout Evidence:
  shipped checker/tests enforce the optional-ref combination matrix and reject
  reintegration-without-restoration or mismatched restoration-chain posture.

### Edge 5: Advisory Basis Could Overread Non-Selected Write Semantics

- Risk:
  restoration-local evidence could be read as if `append` / `overwrite` /
  `rename` / `delete` were in play even though `V64` still preserves the narrow
  shipped write posture.
- Response:
  carry preserved write semantics directly in the evidence basis.
  - preserved write-semantics summary remains explicit
  - non-selected mutation semantics may not be inferred from restoration-local evidence
- Closeout Evidence:
  shipped register/checker/tests preserve explicit
  `local_write/create_new` carry-through and reject restoration-local posture
  drift.

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
- Closeout Evidence:
  shipped checker/tests and register summaries preserve explicit path-level
  non-generalization and reject broader authority overread.

### Edge 7: Continuity Or Communication Lineage Could Drift Into Fresh Repo Entitlement

- Risk:
  shipped `V59` or `V61` lineage could be overread as if it minted writable
  entitlement rather than contextualizing the advisory posture.
- Response:
  keep consumed basis contextual and bounded.
  - continuity remains continuity law
  - communication remains communication law
  - neither becomes fresh writable entitlement here
- Closeout Evidence:
  shipped checker/tests consume shipped `V60` / `V61` lineage in bounded
  advisory posture only and preserve non-equivalence to fresh writable
  entitlement.

### Edge 8: Repo-Root Or Input-Path Handling Could Launder Out-Of-Scope Inputs

- Risk:
  lexically outside paths, symlink-root indirection, or a missing explicit
  repo-root override could produce confusing or widened input handling.
- Response:
  keep input-path posture canonical and fail-closed.
  - inputs must remain lexically inside repo root
  - symlink repo root is rejected
  - explicit missing repo root fails closed immediately
  - lexical alias paths fail closed
- Closeout Evidence:
  shipped checker/tests enforce lexical repo-local paths, symlink-root
  rejection, and the follow-up missing-root failure path in `eb87967`.

### Edge 9: Advisory Register Could Quietly Swallow Shell / Execute / Dispatch / Worker Law

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
- Closeout Evidence:
  shipped checker/tests and register summaries preserve explicit
  non-generalization into shell / execute / dispatch / worker authority.

## Current Judgment

- `V64-C` was the right next slice because `V64-A` already closed the first-class
  writable-surface descriptor / lease / admission seam on `main`, `V64-B`
  already closed the restoration / reintegration seam on `main`, and the repo
  still lacked a typed advisory hardening path over that same shipped lineage.
- the shipped result remained properly bounded:
  - one shipped `V64-A` / `V64-B` lineage only
  - one selected writable surface only
  - one exact admitted target only
  - one advisory hardening register only
  - explicit `V60` / `V61` lineage consumption
  - explicit evidence-vs-recommendation separation
  - explicit committed-artifact precedence and frozen-policy replayability anchor
  - explicit optional restoration / reintegration basis fail-closed posture
  - explicit preserved write-semantics carry-through
  - explicit missing-root and repo-local input fail-closed posture
  - no all-repo / shell / execute / dispatch / worker widening
- `V64-C` is now closed on `main`.
- `V64` is now closed on `main`.
- the next family move should be `V65`, not more widening inside `V64`.
