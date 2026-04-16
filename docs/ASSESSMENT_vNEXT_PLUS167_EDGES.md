# Assessment vNext+167 Edges

Status: post-closeout edge assessment for `V61-A` (April 16, 2026 UTC).

Authority layer: closeout evidence on `main`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS167_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: `V61-A` Could Quietly Reopen `V60` Task-Law Compilation

- Risk:
  message interpretation could be over-read as if communication already recompiled
  charter or continuation law.
- Response:
  keep `V61-A` strictly downstream of shipped `V60`.
  - interpretation consumes latest shipped `V60` basis
  - `charter_amendment_candidate` remains posture only
  - no charter/residual/continuation mutation here
- Closeout Evidence:
  shipped `V61-A` checker/tests preserve explicit `V60` basis selection and keep
  `charter_amendment_candidate` posture-only.

### Edge 2: UI Send Access Could Masquerade As Bridge Office

- Risk:
  the resident runtime’s ability to emit over the existing send seam could be treated
  as if explicit bridge-office posture had already landed.
- Response:
  keep office posture out of the starter slice.
  - runtime may emit governed egress
  - that is not explicit bridge-office behavior
  - office binding remains deferred to `V61-B`
- Closeout Evidence:
  merged `v167` diff ships no bridge-office binding surfaces and the decision bundle
  preserves that deferral explicitly.

### Edge 3: Transcript Could Re-Enter As Native Witness

- Risk:
  once communication becomes first-class, transcript or event traffic could be
  over-read as native witness without explicit rewitness law.
- Response:
  keep starter communication non-witnessing by default.
  - transcript remains observability only
  - no message-promotion gate here
  - rewitness remains deferred to `V61-B`
- Closeout Evidence:
  shipped egress semantics remain non-witnessing by default and no rewitness surfaces
  landed in `v167`.

### Edge 4: Surface Classification Could Collapse Into Message Interpretation

- Risk:
  a single descriptor could ambiguously mix surface affordance and message meaning,
  making the membrane soft and discretionary.
- Response:
  keep the split explicit.
  - surface-authority descriptor records surface affordance / bounded authority
    posture only
  - ingress interpretation alone decides message posture
  - both remain replayable
- Closeout Evidence:
  shipped `agentic_de_surface_authority_descriptor@1` and
  `agentic_de_ingress_interpretation_record@1` remain separate typed surfaces with
  replayable checker/tests.

### Edge 5: Starter Scope Could Drift Into Multiple Parallel Communication Seams

- Risk:
  the family planning set names web copilot, workbench, and resident session send
  paths, but the first slice could become too wide if it tries to retrofit them all
  independently.
- Response:
  freeze `V61-A` to one exact backend seam.
  - existing `/urm/copilot/send`
  - `copilot.user_message` only
  - web and workbench remain consumers of that same seam, not separate starter
    retrofits
- Closeout Evidence:
  shipped seam selection stayed fail-closed to the resident `/urm/copilot/send` path
  and one runtime message method only.

### Edge 6: Communication Egress Could Be Over-Read As Act Authority

- Risk:
  once egress is typed, it could be mistaken for execute/ticket/repo authority rather
  than bounded communication posture.
- Response:
  keep egress posture-only in this slice.
  - status / clarification / authority-request / escalation / completion /
    advisory-only postures only
  - no act authority
  - no repo-write authority
  - no native witness by default
- Closeout Evidence:
  shipped egress contract/checker/tests keep communication outputs bounded to posture
  only.

### Edge 7: Review Hardening Could Miss Default Repo-Root Symlink Cases

- Risk:
  the starter runner could reject explicit symlinked repo roots but still accept a
  symlinked default-discovered root, weakening the fail-closed boundary.
- Response:
  keep root selection explicit and fail-closed before resolution.
  - explicit repo root may not be a symlink
  - default-discovered repo root may not be a symlink
  - path-argument mapping remains explicit and auditable
- Closeout Evidence:
  review hardening commit `d1a1b0c054f9191fd99d166a98e78a6712940e18` tightened the
  default root guard and replaced `locals()` path lookup with an explicit path map,
  with regression coverage.

### Edge 8: Connector Or Remote Surfaces Could Be Smuggled Into The Starter

- Risk:
  because `V61` sits upstream of `V62` and `V63`, the starter slice could drift into
  connector trust or remote-operator UX before the membrane is stabilized.
- Response:
  keep later families deferred.
  - no connector-specific transport law
  - no remote-operator UX law
  - no product-surface expansion under cover of starter retrofit
- Closeout Evidence:
  shipped `v167` surfaces remain bounded to the resident send seam with no connector
  or remote-specific transport/runtime law.

## Current Judgment

- `V61-A` was the right next slice because `V60` closed continuation / residual
  identity, but the repo still lacked typed governed communication packets over the
  already-real resident send seam.
- the shipped result remained properly bounded:
  - exact-resident-send-seam-first
  - principal/speaker-typing-first
  - surface-descriptor-first
  - replayable-interpretation-first
  - posture-only-egress-first
  - non-mutating-charter-amendment posture
  - non-office-binding
  - non-rewitnessing
  - non-connector / non-remote / non-repo-authority widening
- `V61-A` is now closed on `main` in the starter sense.
- the next same-family move should be `V61-B`, not widening `V61-A` authority in
  place.
