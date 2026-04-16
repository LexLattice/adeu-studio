# Assessment vNext+167 Edges

Status: planning-edge assessment for `V61-A`.

Authority layer: planning.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS167_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: `V61-A` Could Quietly Reopen `V60` Task-Law Compilation

- Risk:
  ingress interpretation could be over-read as if communication already recompiled
  charter or continuation law.
- Response:
  keep `V61-A` strictly downstream of shipped `V60`.
  - interpretation consumes latest shipped `V60` basis
  - `charter_amendment_candidate` remains posture only
  - no charter/residual/continuation mutation here

### Edge 2: UI Send Access Could Masquerade As Bridge Office

- Risk:
  the resident runtime’s ability to emit over the existing send seam could be treated
  as if explicit bridge-office posture had already landed.
- Response:
  keep office posture out of the starter slice.
  - runtime may emit governed egress
  - that is not explicit bridge-office behavior
  - office binding remains deferred to `V61-B`

### Edge 3: Transcript Could Re-Enter As Native Witness

- Risk:
  once communication becomes first-class, transcript or event traffic could be
  over-read as native witness without explicit rewitness law.
- Response:
  keep starter communication non-witnessing by default.
  - transcript remains observability only
  - no message-promotion gate here
  - rewitness remains deferred to `V61-B`

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

### Edge 7: Connector Or Remote Surfaces Could Be Smuggled Into The Starter

- Risk:
  because `V61` sits upstream of `V62` and `V63`, the starter slice could drift into
  connector trust or remote-operator UX before the membrane is stabilized.
- Response:
  keep later families deferred.
  - no connector-specific transport law
  - no remote-operator UX law
  - no product-surface expansion under cover of starter retrofit

### Edge 8: Latest `V60` Continuation Basis Selection Could Become Ambiguous

- Risk:
  if ingress interpretation or egress derivation can choose among multiple continuation
  artifacts loosely, the membrane becomes non-replayable.
- Response:
  keep latest-basis selection explicit and fail-closed.
  - latest shipped `V60` continuation basis only
  - explicit basis refs
  - same ingress plus same basis plus same frozen policy must yield same outputs

## Current Judgment

- `V61-A` is worth implementing now because `V60` closed continuation / residual
  identity, but the repo still lacks typed governed communication packets over the
  already-real resident send seam.
- the starter should remain properly bounded:
  - exact-resident-send-seam-first
  - principal/speaker-typing-first
  - surface-descriptor-first
  - replayable-interpretation-first
  - posture-only-egress-first
  - non-mutating-charter-amendment posture
  - non-office-binding
  - non-rewitnessing
  - non-connector / non-remote / non-repo-authority widening
- if `V61-A` lands cleanly, the next default same-family move should be `V61-B`,
  not widening `V61-A` authority in place.
