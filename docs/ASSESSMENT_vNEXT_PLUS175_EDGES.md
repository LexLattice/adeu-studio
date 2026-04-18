# Assessment vNext+175 Edges

Status: pre-lock edge assessment for `V63-C`.

Authority layer: planning scaffold only.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS175_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Advisory Remote Hardening Could Quietly Reopen `V63-A` Or `V63-B` Law

- Risk:
  the hardening layer could start replacing shipped session, view, response, or
  richer control-bridge semantics instead of consuming them.
- Response:
  keep `V63-A` and `V63-B` authoritative.
  - shipped `V63-A` session and view remain the only admitted remote basis
  - shipped `V63-A` starter-response lineage remains consumed-only
  - shipped `V63-B` control-bridge lineage remains consumed-only

### Edge 2: Advisory Output Could Become A Soft Remote Sovereign

- Risk:
  one favorable hardening recommendation could drift into apparent permission to
  respond, control, or widen remote authority.
- Response:
  keep advisory output non-entitling and non-sovereign.
  - advisory output is not session admission
  - advisory output is not response authority
  - advisory output is not control authority
  - advisory output is not bridge office

### Edge 3: Narrative Review Could Replace Committed Evidence Basis

- Risk:
  reviewer interpretation or prose could silently outrank the committed shipped
  lineage that the hardening register is supposed to evaluate.
- Response:
  keep committed artifacts first-class and fail closed on drift.
  - committed lane artifacts outrank narrative interpretation
  - explicit evidence basis remains separate from recommendation
  - same evidence chain plus same frozen policy yields the same recommendation

### Edge 4: One Remote Exemplar Could Be Over-Read As Broad Remote-Admin Law

- Risk:
  one shipped admitted remote path could be treated as if it proves broad remote
  admin, all-device, or all-surface control law.
- Response:
  keep the advisory path exact and non-generalizing by default.
  - one admitted remote operator path only
  - not broad remote-admin law
  - not all-device or all-surface law
  - not connector law

### Edge 5: Advisory Register Could Quietly Swallow Repo / Execute / Dispatch Law

- Risk:
  once remote hardening exists, later code or reviewers could over-read it as a
  standing foothold for repo writes, execution, or dispatch.
- Response:
  keep the advisory seam remote-lineage-local only.
  - not repo authority
  - not execute authority
  - not dispatch authority
  - no advisory-to-live promotion

### Edge 6: Cross-Principal Or Connector Semantics Could Bleed Into `V63-C`

- Risk:
  the remote hardening layer could blur `remote_operator` with
  `external_assistant` or `human_via_connector`.
- Response:
  keep principal typing singular in this slice.
  - `remote_operator` selected
  - `external_assistant` not selected here
  - `human_via_connector` not selected here

### Edge 7: Optional Upstream Response Or Control Basis Could Be Over-Read

- Risk:
  absent or mismatched optional upstream response/control refs could be treated as
  if richer intervention evidence had been lawfully carried into the hardening
  register.
- Response:
  keep optional upstream basis explicit and fail-closed.
  - if both optional refs are `none`, no richer intervention overread
  - if one is present, it must match selected principal/session/surface posture
  - selected response/control kind summary stays explicit where present

### Edge 8: Response Or Control Lineage Could Count More Than Once

- Risk:
  shipped session, view, response, and control artifacts from one bounded remote
  seam could be over-read as independent support by repetition.
- Response:
  keep lineage-root non-independence explicit in the hardening layer.
  - field-origin tags remain required
  - dependence tags remain required
  - root dedup summaries remain required

## Current Judgment

- `V63-C` is the right next slice because `V63-A` already closed admitted remote
  session / view / starter-response law and `V63-B` already closed richer typed
  intervention bridge law, while bounded advisory hardening over that same shipped
  remote lineage is still missing.
- the follow-on should stay properly bounded:
  - one admitted remote path only
  - one selected principal only
  - one advisory remote hardening register only
  - consumed shipped `V63-A` session / view / response lineage
  - consumed shipped `V63-B` control-bridge lineage
  - explicit optional response/control basis consistency and fail-closed posture
  - consumed shipped `V60` / `V61` basis
  - explicit committed-artifact precedence and frozen-policy replayability anchor
  - no connector, broad remote-admin, repo, execute, or dispatch widening
- if `V63-C` lands cleanly, `V63` should then be treated as closed on `main`
  rather than widened in place.
