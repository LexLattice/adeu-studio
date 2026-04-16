# Assessment vNext+171 Edges

Status: pre-lock edge assessment for `V62-B`.

Authority layer: planning scaffold only.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS171_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: `V62-B` Could Quietly Reopen Connector Admission Law

- Risk:
  the follow-on slice could start mutating connector admission semantics instead
  of consuming the shipped `V62-A` admitted path.
- Response:
  keep admission fixed and consumed.
  - shipped `V62-A` connector admission remains the only admitted basis
  - `V62-B` adds one egress bridge only
  - no new connector admission record

### Edge 2: Outbound Bridge Could Be Over-Read As Bridge Office

- Risk:
  once outbound bridge exists, connector delivery could drift into “acting as the
  office” rather than consuming shipped office posture.
- Response:
  keep bridge-office posture explicit and downstream-consumed only.
  - consume shipped `V61-B` bridge-office binding where selected
  - outbound bridge is not bridge office by itself
  - bridge-office access is not connector permission

### Edge 3: Rewitness Could Quietly Become Outbound Authority

- Risk:
  positive rewitness could be cited narratively without a concrete basis and drift
  into implicit outbound authority.
- Response:
  keep positive rewitness basis-bearing and fail-closed.
  - witness basis ref or certificate ref when positive
  - direct consumed rewitness basis summary carried when positive
  - missing positive basis fails closed
  - rewitness posture is not outbound authority by itself

### Edge 3A: Optional Office / Rewitness Refs Could Become Ambient Selection

- Risk:
  absent optional refs could be narratively treated as if office or rewitness
  posture was still selected because the runtime previously had capability or the
  connector path remained available.
- Response:
  keep optional basis semantics explicit and non-ambient.
  - `none` means not selected and not consumed in this packet
  - absence may not be inferred from prior emission capability
  - absence may not be inferred from connector availability

### Edge 4: `V62-B` Could Quietly Swallow Human-Via-Connector Semantics

- Risk:
  once the bridge becomes bidirectional, the slice could blur external-assistant
  traffic with broader human-via-connector semantics.
- Response:
  keep principal selection explicit and singular.
  - `external_assistant` selected
  - `human_via_connector` not selected

### Edge 5: Outbound Connector Payload Could Be Over-Read As Semantic Authority

- Risk:
  outbound payload could drift into witness, charter, continuation, or execution
  authority merely because it is leaving through an admitted connector path.
- Response:
  keep outbound bridge transport-bounded and non-sovereign.
  - not native witness
  - not charter amendment
  - not continuation mutation
  - not repo authority
  - not execute authority

### Edge 6: `V62-B` Could Quietly Reopen `V61` Communication Law

- Risk:
  the connector follow-on could start inventing outbound message law independently
  of the already shipped governed communication membrane.
- Response:
  keep the bridge downstream-consumption-only over shipped `V61`.
  - consume shipped `V61-A` communication egress lineage
  - consume shipped `V61-B` office / rewitness posture where selected
  - do not mint connector-native communication law

### Edge 7: One Admitted Connector Path Could Be Over-Read As Broader Trust

- Risk:
  one successful ingress-plus-egress bridge could be treated as if it proved
  broader connector fleet trust, remote-operator law, or repo authority.
- Response:
  keep the follow-on path exact and non-generalizing by default.
  - one exact connector path only
  - not broader connector-fleet trust
  - not remote-operator law
  - not repo authority
  - not execute or dispatch authority

### Edge 8: Bidirectional Bridge Could Quietly Swallow Connector Hardening

- Risk:
  once both directions exist, the follow-on could start making advisory migration
  or provenance-hardening claims without an explicit later lock.
- Response:
  keep `V62-B` as bridge completion only.
  - no connector hardening register yet
  - no provenance-drift recommendation yet
  - later migration scope remains for `V62-C`

## Current Judgment

- `V62-B` is the right next slice because `V62-A` already solved one admitted
  connector path plus one inbound bridge, and the next missing bounded step is one
  explicit outbound bridge over that same admitted connector lineage.
- the follow-on should stay properly bounded:
  - same admitted connector path only
  - same selected principal only
  - shipped `V62-A` admission and ingress bridge consumed intact
  - one new egress bridge packet only
  - explicit `V61-B` office / rewitness consumption where selected
  - direct consumed rewitness basis summary when positive
  - explicit continuation-basis selection summary
  - no human-via-connector law
  - no connector hardening yet
  - no remote-operator law
  - no repo, execute, or dispatch widening
- the next bundle after this follow-on, if `V62-B` lands cleanly, should be
  `V62-C` as the advisory connector hardening / provenance-drift lane rather than
  more bridge widening in place.
