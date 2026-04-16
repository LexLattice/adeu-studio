# Assessment vNext+170 Edges

Status: pre-lock edge assessment for `V62-A`.

Authority layer: planning scaffold only.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS170_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Connector Snapshot Visibility Could Quietly Become Admission Authority

- Risk:
  the starter slice could treat connector snapshot existence or exposure visibility
  as if it already proved lawful admission.
- Response:
  keep connector admission explicit, typed, replayable, and fail-closed.
  - snapshot visibility alone is not admission
  - exposure visibility alone is not admission
  - admission verdict stays inside an explicit starter verdict family
  - missing or stale snapshot / exposure / freshness basis fails closed

### Edge 2: External Assistant Traffic Could Be Over-Read As Native Witness Or Task Law

- Risk:
  raw upstream assistant output could drift into witness, charter, continuation, or
  act authority merely because it arrived through an admitted connector path.
- Response:
  keep the ingress bridge transport-bounded and non-sovereign.
  - not native witness
  - not charter compilation
  - not continuation mutation
  - not act authority

### Edge 3: `V62-A` Could Quietly Swallow `V62-B`

- Risk:
  the starter slice could start claiming full bidirectional bridge semantics or rich
  provenance carry-through under cover of “connector bridge.”
- Response:
  keep the first slice ingress-only and narrower than `V62-B`.
  - connector admission plus ingress bridge only
  - no egress bridge packet yet
  - no richer bidirectional bridge claims yet

### Edge 4: Human-Via-Connector Semantics Could Slip Into The External-Assistant Slice

- Risk:
  once principal typing exists, the starter slice could become vague about whether it
  selected external-assistant traffic only or broader connector-carried human
  semantics too.
- Response:
  keep principal selection explicit and singular.
  - `external_assistant` selected
  - `human_via_connector` not selected

### Edge 5: Connector Bridge Could Quietly Reopen `V61` Communication Law

- Risk:
  the connector family could start interpreting message meaning independently of the
  already shipped governed communication membrane.
- Response:
  keep bridge semantics downstream-consumption-only over shipped `V61`.
  - consume shipped `V61-A` communication ingress / descriptor / interpretation
    lineage only in `V62-A`
  - do not consume `V61-B` bridge-office or rewitness posture as live ingress basis
    in the starter slice
  - do not mint connector-native communication law

### Edge 6: One Connector Path Could Be Over-Read As Broader Connector Or Remote Law

- Risk:
  one admitted connector success could be treated as if it proved broader
  connector-fleet trust, human-via-connector law, or remote-operator law.
- Response:
  keep the starter path exact and non-generalizing by default.
  - one exact connector path only
  - not broader connector-fleet trust law
  - not human-via-connector law
  - not remote-operator law

### Edge 7: Connector Starter Scope Could Drift Into Repo Or Execution Authority

- Risk:
  because the selected downstream exemplar is still the continuity-bound
  `local_write/create_new` path, the connector slice could be over-read as repo
  authority or execution authority.
- Response:
  keep `V62-A` transport-and-admission only.
  - not repo-write authority
  - not execute authority
  - not dispatch authority
  - same downstream exemplar remains consumed context only

### Edge 8: Freshness Basis Could Be Too Soft To Replay

- Risk:
  connector admission could look typed while still relying on ambient runtime
  freshness judgment.
- Response:
  keep freshness basis explicit and replayable.
  - `execution_mode = live`
  - explicit `min_acceptable_ts` posture when present
  - same snapshot / exposure / freshness basis plus same frozen policy yields the
    same admission verdict

### Edge 9: Provenance Could Be Asserted In Prose But Not Carried In The Starter Surfaces

- Risk:
  the starter could describe the connector bridge as provenance-bearing while leaving
  provenance and root-dedup implicit in the actual typed surfaces.
- Response:
  carry provenance explicitly on both new records.
  - `field_origin_tags`
  - `field_dependence_tags`
  - `root_origin_dedup_summary`

## Current Judgment

- `V62-A` is the right first slice because the repo already has real connector
  snapshot / exposure infrastructure and real `V61` governed communication law, but
  it still lacks one explicit admitted connector path and one bounded
  external-assistant ingress bridge over that stack.
- the starter should stay properly bounded:
  - one admitted connector path only
  - one selected principal only
  - one connector admission record
  - one ingress bridge packet
  - one consumed `V61` communication lineage
  - no egress bridge yet
  - no human-via-connector law
  - no remote-operator law
  - no repo or execute authority widening
- the next bundle after this starter, if `V62-A` lands cleanly, should be `V62-B`
  as the explicit bidirectional bridge follow-on rather than a vague widening of the
  starter contract.
