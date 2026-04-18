# Assessment vNext+172 Edges

Status: pre-lock edge assessment for `V62-C`.

Authority layer: planning scaffold only.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS172_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Advisory Connector Hardening Could Quietly Reopen Connector Admission Law

- Risk:
  the advisory slice could start changing connector admission semantics instead of
  consuming the shipped `V62-A` admitted path.
- Response:
  keep admission fixed and consumed.
  - shipped `V62-A` connector admission remains the only admitted basis
  - `V62-C` adds one advisory register only
  - no new connector admission record

### Edge 2: Advisory Output Could Be Over-Read As Bridge Or Office Authority

- Risk:
  once connector hardening exists, a favorable advisory result could drift into
  “permission to bridge” or “permission to act as the office.”
- Response:
  keep advisory output non-entitling and non-sovereign.
  - advisory output is not connector permission
  - advisory output is not bridge office
  - advisory output is not rewitness
  - advisory output is not human-via-connector selection

### Edge 3: Positive Rewitness Could Be Over-Read Without Concrete Basis

- Risk:
  the advisory layer could cite positive rewitness narratively without carrying the
  concrete basis or certificate posture that made it lawful upstream.
- Response:
  keep positive rewitness basis-bearing and explicit.
  - witness basis ref or certificate posture when relevant
  - explicit basis carried in the evidence basis
  - missing or inconsistent basis fails closed

### Edge 3A: Positive Rewitness Basis Carry-Through Could Drift From Upstream Posture

- Risk:
  the advisory evidence basis could carry positive rewitness basis or certificate
  fields that do not actually match the selected upstream rewitness posture.
- Response:
  keep rewitness-basis carry-through posture-consistent and fail-closed.
  - no positive rewitness selected upstream means basis/certificate posture stays
    `none`
  - carried basis/certificate posture must match the selected upstream rewitness
    posture
  - inconsistent carry-through fails closed

### Edge 4: Candidate Labels Could Become Soft Authorization

- Risk:
  connector-hardening or connector-migration candidates could read like implied
  approvals rather than advisory path-level outcomes.
- Response:
  keep candidate outcomes bounded and unspecified.
  - non-entitling
  - non-escalating by themselves
  - later scope unspecified unless a later lock selects it

### Edge 5: One Successful Connector Lineage Could Be Over-Read As Fleet-Level Law

- Risk:
  one admitted external-assistant connector path could be treated as if it proves
  broader connector-fleet trust, human-via-connector law, or remote-operator law.
- Response:
  keep the advisory path exact and non-generalizing by default.
  - one exact connector path only
  - not broader connector-fleet trust
  - not human-via-connector law
  - not remote-operator law
  - not bridge-office-family or rewitness-family law

### Edge 6: Advisory Register Could Quietly Swallow Repo / Execute / Dispatch Law

- Risk:
  once connector drift is being discussed, the advisory layer could start making
  repo-authority, execute-authority, or dispatch-authority claims.
- Response:
  keep the advisory seam transport- and connector-local only.
  - not repo authority
  - not execute authority
  - not dispatch authority
  - not product authority

### Edge 7: Artifact Refs Could Replace Shipped Verdicts

- Risk:
  `V62-C` could technically consume the right artifacts while ignoring the actual
  connector, communication, office, and rewitness verdicts that make the path
  lawful.
- Response:
  keep hardening dependent on shipped facts and verdicts, not refs alone.
  - admission verdict required
  - selected principal required
  - latest continuation basis and selection summary required
  - relevant communication and rewitness posture required

### Edge 8: Connector Hardening Could Quietly Mutate Live Behavior

- Risk:
  “hardening” could become live bridge mutation under advisory cover.
- Response:
  keep outputs advisory-only and candidate-only.
  - no connector admission mutation
  - no ingress or egress bridge mutation
  - no human-via-connector selection
  - no advisory-to-live promotion
  - `keep_warning_only` retains current advisory posture only

## Current Judgment

- `V62-C` is the right next slice because `V62-A` and `V62-B` already closed one
  exact admitted connector path plus bounded inbound/outbound bridge lineage, and
  the next missing bounded step is one advisory connector hardening /
  provenance-drift surface over that same lineage.
- the follow-on should stay properly bounded:
  - same admitted connector path only
  - same selected principal only
  - shipped `V62-A` and `V62-B` lineage consumed intact
  - one advisory connector hardening register only
  - explicit evidence-vs-recommendation separation
  - explicit positive rewitness basis posture where relevant
  - explicit continuation-basis selection summary
  - no human-via-connector law
  - no broader connector-fleet trust
  - no remote-operator law
  - no repo, execute, or dispatch widening
- the next move after this advisory slice, if `V62-C` lands cleanly, should be a
  new family selection rather than more `V62` authority widening in place.
