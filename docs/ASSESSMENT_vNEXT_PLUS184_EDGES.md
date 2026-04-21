# Assessment vNext+184 Edges

Status: starter edge assessment for `V66-C`.

Authority layer: planning / starter assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS184_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Compile Report Could Quietly Become Source Authority

- Risk:
  the advisory compile report could be overread as if it changes source truth,
  migration posture, or lock authority by itself.
- Response:
  keep compile-report posture advisory and fail-closed.
  - compile report is not source authority by itself
  - compile report is not transition law by itself

### Edge 2: Prose-Boundary Notices Could Quietly Infer Policy From Prose

- Risk:
  warning surfaces could start treating normative-sounding prose as if it were
  compiled policy.
- Response:
  keep prose-boundary notices evidence-bound and explicit.
  - only recognized authority blocks compile
  - examples, quotes, and reader projections do not become policy by tone

### Edge 3: Generated Reader Views Could Re-Enter As Authority Inputs

- Risk:
  `V66-C` could accidentally treat generated reader projections as if they were
  governing source or transition-law evidence.
- Response:
  keep generated projections shaping-only and non-authoritative.
  - generated projections remain excluded from governed source discovery
  - generated projections remain non-authoritative even when they render
    authority text

### Edge 4: Semantic Diff Could Quietly Become Promotion Law

- Risk:
  drift visibility could be overread as if it authorizes markdown transition or
  source migration by itself.
- Response:
  keep semantic diff review-only and shaping-only.
  - semantic diff records visibility only
  - semantic diff is not authority by itself

### Edge 5: `V66-C` Could Widen Beyond The Same Governed Source Set

- Risk:
  advisory hardening could start rediscovering or classifying new docs outside
  the shipped `V66-A` / `V66-B` lineage.
- Response:
  keep the carried source set exact and fail-closed.
  - same shipped governed ANM source set only
  - no fresh source-set widening by default

### Edge 6: Advisory Outcomes Could Quietly Become Supersession Pressure

- Risk:
  advisory outcomes such as `candidate_for_later_markdown_transition_review`
  could be overread as if they were active transition law.
- Response:
  keep candidate outcomes non-entitling and non-escalating.
  - no advisory outcome supersedes markdown by itself
  - explicit shipped lock-level transition law remains required

### Edge 7: Consumed Basis Could Become Prose-Only Instead Of Mechanically Bound

- Risk:
  the advisory reports could talk about shipped `V66-A` / `V66-B` lineage
  without carrying exact refs and hashes, weakening replayability.
- Response:
  keep consumed lineage exact and hashed.
  - emitted `V66-C` artifacts must carry exact consumed-basis refs and hashes
  - same basis plus same frozen policy must yield the same advisory result

### Edge 8: Invalid Structure Could Quietly Collapse Into A Recommendation

- Risk:
  missing prior basis, hash mismatch, or bad notice evidence could still yield a
  nominal recommendation instead of invalidating the report.
- Response:
  keep `report_status` distinct from the advisory outcome.
  - structural invalidity blocks the recommendation
  - the recommendation is only meaningful when `report_status == valid`

## Current Judgment

- `V66-C` is the right next slice because `V66-A` and `V66-B` already closed the
  bounded source discovery, authority-profile, class-policy, migration-binding,
  generated reader-projection, and semantic-diff seams on `main`, while the repo
  still lacks explicit advisory adoption hardening over that same lineage.
- the proposed slice remains properly bounded:
  - same shipped `V66-A` / `V66-B` lineage only
  - one compile-report seam only
  - one prose-boundary notice seam only
  - exact consumed-basis refs and hashes remain first-class
  - frozen policy anchor remains explicit
  - structural report validity remains distinct from advisory recommendation
  - generated projection and semantic diff remain shaping-only
  - current markdown remains controlling absent explicit shipped transition law
  - no fresh source-set widening
  - no markdown supersession or source-of-truth promotion by advisory output
