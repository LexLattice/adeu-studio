# Assessment vNext+187 Edges

Status: planning-edge assessment for `V67-C`.

Authority layer: planning / starter assessment.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS187_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Bridge Status Could Collapse Into Ergonomic Or Conformance Judgment

- Risk:
  advisory bridge validity or drift posture could be flattened into prior
  ergonomic `overall_judgment` or into released UX conformance judgment.
- Response:
  keep bridge statuses bounded and separate.

### Edge 2: Runtime Evidence Could Quietly Become Layout Authority

- Risk:
  realized runtime measurements or drift rows could be overread as permission to
  adapt or mutate layout directly.
- Response:
  keep `V67-C` advisory-only and forbid direct runtime layout authority here.

### Edge 3: Missing Required Runtime Evidence Could Disappear Into Clean Output

- Risk:
  a bridge report could report clean posture while required runtime measurement
  obligations were never satisfied.
- Response:
  keep missing required runtime evidence explicit with stable mismatch families
  and advisory-incomplete status.

### Edge 4: Runtime Provenance Could Be Too Weak For The Claimed Comparison

- Risk:
  planning declarations, screenshot-only material, or inadmissible runtime rows
  could be mistaken for lawful realized-measurement evidence.
- Response:
  keep provenance and admissibility explicit and fail closed on invalid runtime
  evidence shape.

### Edge 5: The Bridge Could Quietly Reopen Released UX Diagnostics

- Risk:
  convenience wiring could add ergonomic drift families directly into
  `ux_morph_diagnostics@1` or `ux_conformance_report@1`.
- Response:
  keep `V67-C` on its own bounded runtime bridge artifacts and leave released UX
  governance artifacts unchanged.

### Edge 6: Drift Families Could Become Unstable Narrative Strings

- Risk:
  runtime mismatch rows could drift into prose-only output and lose replayable
  mismatch semantics.
- Response:
  freeze stable runtime mismatch families and keep them machine-readable.

### Edge 7: Runtime Candidate Realization Could Drift From Shipped Adjudication

- Risk:
  realized runtime evidence could target a different candidate profile or source
  basis than the adjudication result it claims to compare against.
- Response:
  preserve exact request/result/evidence lineage and fail closed on basis
  mismatch.

## Current Judgment

- `V67-C` is the right active next slice because `V67-A` and `V67-B` now ship on
  `main` and the missing remaining family seam is bounded runtime / conformance
  hardening over that shipped adjudication lineage
- the slice should stay deliberately finite:
  - typed runtime measurement evidence
  - typed advisory bridge report
  - exact lineage checks
  - stable drift / incompleteness mismatch families
  - advisory-only bridge statuses
- `V67-C` should not attempt adaptive runtime control, direct layout mutation,
  or mutation of released UX diagnostics / conformance artifacts
- if `v187` ships cleanly, the `V67` family should be in position for one final
  full-family closeout on `main`.
