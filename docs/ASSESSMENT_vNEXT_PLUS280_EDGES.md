# Assessment vNext+280 Edges

Status: pre-lock assessment for `BRL-0-C`.

Authority layer: planning.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS280_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Pre-Implementation Edge Review

### Edge 1: Impact Cone Selection Becomes Probe Generation

- Required containment:
  `BRL-0-C` may select from existing manifest-declared probes and owner-surface
  rows. It may not invent new probes, argv, fixtures, canonicalization profiles,
  or expected observation hashes.

### Edge 2: Partial Replay Becomes Full No-Regression Claim

- Required containment:
  certificate scope must be bounded to covered probes and owner surfaces. A
  partial impact-cone replay cannot claim full-manifest preservation.

### Edge 3: Suite-Root Match Becomes Product Truth

- Required containment:
  even a full-manifest replay match is preservation evidence only. It does not
  prove product correctness, HOB closure, OTB transition legality, or official
  readiness.

### Edge 4: Missing Sentinel Coverage Is Silently Ignored

- Required containment:
  touched owner surfaces with no selected sentinel coverage must become blockers
  or stale-lock rows, not omissions.

### Edge 5: Staleness Report Becomes Automatic Refresh

- Required containment:
  stale-lock reports may identify refresh requirements. They may not update
  manifests, expected hashes, owner maps, fixtures, or handoff records.

### Edge 6: Integration Handoff Becomes Transition Authority

- Required containment:
  handoff rows may constrain downstream phases. They may not grant OTB
  transition legality or HOB subtree closure.

### Edge 7: C Leaks Into Product Workflow

- Required containment:
  source patching, worker dispatch, ProgramBench workflow integration,
  product truth, official-eval readiness, and future-family selection remain
  outside `BRL-0-C`.

## Implementation Watchpoints

- Preserve A/B released record validation and hash checks.
- Require candidate change identity and owner-surface scope before partial
  impact-cone selection.
- Keep selected, required, omitted, missing, stale, and blocked sentinels
  separate.
- Keep certificate posture narrower than or equal to covered replay evidence.
- Include deterministic ordering tests for selected probes, blockers,
  staleness rows, handoff rows, and certificate hashes.
