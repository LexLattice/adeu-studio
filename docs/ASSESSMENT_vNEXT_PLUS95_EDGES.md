# Assessment vNext+95 Edges

Status: planning-edge assessment for `V42-G1`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS95_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Puzzle Source Authority Ambiguity

- Risk:
  local puzzle inputs could be pulled from mixed or ambiguous sources while presented as
  one authoritative cohort.
- Response:
  require explicit source-kind and source-ref binding per puzzle and reject mixed/unknown
  source posture.

### Edge 2: Selection Register Drift

- Risk:
  the three-puzzle cohort could be changed after outcomes are observed, creating
  non-auditable demo selection.
- Response:
  require a predeclared selection register and fail closed on retrospective swap.

### Edge 3: Deterministic Freeze Instability

- Risk:
  normalization/freeze could produce different bundle identities across runs.
- Response:
  require deterministic canonicalization plus stable puzzle hash and bundle ID replay
  checks.

### Edge 4: Provenance Laundering

- Risk:
  puzzle bundle artifacts could carry IDs and hashes without verifiable provenance refs.
- Response:
  require provenance refs as first-class typed fields and reject omissions.

### Edge 5: Premature Lane Widening

- Risk:
  `V42-G1` implementation could silently widen into agent-run execution (`G2`) or
  multi-puzzle harness orchestration (`G3`).
- Response:
  keep this slice bounded to ingest/freeze surfaces only and block downstream execution
  lane activation.

### Edge 6: Released Stack Redefinition Drift

- Risk:
  local ingest work could reopen or reinterpret released `V42-A`..`V42-F` semantics.
- Response:
  treat `V42-G1` as workflow consumption over released contracts, not ladder
  redefinition.

### Edge 7: Narrative Overclaim from Ingest Artifacts

- Risk:
  descriptive fields in puzzle bundles could be treated as authoritative performance or
  competition evidence.
- Response:
  keep summary fields non-authoritative and constrain authority to typed source,
  selection, and identity surfaces.

## Current Judgment

- `V42-G1` is the correct immediate seam because the next practical blocker is
  authoritative, deterministic local puzzle ingest/freeze before any reasoning-agent run
  bridge or local harness orchestration widening.
