# Assessment vNext+81 Edges

Status: planning-edge assessment for `V40-E`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS81_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: UX Source-Bypass Drift

- Risk:
  the slice could synthesize `ux_domain_packet@1` directly from local semantic or
  prompt-shaped state instead of binding it to released semantic-root, conformance,
  checkpoint, and projection surfaces.
- Response:
  require every emitted UX packet to preserve explicit architecture and projection
  lineage and reject direct-from-root or direct-from-prompt shortcuts.

### Edge 2: UX Governance Drift

- Risk:
  the architecture compiler could silently fork the released UX governance family by
  redefining approved-profile or authority-boundary semantics locally.
- Response:
  consume the released `ux_domain_packet@1` target-family contract from
  `packages/adeu_core_ir` and fail closed on profile or authority mismatch.

### Edge 3: Blocked-Source Honesty Drift

- Risk:
  blocked architecture or blocked projection state could still be represented as a
  lawful emitted UX packet.
- Response:
  keep blocked/no-emit behavior explicit and require committed blocked fixtures plus
  fail-closed guards for blocked architecture/projection lineage.

### Edge 4: Morph / Surface-Compiler Creep

- Risk:
  the first UX compatibility baseline could widen immediately into `ux_morph_ir`,
  rendered-surface export, or broader UI compiler release before the first emitted UX
  packet seam is stable.
- Response:
  keep `ux_domain_packet@1` as the only lawful UX target in `vNext+81` and defer
  `ux_morph_ir` plus surface compiler export to later explicit follow-on work.

### Edge 5: Prompt-to-Surface Collapse

- Risk:
  the slice could be interpreted as permission to generate UI surfaces directly from
  architecture intent.
- Response:
  freeze the rule that `V40-E` remains typed and intermediate only; no direct React
  tree generation, workbench release, or prompt-to-surface path is lawful in this arc.

### Edge 6: Profile / Authority Provenance Drift

- Risk:
  emitted UX packets could validate structurally while drifting from the released
  approved-profile id, supporting-artifact posture, or authority-boundary policy.
- Response:
  require exact compatibility checks against the released UX governance lane and reject
  local rewrites or silent defaulting.

### Edge 7: Formal-Sidecar Timing Drift

- Risk:
  the Lean sidecar may still be reconciling shipped `V40-C` laws and could be mistaken
  for a blocker on `V40-E` starter planning.
- Response:
  keep the formal lane parallel and optional for `V40-E` planning, reconcile it before
  any authoritative wiring, and do not let it redefine the main UX-lowering contract.

## Current Judgment

- `V40-E` is worth implementing now because the repo has released architecture meaning,
  deterministic conformance, bounded hybrid disposition, and one honest core lowering,
  but still lacks a narrow typed UX-domain target that proves compatibility without
  collapsing into direct surface generation.
