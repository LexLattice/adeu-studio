# Assessment vNext+80 Edges

Status: planning-edge assessment for `V40-D`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS80_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Lowering Source-Bypass Drift

- Risk:
  the slice could synthesize projection artifacts from ad hoc local state instead of
  binding them to released `V40-A` semantic-root, `V40-B` conformance, and `V40-C`
  checkpoint-trace surfaces.
- Response:
  require every bundle and manifest artifact to carry explicit semantic, conformance,
  and checkpoint lineage and reject direct-from-root lowering shortcuts.

### Edge 2: Projection Honesty Drift

- Risk:
  projection units could claim `ready` while unresolved blocking ambiguity or blocked
  conformance state remains active.
- Response:
  keep blocked-by-ambiguity refs explicit, require source conformance `ready` plus no
  active unit-local blockers before any unit may claim `ready`, and fail closed when
  any blocked unit carries emitted output refs.

### Edge 3: Ghost Manifest Lineage

- Risk:
  emitted lowering artifacts could appear without an inspectable map back to consumed
  ASIR refs, target family, and compiler entrypoint.
- Response:
  freeze manifest/source-lineage requirements so no emitted projection surface can
  exist without explicit provenance.

### Edge 4: Target-Family Widening

- Risk:
  the first lowering baseline could silently widen from `adeu_core_ir@0.1` into UX or
  other target families before the narrow projection seam is stable.
- Response:
  keep `adeu_core_ir@0.1` as the only lawful target family in `vNext+80` and defer UX
  compatibility to `V40-E`.

### Edge 5: Adjudication / Projection Collapse

- Risk:
  final adjudication from `V40-C` could be mistaken for direct permission to claim
  ready emitted projection surfaces.
- Response:
  preserve the architecture rule that checkpoint adjudication and projection readiness
  remain distinct downstream surfaces with distinct authority, and freeze
  `escalated_human` lineage as blocking at lowering time.

### Edge 6: Edge-Vocabulary Inflation

- Risk:
  the first lowering baseline could overreach into a broad or unstable graph vocabulary
  instead of proving one narrow shared-integrity mapping.
- Response:
  keep starter lowering bounded to the architecture doc’s recommended
  `adeu_core_ir@0.1` node mapping and a narrow initial edge family.

### Edge 7: Blocked Output Surface Inflation

- Risk:
  blocked projection units could still emit artifacts that look authoritative and
  complete, undermining the honesty boundary.
- Response:
  require blocked-honesty fixtures and fail-closed guards so blocked units carry empty
  `output_artifact_refs` and cannot imply authoritative emitted output exists.

### Edge 8: Formal-Sidecar Timing Drift

- Risk:
  the Lean sidecar may still be catching up to the shipped `V40-C` artifact contract
  and could be mistaken for a blocker on `V40-D` starter planning.
- Response:
  keep the formal lane parallel and optional for `V40-D` planning, reconcile it before
  authoritative wiring, and do not let it redefine the main lowering contract.

## Current Judgment

- `V40-D` is worth implementing now because the repo has released architecture meaning,
  deterministic conformance, and bounded hybrid disposition, but still lacks one narrow
  deterministic lowering into shared integrity space with honest projection lineage.
