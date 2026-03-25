# Assessment vNext+82 Edges

Status: planning-edge assessment for `V40-F`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS82_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Family Release Overclaim Drift

- Risk:
  the slice could describe the completed ASIR ladder too broadly and silently treat
  deferred surfaces as shipped family scope.
- Response:
  require exact released-vs-deferred surface accounting and fail closed on omitted or
  vague deferred posture.

### Edge 2: Evidence-Source Bypass Drift

- Risk:
  the family summary could be built from prose or maintainer memory rather than from
  released evidence refs and hashes.
- Response:
  require canonical family evidence to consume released `V40-A` through `V40-E`
  evidence inputs and closeout docs explicitly.

### Edge 3: Stop-Gate Continuity Drift

- Risk:
  a family-integration slice could quietly fork the stop-gate schema family or expand
  the metric-key set while claiming to be release-only.
- Response:
  freeze `stop_gate_metrics@1` and exact metric-key equality versus `vNext+81`.

### Edge 4: Runtime-Observability Authority Drift

- Risk:
  runtime-observability delta rows could be treated as if they were allowed to change
  shipped/deferred family status or block canonical family evidence materialization.
- Response:
  keep runtime observability required but informational only and forbid it from
  changing release posture or continuity status by itself.

### Edge 5: Formal-Sidecar Authority Inflation

- Risk:
  the active Aristotle / Lean sidecar lane could be mistaken for authoritative family
  release evidence.
- Response:
  keep the formal lane parallel and optional, and reject any family release artifact
  that treats it as required release authority.

### Edge 6: Path-Lineage Gaps

- Risk:
  the family evidence artifact could mention `V40-A` through `V40-E` generally while
  failing to bind one or more released path closeouts by exact ref and hash.
- Response:
  require exact per-path evidence closure for all released current-family paths.

### Edge 7: Schema-Parity Drift

- Risk:
  the new `v40f_architecture_release_integration_evidence@1` artifact family could be
  released without the same authoritative/mirrored schema-discipline used elsewhere in
  the family.
- Response:
  require authoritative schema under `packages/adeu_architecture_compiler/schema/`,
  mirrored export under `spec/`, and byte-for-byte parity after canonical export.

### Edge 8: UX/Workbench Boundary Collapse

- Risk:
  the release-integration lane could imply that shipped `ux_domain_packet@1`
  compatibility is equivalent to rendered-surface or workbench release.
- Response:
  keep `V40-E`’s typed IR-only authority posture explicit and preserve deferred
  `ux_morph_ir`, surface compiler, and workbench route status.

## Current Judgment

- `V40-F` is worth implementing now because the repo has released the full bounded
  `V40-A` through `V40-E` ladder, but still lacks one canonical family evidence and
  release surface that binds those shipped paths together honestly without widening the
  stop-gate contract or misreporting deferred surfaces.
