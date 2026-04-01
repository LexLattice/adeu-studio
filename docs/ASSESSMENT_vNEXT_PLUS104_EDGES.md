# Assessment vNext+104 Edges

Status: planning-edge assessment for `V45-E`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS104_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Hotspot-To-Mutation Laundering

- Risk:
  surfaced hotspots or consolidation candidates could be overread as authorization to
  split, merge, or refactor code immediately.
- Response:
  keep descriptive findings, optimization candidates, and amendment entitlement as
  distinct typed fields and freeze starter entitlement to a negative posture only.

### Edge 2: Priority Inflation

- Risk:
  priority posture could be interpreted as scheduling, release-gating, or merge-order
  authority instead of descriptive planning input.
- Response:
  keep `priority_posture` descriptive-only and explicitly non-authorizing in the first
  release.

### Edge 3: Support-Basis Thinness

- Risk:
  optimization rows could become elegant summaries with weak actual support, especially
  when driven by file length, naming repetition, or vague concentration signals alone.
- Response:
  require explicit `support_basis`, explicit source artifact refs, and fail-closed
  rejection of unsupported optimization claims.

### Edge 4: Cross-Artifact Drift Relative To `V45-A` Through `V45-D`

- Risk:
  the register could cite entity, schema, symbol, dependency, or test-intent surfaces
  that do not actually match the same snapshot identity or artifact-local source-scope
  posture.
- Response:
  require shared snapshot identity, explicit source-scope compatibility, and fail
  closed on unresolved or mismatched bound references.

### Edge 5: Scope-Ref Ambiguity

- Risk:
  optimization entries could point at vague prose scopes or dangling identifiers rather
  than resolvable bounded surfaces.
- Response:
  require typed finding scopes, explicit carrier semantics for
  `cross_surface_cluster`, and reject unresolved internal scope refs.

### Edge 6: Mixed-Finding Flattening

- Risk:
  structural, semantic, governance, and surface compression signals could collapse into
  one primary label and discard the mixed character of the finding.
- Response:
  freeze a bounded starter compression-axis vocabulary, keep one primary axis explicit
  per row, and allow bounded secondary tags for mixed findings.

### Edge 7: Descriptive Plane Drift Into `V45-F`

- Risk:
  the optimization register could widen early into descriptive-to-normative binding,
  recursive governance, or amendment-routing logic.
- Response:
  keep `v104` bounded to `repo_optimization_register@1` only and defer `V45-F`.

### Edge 8: Snapshot Overread

- Risk:
  one snapshot-bound optimization register could be treated as current repo truth after
  the repo changes.
- Response:
  keep snapshot validity posture explicit and treat stale outputs as historical
  evidence only.

## Current Judgment

- `V45-E` is worth implementing now because `V45-A` through `V45-D` already provide
  the descriptive substrate needed for a bounded optimization-register seam.
- the first release should stay strictly diagnostic-first and non-promotional so later
  normative or amendment lanes consume it without being silently authorized by it.
