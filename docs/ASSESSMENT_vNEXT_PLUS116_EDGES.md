# Assessment vNext+116 Edges

Status: planning-edge assessment for `V48-E`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS116_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Released `V48-D` Bypass

- Risk:
  the topology lane could silently bypass the released conformance surface and bind
  directly to raw boundary, attestation, provenance, or compiled-binding carriers.
- Response:
  freeze one starter input shape only:
  exactly one released parent `worker_boundary_conformance_report@1` and exactly one
  released child `worker_boundary_conformance_report@1`.

### Edge 2: Parent/Child Role Ambiguity

- Risk:
  a topology artifact could look typed while leaving parent/child ordering or role
  posture ambiguous.
- Response:
  freeze one explicit edge kind only:
  `supervisor_to_worker`, with parent role `supervisor` and child role `worker`.

### Edge 3: Child-Lineage Omission

- Risk:
  the topology lane could overread one parent conformance report as enough evidence,
  leaving the child side underdefined.
- Response:
  require exactly one explicit child conformance report and fail closed on omission.

### Edge 4: Boundary Equality Drift

- Risk:
  the child side could silently widen beyond the parent compiled boundary while still
  appearing reachable.
- Response:
  select exact parent/child compiled-boundary equality only in the starter slice as a
  deliberate first-slice restriction and do not authorize any widening algebra here.

### Edge 5: Repo / Snapshot Identity Drift

- Risk:
  parent and child could appear connected while actually drifting across repo or
  snapshot identity.
- Response:
  require exact same `repo_ref`, `snapshot_id`, and `snapshot_sha256` posture across
  the accepted topology.

### Edge 6: Non-Conformant Child Laundering

- Risk:
  a child run that is `non_conformant` or `incomplete_evidence` could still be
  treated as an accepted handoff topology by local convention.
- Response:
  freeze accepted starter topology to already conformant parent and child reports only.

### Edge 7: Delegated Task Identity Ambiguity

- Risk:
  the topology edge could be typed while leaving parent task identity, delegated task
  identity, or child task identity ambiguous, implicit, or only described in prose.
- Response:
  require one explicit parent task identity, one explicit delegated task identity,
  one explicit child task identity, and one explicit delegation-edge identity in every
  accepted topology.

### Edge 8: Handoff Result Ambiguity

- Risk:
  the first topology release could rely on prose to explain whether a handoff was
  completed, rejected, or unresolved.
- Response:
  freeze one bounded handoff-result vocabulary, and state explicitly that accepted
  starter topology uses `completed` while `rejected` and `incomplete_lineage` remain
  typed emitted reject / fail-closed states rather than accepted completion posture.

### Edge 9: Self-Edge Laundering

- Risk:
  the same worker subject could appear as both parent and child, turning topology into
  a relabelled single-worker replay.
- Response:
  require parent and child worker subjects to be distinct and fail closed on
  self-edge posture.

### Edge 10: Diagnostic-Family Drift

- Risk:
  the surface could expose `supporting_diagnostic_ids` while leaving the actual
  failure-family taxonomy underdefined.
- Response:
  freeze one starter supporting-diagnostic family vocabulary rather than leaving
  failure posture implementation-defined.

### Edge 11: Worker/Worker Creep

- Risk:
  the first topology release could quietly widen from supervisor/worker into
  worker/worker doctrine without making that seam explicit.
- Response:
  keep worker/worker doctrine out of the selected starter slice.

### Edge 12: Recursive Fan-Out Creep

- Risk:
  the first topology release could widen into recursive delegation trees, many-child
  algebra, or repo-wide orchestration regime before one bounded handoff edge is
  stable.
- Response:
  freeze one parent, one child, one edge only and keep recursive fan-out deferred.

### Edge 13: Prompt Authority Drift

- Risk:
  prompt text, chat prose, or `AGENTS.md` could still define delegated topology even
  after typed parent/child lineage exists.
- Response:
  keep prose projection-only and make topology-conflicting prose fail closed.

### Edge 14: Authority Expansion Through Topology

- Risk:
  because `V48-E` explicitly links workers, it could be overread as minting broader
  execution or approval authority than the released shared compiled boundary already
  allows.
- Response:
  keep the surface constrain-only, non-executive, non-approving, and same-boundary
  only.

### Edge 15: Package-Boundary Sprawl

- Risk:
  the topology lane could sprawl back into `adeu_repo_description`,
  `adeu_semantic_source`, or `adeu_commitments_ir` instead of first stabilizing as a
  harness-owned bridge surface.
- Response:
  keep `V48-E` bounded to `adeu_agent_harness` and consume earlier released bridge
  surfaces as upstream inputs only.

## Current Judgment

- `V48-E` is worth implementing now because `V48-A` through `V48-D` already released
  the binding, compiled-boundary, worker-envelope, and single-worker conformance
  halves of the bridge on `main`, while typed delegated topology remains the only
  selected unshipped seam inside the current `V48` family.
- the right next move is one bounded `supervisor_to_worker` handoff edge rather than
  generic orchestration, because ADEU should make one explicit two-worker relation
  inspectable before widening into worker/worker doctrine, recursive fan-out, or any
  repo-wide orchestration regime.
