# Assessment vNext+71 Edges

Status: planning-edge assessment for `V38-A`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS71_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Payload Drift Into Generic AI Planning

- Risk:
  the slice could widen into a general-purpose planner instead of a bounded
  ADEU/UDEO packet compiler.
- Response:
  keep the committed reference fixture narrow and tied to the current master
  payload plus the existing URM tool surface.

### Edge 2: Runtime Role Inflation

- Risk:
  the slice could overreach by inventing many new runtime roles when the repo
  already has a released delegated-role surface.
- Response:
  keep runtime roles minimal and express richer semantics inside typed session
  packets unless a role split is clearly necessary.

### Edge 3: Parallel Family Drift

- Risk:
  the slice could ship both a brokered-reflexive family and a parallel
  `reflexive_governance` family, leaving overlapping schemas and exports.
- Response:
  keep `brokered_reflexive_execution.py` as the only active family in this
  slice and realign docs/tests/fixtures to that substrate.

### Edge 4: Sentinel Overclaim

- Risk:
  "sentinel" semantics could be claimed in prose without enforceable guardrail
  fields.
- Response:
  require explicit guardrails, declared protected aims, licensed intervention
  depth, and failure/stop conditions in the typed plan.

### Edge 5: Review Loop Informality

- Risk:
  adversarial review and code review could remain implicit habits rather than
  typed delegated session packets.
- Response:
  materialize them as first-class session roles with explicit budget posture and
  truth conditions.

### Edge 6: Policy Surface Shadow Gap

- Risk:
  the compile surface could pass the direct route but remain unavailable through
  capability policy or UI allowlists.
- Response:
  keep capability lattice, packaged mirror, runtime role policy, and Copilot
  allowlist in sync for the advisory compile action.

## Current Judgment

- `V38-A` is worth implementing now because it closes a real substrate gap
  between the repo's philosophical control plane and its released orchestration
  runtime.
