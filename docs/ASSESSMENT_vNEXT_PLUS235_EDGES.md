# Assessment vNext+235 Edges

Status: pre-lock edge assessment for `V83-C`.

Authority layer: planning / starter scaffold.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS235_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Projection Packet Could Become Implementation

- Starter containment:
  `V83-C` may emit implementation-spec projection packets for review only.
  Packets must carry non-implementation posture and cannot claim code changed.
- Expected implementation proof:
  projection packets with implementation, PR, commit, merge, release, or
  work-packet execution claims reject.

### Edge 2: Projection Packet Could Drop Released Substrate

- Starter containment:
  every packet must reference known released `V83-A` intent rows and released
  `V83-B` edge, obligation, and drift rows.
- Expected implementation proof:
  packets without known intent, edge decomposition, obligation map, or drift
  register refs reject.

### Edge 3: Generated Projection Could Become Authority

- Starter containment:
  model / agent / mixed projection provenance remains candidate-only and must
  cite prompt context, actor/profile refs, and input intent / edge /
  obligation refs.
- Expected implementation proof:
  model- or agent-generated projection packets without provenance rows reject.

### Edge 4: Quality Gate Could Pass From Tests Alone

- Starter containment:
  quality gates require source binding, semantic edge coverage, validation
  evidence, reject fixtures, non-goal preservation, authority boundary checks,
  and future-family boundary checks.
- Expected implementation proof:
  gates passing with tests only and no semantic coverage reject.

### Edge 5: Ready Posture Could Hide Drift

- Starter containment:
  projection packets and handoffs must carry blockers and warnings explicitly.
  Ready posture cannot erase blocking drift.
- Expected implementation proof:
  ready packets or handoffs with carried blockers reject.

### Edge 6: Implementation Spec Rows Could Use Broad Targets

- Starter containment:
  implementation spec rows must reference bounded concrete target surfaces and
  known artifact obligations.
- Expected implementation proof:
  broad repo/package/glob target surfaces marked ready reject.

### Edge 7: Work-Packet Handoff Could Become Work Authority

- Starter containment:
  handoffs require `work_packet_authority_posture` and
  `implementation_lock_requirement`; later lock authority remains required.
- Expected implementation proof:
  handoffs marked ready to implement now, missing canonical later-lock
  requirement, or marked executed reject.

### Edge 8: Meta-Orchestrator / Morphic / Direct OAI Could Become Runtime

- Starter containment:
  meta-orchestrator, Morphic UX, and direct OAI handoffs remain review-only or
  future-family-only. They do not mutate workflow state, UI runtime, or
  provider runtime behavior.
- Expected implementation proof:
  runtime-transition, UI-change, or provider-authority claims reject.

### Edge 9: Family Closeout Could Select V84

- Starter containment:
  closeout alignment may close `V83` only. It must carry future pressure
  without selecting `V84` or any later family.
- Expected implementation proof:
  closeout rows selecting `V84`, product work, graph memory, runtime,
  implementation, release, or recursive policy authority reject.

## Residual Edges

- A later family may need to decide whether emitted handoff pressure should
  become implementation work-packet activation review, Morphic UX projection
  implementation, direct OAI harness implementation, generalized digital
  artifact projection, graph memory, or another family.
- `V83-C` should not preselect that next family; it should only make the
  handoff pressure source-bound and reviewable.

## Current Judgment

The `vNext+235` starter scope is ready for a bounded `V83-C` implementation
draft. The active implementation should ship only implementation-spec
projection packet, intent-to-work-packet handoff, and family closeout alignment
records. The main risks are projection-as-implementation, generated-spec
authority drift, test-only quality gates, hidden drift blockers, broad target
laundering, work-packet authority laundering, runtime-surface leakage, and
early `V84` selection; all are represented as required starter validators and
reject fixtures.
