# Assessment vNext+90 Edges

Status: post-closeout edge assessment for `V42-B`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS90_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "authoritative_scope": "v90_closeout_edge_assessment",
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Task-Packet Lineage Drift

- Risk:
  observation or hypothesis artifacts could be authored against ambient or synthetic
  state while claiming released packet lineage.
- Response:
  require one released `adeu_arc_task_packet@1` lineage binding in both artifacts and
  fail closed on missing or mismatched packet identity.

### Edge 2: O/E Typing Collapse

- Risk:
  direct observations and derived inferences could be blended inside one untyped field,
  making evidence quality unverifiable.
- Response:
  require per-entry direct-vs-derived typing, evidence refs, and explicit unresolved
  posture in observation artifacts.

### Edge 2A: Ontology Hidden In Observation Prose

- Risk:
  ontology decomposition could remain implicit inside observation text so `O` is not
  statically inspectable as its own surface.
- Response:
  require first-class ontology inventory surfaces (`ontology_register`,
  entity/relation/state-partition inventories, ontology uncertainty register).

### Edge 2B: Coverage Denominator Drift

- Risk:
  decomposition coverage could become decorative if denominator and required dimensions
  are not explicit.
- Response:
  require denominator-bound coverage via explicit coverage basis, required dimensions,
  and missing-dimension register.

### Edge 3: Hypothesis Support Laundering

- Risk:
  hypotheses could be emitted as plausible prose without explicit observation support
  refs, then treated as settled interpretation.
- Response:
  require hypothesis entries to bind to typed observation refs and explicit claim
  posture.

### Edge 3A: Derived Observation / Hypothesis Bleed

- Risk:
  derived observation fields could be used to smuggle candidate governing-transform
  claims that should live in hypothesis artifacts.
- Response:
  reject derived observations that depend on task-rule interpretation and require such
  content to appear only in hypothesis surfaces with explicit posture.

### Edge 4: Ambiguity Erasure

- Risk:
  unresolved ambiguity could disappear when working hypothesis posture is emitted,
  causing counterfeit certainty.
- Response:
  require explicit ambiguity register plus non-committing working-hypothesis posture
  that preserves unresolved alternatives.

### Edge 5: Impossibility Overclaim

- Risk:
  bounded local search failure could be promoted to impossibility in hypothesis output.
- Response:
  reject unsupported impossibility posture and require explicit conjectural/blocked
  posture where evidence is insufficient.

### Edge 6: Hidden Solver Widening

- Risk:
  `V42-B` could smuggle action-search, rollout, or scorecard semantics into
  observation/hypothesis fields under neutral naming.
- Response:
  keep `V42-B` bounded to observation + hypothesis only and reject action/rollout/
  scorecard authority leakage.

### Edge 7: Deontic Boundary Loss

- Risk:
  mode/legal admissibility carried by task packet could be dropped or recomputed
  informally by solver-local interpretation.
- Response:
  require explicit deontic admissibility carry-through from packet authority and fail
  closed on posture drift.

### Edge 8: Utility Surface Re-Hiding

- Risk:
  utility/pressure semantics could be referenced in doctrine but remain implicit in
  artifact output, enabling hidden prioritization.
- Response:
  require explicit utility-pressure register in hypothesis artifacts, bounded to
  non-committing interpretation posture in `V42-B`.

## Current Judgment

- `V42-B` is the correct next slice because it enforces explicit ARC decomposition and
  interpretation posture before any tactical action commitment.
- The slice is safe only if ontology inventory, denominator-bound coverage,
  derived-vs-hypothesis separation, ambiguity carry-through, and impossibility restraint
  remain machine-checkable and fail closed.
