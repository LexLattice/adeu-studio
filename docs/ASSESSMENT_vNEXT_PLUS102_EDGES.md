# Assessment vNext+102 Edges

Status: planning-edge assessment for `V45-C` corrective hardening (`100-bis`).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS102_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Silent Rewrite Drift

- Risk:
  the corrective slice could quietly mutate the released `@1` surface rather than make
  the corrective-release posture explicit.
- Response:
  prefer `repo_arc_dependency_register@2` and keep the released `@1` artifact as
  historical baseline context.

### Edge 2: Provenance Laundering

- Risk:
  generic evidence lists could continue to hide which source surfaces actually support
  each entry and edge.
- Response:
  require explicit source-set provenance plus per-entry and per-edge source artifact
  refs, and require every `source_artifact_ref` to resolve inside the declared
  `source_set`.

### Edge 3: Blocker Projection Drift

- Risk:
  entry-level blocker lists could drift away from the dependency-edge subset that
  actually carries blocking force.
- Response:
  require exact reconciliation between `blocker_arc_ids` / `blocked_by_arc_ids` and the
  incoming unresolved hard-edge subset for each blocked entry.

### Edge 4: Epistemic Posture Blur

- Risk:
  consumers could overread inferred dependency claims as direct observation if
  derivation posture and method remain implicit.
- Response:
  require explicit artifact-level extraction posture and explicit entry/edge derivation
  posture and method.

### Edge 5: Cycle Law Without Representation

- Risk:
  the seam could keep talking about cycle posture without a field that actually carries
  it.
- Response:
  add explicit cycle posture and cycle detection scope to the corrected artifact shape.

### Edge 6: Vocabulary Folklore

- Risk:
  underdefined terms such as `supports_all_three_way_claim` or an unexplained
  machine-enforced pending list could harden into folklore rather than doctrine.
- Response:
  remove undefined vocabulary and replace it only with bounded explicitly defined
  posture and method vocabularies.

### Edge 7: Object-Boundary Collapse

- Risk:
  the corrected register could be mistaken for the later code dependency graph and then
  consumed with stronger authority than intended.
- Response:
  keep the artifact boundary explicit: this slice is planning/open-arc dependency
  posture only.

### Edge 8: Authority Creep

- Risk:
  better dependency visibility could still be overread as scheduling, plan-resolution,
  or mutation entitlement.
- Response:
  keep the corrected surface descriptive-first and non-promotional.

## Current Judgment

- a bounded `V45-C` corrective follow-up is justified before stronger `V45-B`
  consumers rely on the released `repo_arc_dependency_register@1` surface;
- the safest correction is provenance/epistemic/cycle hardening, not broader widening
  into code-self-description or recursive-governance binding.
