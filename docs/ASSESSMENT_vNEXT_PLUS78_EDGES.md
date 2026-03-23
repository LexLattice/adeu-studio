# Assessment vNext+78 Edges

Status: planning-edge assessment for `V40-B`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS78_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Root-Redefinition Drift

- Risk:
  `V40-B` could silently reinterpret or rewrite the released `V40-A` root-family
  contract while claiming only to compile it.
- Response:
  require the compiler package to consume the released root artifacts as authoritative
  inputs rather than minting replacement semantics.

### Edge 2: Conformance / Hybrid Collapse

- Risk:
  the first compiler slice could smuggle checkpoint/oracle behavior into the
  conformance report and blur deterministic readiness with hybrid adjudication.
- Response:
  keep `adeu_architecture_conformance_report@1` deterministic only and defer all
  checkpoint/oracle surfaces to `V40-C`.

### Edge 3: Gating Without Honest Lineage

- Risk:
  `blocked` or `ready` could be emitted as naked status without explicit failed-check
  ids or blocking ambiguity refs.
- Response:
  freeze blocked/ready gating as lineage-bearing output with explicit
  `failed_check_ids`, `blocking_ambiguity_refs`, and consumed-root replay lineage.

### Edge 4: Check-ID Instability

- Risk:
  compiler diagnostics could ship before stable semantic check-id families are frozen,
  making later conformance and closeout evidence harder to compare honestly.
- Response:
  release stable deterministic check-id families now for ontology, epistemics,
  deontics, utility, and pre-projection gating.

### Edge 5: Whole-ASIR Integrity Underreach

- Risk:
  `V40-B` could ship only section-local validators and miss the cross-section integrity
  pass that actually makes ASIR assemblable as one governed semantic object.
- Response:
  require one whole-ASIR integrity pass in the first compiler baseline.

### Edge 6: Premature Projection Leakage

- Risk:
  the compiler slice could start emitting projection manifests or lowered artifacts
  before the conformance lane itself is frozen.
- Response:
  keep emitted artifact refs empty in `V40-B` and defer all projection families to
  `V40-D`.

### Edge 7: Static Escalation vs Hybrid Drift

- Risk:
  `human_escalation_refs` could smuggle hybrid or checkpoint semantics into the
  deterministic conformance report before `V40-C` exists.
- Response:
  constrain `human_escalation_refs` to static deterministic escalation lineage only and
  forbid checkpoint-trace, oracle, or hybrid artifact refs in `V40-B`.

### Edge 8: Pre-Projection Check-Family Overreach

- Risk:
  `ASIR-P-xxx` could be interpreted as full projection-manifest integrity even though
  no projection bundle or manifest surface is released in this slice.
- Response:
  freeze `ASIR-P-xxx` in `V40-B` to pre-projection readiness honesty, blocked/ready
  correctness, and empty emitted-artifact posture only.

## Current Judgment

- `V40-B` is worth starting now because `V40-A` is closed on `main`, the repo now has a
  stable semantic-root substrate, and deterministic assembly/conformance is the
  narrowest next arc that turns those released artifacts into a usable compiler lane
  without widening prematurely into hybrid execution or downstream lowerings.
