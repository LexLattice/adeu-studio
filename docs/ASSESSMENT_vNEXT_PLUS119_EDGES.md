# Assessment vNext+119 Edges

Status: planning-edge assessment for `V49-C`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS119_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Released-Contract Bypass

- Risk:
  the lowering lane could skip released `V49-A` / `V49-B` contracts and lower from ad
  hoc intermediate structures.
- Response:
  require exactly one released normal form and one released transform contract in,
  with one bounded seed contract out.

### Edge 2: Upstream Outcome Shortcutting

- Risk:
  the lowering lane could silently choose one candidate out of
  `typed_alternatives` or otherwise lower from non-`resolved_singleton` recovery
  outputs.
- Response:
  admit lowering only from directly authored released `V49-A` normal forms or
  released `V49-B` outputs whose `parse_status` is exactly `resolved_singleton`.

### Edge 3: Required-Relation Softness

- Risk:
  missing required singleton relations could be silently repaired into apparent
  success.
- Response:
  fail closed on missing required singleton relations.

### Edge 4: Singleton Multiplicity Drift

- Risk:
  duplicate singleton relations could be tolerated inconsistently across
  implementations.
- Response:
  require duplicate singleton relations to fail closed.

### Edge 5: Multi-Relation Ordering Drift

- Risk:
  emitted path/effect/artifact sets could depend on incidental iteration order.
- Response:
  require deterministic dedupe and ordering by canonical `object_value`.

### Edge 6: `produce_artifact_kind` Multiplicity Drift

- Risk:
  the starter lowering slice could treat `produce_artifact_kind` as both singleton and
  multi-valued, leaving the multiplicity law to implementation taste.
- Response:
  freeze `produce_artifact_kind` as a required singleton relation in `V49-C` and emit
  it as one canonical artifact family represented as a single-item deterministic set.

### Edge 7: Unsupported Relation Laundering

- Risk:
  unsupported relation kinds or transform mismatches could be silently dropped while
  still producing a seed.
- Response:
  require unsupported relation kinds and transform mismatches to fail closed.

### Edge 8: Consumed Normal-Form Anchor Drift

- Risk:
  `transform_v48_seed.py` could end up defining what parts of the released normal form
  actually matter because the consumed input anchors are left implicit.
- Response:
  freeze the minimum consumed normal-form anchors in the lock: schema, profile/domain
  lineage, statement cores, identity-bearing per-core fields, and semantic hash.

### Edge 9: Fixed-Default Overreach

- Risk:
  `fixed_defaults` could become a back door for parser heuristics or bridge semantics.
- Response:
  treat `fixed_defaults` as contract-declared constant projection only, and fail closed
  if a fixed default conflicts with a relation-derived emitted value.

### Edge 10: Seed Contract Overreach

- Risk:
  the first lowering slice could emit something closer to a `V48-A` binding profile or
  a compiled boundary than to a narrow seed.
- Response:
  keep the emitted contract pre-bridge and pre-runtime, with one bounded seed family
  only, and state explicitly that it is not a `V48-A` binding profile without the
  later `V49-D` bridge.

### Edge 11: Bridge Laundering

- Risk:
  the first lowering slice could quietly add `V48-A` / `V48-B` helper behavior.
- Response:
  defer all downstream `V48` bridge helpers to `V49-D`.

### Edge 12: Projection Leakage Into Identity

- Risk:
  notices, diagnostics, or incidental lowering explanations could quietly change seed
  identity.
- Response:
  compute deterministic seed identity from the bounded emitted seed payload only.

### Edge 13: Consumer Prematurity

- Risk:
  symbol audit, paper semantics, simulation, or product consumers could leak into the
  first lowering release and blur ownership.
- Response:
  keep `V49-C` bounded to lowering behavior, fixtures, and targeted tests only.

## Current Judgment

- `V49-C` is worth implementing next because `V49-A` has already frozen the substrate
  contracts and `V49-B` has already frozen bounded recovery into those contracts on
  `main`.
- the next move should remain narrowly deterministic: one released normal form plus
  one released transform contract into one bounded seed, with fail-closed reject
  posture, explicit `resolved_singleton` gating for recovery-derived inputs, and no
  downstream `V48` helper widening yet.
