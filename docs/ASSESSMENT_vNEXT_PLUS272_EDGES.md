# Assessment vNext+272 Edges

Status: starter edge assessment for `HOB-0-A`.

Authority layer: planning / starter gate.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS272_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Broker Becomes Semantic Judge

- Risk:
  the tool could decide applicability instead of validating model-authored
  activation rows.
- Starter containment:
  `HOB-0-A` records activation as supplied judgment and validates only catalog
  refs, vocabulary, warrants, and row shape.

### Edge 2: A Accidentally Implements Closure Aggregation

- Risk:
  traversal validation could blur into full subtree closure/readiness summary.
- Starter containment:
  A may reject invalid closure/readiness claims and emit blockers/frontiers, but
  full closure aggregation is deferred to `HOB-0-B`.

### Edge 3: Missing Children Silently Disappear

- Risk:
  selected parents could omit inherited children and still appear complete.
- Starter containment:
  selected parents import children from the catalog, and missing inherited
  children fail closed.

### Edge 4: Irrelevance Becomes A Prose Escape Hatch

- Risk:
  a worker marks a child irrelevant with weak prose.
- Starter containment:
  proof-sensitive statuses require structured proof rows with allowed proof
  types, protected surfaces, warrant refs, and evidence refs.

### Edge 5: Scoped Deferral Masquerades As Irrelevance

- Risk:
  a scoped deferral could close a parent or support gold readiness.
- Starter containment:
  scoped deferral is not irrelevance proof and blocks gold readiness.

### Edge 6: `not_inherited` And `optional_observed` Become Escape Hatches

- Risk:
  rows could avoid traversal through permissive inheritance statuses.
- Starter containment:
  `not_inherited` is allowed only when catalog default or inactive parent
  permits it; `optional_observed` cannot close a parent without local triggering
  or explicit promotion.

### Edge 7: Stale Catalog Ledgers Reused After Tree Changes

- Risk:
  a ledger from an older ontology catalog could be treated as current.
- Starter containment:
  every catalog, activation, ledger, and validation report binds catalog id,
  version, hash, and authority posture.

### Edge 8: Frontier Output Becomes Implementation Authority

- Risk:
  next-frontier rows could be read as permission to code or dispatch workers.
- Starter containment:
  frontier rows name required next descent actions only; non-authority guardrail
  denies probe execution, implementation, worker dispatch, product authority,
  and future-family selection.

### Edge 9: Probe Matrices Sneak Into A

- Risk:
  A could start generating concrete probes before closure/frontier semantics are
  stable.
- Starter containment:
  probe-matrix planning is deferred to `HOB-0-B`.

### Edge 10: Canonical Determinism Is Claimed But Not Tested

- Risk:
  row-order differences could change outputs or hashes.
- Starter containment:
  the starter fixture set requires shuffled input order to produce stable
  canonical output order and hash.

## Current Judgment

`HOB-0-A` is safe to draft as the first slice if it stays limited to catalog
validation, activation row validation, inherited ledger expansion, traversal
validation, next-frontier emission, and non-authority guardrails.

The strongest implementation risk is slice creep. The first PR should prove the
broker's deterministic traversal behavior with small fixtures before any
probe-matrix, implementation-batch, or delta-attribution machinery is added.
