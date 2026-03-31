# Assessment vNext+101 Edges

Status: planning-edge assessment for `V45-B`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS101_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Symbol-As-Authority Drift

- Risk:
  symbol-catalog outputs could be overread as refactor or scheduling authority.
- Response:
  keep symbol and dependency outputs descriptive-first and non-promotional.

### Edge 2: Dangling Dependency Laundering

- Risk:
  dependency edges could reference unknown symbol or module targets while still
  appearing valid, or collapse several endpoint kinds into one untyped ref string.
- Response:
  fail closed on any edge whose internal endpoints are not present in typed symbol or
  declared internal module-boundary surfaces, and require explicit endpoint kinds for
  boundary targets.

### Edge 3: Symbol-Role Overclaim

- Risk:
  symbol-role classifications could collapse into vague naming heuristics or unstated
  assumptions about implementation importance.
- Response:
  require explicit role-classification posture and classification method on typed symbol
  entries.

### Edge 4: Snapshot Overread

- Risk:
  one snapshot-bound symbol/dependency graph could be overread as current repo truth
  after repo drift.
- Response:
  keep snapshot validity posture explicit and treat stale outputs as historical.

### Edge 5: Provenance Regression Relative To `V102`

- Risk:
  `V45-B` could regress below the provenance rigor added in the `V45-C` hardening pass
  by omitting `source_set_hash`, top-level extraction posture/method, or per-row source
  and derivation anchors.
- Response:
  carry forward explicit source-set hash, top-level extraction posture/method, per-symbol
  source artifact refs, and per-edge derivation posture/method.

### Edge 6: Cross-Artifact Drift

- Risk:
  the symbol catalog and dependency graph could each validate independently while
  drifting across snapshot identity, source-set identity, or internal endpoint
  resolution.
- Response:
  require the emitted pair to reconcile over the same snapshot/source-set binding and
  require internal graph endpoints to resolve against the emitted symbol catalog or the
  declared internal module-boundary namespace.

### Edge 7: Whole-Repo And Cross-Language Scope Creep

- Risk:
  the first code-graph seam could widen early into whole-repo exhaustive or
  multi-language inventory work.
- Response:
  keep `v101` bounded to one explicit Python source-set posture only.

### Edge 8: Boundary Endpoint Ambiguity

- Risk:
  legitimate stdlib, third-party, or otherwise out-of-scope dependencies could be
  either rejected incorrectly or silently accepted as dangling strings if boundary
  typing remains implicit.
- Response:
  make external or out-of-scope dependencies explicit through bounded endpoint-kind and
  dependency-posture vocabularies rather than leaving them untyped.

### Edge 9: Test-Intent Laundering

- Risk:
  typed code-graph outputs could be overread as test-intent or invariant-binding
  doctrine.
- Response:
  defer test-intent matrix release to later `V45-D` work.

### Edge 10: Optimization Entitlement Creep

- Risk:
  hotspot or dependency concentration signals could be interpreted as automatic split,
  abstraction, or optimization entitlement.
- Response:
  keep `V45-B` descriptive-only and defer optimization-register doctrine to `V45-E`.

## Current Judgment

- `V45-B` is worth starting now because the next missing descriptive layer after the
  released `V45-A` and `V45-C` baselines is typed code-level self-description.
- The safest first seam is symbol catalog plus typed dependency graph release, not
  optimization advice, test-intent claims, or normative binding.
