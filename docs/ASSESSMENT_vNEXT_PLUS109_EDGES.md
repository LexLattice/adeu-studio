# Assessment vNext+109 Edges

Status: pre-lock edge assessment for `V47-D` (April 2, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS109_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Owner-Layer Vocabulary Drift

- Risk:
  `V47-D` could introduce a new bootstrap owner-layer term that drifts from the
  earlier released bootstrap vocabulary instead of projecting it consistently.
- Response:
  freeze one normalized bootstrap owner-layer term for ownership-profile rows and make
  explicit that it is the same bootstrap concept already used by released
  bootstrap predicate-contract surfaces.

### Edge 2: Implicit Selector Promotion

- Risk:
  bootstrap string selectors could be silently reinterpreted as imported O-owned
  selector handles by naming or code convention alone.
- Response:
  require explicit selector ref kind, explicit selector owner layer, and explicit
  imported handle refs where owned posture is claimed.

### Edge 3: Implicit Predicate Promotion

- Risk:
  bootstrap predicate contracts could be silently reinterpreted as imported E-owned
  predicate-registry bindings without typed transition doctrine.
- Response:
  require explicit predicate ref kind, explicit predicate owner layer, and explicit
  imported registry refs where owned posture is claimed.

### Edge 4: Row Mutual-Exclusion Drift

- Risk:
  selector or predicate rows could carry both bootstrap and imported ref fields at
  once, leaving contradictory mixed state inside a single row.
- Response:
  freeze explicit per-row mutual-exclusion invariants tying ref kind, owner layer, and
  required/forbidden ref fields together.

### Edge 5: Compatibility-Matrix Thinness

- Risk:
  compatibility posture could stay persuasive in prose while the actual bootstrap vs
  owned combinations remain under-specified.
- Response:
  require a first-class compatibility matrix covering the four selector/predicate
  ownership combinations with explicit allowed/forbidden, replay, later-lock, and
  mixed-ownership-constrained fields.

### Edge 6: Bootstrap Retirement Laundering

- Risk:
  a slice could imply that bootstrap selectors/predicate contracts are retired without
  the later-lock posture needed to authorize that retirement.
- Response:
  require explicit bootstrap-retirement posture and fail closed when retirement is
  claimed without later-lock binding.

### Edge 7: Imported-Ref Resolution Drift

- Risk:
  imported selector handles or predicate-registry refs could be dangling, stale, or
  identity/version incompatible while still looking syntactically valid.
- Response:
  require imported refs to resolve fail closed against the declared snapshot,
  source-scope, and declared identity/version binding.

### Edge 8: Snapshot / Source-Scope Drift

- Risk:
  ownership-transition rows could bind together incompatible snapshots or source scopes
  and still look structurally plausible.
- Response:
  require same snapshot identity and explicit artifact-local source-scope compatibility
  checks.

### Edge 9: Backward-Compatibility Erasure

- Risk:
  the ownership-transition lane could break replay or interpretation of released
  bootstrap `V47-A` / `V47-B` / `V47-C` artifacts while claiming compatibility.
- Response:
  require explicit backward-compatible bootstrap replay and reject silent semantic
  reinterpretation.

### Edge 10: Authority Leakage Through Owned Surfaces

- Risk:
  imported owned selector/predicate posture could be overread as authority to mint
  execution, approval, migration, or consumer-binding powers.
- Response:
  keep the slice explicitly non-executive, non-migratory, and non-consumer-binding,
  with anti-leakage reject fixtures.

### Edge 11: Schema/Fixture Drift

- Risk:
  typed ownership doctrine could look clean in prose while authoritative schema,
  mirrored schema, and accepted fixtures drift apart.
- Response:
  require parity across docs, authoritative schema, mirrored schema, and committed
  fixtures for the released ownership profile.

### Edge 12: Package-Boundary Sprawl

- Risk:
  an ownership-transition lane could sprawl into unrelated packages or downstream
  consumers before the bounded profile surface is stable.
- Response:
  keep `V47-D` bounded to `adeu_semantic_source` plus `adeu_commitments_ir`.

## Current Judgment

- `V47-D` is the right next move because `V47-A` through `V47-C` already released the
  bounded ANM substrate, hardening layer, and coexistence/adoption doctrine, while
  explicit ownership transition remains the next unclosed gap.
- The slice is only worth shipping if it stays transition-first and non-authorizing:
  explicit owner layers, explicit compatibility posture, explicit bootstrap-retirement
  posture, and fail-closed anti-leakage rules.
- If `V47-D` cannot keep those boundaries machine-inspectable, the lane should narrow
  rather than quietly widening into migration, downstream consumers, or authority
  laundering.
