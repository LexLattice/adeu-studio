# V53-D Semantic IR Bridge (Stage 1)

## Scope Lock

This semantic lowering is bounded to one `V53-D` probe-strategy/test-intent seam in
`packages/adeu_edge_ledger`, downstream of released `V53-A`/`V53-B`/`V53-C` and released
`V45-D` test-intent surfaces.

## Semantic Objects

- **Bridge contract artifact**:
  `adeu_edge_probe_test_intent_bridge@1`
- **Bridge row**:
  one deterministic mapping row per `repo_test_intent_matrix@1` entry
- **Bridge statuses** (frozen for this seam):
  - `mapped_from_applicability_frame`
  - `no_applicable_probe_in_frame`
  - `out_of_scope_non_symbol_guard`
  - `out_of_scope_outside_v50_scope`

## Authoritative Invariants

1. **No probe mapping without applicability-frame membership**
   - Probe-template selection is admitted only when the guarded surface is `internal_symbol`
     and a matching `SymbolEdgeApplicabilityFrame` exists for that exact `symbol_id`.
2. **No bypass of applicability/frame law**
   - Mapped probes must be drawn from the bound frame rows with
     `applicable|underdetermined` status and from that row’s
     `suggested_probe_template_refs` only.
3. **Bounded V50 posture**
   - `internal_symbol` rows outside admitted V50 symbol kinds or without explicit frame
     membership remain out-of-scope in this seam; no silent widening into new scope.
4. **Fail-closed over V45-D/V45-B bindings**
   - The bridge must bind to and validate against supplied V45-D matrix + V45-B
     symbol/dependency pair before mapping.
5. **Deterministic identity**
   - Row and bridge IDs/hashes are canonical-hash-derived and replay-stable.

## Contract Item Lowering

- `C1`: Release one bounded bridge schema in `adeu_edge_ledger` with authoritative+mirror
  export.
- `C2`: Deterministically cover every V45-D test-intent entry exactly once.
- `C3`: Enforce no mapping when no admissible applicability-frame membership exists.
- `C4`: Enforce mapped probe refs are subset of frame suggestions only.
- `C5`: Preserve out-of-scope posture for non-symbol guards and out-of-scope symbol rows.
- `C6`: Keep implementation/test verification bounded to `packages/adeu_edge_ledger`.

## Stage-2 Transposition Target

Stage 2 must materialize this exact semantic IR without widening runtime, mutation,
reviewer platform, governance, CI-governance semantics, or broad probe execution framework.
