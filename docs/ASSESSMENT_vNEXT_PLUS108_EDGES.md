# Assessment vNext+108 Edges

Status: pre-lock edge assessment for `V47-C` (April 2, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS108_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Non-Override Collapse

- Risk:
  companion ANM posture could be mistaken for automatic supersession of current markdown
  lock/planning authority.
- Response:
  require explicit current-markdown authority relation, explicit non-override rule, and
  an exact invariant between that relation and
  `requires_later_lock_for_supersession`.

### Edge 2: Companion-Posture Ambiguity

- Risk:
  the same source could be read as standalone in one place and companion in another,
  leaving adoption posture implementation-defined.
- Response:
  classify source posture deterministically and require explicit host-or-companion
  linkage plus explicit companion embedding posture for companion rows.

### Edge 3: Silent Migration Doctrine

- Risk:
  bounded coexistence work could quietly become a migration mandate.
- Response:
  freeze migration posture vocabulary and reject repo-wide conversion claims in
  `V47-C`.

### Edge 4: Snapshot / Source-Scope Drift

- Risk:
  coexistence rows could bind together incompatible snapshots or source scopes and still
  look superficially plausible.
- Response:
  require same snapshot identity and explicit artifact-local source-scope compatibility
  checks.

### Edge 5: Orphaned Or Contradictory Linkage

- Risk:
  a companion row could point to a host that is missing, stale, source-scope
  incompatible, or authority-contradictory, while still looking structurally valid.
- Response:
  fail closed on orphaned, stale, or contradictory host-or-companion linkage.

### Edge 6: Adoption-Boundary Thinness

- Risk:
  the lane could classify source posture but still fail to say what the released ANM
  stack may constrain now versus what still requires later lock-level adoption.
- Response:
  ship explicit adoption-boundary rows with `allowed_now`, `later_lock_required`, and
  `forbidden` surfaces.

### Edge 7: Constrain-Action Overreach

- Risk:
  coexistence doctrine could claim vague “influence” without freezing which constrain
  actions are actually allowed.
- Response:
  enumerate allowed constrain actions exactly and require adoption-boundary rows to use
  the same frozen action vocabulary.

### Edge 8: Ownership-Transition Leakage

- Risk:
  coexistence/adoption work could quietly reopen the later selector/predicate ownership
  transition lane.
- Response:
  forbid imported O-owned selector handles and imported E-owned predicate registries in
  this slice.

### Edge 9: Execution Or Approval Laundering

- Risk:
  because `V47-C` talks about policy-bearing adoption, it could be overread as
  execution, approval, waiver, or deferral authority.
- Response:
  keep the release explicitly non-executive and non-approving, with later lock-level
  adoption still required for those powers.

### Edge 10: Example-Backed Coexistence Drift

- Risk:
  coexistence doctrine could stay persuasive in prose while fixtures fail to make
  standalone, companion, mixed-scope, and adoption-boundary posture legible.
- Response:
  require accepted fixtures for each of those postures plus reject fixtures for the
  failure modes they are meant to block.

### Edge 11: Package-Boundary Sprawl

- Risk:
  an adoption/doctrine lane could sprawl into unrelated packages or general docs tooling
  before the bounded profile surface is stable.
- Response:
  keep `V47-C` bounded to `adeu_semantic_source` plus `adeu_commitments_ir`.

## Current Judgment

- `V47-C` is the right next move because `V47-A` and `V47-B` already released the ANM
  substrate and its first hardening layer, while coexistence/adoption doctrine remains
  the next unclosed gap.
- The slice is only worth shipping if it stays doctrine-first and non-executive:
  explicit non-override, explicit companion posture, explicit migration discipline, and
  explicit adoption boundaries.
- If `V47-C` cannot keep those boundaries machine-inspectable, the lane should narrow
  rather than quietly widening into migration, ownership transition, or authority
  laundering.
