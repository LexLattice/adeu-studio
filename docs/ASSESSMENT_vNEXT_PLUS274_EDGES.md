# Assessment vNext+274 Edges

Status: starter edge assessment for `HOB-0-C`.

Authority layer: planning / starter gate.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS274_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Edge Review

### Edge 1: Delta Attribution Becomes Product Truth

- Risk:
  attribution rows could be read as clean behavior truth instead of pressure
  over numbered obligations.
- Starter containment:
  every attribution row requires `evidence_boundary_posture`, and clean product
  truth is outside C authority.

### Edge 2: Score Movement Becomes Macro Closure

- Risk:
  official-like score movement could be interpreted as macro closure.
- Starter containment:
  score movement cannot close a macro without released closure evidence; score
  rows remain pressure, not closure proof.

### Edge 3: Post-Eval Pressure Is Laundered As Clean Evidence

- Risk:
  official failures, postmortem rows, or source-postmortem pressure could be
  mislabeled as clean first-pass semantic evidence.
- Starter containment:
  allowed evidence boundary postures distinguish `post_eval_pressure_only`,
  `official_like_pressure`, `source_postmortem_pressure`, and
  `clean_first_pass_disallowed`.

### Edge 4: Stale Ledger Reuse After Catalog Changes

- Risk:
  old ledgers or probe plans could be reused after the numbered catalog
  changes.
- Starter containment:
  stale-ledger invalidation reports require prior/current catalog
  id/version/hash and fail closed on unhandled hash changes.

### Edge 5: Integration Handoff Becomes Future-Family Selection

- Risk:
  handoff rows could grant ProgramBench, semantic compiler, probe execution,
  implementation, or future-family authority.
- Starter containment:
  handoff rows are pressure-only and require explicit non-selection and
  non-authority postures.

### Edge 6: C Reopens A Or B Decisions

- Risk:
  C could re-decide semantic applicability from A or recompute closure outside
  released B records.
- Starter containment:
  C consumes released A/B records and validates catalog continuity; it does not
  reopen activation or closure computation.

### Edge 7: Family Closeout Hides Unresolved Blockers

- Risk:
  family closeout alignment could mark the family closed while unresolved B or
  C blockers remain.
- Starter containment:
  closeout alignment must list closed slices and residual deferred refs, and it
  fails closed on unresolved blockers.

### Edge 8: Canonical Determinism Is Claimed But Not Tested

- Risk:
  row-order differences could change attribution, stale-ledger, handoff, or
  closeout hashes.
- Starter containment:
  the starter fixture set requires shuffled input order to preserve output
  order and canonical hashes.

## Current Judgment

`HOB-0-C` is safe to draft as the final slice if it stays limited to delta
attribution, stale-ledger invalidation, pressure-only integration handoff, and
family closeout alignment over released `HOB-0-A` / `HOB-0-B` artifacts.

The strongest implementation risks are evidence laundering and score-to-closure
promotion. The first C PR should prove evidence-boundary discipline with small
deterministic fixtures before any probe runner, worker orchestration,
ProgramBench integration, or implementation-authority machinery is added.
