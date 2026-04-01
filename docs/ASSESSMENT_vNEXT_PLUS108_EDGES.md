# Assessment vNext+108 Edges

Status: post-closeout edge assessment for `V47-C` (April 2, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS108_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
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
- Closeout Evidence:
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  `packages/adeu_semantic_source/tests/fixtures/v47c/reference_coexistence_spec.json`,
  and tests `test_v47c_reference_profile_replays_deterministically`,
  `test_v47c_rejects_inconsistent_supersession_spec`, and
  `test_v47c_rejects_inconsistent_supersession_fields`.

### Edge 2: Companion-Posture Ambiguity

- Risk:
  the same source could be read as standalone in one place and companion in another,
  leaving adoption posture implementation-defined.
- Response:
  classify source posture deterministically and require explicit host-or-companion
  linkage plus explicit companion embedding posture for companion rows.
- Closeout Evidence:
  source-posture classification in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  committed fixtures `standalone_policy.adeu.md`, `companion_policy.md`,
  `current_authority.md`, and accepted profile fixture
  `packages/adeu_commitments_ir/tests/fixtures/v47c/reference_anm_markdown_coexistence_profile.json`.

### Edge 3: Silent Migration Doctrine

- Risk:
  bounded coexistence work could quietly become a migration mandate.
- Response:
  freeze migration posture vocabulary and reject repo-wide conversion claims in
  `V47-C`.
- Closeout Evidence:
  `MigrationDiscipline` in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  migration enforcement in `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  and test `test_v47c_rejects_source_row_posture_forbidden_by_migration_discipline`.

### Edge 4: Snapshot / Source-Scope Drift

- Risk:
  coexistence rows could bind together incompatible snapshots or source scopes and still
  look superficially plausible.
- Response:
  require same snapshot identity and explicit artifact-local source-scope compatibility
  checks.
- Closeout Evidence:
  same-snapshot/source-scope checks in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  accepted mixed-scope reference spec
  `packages/adeu_semantic_source/tests/fixtures/v47c/reference_coexistence_spec.json`,
  and deterministic replay coverage in `test_v47c_reference_profile_replays_deterministically`.

### Edge 5: Orphaned Or Contradictory Linkage

- Risk:
  a companion row could point to a host that is missing, stale, source-scope
  incompatible, or authority-contradictory, while still looking structurally valid.
- Response:
  fail closed on orphaned, stale, or contradictory host-or-companion linkage.
- Closeout Evidence:
  reject specs `reject_orphaned_host_spec.json` and
  `reject_stale_or_contradictory_host_spec.json`,
  plus tests `test_v47c_rejects_orphaned_host_linkage`,
  `test_v47c_rejects_stale_or_contradictory_host_linkage`, and
  `test_v47c_rejects_contradictory_host_authority_kind`.

### Edge 6: Adoption-Boundary Thinness

- Risk:
  the lane could classify source posture but still fail to say what the released ANM
  stack may constrain now versus what still requires later lock-level adoption.
- Response:
  ship explicit adoption-boundary rows with `allowed_now`, `later_lock_required`, and
  `forbidden` surfaces.
- Closeout Evidence:
  `AnmAdoptionBoundaryRow` in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  accepted adoption-boundary rows in
  `packages/adeu_semantic_source/tests/fixtures/v47c/reference_coexistence_spec.json`,
  and accepted profile replay in `test_v47c_reference_profile_replays_deterministically`.

### Edge 7: Constrain-Action Overreach

- Risk:
  coexistence doctrine could claim vague “influence” without freezing which constrain
  actions are actually allowed.
- Response:
  enumerate allowed constrain actions exactly and require adoption-boundary rows to use
  the same frozen action vocabulary.
- Closeout Evidence:
  `AllowedConstrainAction` typing and exported schema parity in
  `packages/adeu_commitments_ir/tests/test_export_schema.py`,
  plus `test_v47c_rejects_boundary_action_drift_spec` and
  `test_v47c_rejects_boundary_action_outside_frozen_vocabulary`.

### Edge 8: Ownership-Transition Leakage

- Risk:
  coexistence/adoption work could quietly reopen the later selector/predicate ownership
  transition lane.
- Response:
  forbid imported O-owned selector handles and imported E-owned predicate registries in
  this slice.
- Closeout Evidence:
  frozen `V47-C` lock scope in `docs/LOCKED_CONTINUATION_vNEXT_PLUS108.md`,
  bounded implementation footprint in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py` and
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  and absence of ownership-transition surfaces in shipped `v47c` fixtures.

### Edge 9: Execution Or Approval Laundering

- Risk:
  because `V47-C` talks about policy-bearing adoption, it could be overread as
  execution, approval, waiver, or deferral authority.
- Response:
  keep the release explicitly non-executive and non-approving, with later lock-level
  adoption still required for those powers.
- Closeout Evidence:
  adoption-boundary action matrix in the committed `v47c` profile fixture,
  bounded constrain-action vocabulary in `anm_models.py`,
  and the frozen non-executive/non-approving scope in
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS108.md`.

### Edge 10: Example-Backed Coexistence Drift

- Risk:
  coexistence doctrine could stay persuasive in prose while fixtures fail to make
  standalone, companion, mixed-scope, and adoption-boundary posture legible.
- Response:
  require accepted fixtures for each of those postures plus reject fixtures for the
  failure modes they are meant to block.
- Closeout Evidence:
  accepted standalone/companion/current-authority/reference profile fixtures under
  `packages/adeu_semantic_source/tests/fixtures/v47c/` and
  `packages/adeu_commitments_ir/tests/fixtures/v47c/`,
  plus reject specs for supersession, orphaned/stale linkage, and action drift.

### Edge 11: Package-Boundary Sprawl

- Risk:
  an adoption/doctrine lane could sprawl into unrelated packages or general docs tooling
  before the bounded profile surface is stable.
- Response:
  keep `V47-C` bounded to `adeu_semantic_source` plus `adeu_commitments_ir`.
- Closeout Evidence:
  shipped implementation footprint in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  and bounded package selection in `docs/LOCKED_CONTINUATION_vNEXT_PLUS108.md`.

## Current Judgment

- `V47-C` was the right next move because `V47-A` and `V47-B` had already released the
  bounded ANM substrate and its first hardening layer on `main`, while coexistence and
  companion-doc adoption doctrine remained the next unclosed gap.
- `V47-C` on `main` now resolves that gap by shipping one typed coexistence profile
  with deterministic source-posture classification, explicit non-override and
  embedding posture, bounded migration discipline, and explicit adoption-boundary rows.
- the shipped seam remains doctrine-first and non-authorizing, so later `V47-D+`
  ownership-transition or downstream-consumer lanes can build on it without being
  silently authorized by companion ANM existence alone.
