# Assessment vNext+97 Edges

Status: post-closeout edge assessment for `V42-G3` (March 29, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS97_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Selection Register Drift

- Risk:
  harness execution could use puzzles outside the frozen selection register.
- Response:
  selection authority remains typed and fail-closed on undeclared puzzle IDs.
- Closeout Evidence:
  accepted fixture binds one released selection register and rejected fixture
  `.../adeu_arc_three_puzzle_harness_record_v97_reject_retroactive_selection_swap.json`.

### Edge 2: Retrospective Swap and Canonical-Order Drift

- Risk:
  outcomes could influence puzzle replacement or execution order after observation.
- Response:
  exact canonical order from selection register is enforced; swap/order drift is
  rejected fail-closed.
- Closeout Evidence:
  rejected fixtures
  `..._reject_retroactive_selection_swap.json` and
  `..._reject_canonical_order_violation.json`.

### Edge 3: Incomplete-Entry Laundering

- Risk:
  harness records could claim completion while omitting one canonical puzzle entry.
- Response:
  exactly three canonical puzzle-entry slots are required for accepted records.
- Closeout Evidence:
  rejected fixture
  `.../adeu_arc_three_puzzle_harness_record_v97_reject_omitted_third_entry_laundering.json`
  and model constraints in `three_puzzle_harness.py`.

### Edge 4: Per-Puzzle Stage-Evidence Regression

- Risk:
  harness derivation could accept weaker or overridden stage evidence than the bound
  `V42-G2` run record.
- Response:
  per-entry stage evidence must exactly match the staged evidence derived from the bound
  reasoning-run record; drift is rejected fail-closed.
- Closeout Evidence:
  stage-evidence parity checks in
  `packages/adeu_arc_agi/src/adeu_arc_agi/three_puzzle_harness.py` and targeted test
  `test_v97_derive_rejects_stage_evidence_override_drift`.

### Edge 5: Cross-Puzzle Runtime Identity-Chain Mismatch

- Risk:
  a harness could aggregate runs from mixed runtime contexts while presenting one
  coherent run boundary.
- Response:
  all three runs must share `environment_ref`, `session_ref`, and
  `competition_scope_ref`; mixed identity chains are rejected fail-closed.
- Closeout Evidence:
  runtime-identity consistency checks in `three_puzzle_harness.py` and targeted test
  `test_v97_derive_rejects_mixed_runtime_identity_chain`.

### Edge 6: Cross-Puzzle Config Drift

- Risk:
  run-config differences across puzzles could be silently treated as comparable output.
- Response:
  cross-puzzle agent/config identity remains required unless explicit divergence posture
  is typed.
- Closeout Evidence:
  rejected fixture
  `.../adeu_arc_three_puzzle_harness_record_v97_reject_untyped_config_drift.json`.

### Edge 7: Harness Sequence Non-Determinism

- Risk:
  harness sequence ordering/evidence could drift while still appearing structurally
  complete.
- Response:
  structured monotonic `harness_sequence_entries` with per-step evidence refs is
  required.
- Closeout Evidence:
  rejected fixture
  `.../adeu_arc_three_puzzle_harness_record_v97_reject_missing_monotonic_sequence_evidence.json`.

### Edge 8: Aggregation Contradiction

- Risk:
  optional harness aggregate refs could contradict per-puzzle downstream refs.
- Response:
  aggregate refs are optional but, when present, must be recomputed and match
  per-puzzle refs exactly.
- Closeout Evidence:
  aggregate-ref recomputation checks in `three_puzzle_harness.py` and rejected fixture
  `..._reject_aggregated_ref_contradiction.json`.

### Edge 9: Premature Widening Into G4

- Risk:
  `V42-G3` could silently widen into behavior-evidence synthesis semantics.
- Response:
  shipped surfaces remain bounded to deterministic three-puzzle orchestration only;
  `V42-G4` remains deferred.
- Closeout Evidence:
  delivered schemas/fixtures/tests are bounded to `adeu_arc_three_puzzle_harness_record@1`
  and do not mint `V42-G4` evidence-synthesis artifacts.

### Edge 10: Narrative Overclaim

- Risk:
  run summary text could be interpreted as authoritative over typed harness fields.
- Response:
  narrative remains non-authoritative and subordinate to typed identity/occupation
  surfaces.
- Closeout Evidence:
  `run_summary` forbidden-term validation in `three_puzzle_harness.py`.

## Current Judgment

- `V42-G3` closeout on `main` resolves the practical deterministic multi-puzzle local
  orchestration seam over released `V42-G1`/`V42-G2` surfaces.
- The shipped baseline preserves fail-closed posture for selection/order/entry/stage/
  identity/config/aggregation contradictions under one typed three-puzzle harness
  boundary.
- Remaining practical widening now belongs to `V42-G4` (behavior mapping and evidence
  bundle), while retaining the authority discipline established through `V42-G1`..`G3`.
