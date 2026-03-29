# Assessment vNext+98 Edges

Status: post-closeout edge assessment for `V42-G4` (March 29, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS98_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Harness-Binding Drift

- Risk:
  behavior bundles could detach from one released three-puzzle harness identity.
- Response:
  authoritative-surface binding to `harness_record_id` remains required and fail-closed.
- Closeout Evidence:
  rejected fixture
  `.../adeu_arc_behavior_evidence_bundle_v98_reject_harness_binding_mismatch.json`.

### Edge 2: Canonical Per-Puzzle Order Drift

- Risk:
  behavior entries could reorder puzzle identities while appearing structurally valid.
- Response:
  exactly three canonical per-puzzle entries are required in fixed order.
- Closeout Evidence:
  rejected fixture
  `.../adeu_arc_behavior_evidence_bundle_v98_reject_canonical_order_drift.json`.

### Edge 3: Cross-Puzzle Support Laundering

- Risk:
  cross-puzzle pattern claims could be emitted without valid support bindings to
  per-puzzle behavior entries.
- Response:
  support puzzle IDs, support behavior-entry refs, and support evidence refs are all
  required and cross-checked fail-closed.
- Closeout Evidence:
  rejected fixture
  `.../adeu_arc_behavior_evidence_bundle_v98_reject_cross_pattern_unsupported_by_per_puzzle_entries.json`.

### Edge 4: Failure-Mode Evidence Omission

- Risk:
  failure taxonomy entries could survive without typed evidence anchors.
- Response:
  failure-mode catalog entries require typed evidence refs with stable taxonomy fields.
- Closeout Evidence:
  rejected fixture
  `.../adeu_arc_behavior_evidence_bundle_v98_reject_missing_failure_mode_evidence_anchors.json`.

### Edge 5: Readiness/Necessity Claim Laundering

- Risk:
  claim-posture text could overclaim readiness or universal necessity.
- Response:
  forbidden-term checks and typed limitation posture keep claim scope bounded.
- Closeout Evidence:
  rejected fixture
  `.../adeu_arc_behavior_evidence_bundle_v98_reject_unsupported_readiness_claim_laundering.json`
  and regression test
  `test_v98_rejects_forbidden_reexecution_term_in_replay_scope_note`.

### Edge 6: Authority-Boundary Inversion

- Risk:
  narrative/descriptive surfaces could override typed authoritative surfaces.
- Response:
  boundary register remains structured and fail-closed on violation flags.
- Closeout Evidence:
  rejected fixture
  `.../adeu_arc_behavior_evidence_bundle_v98_reject_authority_boundary_contradiction.json`.

### Edge 7: Missing Per-Puzzle Upstream Refs

- Risk:
  behavior entries could omit required run/eval upstream lineage.
- Response:
  required per-puzzle upstream refs remain typed and non-empty.
- Closeout Evidence:
  rejected fixture
  `.../adeu_arc_behavior_evidence_bundle_v98_reject_missing_per_puzzle_upstream_refs.json`.

### Edge 8: Deterministic Replay Overclaim

- Risk:
  deterministic replay fields could still permit fresh model re-execution claims.
- Response:
  replay scope remains fixed-artifact/evidence only and rejects forbidden
  re-execution terms fail-closed.
- Closeout Evidence:
  validator enforcement in
  `packages/adeu_arc_agi/src/adeu_arc_agi/behavior_evidence_bundle.py` and targeted
  regression coverage in `test_arc_behavior_evidence_bundle_v42g4.py`.

### Edge 9: Cross-Puzzle Config Overreach

- Risk:
  inferred all-three claims could overreach when config posture is heterogeneous.
- Response:
  cross-puzzle config-consistency posture is carried and limitation posture is required
  for divergent all-three claims.
- Closeout Evidence:
  config-consistency checks in `behavior_evidence_bundle.py` plus accepted/rejected
  fixture replay coverage.

### Edge 10: Solver-Authority Minting

- Risk:
  synthesis could mint new semantic solver/puzzle-rule/capability authority absent
  upstream typed artifacts.
- Response:
  claim and summary surfaces remain non-authoritative and bounded to upstream typed
  evidence linkage.
- Closeout Evidence:
  authority-term guardrails in `behavior_evidence_bundle.py` and fail-closed fixture
  ladder coverage in `apps/api/fixtures/arc_agi/vnext_plus98/`.

## Current Judgment

- `V42-G4` closeout on `main` resolves the bounded behavior-evidence synthesis seam
  over released `V42-G3` harness outputs with typed support-bound, fail-closed
  evidence posture.
- The shipped baseline preserves deterministic replay scope discipline and rejects
  claim/authority laundering paths under one canonical
  `adeu_arc_behavior_evidence_bundle@1` boundary.
- With `V42-G1`..`V42-G4` closed on `main`, next-family selection is a planning choice
  beyond this closeout assessment.
