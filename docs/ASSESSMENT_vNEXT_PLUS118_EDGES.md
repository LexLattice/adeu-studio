# Assessment vNext+118 Edges

Status: post-closeout edge assessment for `V49-B` (April 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS118_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: `V49-A` Contract Bypass

- Risk:
  the recovery lane could claim `V49-B` ownership while emitting ad hoc local
  structures instead of the released `V49-A` contracts.
- Response:
  keep one released parse profile in and one released parse-result contract out.
- Closeout Evidence:
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/parser.py`,
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py`, and parser replay
  fixtures under `packages/adeu_semantic_forms/tests/fixtures/v49b/`.

### Edge 2: Heuristic Widening

- Risk:
  the first recovery slice could mint new relation kinds, lane tags, object kinds, or
  domains under the cover of natural-language parsing.
- Response:
  keep recovery bounded to released `V49-A` vocabularies and the starter domain
  `repo_policy_work` only.
- Closeout Evidence:
  profile-bound parser recovery in
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/parser.py` plus committed
  `v49b` fixtures.

### Edge 3: Candidate Distinctness Drift

- Risk:
  two implementations could emit different dedupe behavior while both claiming to
  produce the same typed result.
- Response:
  freeze candidate sameness to released `normal_form.semantic_hash` only and require
  dedupe before outcome classification.
- Closeout Evidence:
  `_dedupe_candidates(...)` in
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/parser.py` and
  `test_dedupe_candidates_collapses_same_semantic_hash`.

### Edge 4: Candidate Ordering Drift

- Risk:
  alternative ordering could depend on incidental iteration order, alias scan order,
  or cartesian-product order.
- Response:
  require deterministic alternative ordering by canonical semantic hash before
  `candidate_rank` assignment.
- Closeout Evidence:
  parser ordering logic and
  `packages/adeu_semantic_forms/tests/test_semantic_forms_parser.py::test_typed_alternatives_are_sorted_by_semantic_hash`.

### Edge 5: Outcome Boundary Drift

- Risk:
  behavior could blur the distinction between `typed_alternatives`,
  `clarification_required`, and `rejected_unsupported`.
- Response:
  freeze the outcome vocabulary and require committed fixtures for each starter
  outcome, including zero-candidate clarification posture.
- Closeout Evidence:
  parser replay fixtures for resolved singleton, typed alternatives, clarification
  required, rejected unsupported, and exact-anchor precedence under
  `packages/adeu_semantic_forms/tests/fixtures/v49b/`.

### Edge 6: Unsupported Laundering

- Risk:
  unsupported inputs could be quietly coerced into apparent success.
- Response:
  require explicit `rejected_unsupported` posture driven by released unsupported
  patterns and out-of-domain detection.
- Closeout Evidence:
  reject posture in parser source and
  `reference_semantic_parse_result_rejected_unsupported.json`.

### Edge 7: Alias / Anchor Precedence Drift

- Risk:
  the parser could silently invent precedence between exact anchors, aliases, partial
  matches, and conflicting cues.
- Response:
  freeze explicit precedence and require equal-strength conflicts to fail closed
  rather than choose silently.
- Closeout Evidence:
  precedence logic in parser source and
  `reference_semantic_parse_result_exact_anchor_precedence.json`.

### Edge 8: Clarification Shell Leakage

- Risk:
  the first recovery release could emit partial unresolved candidate shells and still
  call the result `clarification_required`.
- Response:
  freeze clarification to zero candidates only plus typed ambiguity diagnostics.
- Closeout Evidence:
  parser outcome logic and
  `reference_semantic_parse_result_clarification_required.json`.

### Edge 9: Projection Leakage Into Identity

- Risk:
  explanatory evidence, notices, or ambiguity notes could quietly become effective
  identity fields.
- Response:
  explicitly reuse the released `V49-A` identity-versus-projection split inside all
  emitted recovery artifacts.
- Closeout Evidence:
  parser emits released `V49-A` normal forms only; candidate distinctness remains
  `normal_form.semantic_hash` only; support-only explanations remain
  `evidence_summary`, notices, and ambiguity notes.

### Edge 10: Multi-Profile Or Multi-Domain Creep

- Risk:
  the first recovery release could overreach into profile selection, domain selection,
  or batched recovery.
- Response:
  freeze one input text, one released parse profile, and one starter domain only.
- Closeout Evidence:
  parser entrypoint and replay tests operate on one text and one released
  `repo_policy_work` profile only.

### Edge 11: Lowering Laundering

- Risk:
  the first recovery slice could quietly start performing deterministic lowering or
  `V48` seed emission.
- Response:
  defer all lowering to `V49-C` and all downstream bridge helpers to `V49-D`.
- Closeout Evidence:
  absence of lowering / bridge implementation files under
  `packages/adeu_semantic_forms`, and no `V48` helper surface shipped in `v118`.

### Edge 12: Consumer Prematurity

- Risk:
  symbol audit, paper semantics, simulation, or product consumers could leak into the
  first recovery release and blur slice ownership.
- Response:
  keep `V49-B` bounded to parser behavior, fixtures, and targeted tests only.
- Closeout Evidence:
  shipped scope limited to `parser.py`, package exports, fixtures, tests, and
  support-only closeout artifacts.

### Edge 13: Under-Constrained Forbid-Effect Recovery

- Risk:
  recovery could silently collapse multiple matched `forbid_effect` cues into one
  winner, under-representing bounded constraint posture.
- Response:
  preserve all recovered `forbid_effect` matches while keeping mutation/artifact
  recovery bounded to the selected best candidate set.
- Closeout Evidence:
  parser effect-recovery logic and
  `packages/adeu_semantic_forms/tests/test_semantic_forms_parser.py::test_all_recovered_forbid_effects_are_preserved`.

## Current Judgment

- `V49-B` was the right next `V49` move because `V49-A` had already frozen the starter
  contracts, identity law, ambiguity posture, and unsupported posture on `main`.
- the shipped result is properly narrow: one repo-owned `adeu_semantic_forms`
  parser, one released `repo_policy_work` profile, one released parse-result contract
  family, semantic-hash candidate distinctness, deterministic alternative ordering,
  zero-candidate clarification posture, explicit anchor precedence, preserved
  multi-effect forbid recovery, deterministic fixtures, and no lowering, bridge, or
  product-surface widening.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md` should now be read with `V49-B` closed on
  `main` and the branch-local default next path advanced to `V49-C`.
