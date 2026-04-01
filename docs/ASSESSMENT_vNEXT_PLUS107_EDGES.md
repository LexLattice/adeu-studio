# Assessment vNext+107 Edges

Status: post-closeout edge assessment for `V47-B` (April 2, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS107_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Vocabulary Creep Without Example Discipline

- Risk:
  fact-kind or provenance-mode enums could widen informally, turning the hardening lane
  into open-ended drift.
- Response:
  permit only bounded enum additions that are backed by schema, accepted examples, and
  deterministic replay.
- Closeout Evidence:
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  `packages/adeu_commitments_ir/tests/test_anm_models.py::test_v47b_fact_type_and_provenance_mode_vocabularies_are_exact`,
  and committed `v47b` example payloads under
  `packages/adeu_commitments_ir/tests/fixtures/v47b/`.

### Edge 2: Example Collapse Across Artifact Boundaries

- Risk:
  concrete examples could be written as mixed evaluator payloads instead of preserving
  source, IR, facts, results, and ledger as distinct surfaces.
- Response:
  keep example families artifact-separated and require compiled companions for each
  released surface.
- Closeout Evidence:
  accepted standalone and companion example families under
  `packages/adeu_semantic_source/tests/fixtures/v47b/` and
  `packages/adeu_commitments_ir/tests/fixtures/v47b/`,
  plus deterministic replay coverage in
  `packages/adeu_semantic_source/tests/test_anm.py::test_v47b_examples_replay_deterministically`.

### Edge 3: Companion-Posture Overreach

- Risk:
  companion examples could be overread as broader coexistence or migration doctrine.
- Response:
  keep `V47-B` to minimal example-backed coexistence only and defer broader doctrine to
  `V47-C`.
- Closeout Evidence:
  bounded companion selector handling in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  companion fixtures
  `packages/adeu_semantic_source/tests/fixtures/v47b/companion_policy.md` and
  `packages/adeu_commitments_ir/tests/fixtures/v47b/companion_reference_*.json`,
  and the frozen scope in `docs/LOCKED_CONTINUATION_vNEXT_PLUS107.md`.

### Edge 4: Clause-Scope Blocker Example Thinness

- Risk:
  the family could ship hardened schemas/examples without making clause-scope blocker
  posture legible in accepted examples.
- Response:
  require at least one accepted example that shows clause-scope blocker results without
  fabricated ledger rows.
- Closeout Evidence:
  `packages/adeu_semantic_source/tests/fixtures/v47b/clause_scope_blocker_policy.adeu.md`,
  `packages/adeu_commitments_ir/tests/fixtures/v47b/clause_scope_blocker_reference_policy_evaluation_result_set.json`,
  `packages/adeu_commitments_ir/tests/fixtures/v47b/clause_scope_blocker_reference_policy_obligation_ledger.json`,
  and `packages/adeu_semantic_source/tests/test_anm.py::test_v47b_clause_scope_blocker_example_stays_distinct_from_subject_rows`.

### Edge 5: Zero-Match Example Thinness

- Risk:
  selector zero-match could remain implementation knowledge rather than committed
  example-backed doctrine.
- Response:
  require at least one accepted example that shows zero-match notice posture with no
  first ledger row.
- Closeout Evidence:
  `packages/adeu_commitments_ir/tests/fixtures/v47b/standalone_zero_match_policy_evaluation_result_set.json`,
  `packages/adeu_commitments_ir/tests/fixtures/v47b/standalone_zero_match_policy_obligation_ledger.json`,
  and `packages/adeu_semantic_source/tests/test_anm.py::test_v47b_zero_match_emits_notices_without_first_ledger_rows`.

### Edge 6: Stale-Row Reconciliation Drift

- Risk:
  a previously instantiated obligation row might disappear silently when a later run
  hits zero-match, clause-scope blocker posture, or partial subject disappearance.
- Response:
  transition stale rows fail closed to `blocked_unknown_resolution` whenever the clause
  is still present in the current run but the prior obligation row was not refreshed.
- Closeout Evidence:
  reconciliation logic in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  accepted reconciled ledger fixture
  `packages/adeu_commitments_ir/tests/fixtures/v47b/standalone_zero_match_reconciled_policy_obligation_ledger.json`,
  and tests
  `test_v47b_zero_match_after_prior_instantiation_reconciles_existing_rows`,
  `test_v47b_clause_scope_blocker_reconciles_prior_rows_fail_closed`, and
  `test_v47b_missing_subject_reconciles_prior_row_fail_closed`.

### Edge 7: Union-Shape Drift

- Risk:
  fact or result example hardening could flatten typed unions back into universal row
  shapes for convenience.
- Response:
  keep union carriers explicit and reject malformed catch-all example rows.
- Closeout Evidence:
  tagged unions in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  reject fixtures
  `packages/adeu_commitments_ir/tests/fixtures/v47b/reject_value_type_fact_non_string_values.json`
  and
  `packages/adeu_commitments_ir/tests/fixtures/v47b/reject_clause_scope_row_with_subject_ref.json`,
  plus rejection coverage in `packages/adeu_commitments_ir/tests/test_anm_models.py`.

### Edge 8: Schema/Export Parity Drift

- Risk:
  prose docs, authoritative schemas, mirrored exports, and accepted examples could drift
  apart while all still look individually plausible.
- Response:
  require explicit parity across docs, authoritative schema, mirrored schema, and
  committed example payloads for the hardened vocabulary and row-shape grammar.
- Closeout Evidence:
  exported schema parity in
  `packages/adeu_commitments_ir/tests/test_export_schema.py`,
  authoritative schema `packages/adeu_commitments_ir/schema/checker_fact_bundle.v1.json`,
  mirror schema `spec/checker_fact_bundle.schema.json`,
  and committed `v47b` fixtures under
  `packages/adeu_commitments_ir/tests/fixtures/v47b/`.

### Edge 9: Hardening-Lane Authority Laundering

- Risk:
  because `V47-B` is example-oriented, it could accidentally smuggle stronger normative
  authority into facts, results, or ledger examples.
- Response:
  keep all examples bounded to the same non-executive, non-self-authorizing posture as
  released `V47-A`.
- Closeout Evidence:
  bounded lock surface in `docs/LOCKED_CONTINUATION_vNEXT_PLUS107.md`,
  fact-only checker bundles and typed result/ledger models in
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  and accepted/reject example coverage in the `v47b` fixture ladder.

### Edge 10: Package-Boundary Drift

- Risk:
  example and schema hardening could sprawl into unrelated packages or adoption docs too
  early.
- Response:
  keep `V47-B` bounded to `adeu_semantic_source` plus `adeu_commitments_ir`.
- Closeout Evidence:
  shipped implementation footprint in
  `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`,
  `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`,
  and bounded package selection in `docs/LOCKED_CONTINUATION_vNEXT_PLUS107.md`.

## Current Judgment

- `V47-B` was the right next move because `V47-A` had already closed the substrate
  seam on `main`, and the next real gap was schema/example/vocabulary hardening rather
  than new ANM architecture.
- `V47-B` on `main` now resolves that hardening gap by shipping explicit standalone,
  companion, clause-scope blocker, zero-match, and stale-row reconciliation examples
  over the released ANM / `D@1` pipeline.
- the shipped seam remains hardening-only and non-authorizing, so later `V47-C+`
  coexistence, ownership-transition, or downstream-consumer lanes can build on it
  without being silently authorized by facts, results, or ledger state.
