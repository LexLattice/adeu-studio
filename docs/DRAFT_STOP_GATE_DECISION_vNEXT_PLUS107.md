# Draft Stop-Gate Decision (Post vNext+107)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS107.md`

Status: draft decision note (post-hoc closeout capture, April 2, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS107.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v107_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+107` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS107.md`.
- This note captures bounded `V47-B` hardening evidence only; it does not authorize
  current-markdown override, repo-wide migration, imported selector/predicate
  ownership transition, mutation, scheduling, approval posture, waiver issuance,
  deferral issuance, or recursive execution by itself.
- Canonical `V47-B` release in v107 is carried by the shipped
  `adeu_semantic_source` / `adeu_commitments_ir` source, model, schema-export, and
  deterministic fixture surfaces plus the canonical
  `v47b_authoritative_normative_markdown_hardening_evidence@1` evidence input under
  `artifacts/agent_harness/v107/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#329` (`V47-B: harden ANM schema/example parity`)
- arc-completion merge commit: `ead1e1b7c5039fbfa6fd7265a51b37c505d0067b`
- merged-at timestamp: `2026-04-01T21:08:45Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v107_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v107_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v107_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v107/evidence_inputs/metric_key_continuity_assertion_v107.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v107/evidence_inputs/runtime_observability_comparison_v107.json`
  - `V47-B` release evidence input:
    `artifacts/agent_harness/v107/evidence_inputs/v47b_authoritative_normative_markdown_hardening_evidence_v107.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v107/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS107_EDGES.md`

## Exit-Criteria Check (vNext+107)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V47-B` merged with green CI | required | `pass` | PR `#329`, merge commit `ead1e1b7c5039fbfa6fd7265a51b37c505d0067b`, checks `python/web/lean-formal = pass` |
| Released `V47-A` typed artifacts retain authoritative/mirror schema parity after hardening | required | `pass` | `packages/adeu_commitments_ir/schema/*.v1.json`, `spec/*.schema.json`, and parity coverage in `packages/adeu_commitments_ir/tests/test_export_schema.py` |
| Widened checker fact-kind and provenance vocabularies are explicit, bounded, and exact in code, schemas, and tests | required | `pass` | `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`, schema exports for `checker_fact_bundle@1`, `packages/adeu_commitments_ir/tests/test_anm_models.py::test_v47b_fact_type_and_provenance_mode_vocabularies_are_exact`, and accepted `v47b` fixtures |
| Accepted standalone and companion ANM examples replay deterministically into committed `D-IR` / contract / fact / result / ledger artifacts | required | `pass` | `packages/adeu_semantic_source/tests/test_anm.py::test_v47b_examples_replay_deterministically` and committed fixtures under `packages/adeu_commitments_ir/tests/fixtures/v47b/` |
| Clause-scope blocker rows remain distinct from subject-scoped result rows and do not fabricate ledger rows | required | `pass` | `packages/adeu_semantic_source/tests/test_anm.py::test_v47b_clause_scope_blocker_example_stays_distinct_from_subject_rows`, `clause_scope_blocker_reference_policy_evaluation_result_set.json`, and `clause_scope_blocker_reference_policy_obligation_ledger.json` |
| First-run zero-match emits notices with no first ledger row | required | `pass` | `packages/adeu_semantic_source/tests/test_anm.py::test_v47b_zero_match_emits_notices_without_first_ledger_rows` plus `standalone_zero_match_policy_evaluation_result_set.json` and `standalone_zero_match_policy_obligation_ledger.json` |
| Previously instantiated rows fail closed when the current run leaves them stale through zero-match, clause-scope blocker, or subject disappearance | required | `pass` | reconciliation logic in `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`, `standalone_zero_match_reconciled_policy_obligation_ledger.json`, and tests `test_v47b_zero_match_after_prior_instantiation_reconciles_existing_rows`, `test_v47b_clause_scope_blocker_reconciles_prior_rows_fail_closed`, and `test_v47b_missing_subject_reconciles_prior_row_fail_closed` |
| Companion selector coverage remains bounded and does not reopen coexistence or migration doctrine | required | `pass` | companion selector handling in `anm.py`, companion fixtures `companion_policy.md` and `companion_reference_*.json`, and lock boundary in `docs/LOCKED_CONTINUATION_vNEXT_PLUS107.md` |
| Example carriers remain typed unions and reject malformed widening drift | required | `pass` | `CheckerFactRow` / `PolicyEvaluationResultRow` unions in `anm_models.py`, reject fixtures `reject_value_type_fact_non_string_values.json` and `reject_clause_scope_row_with_subject_ref.json`, and rejection coverage in `packages/adeu_commitments_ir/tests/test_anm_models.py` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v107_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v107/evidence_inputs/metric_key_continuity_assertion_v107.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v107/evidence_inputs/runtime_observability_comparison_v107.json` |

## Stop-Gate Summary

```json
{
  "schema": "v107_closeout_stop_gate_summary@1",
  "arc": "vNext+107",
  "target_path": "V47-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v106": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 111,
  "runtime_observability_delta_ms": 3
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v106_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v107_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+106","current_arc":"vNext+107","baseline_source":"artifacts/stop_gate/report_v106_closeout.md","current_source":"artifacts/stop_gate/report_v107_closeout.md","baseline_elapsed_ms":108,"current_elapsed_ms":111,"delta_ms":3,"notes":"v107 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V47-B hardening lane: widened value_type_observation and indirect provenance vocabulary, companion selector coverage, committed standalone and companion example families, clause-scope blocker examples, zero-match first-run posture, later stale-row fail-closed reconciliation, and retained authoritative/mirrored schema export parity."}
```

## V47B Authoritative Normative Markdown Hardening Evidence

```json
{"schema":"v47b_authoritative_normative_markdown_hardening_evidence@1","evidence_input_path":"artifacts/agent_harness/v107/evidence_inputs/v47b_authoritative_normative_markdown_hardening_evidence_v107.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS107.md#v107-continuation-contract-machine-checkable","merged_pr":"#329","merge_commit":"ead1e1b7c5039fbfa6fd7265a51b37c505d0067b","d1_normalized_ir_authoritative_schema_path":"packages/adeu_commitments_ir/schema/d1_normalized_ir.v1.json","d1_normalized_ir_mirror_schema_path":"spec/d1_normalized_ir.schema.json","predicate_contracts_bootstrap_authoritative_schema_path":"packages/adeu_commitments_ir/schema/predicate_contracts_bootstrap.v1.json","predicate_contracts_bootstrap_mirror_schema_path":"spec/predicate_contracts_bootstrap.schema.json","checker_fact_bundle_authoritative_schema_path":"packages/adeu_commitments_ir/schema/checker_fact_bundle.v1.json","checker_fact_bundle_mirror_schema_path":"spec/checker_fact_bundle.schema.json","policy_evaluation_result_set_authoritative_schema_path":"packages/adeu_commitments_ir/schema/policy_evaluation_result_set.v1.json","policy_evaluation_result_set_mirror_schema_path":"spec/policy_evaluation_result_set.schema.json","policy_obligation_ledger_authoritative_schema_path":"packages/adeu_commitments_ir/schema/policy_obligation_ledger.v1.json","policy_obligation_ledger_mirror_schema_path":"spec/policy_obligation_ledger.schema.json","accepted_standalone_source_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47b/standalone_policy.adeu.md","accepted_companion_source_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47b/companion_policy.md","accepted_clause_scope_blocker_source_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47b/clause_scope_blocker_policy.adeu.md","accepted_standalone_d1_normalized_ir_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47b/standalone_reference_d1_normalized_ir.json","accepted_companion_d1_normalized_ir_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47b/companion_reference_d1_normalized_ir.json","accepted_standalone_predicate_contracts_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47b/standalone_reference_predicate_contracts_bootstrap.json","accepted_standalone_fact_bundle_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47b/standalone_fact_bundle.json","accepted_companion_fact_bundle_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47b/companion_fact_bundle.json","accepted_standalone_result_set_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47b/standalone_reference_policy_evaluation_result_set.json","accepted_companion_result_set_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47b/companion_reference_policy_evaluation_result_set.json","accepted_clause_scope_blocker_result_set_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47b/clause_scope_blocker_reference_policy_evaluation_result_set.json","accepted_zero_match_result_set_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47b/standalone_zero_match_policy_evaluation_result_set.json","accepted_standalone_ledger_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47b/standalone_reference_policy_obligation_ledger.json","accepted_zero_match_ledger_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47b/standalone_zero_match_policy_obligation_ledger.json","accepted_zero_match_reconciled_ledger_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47b/standalone_zero_match_reconciled_policy_obligation_ledger.json"}
```

## Recommendation (Post v107)

- gate decision:
  - `V47B_AUTHORITATIVE_NORMATIVE_MARKDOWN_HARDENING_COMPLETE_ON_MAIN`
- rationale:
  - v107 closes the bounded `V47-B` hardening seam on `main` by taking the released
    `V47-A` substrate and making its committed example/schema surface explicit,
    deterministic, and auditable without reopening architecture.
  - the shipped slice widens vocabulary only in bounded, typed ways:
    `value_type_observation` for checker facts and `indirect` for provenance mode.
  - companion-posture examples now compile and evaluate through the same released chain
    without collapsing into clause-scope blockers or broader coexistence doctrine.
  - clause-scope blocker posture, first-run zero-match posture, and stale-row
    reconciliation after later sparse or missing subjects are all now explicit,
    committed, and fail closed in the accepted example family.
  - authoritative schemas, mirrored exports, committed examples, and targeted tests
    remain in parity for the hardened vocabulary and row-shape grammar.
  - the slice remains non-executive and non-migratory: it does not authorize
    current-markdown override, imported O/E ownership transition, waiver/deferral
    issuance, mutation, scheduling, or approval by facts, results, or ledger rows.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`+3 ms` vs v106 baseline).
  - later `V47` work, if selected, should now focus on broader coexistence and
    companion-doc adoption doctrine on top of the closed `V47-A` + `V47-B` stack.
