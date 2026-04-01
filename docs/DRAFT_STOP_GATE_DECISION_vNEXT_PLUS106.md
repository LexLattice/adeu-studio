# Draft Stop-Gate Decision (Post vNext+106)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md`

Status: draft decision note (post-hoc closeout capture, April 1, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS106.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v106_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+106` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md`.
- This note captures bounded `V47-A` release evidence only; it does not authorize
  mutation, scheduling, approval posture, waiver issuance, deferral issuance, or
  recursive execution by itself.
- Canonical `V47-A` release in v106 is carried by the shipped
  `adeu_semantic_source` / `adeu_commitments_ir` source, model, schema-export, and
  deterministic fixture surfaces plus the canonical
  `v47a_authoritative_normative_markdown_substrate_evidence@1` evidence input under
  `artifacts/agent_harness/v106/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#328` (`V47-A: implement v106 ANM D1 substrate`)
- arc-completion merge commit: `c89991552fbd72ac36906fdc879c677a031d9369`
- merged-at timestamp: `2026-04-01T19:01:31Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v106_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v106_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v106_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v106/evidence_inputs/metric_key_continuity_assertion_v106.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v106/evidence_inputs/runtime_observability_comparison_v106.json`
  - `V47-A` release evidence input:
    `artifacts/agent_harness/v106/evidence_inputs/v47a_authoritative_normative_markdown_substrate_evidence_v106.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v106/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS106_EDGES.md`

## Exit-Criteria Check (vNext+106)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V47-A` merged with green CI | required | `pass` | PR `#328`, merge commit `c89991552fbd72ac36906fdc879c677a031d9369`, checks `python/web/lean-formal = pass` |
| Canonical `d1_normalized_ir@1`, `predicate_contracts_bootstrap@1`, `checker_fact_bundle@1`, `policy_evaluation_result_set@1`, and `policy_obligation_ledger@1` shipped with authoritative/mirror schema parity | required | `pass` | `packages/adeu_commitments_ir/schema/*.v1.json`, `spec/*.schema.json`, and parity coverage in `packages/adeu_commitments_ir/tests/test_export_schema.py` |
| Deterministic replay over the accepted `V47-A` reference chain is stable | required | `pass` | `packages/adeu_semantic_source/tests/test_anm.py::test_v47a_reference_chain_replays_deterministically` plus committed fixtures under `packages/adeu_commitments_ir/tests/fixtures/v47a/` |
| Authoritative policy semantics compile only from explicit `D@1` blocks and no prose inference path exists outside them | required | `pass` | parser/compiler enforcement in `packages/adeu_semantic_source/src/adeu_semantic_source/anm.py`, reject fixture `packages/adeu_semantic_source/tests/fixtures/v47a/reject_prose_only_obligation.md`, and rejection coverage in `packages/adeu_semantic_source/tests/test_anm.py` |
| `D-IR` preserves first-class selector refs and clause-to-selector linkage | required | `pass` | shipped `d1_normalized_ir@1` schema/model surfaces in `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`, `packages/adeu_commitments_ir/schema/d1_normalized_ir.v1.json`, and accepted fixture `packages/adeu_commitments_ir/tests/fixtures/v47a/reference_d1_normalized_ir.json` |
| Result rows support both subject-scoped evaluations and clause-scope blocker rows without fabricating ledger rows | required | `pass` | `PolicyEvaluationResultSet` / `PolicyObligationLedger` validation in `anm_models.py`, accepted result fixture `reference_policy_evaluation_result_set.json`, reject fixture `reject_clause_scope_blocker_fabricated_ledger_row.json`, and coverage in `packages/adeu_commitments_ir/tests/test_anm_models.py` |
| Selector zero-match remains distinct from `gated_off` and does not create a first ledger row | required | `pass` | `packages/adeu_semantic_source/tests/test_anm.py::test_v47a_zero_match_emits_notice_without_ledger_rows`, `packages/adeu_commitments_ir/tests/fixtures/v47a/zero_match_fact_bundle.json`, and shipped ledger projection logic in `anm.py` |
| Bootstrap predicate contracts remain semantic and scope-independent, and missing qualifier contracts fail closed | required | `pass` | `packages/adeu_commitments_ir/tests/fixtures/v47a/reference_predicate_contracts_bootstrap.json`, predicate contract models in `anm_models.py`, and `packages/adeu_semantic_source/tests/test_anm.py::test_v47a_missing_qualifier_contract_fails_closed` |
| Checker bundles remain fact-only tagged unions with starter vocabulary exact match | required | `pass` | `CheckerFactBundle` model in `anm_models.py`, accepted fixture `reference_fact_bundle.json`, reject fixture `reject_fact_bundle_with_verdict.json`, and vocabulary/shape checks in `packages/adeu_commitments_ir/tests/test_anm_models.py` |
| Shared canonical hashing is reused rather than local canonical-json helpers drifting by package | required | `pass` | `stable_payload_hash` in `packages/adeu_commitments_ir/src/adeu_commitments_ir/anm_models.py`, `urm_runtime.hashing` reuse, and canonical-json conformance coverage exercised during PR `#328` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v106_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v106/evidence_inputs/metric_key_continuity_assertion_v106.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v106/evidence_inputs/runtime_observability_comparison_v106.json` |

## Stop-Gate Summary

```json
{
  "schema": "v106_closeout_stop_gate_summary@1",
  "arc": "vNext+106",
  "target_path": "V47-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v105": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 108,
  "runtime_observability_delta_ms": 12
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v105_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v106_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+105","current_arc":"vNext+106","baseline_source":"artifacts/stop_gate/report_v105_closeout.md","current_source":"artifacts/stop_gate/report_v106_closeout.md","baseline_elapsed_ms":96,"current_elapsed_ms":108,"delta_ms":12,"notes":"v106 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V47-A ANM/D@1 substrate: markdown-native authoritative blocks, normalized D-IR with explicit selector refs, semantic bootstrap predicate contracts, fact-only checker bundles, run-specific result sets, cross-run ledger projection, fail-closed clause-scope blocker posture, and shared canonical hash reuse instead of package-local canonical-json drift."}
```

## V47A Authoritative Normative Markdown Substrate Evidence

```json
{"schema":"v47a_authoritative_normative_markdown_substrate_evidence@1","evidence_input_path":"artifacts/agent_harness/v106/evidence_inputs/v47a_authoritative_normative_markdown_substrate_evidence_v106.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS106.md#v106-continuation-contract-machine-checkable","merged_pr":"#328","merge_commit":"c89991552fbd72ac36906fdc879c677a031d9369","d1_normalized_ir_authoritative_schema_path":"packages/adeu_commitments_ir/schema/d1_normalized_ir.v1.json","d1_normalized_ir_mirror_schema_path":"spec/d1_normalized_ir.schema.json","predicate_contracts_bootstrap_authoritative_schema_path":"packages/adeu_commitments_ir/schema/predicate_contracts_bootstrap.v1.json","predicate_contracts_bootstrap_mirror_schema_path":"spec/predicate_contracts_bootstrap.schema.json","checker_fact_bundle_authoritative_schema_path":"packages/adeu_commitments_ir/schema/checker_fact_bundle.v1.json","checker_fact_bundle_mirror_schema_path":"spec/checker_fact_bundle.schema.json","policy_evaluation_result_set_authoritative_schema_path":"packages/adeu_commitments_ir/schema/policy_evaluation_result_set.v1.json","policy_evaluation_result_set_mirror_schema_path":"spec/policy_evaluation_result_set.schema.json","policy_obligation_ledger_authoritative_schema_path":"packages/adeu_commitments_ir/schema/policy_obligation_ledger.v1.json","policy_obligation_ledger_mirror_schema_path":"spec/policy_obligation_ledger.schema.json","accepted_source_fixture_path":"packages/adeu_semantic_source/tests/fixtures/v47a/reference_policy.adeu.md","accepted_d1_normalized_ir_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47a/reference_d1_normalized_ir.json","accepted_predicate_contracts_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47a/reference_predicate_contracts_bootstrap.json","accepted_fact_bundle_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47a/reference_fact_bundle.json","accepted_policy_evaluation_result_set_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47a/reference_policy_evaluation_result_set.json","accepted_policy_obligation_ledger_fixture_path":"packages/adeu_commitments_ir/tests/fixtures/v47a/reference_policy_obligation_ledger.json"}
```

## Recommendation (Post v106)

- gate decision:
  - `V47A_AUTHORITATIVE_NORMATIVE_MARKDOWN_SUBSTRATE_COMPLETE_ON_MAIN`
- rationale:
  - v106 closes the bounded `V47-A` starter seam on `main` by shipping the first
    authoritative markdown-to-ledger substrate:
    `D@1` source blocks, normalized `D-IR`, semantic bootstrap predicate contracts,
    fact-only checker bundles, run-specific evaluation result sets, and cross-run
    ledger projection.
  - the shipped slice remains non-executive and non-migratory: it does not infer
    obligations from prose outside `D@1`, does not mint waiver/deferral/mutation
    authority, and does not force repo-wide markdown supersession.
  - review hardening closed concrete brittleness risks by making qualifier contracts
    fail closed when absent, enforcing type-sensitive equality, rejecting
    scope-mismatched prior ledgers, and reusing shared canonical hashing instead of
    package-local canonical-json helpers.
  - selector zero-match, `gated_off`, and clause-scope `unknown_resolution` remain
    distinct typed postures rather than being collapsed into fabricated ledger rows.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`+12 ms` vs v105 baseline).
  - later `V47` work, if selected, should widen schema/example hardening and
    coexistence doctrine on top of the now-released `V47-A` substrate rather than
    reopening its bounded first-slice contract.
