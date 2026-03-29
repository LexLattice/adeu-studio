# Draft Stop-Gate Decision (Post vNext+97)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS97.md`

Status: draft decision note (post-hoc closeout capture, March 29, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS97.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v97_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+97` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS97.md`.
- This note captures `V42-G3` closeout evidence only; it does not authorize
  behavior-evidence synthesis widening (`V42-G4`), benchmark tournament execution,
  API/web operator routes, or generalized multi-agent/multi-benchmark orchestration.
- Canonical `V42-G3` release in v97 is carried by the
  `packages/adeu_arc_agi`/`packages/adeu_arc_solver` three-puzzle harness surfaces,
  deterministic fixture replay under `apps/api/fixtures/arc_agi/vnext_plus97/`, and
  the canonical `v42g3_arc_three_puzzle_harness_evidence@1` evidence input under
  `artifacts/agent_harness/v97/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `3f946090da68a0e270d8df182d46f4a5edb26282`
- merged implementation PRs:
  - `#319` (`V42-G3: implement v97 three-puzzle local harness record`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v97_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v97_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v97_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v97/evidence_inputs/metric_key_continuity_assertion_v97.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v97/evidence_inputs/runtime_observability_comparison_v97.json`
  - `V42-G3` harness evidence input:
    `artifacts/agent_harness/v97/evidence_inputs/v42g3_arc_three_puzzle_harness_evidence_v97.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v97/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS97_EDGES.md`

## Exit-Criteria Check (vNext+97)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V42-G3` merged with green CI | required | `pass` | PR `#319`, merge commit `3f946090da68a0e270d8df182d46f4a5edb26282` |
| Canonical `adeu_arc_three_puzzle_harness_record@1` shipped with authoritative/mirror schema parity | required | `pass` | `packages/adeu_arc_agi/schema/adeu_arc_three_puzzle_harness_record.v1.json`, `spec/adeu_arc_three_puzzle_harness_record.schema.json` |
| Deterministic harness replay over accepted fixture is stable | required | `pass` | replay checks in `packages/adeu_arc_agi/tests/test_arc_three_puzzle_harness_v42g3.py` and accepted fixture `apps/api/fixtures/arc_agi/vnext_plus97/adeu_arc_three_puzzle_harness_record_v97_reference.json` |
| Harness materializes exactly three canonical puzzle-entry slots | required | `pass` | exact-length + canonical-index constraints in `packages/adeu_arc_agi/src/adeu_arc_agi/three_puzzle_harness.py` |
| Retrospective swap, canonical-order drift, duplicate identity, and omitted-entry laundering are rejected fail-closed | required | `pass` | rejected fixtures `..._reject_retroactive_selection_swap.json`, `..._reject_canonical_order_violation.json`, `..._reject_duplicate_puzzle_identity.json`, `..._reject_omitted_third_entry_laundering.json` |
| Per-puzzle `V42-G2` stage-evidence parity is enforced fail-closed | required | `pass` | stage-evidence parity enforcement + targeted test in `three_puzzle_harness.py` and `test_arc_three_puzzle_harness_v42g3.py` |
| Cross-puzzle runtime identity-chain and config consistency are enforced fail-closed | required | `pass` | cross-run `environment/session/competition` and config-consistency checks in `three_puzzle_harness.py` with rejection coverage |
| Optional harness aggregate refs are consistency-checked against per-puzzle refs | required | `pass` | aggregate-ref recomputation checks in `three_puzzle_harness.py` and rejected fixture `..._reject_aggregated_ref_contradiction.json` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v97_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v97/evidence_inputs/metric_key_continuity_assertion_v97.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v97/evidence_inputs/runtime_observability_comparison_v97.json` |

## Stop-Gate Summary

```json
{
  "schema": "v97_closeout_stop_gate_summary@1",
  "arc": "vNext+97",
  "target_path": "V42-G3",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v96": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 83,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v96_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v97_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+96","baseline_elapsed_ms":83,"baseline_source":"artifacts/stop_gate/report_v96_closeout.md","current_arc":"vNext+97","current_elapsed_ms":83,"current_source":"artifacts/stop_gate/report_v97_closeout.md","delta_ms":0,"notes":"v97 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while adding the bounded V42-G3 three-puzzle harness baseline on main.","schema":"runtime_observability_comparison@1"}
```

## V42G3 Three-Puzzle Harness Evidence

```json
{"schema":"v42g3_arc_three_puzzle_harness_evidence@1","evidence_input_path":"artifacts/agent_harness/v97/evidence_inputs/v42g3_arc_three_puzzle_harness_evidence_v97.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS97.md#v97-continuation-contract-machine-checkable","merged_pr":"#319","merge_commit":"3f946090da68a0e270d8df182d46f4a5edb26282","three_puzzle_harness_authoritative_schema_path":"packages/adeu_arc_agi/schema/adeu_arc_three_puzzle_harness_record.v1.json","three_puzzle_harness_mirror_schema_path":"spec/adeu_arc_three_puzzle_harness_record.schema.json","accepted_reference_fixture_path":"apps/api/fixtures/arc_agi/vnext_plus97/adeu_arc_three_puzzle_harness_record_v97_reference.json"}
```

## Recommendation (Post v97)

- gate decision:
  - `V42G3_THREE_PUZZLE_HARNESS_BASELINE_COMPLETE_ON_MAIN`
- rationale:
  - v97 closes the bounded `V42-G3` baseline with deterministic three-puzzle local
    harness orchestration over released `V42-G1` and `V42-G2` surfaces, strict
    per-puzzle staged-evidence carry-through, and fail-closed rejection of
    swap/order/identity/config/aggregation drift on `main`.
  - behavior-evidence synthesis (`V42-G4`) remains deferred.
  - no stop-gate schema-family or metric-key regressions were introduced; runtime
    observability changed only informationally.
  - the next default seam now belongs to `V42-G4` widening selection rather than
    another `V42-G3` continuation.
