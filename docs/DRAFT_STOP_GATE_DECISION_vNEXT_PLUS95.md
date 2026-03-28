# Draft Stop-Gate Decision (Post vNext+95)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS95.md`

Status: draft decision note (post-hoc closeout capture, March 29, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS95.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v95_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+95` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS95.md`.
- This note captures `V42-G1` closeout evidence only; it does not authorize
  reasoning-agent run bridge widening (`V42-G2`), local three-puzzle harness
  orchestration (`V42-G3`), behavior-evidence synthesis widening (`V42-G4`), benchmark
  tournament execution, API/web operator routes, or generalized multi-agent/
  multi-benchmark orchestration.
- Canonical `V42-G1` release in v95 is carried by the `packages/adeu_arc_agi` and
  `packages/adeu_arc_solver` puzzle-ingest/freeze surfaces, deterministic fixture replay
  under `apps/api/fixtures/arc_agi/vnext_plus95/`, and the canonical
  `v42g1_arc_puzzle_input_bundle_evidence@1` evidence input under
  `artifacts/agent_harness/v95/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `76c5c4bd3173188ddd34c55cd68cf17efa6fc149`
- merged implementation PRs:
  - `#317` (`V42-G1: local puzzle ingest and deterministic freeze bundle`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v95_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v95_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v95_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v95/evidence_inputs/metric_key_continuity_assertion_v95.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v95/evidence_inputs/runtime_observability_comparison_v95.json`
  - `V42-G1` puzzle ingest/freeze evidence input:
    `artifacts/agent_harness/v95/evidence_inputs/v42g1_arc_puzzle_input_bundle_evidence_v95.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v95/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS95_EDGES.md`

## Exit-Criteria Check (vNext+95)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V42-G1` merged with green CI | required | `pass` | PR `#317`, merge commit `76c5c4bd3173188ddd34c55cd68cf17efa6fc149` |
| Canonical `adeu_arc_puzzle_input_bundle@1` shipped with authoritative/mirror schema parity | required | `pass` | `packages/adeu_arc_agi/schema/adeu_arc_puzzle_input_bundle.v1.json`, `spec/adeu_arc_puzzle_input_bundle.schema.json` |
| Deterministic ingest/freeze replay over accepted bundle fixture is stable | required | `pass` | replay checks in `packages/adeu_arc_agi/tests/test_arc_puzzle_input_bundle_v42g1.py` and accepted fixture `apps/api/fixtures/arc_agi/vnext_plus95/adeu_arc_puzzle_input_bundle_v95_reference.json` |
| Puzzle source authority is bounded to released enum with deterministic precedence policy | required | `pass` | `source_kind` enum and precedence checks in `packages/adeu_arc_agi/src/adeu_arc_agi/puzzle_input_bundle.py` |
| Selection register binding is typed and fixed to exactly three selected puzzle IDs | required | `pass` | register identity/hash checks and fixed cohort fixture `apps/api/fixtures/arc_agi/vnext_plus95/adeu_arc_puzzle_selection_register_v95_reference.json` |
| Missing provenance refs are rejected fail-closed | required | `pass` | rejected fixture `.../adeu_arc_puzzle_input_bundle_v95_reject_missing_provenance_refs.json` |
| Per-puzzle and bundle identity-hash mismatches are rejected fail-closed | required | `pass` | rejected fixtures `..._reject_per_puzzle_identity_hash_mismatch.json` and `..._reject_bundle_identity_hash_mismatch.json` |
| Retrospective selection swap and canonical-order drift are rejected fail-closed | required | `pass` | rejected fixture `..._reject_retroactive_selection_swap.json` |
| Duplicate puzzle identity within one bundle is rejected fail-closed | required | `pass` | rejected fixture `..._reject_duplicate_puzzle_identity.json` |
| Deterministic replay is bounded to frozen local payload evidence, not live external fetch behavior | required | `pass` | frozen payload fixtures `adeu_arc_puzzle_payload_v95_arcagi3_local_p00{1,2,3}.json` and validators in `puzzle_input_bundle.py` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v95_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v95/evidence_inputs/metric_key_continuity_assertion_v95.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v95/evidence_inputs/runtime_observability_comparison_v95.json` |

## Stop-Gate Summary

```json
{
  "schema": "v95_closeout_stop_gate_summary@1",
  "arc": "vNext+95",
  "target_path": "V42-G1",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v94": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 101,
  "runtime_observability_delta_ms": 9
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v94_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v95_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+94","baseline_elapsed_ms":92,"baseline_source":"artifacts/stop_gate/report_v94_closeout.md","current_arc":"vNext+95","current_elapsed_ms":101,"current_source":"artifacts/stop_gate/report_v95_closeout.md","delta_ms":9,"notes":"v95 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while adding the bounded V42-G1 local puzzle ingest/freeze baseline on main.","schema":"runtime_observability_comparison@1"}
```

## V42G1 Puzzle Ingest/Freeze Evidence

```json
{"schema":"v42g1_arc_puzzle_input_bundle_evidence@1","evidence_input_path":"artifacts/agent_harness/v95/evidence_inputs/v42g1_arc_puzzle_input_bundle_evidence_v95.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS95.md#v95-continuation-contract-machine-checkable","merged_pr":"#317","merge_commit":"76c5c4bd3173188ddd34c55cd68cf17efa6fc149","puzzle_bundle_authoritative_schema_path":"packages/adeu_arc_agi/schema/adeu_arc_puzzle_input_bundle.v1.json","puzzle_bundle_mirror_schema_path":"spec/adeu_arc_puzzle_input_bundle.schema.json","accepted_reference_fixture_path":"apps/api/fixtures/arc_agi/vnext_plus95/adeu_arc_puzzle_input_bundle_v95_reference.json"}
```

## Recommendation (Post v95)

- gate decision:
  - `V42G1_PUZZLE_INGEST_FREEZE_BASELINE_COMPLETE_ON_MAIN`
- rationale:
  - v95 closes the bounded `V42-G1` baseline with typed puzzle-source authority,
    deterministic three-puzzle selection-register binding, canonical order and hash
    integrity, and fail-closed rejection of provenance/swap/identity drift on `main`.
  - reasoning-agent bridge (`V42-G2`), three-puzzle harness orchestration (`V42-G3`),
    and behavior-evidence synthesis (`V42-G4`) remain deferred.
  - no stop-gate schema-family or metric-key regressions were introduced; runtime
    observability changed only informationally.
  - the next default seam now belongs to `V42-G2` widening selection rather than
    another `V42-G1` continuation.
