# Draft Stop-Gate Decision (Post vNext+96)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS96.md`

Status: draft decision note (post-hoc closeout capture, March 29, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS96.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v96_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+96` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS96.md`.
- This note captures `V42-G2` closeout evidence only; it does not authorize
  three-puzzle harness orchestration widening (`V42-G3`), behavior-evidence synthesis
  widening (`V42-G4`), benchmark tournament execution, API/web operator routes, or
  generalized multi-agent/multi-benchmark orchestration.
- Canonical `V42-G2` release in v96 is carried by the
  `packages/adeu_arc_agi`/`packages/adeu_arc_solver` reasoning-run surfaces,
  deterministic fixture replay under `apps/api/fixtures/arc_agi/vnext_plus96/`, and
  the canonical `v42g2_arc_reasoning_run_record_evidence@1` evidence input under
  `artifacts/agent_harness/v96/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `2c7214ec2c2773256ed0b1ec390105f4d7f7c52a`
- merged implementation PRs:
  - `#318` (`V42-G2: reasoning-agent run bridge`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v96_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v96_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v96_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v96/evidence_inputs/metric_key_continuity_assertion_v96.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v96/evidence_inputs/runtime_observability_comparison_v96.json`
  - `V42-G2` reasoning-run evidence input:
    `artifacts/agent_harness/v96/evidence_inputs/v42g2_arc_reasoning_run_record_evidence_v96.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v96/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS96_EDGES.md`

## Exit-Criteria Check (vNext+96)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V42-G2` merged with green CI | required | `pass` | PR `#318`, merge commit `2c7214ec2c2773256ed0b1ec390105f4d7f7c52a` |
| Canonical `adeu_arc_reasoning_run_record@1` shipped with authoritative/mirror schema parity | required | `pass` | `packages/adeu_arc_agi/schema/adeu_arc_reasoning_run_record.v1.json`, `spec/adeu_arc_reasoning_run_record.schema.json` |
| Deterministic single-attempt replay over accepted run-record fixture is stable | required | `pass` | replay checks in `packages/adeu_arc_agi/tests/test_arc_reasoning_run_record_v42g2.py` and accepted fixture `apps/api/fixtures/arc_agi/vnext_plus96/adeu_arc_reasoning_run_record_v96_reference.json` |
| In-band stage occupation carries stage-aware refs plus monotonic `emission_sequence_register` | required | `pass` | staged evidence/lifecycle checks in `packages/adeu_arc_agi/src/adeu_arc_agi/reasoning_run_record.py` |
| Post-hoc reconstruction and all-at-once compatible dump postures are rejected fail-closed | required | `pass` | rejected fixtures `..._reject_post_hoc_reconstruction.json` and `..._reject_all_at_once_dump_without_staged_monotonic_evidence.json` |
| Missing intermediate occupancy, identity-chain mismatch, and rollout-posture contradiction are rejected fail-closed | required | `pass` | rejected fixtures `..._reject_missing_intermediate_occupancy.json`, `..._reject_identity_chain_mismatch.json`, `..._reject_rollout_presence_posture_contradiction.json` |
| Hidden-branching laundering over typed surfaces is rejected fail-closed | required | `pass` | rejected fixture `..._reject_hidden_branching_laundering.json` |
| Blocked/deferred posture remains admissible with required `action_proposal_ref` and without forced rollout | required | `pass` | `run_terminal_posture`/`rollout_presence_posture` rules in `reasoning_run_record.py` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v96_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v96/evidence_inputs/metric_key_continuity_assertion_v96.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v96/evidence_inputs/runtime_observability_comparison_v96.json` |

## Stop-Gate Summary

```json
{
  "schema": "v96_closeout_stop_gate_summary@1",
  "arc": "vNext+96",
  "target_path": "V42-G2",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v95": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 83,
  "runtime_observability_delta_ms": -18
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v95_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v96_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+95","baseline_elapsed_ms":101,"baseline_source":"artifacts/stop_gate/report_v95_closeout.md","current_arc":"vNext+96","current_elapsed_ms":83,"current_source":"artifacts/stop_gate/report_v96_closeout.md","delta_ms":-18,"notes":"v96 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while adding the bounded V42-G2 reasoning-run bridge baseline on main.","schema":"runtime_observability_comparison@1"}
```

## V42G2 Reasoning-Run Bridge Evidence

```json
{"schema":"v42g2_arc_reasoning_run_record_evidence@1","evidence_input_path":"artifacts/agent_harness/v96/evidence_inputs/v42g2_arc_reasoning_run_record_evidence_v96.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS96.md#v96-continuation-contract-machine-checkable","merged_pr":"#318","merge_commit":"2c7214ec2c2773256ed0b1ec390105f4d7f7c52a","reasoning_run_record_authoritative_schema_path":"packages/adeu_arc_agi/schema/adeu_arc_reasoning_run_record.v1.json","reasoning_run_record_mirror_schema_path":"spec/adeu_arc_reasoning_run_record.schema.json","accepted_reference_fixture_path":"apps/api/fixtures/arc_agi/vnext_plus96/adeu_arc_reasoning_run_record_v96_reference.json"}
```

## Recommendation (Post v96)

- gate decision:
  - `V42G2_REASONING_RUN_BRIDGE_BASELINE_COMPLETE_ON_MAIN`
- rationale:
  - v96 closes the bounded `V42-G2` baseline with typed run/puzzle/config identity
    binding, staged in-band ladder evidence, lifecycle/terminal/rollout posture
    coherence, and fail-closed rejection of reconstruction/ordering/branching drift on
    `main`.
  - three-puzzle harness orchestration (`V42-G3`) and behavior-evidence synthesis
    (`V42-G4`) remain deferred.
  - no stop-gate schema-family or metric-key regressions were introduced; runtime
    observability changed only informationally.
  - the next default seam now belongs to `V42-G3` widening selection rather than
    another `V42-G2` continuation.
