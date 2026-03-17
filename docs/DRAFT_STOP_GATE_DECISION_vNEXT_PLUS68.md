# Draft Stop-Gate Decision (Post vNext+68)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS68.md`

Status: draft decision note (post-hoc closeout capture, March 17, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS68.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v68_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+68` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS68.md`.
- This note captures `V37-C` executable reference-loop closeout evidence only; it does
  not authorize any `V37-D` drift-diagnostics or conformance lane, any `V37-E`
  control-update export, or any autonomous repo mutation by itself.
- Canonical `V37-C` release in v68 is carried by canonical
  `meta_loop_checkpoint_result_manifest@1`, one accepted executed
  `meta_loop_run_trace@1`, one accepted executable reference loop bound back to the
  released `V37-A` and `V37-B` tuples, and canonical
  `v37c_reference_loop_evidence@1`; those artifacts remain bound to the intentional
  first executed hard-checkpoint subset, the authoritative
  `apps/api/scripts/build_stop_gate_metrics.py` executor for stop-gate generation,
  actual branch/retry outcome capture, failed-attempt manifest rows, explicit
  executed-run trace semantics distinct from the frozen v67 reference trace, and the
  checkpoint truth boundary, and v68 does not fork the stop-gate schema family or
  metric keyset.
- Runtime-observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `dd856bc9604103ab3ff17abc176ff34b55e658c2`
- arc-completion CI runs:
  - PR `#285`
    - merge commit: `074db1beb6930578cd18cb5701f6b8ea308a00f8`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23210768775`
    - conclusion: `success`
  - PR `#286`
    - merge commit: `dd856bc9604103ab3ff17abc176ff34b55e658c2`
    - URL:
      `https://github.com/LexLattice/adeu-studio/actions/runs/23212629112`
    - conclusion: `success`
- merged implementation PRs:
  - `#285` (`core_ir: implement v68 executable reference loop baseline`)
  - `#286` (`core_ir: add v68 c2 reference loop evidence`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v68_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v68_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v68_closeout.md`
  - runtime observability evidence input:
    `artifacts/agent_harness/v68/evidence_inputs/runtime_observability_comparison_v68.json`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v68/evidence_inputs/metric_key_continuity_assertion_v68.json`
  - executable reference-loop evidence input:
    `artifacts/agent_harness/v68/evidence_inputs/v37c_reference_loop_evidence_v68.json`
- supporting deterministic runtime closeout artifacts (reproducible):
  - committed runtime evidence root: `artifacts/agent_harness/v68/runtime/evidence/codex/`
  - parent session raw/event streams:
    `artifacts/agent_harness/v68/runtime/evidence/codex/copilot/v68-closeout-main-1/`
  - the committed runtime stream is provenance-only for the closeout gate; v68 closes
    the first executable `V37-C` lane, but actual gate-relevant truth remains carried
    by normalized checkpoint results and the accepted `v37c_reference_loop_evidence@1`
    artifact rather than by raw event-stream prose.
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS68_EDGES.md`

## Exit-Criteria Check (vNext+68)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `C1` merged with green CI | required | `pass` | PR `#285`, merge commit `074db1beb6930578cd18cb5701f6b8ea308a00f8`, Actions run `23210768775` |
| `C2` merged with green CI | required | `pass` | PR `#286`, merge commit `dd856bc9604103ab3ff17abc176ff34b55e658c2`, Actions run `23212629112` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v68_closeout.json` keeps `schema = "stop_gate_metrics@1"` and `valid = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v68/evidence_inputs/metric_key_continuity_assertion_v68.json` records exact keyset equality versus v67 |
| Canonical `meta_loop_checkpoint_result_manifest@1`, one accepted executable reference run, and evidence artifact emitted and hash-bound | required | `pass` | `artifacts/agent_harness/v68/evidence_inputs/v37c_reference_loop_evidence_v68.json` records the canonical schema/reference paths and hashes |
| Accepted executable reference run binds exactly to the released `V37-A` and `V37-B` reference pairs | required | `pass` | `v37c_reference_loop_evidence_v68.json` records `v37a_reference_tuple_consumed_without_drift = true` and `v37b_reference_tuple_consumed_without_drift = true` |
| Actual hard checkpoint outputs are captured from real executor bindings under the shared tuple | required | `pass` | `v37c_reference_loop_evidence_v68.json` records `hard_checkpoint_results_captured_from_actual_executors = true` |
| Executed hard-checkpoint subset is explicit and intentional for the first accepted run | required | `pass` | `v37c_reference_loop_evidence_v68.json` records `executed_capability_subset_declared_intentionally = true` |
| The authoritative stop-gate executor surface is frozen and verified | required | `pass` | `v37c_reference_loop_evidence_v68.json` records `authoritative_stop_gate_executor_binding_verified = true` |
| The accepted executed trace is distinct from the frozen `V37-B` reference trace and records realized branch/retry outcomes when exercised | required | `pass` | `v37c_reference_loop_evidence_v68.json` records `executed_run_trace_artifact_distinct_from_v67_reference_trace = true`, `executed_run_trace_mode_verified = true`, and `actual_branch_and_retry_outcomes_verified = true` |
| Attempted failed checkpoint steps still emit normalized manifest rows | required | `pass` | `v37c_reference_loop_evidence_v68.json` records `failed_checkpoint_attempts_still_emit_normalized_result_rows = true` |
| Observed gate truth remains derived from actual checkpoint outputs rather than from reasoning prose | required | `pass` | `v37c_reference_loop_evidence_v68.json` records `reasoning_vs_checkpoint_truth_boundary_preserved = true` |
| No diagnostics, conformance, or control-update export is released | required | `pass` | `v37c_reference_loop_evidence_v68.json` records `v37c_scope_boundary_preserved = true` and the closeout artifact set contains only `V37-C` executable-loop surfaces |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v68/evidence_inputs/runtime_observability_comparison_v68.json` plus the comparison table below |

Summary:

- `schema = "stop_gate_metrics@1"`
- `valid = true`
- `all_passed = true`
- `issues = []`
- `derived_cardinality = 80` (computed from `metrics` keyset cardinality)

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v67_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v68_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison (v67 Baseline vs v68 Closeout)

```json
{"baseline_arc":"vNext+67","baseline_elapsed_ms":133,"baseline_source":"artifacts/stop_gate/report_v67_closeout.md","current_arc":"vNext+68","current_elapsed_ms":110,"current_source":"artifacts/stop_gate/report_v68_closeout.md","delta_ms":-23,"notes":"v68 closeout remains informational-only for runtime timing/byte observability under frozen stop-gate semantics and the first bounded executable reference-loop lane.","schema":"runtime_observability_comparison@1"}
```

| Arc | Source | total_fixtures | total_replays | elapsed_ms | bytes_hashed_per_replay | bytes_hashed_total | valid | all_passed |
|---|---|---:|---:|---:|---:|---:|---|---|
| `vNext+67` baseline | `artifacts/stop_gate/metrics_v67_closeout.json` | `22` | `78` | `133` | `68230` | `204690` | `true` | `true` |
| `vNext+68` closeout | `artifacts/stop_gate/metrics_v68_closeout.json` | `22` | `78` | `110` | `68230` | `204690` | `true` | `true` |

## V37-C Reference Loop Evidence

```json
{
  "actual_branch_and_retry_outcomes_verified": true,
  "authoritative_stop_gate_executor_binding_verified": true,
  "checkpoint_result_manifest_emitted_and_hash_bound": true,
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS68.md#v37c_executable_reference_loop_contract@1",
  "evidence_input_path": "artifacts/agent_harness/v68/evidence_inputs/v37c_reference_loop_evidence_v68.json",
  "executed_capability_subset_declared_intentionally": true,
  "executed_meta_loop_run_trace_reference_hash": "7ada573c2cea3fd2da4109cb24721e02b036f930b5c2b12e67b3e81de7d33fbc",
  "executed_meta_loop_run_trace_reference_path": "apps/api/fixtures/meta_testing/vnext_plus68/meta_loop_run_trace_arc_closeout_v65_executed_reference.json",
  "executed_reference_run_emitted": true,
  "executed_run_trace_artifact_distinct_from_v67_reference_trace": true,
  "executed_run_trace_mode_verified": true,
  "executed_step_order_matches_v37b_contract": true,
  "failed_checkpoint_attempts_still_emit_normalized_result_rows": true,
  "hard_checkpoint_results_captured_from_actual_executors": true,
  "meta_loop_checkpoint_result_manifest_reference_hash": "0cdd387a396f89f1f3c7fedf248500b7d7a6ea8029fbc0a7cbd2812a763dad3a",
  "meta_loop_checkpoint_result_manifest_reference_path": "apps/api/fixtures/meta_testing/vnext_plus68/meta_loop_checkpoint_result_manifest_arc_closeout_v65_reference.json",
  "meta_loop_checkpoint_result_manifest_schema_hash": "a34062016d907fd39d956379548786ec7809e1c3eb22dba7589f179327c4477d",
  "meta_loop_checkpoint_result_manifest_schema_path": "packages/adeu_core_ir/schema/meta_loop_checkpoint_result_manifest.v1.json",
  "meta_loop_run_trace_reference_hash": "b17eac10e9097654fd68da1dbda0f69cc5b1c20cf1793f848f02bb8c9b9ecb77",
  "meta_loop_run_trace_reference_path": "apps/api/fixtures/meta_testing/vnext_plus67/meta_loop_run_trace_arc_closeout_v65_reference.json",
  "meta_loop_run_trace_schema_hash": "81971518dd4596115ce0dde3fbe789040766e4440d415d209079dc4fedf29de1",
  "meta_loop_run_trace_schema_path": "packages/adeu_core_ir/schema/meta_loop_run_trace.v1.json",
  "meta_loop_sequence_contract_reference_hash": "14b1e8bf86d91675c0b952b8086be88bc09fb5e04b9c7c9042912f8638df3c35",
  "meta_loop_sequence_contract_reference_path": "apps/api/fixtures/meta_testing/vnext_plus67/meta_loop_sequence_contract_arc_closeout_v65_reference.json",
  "meta_loop_sequence_contract_schema_hash": "3199f92b8753fa265d11d8d740f4e8a4b8024f818c2ead01b3a20b67e2703939",
  "meta_loop_sequence_contract_schema_path": "packages/adeu_core_ir/schema/meta_loop_sequence_contract.v1.json",
  "meta_module_catalog_reference_hash": "4c2aff7bf2291aff25c17314a0c255f922795631410b562db139d5507eb3cc2b",
  "meta_module_catalog_reference_path": "apps/api/fixtures/meta_testing/vnext_plus66/meta_module_catalog_arc_closeout_v65_reference.json",
  "meta_module_catalog_schema_hash": "cae10e9bd159e7837a97e9504d56626e3a75b2d0635db985bcd8d9bf86478786",
  "meta_module_catalog_schema_path": "packages/adeu_core_ir/schema/meta_module_catalog.v1.json",
  "meta_testing_intent_packet_reference_hash": "3df0427ad51f463866ed77df242a4a7fe34687da9f2e79e975639a9f5df1645b",
  "meta_testing_intent_packet_reference_path": "apps/api/fixtures/meta_testing/vnext_plus66/meta_testing_intent_packet_arc_closeout_v65_reference.json",
  "meta_testing_intent_packet_schema_hash": "c511b7b882b78c0ec2e1365e4bb0490eb9b532d8e874b5829fa89e607a42ec11",
  "meta_testing_intent_packet_schema_path": "packages/adeu_core_ir/schema/meta_testing_intent_packet.v1.json",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v67": true,
  "notes": "v68 closeout evidence is the first executable recursive-compilation lane; it verifies the executed reference run, checkpoint result manifest, actual executor/output binding, and truth-boundary preservation without releasing diagnostics, conformance, or control-update surfaces.",
  "output_artifact_refs_and_hashes_verified": true,
  "reasoning_vs_checkpoint_truth_boundary_preserved": true,
  "schema": "v37c_reference_loop_evidence@1",
  "v37a_meta_intent_module_catalog_evidence_hash": "d50e068729a1cc847183d54842d20fcca5e9c00457d1fd6c24f4e9e661fe0185",
  "v37a_meta_intent_module_catalog_evidence_path": "artifacts/agent_harness/v66/evidence_inputs/v37a_meta_intent_module_catalog_evidence_v66.json",
  "v37a_reference_tuple_consumed_without_drift": true,
  "v37b_reference_tuple_consumed_without_drift": true,
  "v37b_sequence_trace_evidence_hash": "1733d68690650457a8543acde8cc6ef155987888f23686b23aeee3e1a969fcf6",
  "v37b_sequence_trace_evidence_path": "artifacts/agent_harness/v67/evidence_inputs/v37b_sequence_trace_evidence_v67.json",
  "v37c_scope_boundary_preserved": true,
  "verification_passed": true
}
```

## Recommendation (Post v68)

- gate decision:
  - `GO_VNEXT_PLUS69_PLANNING_DRAFT`
- rationale:
  - v68 closes the thin `V37-C` executable recursive-compilation lane with canonical
    `meta_loop_checkpoint_result_manifest@1`, one accepted executed
    `meta_loop_run_trace@1`, one accepted executable reference loop bound to the
    released `V37-A` and `V37-B` tuples, and canonical
    `v37c_reference_loop_evidence@1` integrated on `main`.
  - no stop-gate schema-family, metric-key, or evidence-path regressions were observed
    in closeout.
  - the next safe step, if pursued, is a fresh `vNext+69` planning draft for `V37-D`
    rather than widening the closed `V37-C` executable lane in place.
