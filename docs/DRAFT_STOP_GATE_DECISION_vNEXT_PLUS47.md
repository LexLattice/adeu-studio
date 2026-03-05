# Draft Stop-Gate Decision (Post vNext+47)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS47.md`

Status: draft decision note (post-hoc closeout capture, March 5, 2026 UTC).

## Decision Guardrail (Frozen)

- This draft records `vNext+47` closeout evidence only.
- It must not redefine semantics, locks, or scope from `docs/LOCKED_CONTINUATION_vNEXT_PLUS47.md`.
- This note captures `V33-D` (`W1`/`W2`) closeout evidence only; it does not authorize post-v47 deferred behavior release.
- v47 packaging remains adapter-boundary, artifact-authoritative, and fail-closed under frozen lock text.
- Runtime-observability comparison row is required evidence and remains informational-only in this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `fe857b2e5d529c35ba3ac4c7b5d9306b7c4dfa24`
- arc-completion CI run:
  - Run ID: `22717892624`
  - URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22717892624`
  - conclusion: `success`
- merged implementation PRs:
  - `#243` (`contracts: add V33-D deterministic integrated/standalone packaging lane MVP`)
  - `#244` (`tests: add v47 packaging determinism, policy-equivalence, and fail-closed guard suite`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v47_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v47_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v47_closeout.md`
  - packaging rerun parity summary: `artifacts/agent_harness/v47/closeout_packaging_rerun_parity.json`
  - runtime observability evidence input: `artifacts/agent_harness/v47/evidence_inputs/runtime_observability_comparison_v47.json`
  - metric-key continuity evidence input: `artifacts/agent_harness/v47/evidence_inputs/metric_key_continuity_assertion_v47.json`
  - packaging wiring evidence input: `artifacts/agent_harness/v47/evidence_inputs/v33d_packaging_wiring_evidence_v47.json`
  - integrated packaging manifest: `artifacts/agent_harness/v47/packaging/adeu_integrated/taskpack_ux_packaging_manifest.json`
  - standalone packaging manifest: `artifacts/agent_harness/v47/packaging/standalone/taskpack_ux_packaging_manifest.json`
  - integrated packaging provenance: `artifacts/agent_harness/v47/packaging/adeu_integrated/provenance/949315154ef6b932728b6b8b7123b313cbd889fb816b54d4896317d28ede4661_baeda34f66a5095da7923ce5df3cdc8e2f7147de829a6bd973df31237d897ca4.json`
  - standalone packaging provenance: `artifacts/agent_harness/v47/packaging/standalone/provenance/949315154ef6b932728b6b8b7123b313cbd889fb816b54d4896317d28ede4661_baeda34f66a5095da7923ce5df3cdc8e2f7147de829a6bd973df31237d897ca4.json`
  - cross-mode canonical parity evidence: `artifacts/agent_harness/v47/packaging/parity/closeout_artifact_parity.json`
  - cross-mode policy-equivalence evidence: `artifacts/agent_harness/v47/packaging/parity/closeout_policy_equivalence.json`

- closeout commands:
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_quality_dashboard.py --out artifacts/quality_dashboard_v47_closeout.json --baseline artifacts/quality_dashboard_v46_closeout.json`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --quality-current artifacts/quality_dashboard_v47_closeout.json --quality-baseline artifacts/quality_dashboard_v46_closeout.json --out-json artifacts/stop_gate/metrics_v47_closeout.json --out-md artifacts/stop_gate/report_v47_closeout.md`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=packages/urm_runtime/src:packages/adeu_ir/src .venv/bin/python -c "import json; from pathlib import Path; from urm_runtime.hashing import canonical_json; m46=json.loads(Path('artifacts/stop_gate/metrics_v46_closeout.json').read_text()); m47=json.loads(Path('artifacts/stop_gate/metrics_v47_closeout.json').read_text()); rt46=m46['runtime_observability']; rt47=m47['runtime_observability']; k46=set(m46['metrics']); k47=set(m47['metrics']); out=Path('artifacts/agent_harness/v47/evidence_inputs'); out.mkdir(parents=True, exist_ok=True); runtime={'schema':'runtime_observability_comparison@1','baseline_arc':'vNext+46','current_arc':'vNext+47','baseline_source':'artifacts/stop_gate/report_v46_closeout.md','current_source':'artifacts/stop_gate/report_v47_closeout.md','baseline_elapsed_ms':rt46['elapsed_ms'],'current_elapsed_ms':rt47['elapsed_ms'],'delta_ms':rt47['elapsed_ms']-rt46['elapsed_ms'],'notes':'v47 closeout remains informational-only for timing and runtime byte observability under frozen locks.'}; continuity={'schema':'metric_key_continuity_assertion@1','baseline_metrics_artifact':'artifacts/stop_gate/metrics_v46_closeout.json','current_metrics_artifact':'artifacts/stop_gate/metrics_v47_closeout.json','expected_relation':'exact_keyset_equality','metric_key_exact_set_equal_v46':k46==k47,'metric_key_cardinality':len(k47)}; (out/'runtime_observability_comparison_v47.json').write_text(canonical_json(runtime)+'\\n', encoding='utf-8'); (out/'metric_key_continuity_assertion_v47.json').write_text(canonical_json(continuity)+'\\n', encoding='utf-8')"`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=packages/adeu_agent_harness/src:packages/adeu_ir/src:packages/urm_runtime/src .venv/bin/python -m adeu_agent_harness.package_ux_integrated --deployment-mode adeu_integrated --taskpack-dir artifacts/agent_harness/v46/taskpacks/v41/v46_closeout --verified-result artifacts/agent_harness/v46/verification/949315154ef6b932728b6b8b7123b313cbd889fb816b54d4896317d28ede4661_3c339250e058b8b9392fba75d3a34524a1a0fa40a07f5493bd2c21d66d958780.json --evidence-bundle artifacts/agent_harness/v46/evidence/949315154ef6b932728b6b8b7123b313cbd889fb816b54d4896317d28ede4661_3c339250e058b8b9392fba75d3a34524a1a0fa40a07f5493bd2c21d66d958780.json --verifier-provenance artifacts/agent_harness/v46/evidence/provenance/949315154ef6b932728b6b8b7123b313cbd889fb816b54d4896317d28ede4661_3c339250e058b8b9392fba75d3a34524a1a0fa40a07f5493bd2c21d66d958780.json --runtime-observability-comparison artifacts/agent_harness/v47/evidence_inputs/runtime_observability_comparison_v47.json --metric-key-continuity-assertion artifacts/agent_harness/v47/evidence_inputs/metric_key_continuity_assertion_v47.json --packaging-output-root artifacts/agent_harness/v47/packaging --diagnostic-registry packages/adeu_agent_harness/src/adeu_agent_harness/diagnostic_registry_v47.json --dry-run`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=packages/adeu_agent_harness/src:packages/adeu_ir/src:packages/urm_runtime/src .venv/bin/python -m adeu_agent_harness.package_ux_standalone --deployment-mode standalone --taskpack-dir artifacts/agent_harness/v46/taskpacks/v41/v46_closeout --verified-result artifacts/agent_harness/v46/verification/949315154ef6b932728b6b8b7123b313cbd889fb816b54d4896317d28ede4661_3c339250e058b8b9392fba75d3a34524a1a0fa40a07f5493bd2c21d66d958780.json --evidence-bundle artifacts/agent_harness/v46/evidence/949315154ef6b932728b6b8b7123b313cbd889fb816b54d4896317d28ede4661_3c339250e058b8b9392fba75d3a34524a1a0fa40a07f5493bd2c21d66d958780.json --verifier-provenance artifacts/agent_harness/v46/evidence/provenance/949315154ef6b932728b6b8b7123b313cbd889fb816b54d4896317d28ede4661_3c339250e058b8b9392fba75d3a34524a1a0fa40a07f5493bd2c21d66d958780.json --runtime-observability-comparison artifacts/agent_harness/v47/evidence_inputs/runtime_observability_comparison_v47.json --metric-key-continuity-assertion artifacts/agent_harness/v47/evidence_inputs/metric_key_continuity_assertion_v47.json --packaging-output-root artifacts/agent_harness/v47/packaging --diagnostic-registry packages/adeu_agent_harness/src/adeu_agent_harness/diagnostic_registry_v47.json --dry-run`

## Exit-Criteria Check (vNext+47)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| `W1` merged with green CI | required | `pass` | PR `#243` merged; CI run `22717157194` is `success` |
| `W2` merged with green CI | required | `pass` | PR `#244` merged; CI run `22717892624` is `success` |
| Stop-gate schema-family continuity retained | required | `pass` | `schema = "stop_gate_metrics@1"` in v46 and v47 closeout metrics |
| Stop-gate metric-key continuity retained | required | `pass` | v46 and v47 keysets are exact-set equal (`added_keys = []`, `removed_keys = []`) |
| Deterministic cardinality continuity retained | required | `pass` | metric-key cardinality computed from `metrics` keys is `80 -> 80` |
| V33-D integrated/standalone parity and policy-equivalence are deterministic | required | `pass` | `artifacts/agent_harness/v47/closeout_packaging_rerun_parity.json`, `artifacts/agent_harness/v47/packaging/parity/closeout_artifact_parity.json`, `artifacts/agent_harness/v47/packaging/parity/closeout_policy_equivalence.json` |
| Mode-selection contract is exact-match and fail-closed | required | `pass` | `test_package_ux_rejects_unknown_deployment_mode`, `test_package_ux_rejects_non_exact_case_mode_value`, `test_packaging_cli_requires_explicit_deployment_mode_flag` |
| Packaging failure emits deterministic structured diagnostics and no partial output | required | `pass` | `test_emit_rejection_diagnostic_orders_and_normalizes_paths`, `test_package_ux_emits_rejection_diagnostic_and_no_partial_package_on_failure` |
| Historical continuity posture remains green | required | `pass` | v47 closeout `issues = []`, `valid = true`, `all_passed = true` |
| No boundary-release expansion introduced | required | `pass` | v47 scope remains `V33-D` only (`W1`/`W2`) |

Summary:

- `schema = "stop_gate_metrics@1"`
- `valid = true`
- `all_passed = true`
- `issues = []`
- `derived_cardinality = 80` (computed from `metrics` keyset cardinality)

## Metric-Key Continuity Assertion

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v46_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v47_closeout.json",
  "expected_relation": "exact_keyset_equality"
}
```

## Runtime Observability Comparison (v46 Baseline vs v47 Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+46",
  "current_arc": "vNext+47",
  "baseline_source": "artifacts/stop_gate/report_v46_closeout.md",
  "current_source": "artifacts/stop_gate/report_v47_closeout.md",
  "baseline_elapsed_ms": 122,
  "current_elapsed_ms": 105,
  "delta_ms": -17,
  "notes": "v47 closeout remains informational-only for timing. Runtime byte observability uses a fixed replay-cycle aggregate (`bytes_hashed_replay_cycles = 3`) and is not a direct `total_replays` multiplier."
}
```

| Arc | Source | total_fixtures | total_replays | elapsed_ms | bytes_hashed_per_replay | bytes_hashed_total | valid | all_passed |
|---|---|---:|---:|---:|---:|---:|---|---|
| `vNext+46` baseline | `artifacts/stop_gate/metrics_v46_closeout.json` | `22` | `78` | `122` | `68230` | `204690` | `true` | `true` |
| `vNext+47` closeout | `artifacts/stop_gate/metrics_v47_closeout.json` | `22` | `78` | `105` | `68230` | `204690` | `true` | `true` |

## V33-D Packaging Wiring Evidence

```json
{
  "schema": "v33d_packaging_wiring_evidence@1",
  "integrated_entrypoint": "python -m adeu_agent_harness.package_ux_integrated",
  "standalone_entrypoint": "python -m adeu_agent_harness.package_ux_standalone",
  "deployment_modes": [
    "adeu_integrated",
    "standalone"
  ],
  "artifact_parity_passed": true,
  "policy_equivalence_passed": true,
  "provenance_hash": "0861d646d3d2fbf641932c01990685a3d715d4aa66b80a157f95471edc7dc596",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v46": true,
  "notes": "v47 closeout reruns produced byte-identical integrated/standalone canonical artifact subjects and exact policy-equivalence parity; mode-specific bundle launcher output differs only by deployment mode boundary."
}
```

## Recommendation (Post v47)

- gate decision:
  - `GO_VNEXT_PLUS48_PLANNING_DRAFT`
- rationale:
  - v47 closes `V33-D` (`W1`/`W2`) with deterministic integrated/standalone packaging and fail-closed guard coverage on `main`.
  - no continuity, schema-family, or metric-key regressions were observed in closeout evidence.

## Suggested Next Artifacts

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS48.md`, `docs/ASSESSMENT_vNEXT_PLUS48_EDGES.md`, and `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS48.md` for post-v47 planning.
2. Keep v47 closeout artifacts stable; rerun closeout commands only under frozen deterministic env contract.
3. Keep signing/trust-anchor distribution, matrix-lane parity, zero-trust policy recompute, retry-context automation, and remote/enclave attestation deferred until explicitly locked in later arcs.
