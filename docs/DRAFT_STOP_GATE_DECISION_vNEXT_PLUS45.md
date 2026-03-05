# Draft Stop-Gate Decision (Post vNext+45)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS45.md`

Status: draft decision note (post-hoc closeout capture, March 5, 2026 UTC).

## Decision Guardrail (Frozen)

- This draft records `vNext+45` closeout evidence only.
- It must not redefine semantics, locks, or scope from `docs/LOCKED_CONTINUATION_vNEXT_PLUS45.md`.
- This note captures `V33-B` (`T1`/`T2`) closeout evidence only; it does not authorize `V33-C`/`V33-D` behavior release.
- Runtime-observability comparison row is required evidence and remains informational-only in this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `c43da3bb3a3d29fbb3b47b375e03dfdad220f9bf`
- arc-completion CI run:
  - Run ID: `22696439074`
  - URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22696439074`
  - conclusion: `success`
- merged implementation PRs:
  - `#238` (`contracts: add V33-B constrained taskpack runner + candidate-change-plan policy validation`)
  - `#239` (`tests: add v45 runner determinism and fail-closed guard suite`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v45_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v45_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v45_closeout.md`
  - runner adapter registry: `artifacts/agent_harness/v45/taskpack_runner_adapter_registry.json`
  - runner candidate change plan: `artifacts/agent_harness/v45/candidate_change_plan_closeout.json`
  - runner result run1: `artifacts/agent_harness/v45/closeout_runner_result_run1.json`
  - runner result run2: `artifacts/agent_harness/v45/closeout_runner_result_run2.json`
  - dry-run preview artifact: `artifacts/agent_harness/v45/dry_run_preview/70737c664c5d4263d1d300e7be7224a908619435d756fce044d1f213c8af4aa0_3c339250e058b8b9392fba75d3a34524a1a0fa40a07f5493bd2c21d66d958780.json`
  - runner provenance artifact: `artifacts/agent_harness/v45/dry_run_preview/provenance/70737c664c5d4263d1d300e7be7224a908619435d756fce044d1f213c8af4aa0_3c339250e058b8b9392fba75d3a34524a1a0fa40a07f5493bd2c21d66d958780.json`

- closeout commands:
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_quality_dashboard.py --out artifacts/quality_dashboard_v45_closeout.json --baseline artifacts/quality_dashboard_v44_closeout.json`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src:packages/adeu_agent_harness/src .venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --quality-current artifacts/quality_dashboard_v45_closeout.json --quality-baseline artifacts/quality_dashboard_v44_closeout.json --out-json artifacts/stop_gate/metrics_v45_closeout.json --out-md artifacts/stop_gate/report_v45_closeout.md`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=packages/adeu_agent_harness/src:packages/adeu_ir/src:packages/urm_runtime/src .venv/bin/python -m adeu_agent_harness.run_taskpack --taskpack-dir artifacts/agent_harness/v44/taskpacks/v41/v44_closeout --adapter-registry artifacts/agent_harness/v45/taskpack_runner_adapter_registry.json --adapter-id v45_default --candidate-change-plan artifacts/agent_harness/v45/candidate_change_plan_closeout.json --dry-run > artifacts/agent_harness/v45/closeout_runner_result_run1.json`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONPATH=packages/adeu_agent_harness/src:packages/adeu_ir/src:packages/urm_runtime/src .venv/bin/python -m adeu_agent_harness.run_taskpack --taskpack-dir artifacts/agent_harness/v44/taskpacks/v41/v44_closeout --adapter-registry artifacts/agent_harness/v45/taskpack_runner_adapter_registry.json --adapter-id v45_default --candidate-change-plan artifacts/agent_harness/v45/candidate_change_plan_closeout.json --dry-run > artifacts/agent_harness/v45/closeout_runner_result_run2.json`

## Exit-Criteria Check (vNext+45)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| `T1` merged with green CI | required | `pass` | PR `#238` merged; CI run `22695904167` is `success` |
| `T2` merged with green CI | required | `pass` | PR `#239` merged; CI run `22696439074` is `success` |
| Stop-gate schema-family continuity retained | required | `pass` | `schema = "stop_gate_metrics@1"` in v44 and v45 closeout metrics |
| Stop-gate metric-key continuity retained | required | `pass` | v44 and v45 keysets are exact-set equal (`added_keys = []`, `removed_keys = []`) |
| Deterministic cardinality continuity retained | required | `pass` | metric-key cardinality computed from `metrics` keys is `80 -> 80` |
| V33-B runner dry-run/provenance evidence is deterministic and fail-closed | required | `pass` | run1/run2 runner result payloads are byte-identical; preview/provenance artifacts are byte-identical |
| Historical continuity posture remains green | required | `pass` | v45 closeout `issues = []`, `valid = true`, `all_passed = true` |
| No boundary-release expansion introduced | required | `pass` | v45 scope remains `V33-B` only (`T1`/`T2`) |

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
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v44_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v45_closeout.json",
  "expected_relation": "exact_keyset_equality"
}
```

## Runtime Observability Comparison (v44 Baseline vs v45 Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+44",
  "current_arc": "vNext+45",
  "baseline_source": "artifacts/stop_gate/report_v44_closeout.md",
  "current_source": "artifacts/stop_gate/report_v45_closeout.md",
  "baseline_elapsed_ms": 105,
  "current_elapsed_ms": 133,
  "delta_ms": 28,
  "notes": "v45 adds constrained-runner and deterministic fail-closed guard coverage with closeout runner artifact generation; timing delta remains informational-only in this arc."
}
```

| Arc | Source | total_fixtures | total_replays | elapsed_ms | bytes_hashed_per_replay | bytes_hashed_total | valid | all_passed |
|---|---|---:|---:|---:|---:|---:|---|---|
| `vNext+44` baseline | `artifacts/stop_gate/metrics_v44_closeout.json` | `22` | `78` | `105` | `68230` | `204690` | `true` | `true` |
| `vNext+45` closeout | `artifacts/stop_gate/metrics_v45_closeout.json` | `22` | `78` | `133` | `68230` | `204690` | `true` | `true` |

## V33-B Runner Wiring Evidence

```json
{
  "schema": "v33b_runner_wiring_evidence@1",
  "runner_entrypoint": "python -m adeu_agent_harness.run_taskpack",
  "adapter_surface": "taskpack_runner_adapter_registry@1/candidate_plan_passthrough",
  "dry_run_supported": true,
  "candidate_change_plan_schema": "candidate_change_plan@1",
  "pre_write_policy_validation_passed": true,
  "allowlist_enforcement_passed": true,
  "forbidden_effect_enforcement_passed": true,
  "provenance_hash": "891a56f0fcb46aaf8abe1b618289c323f8875ce38269c9a9e92817f726678414",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v44": true,
  "notes": "Runner closeout dry-run reruns produced byte-identical runner result payload, dry-run preview artifact, and provenance artifact for identical taskpack+candidate-plan input bytes."
}
```

## Recommendation (Post v45)

- gate decision:
  - `GO_VNEXT_PLUS46_PLANNING_DRAFT`
- rationale:
  - v45 closes `V33-B` (`T1`/`T2`) with deterministic constrained-runner wiring and fail-closed guard coverage on `main`.
  - no continuity or boundary regressions were observed in closeout evidence.

## Suggested Next Artifacts

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS46.md`, `docs/ASSESSMENT_vNEXT_PLUS46_EDGES.md`, and `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS46.md` for `V33-C` planning.
2. Keep v45 closeout artifacts stable; rerun closeout commands only under frozen deterministic env contract.
3. Start v46 lock drafting with explicit deterministic auditor/verifier + evidence-writer authority boundaries.
