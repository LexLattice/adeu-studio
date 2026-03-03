# Draft Stop-Gate Decision (Post vNext+41)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md`

Status: draft decision note (interim closeout update, March 4, 2026 UTC).

## Decision Guardrail (Frozen)

- This draft records `vNext+41` closeout evidence only.
- It must not redefine semantics, locks, or scope from `docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md`.
- Any `vNext+42` lock/release decision remains a separate follow-on artifact and is not pre-committed by this note.
- Runtime-observability comparison row is required closeout evidence and is informational-only in v41 (no new timing threshold gate in this arc).
- `semantic_compiler_surface_snapshot@0.1`, `semantic_compiler_surface_diff@0.1`, and `semantic_compiler_evidence_manifest@0.1` remain authoritative continuity contracts consumed by v41 closeout evidence.
- v40 compiler-core input handoff authority remains lock-frozen for v41 closeout interpretation.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `ebb6b6f40ff876750058e416b9e6a1363af72e90`
- arc-completion CI run:
  - Run ID: `22644799322`
  - URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22644799322`
  - conclusion: `success`
- merged implementation PR sequence:
  - `#228` (`P1`) merge commit `d3e84afb2c83272489ca6e0fb33967ee6caf3bdc`
  - `#229` (`P2`) merge commit `ebb6b6f40ff876750058e416b9e6a1363af72e90`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v41_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v41_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v41_closeout.md`
  - surface snapshot output: `artifacts/semantic_compiler/v41/surface_snapshot.json`
  - surface diff output: `artifacts/semantic_compiler/v41/surface_diff.json`
  - evidence manifest output: `artifacts/semantic_compiler/v41/evidence_manifest.json`
  - PR splits output: `docs/generated/semantic_compiler/v41/PR_SPLITS.md`
- closeout commands:
  - `TZ=UTC LC_ALL=C PYTHONWARNINGS=ignore PYTHONPATH=packages/adeu_semantic_compiler/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_ir/src:packages/urm_runtime/src .venv/bin/python -m adeu_semantic_compiler.compile`
  - `TZ=UTC LC_ALL=C PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src .venv/bin/python apps/api/scripts/build_quality_dashboard.py --out artifacts/quality_dashboard_v41_closeout.json`
  - `TZ=UTC LC_ALL=C PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src .venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --quality-current artifacts/quality_dashboard_v41_closeout.json --quality-baseline artifacts/quality_dashboard_v40_closeout.json --out-json artifacts/stop_gate/metrics_v41_closeout.json --out-md artifacts/stop_gate/report_v41_closeout.md`

## Exit-Criteria Check (vNext+41)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| `P1`-`P2` merged with green CI | required | `pass` | PRs `#228`-`#229` merged; arc-completion merge CI run `22644799322` is `success` |
| No new stop-gate metric keys introduced | required | `pass` | metric key set in `artifacts/stop_gate/metrics_v41_closeout.json` equals v40 key set exactly; derived cardinality remains `79` |
| No stop-gate schema-family fork | required | `pass` | `schema = "stop_gate_metrics@1"` in `artifacts/stop_gate/metrics_v41_closeout.json` |
| Deterministic surface snapshot/delta + PR/evidence codegen MVP (`V32-D`) closed and test-covered | required | `pass` | P1/P2 merged in PRs `#228` and `#229` with passing `python` lane at arc closeout |
| Surface-governance/codegen artifact evidence block included | required | `pass` | machine-checkable JSON block in this note (`v32d_surface_codegen_evidence@1`) |
| Existing continuity thresholds remain at required values | required | `pass` | continuity metrics in `artifacts/stop_gate/metrics_v41_closeout.json` pass with `issues = []` |
| Runtime observability comparison row vs v40 baseline included | required | `pass` | machine-checkable JSON block in this note (`runtime_observability_comparison@1`) |
| v36 governance, v37 persistence, v38 commitments, v39 semantic-source, and v40 compiler-core continuity remain green and unreverted | required | `pass` | v36/v37/v38/v39/v40 continuity guard coverage remains green under v41 closeout test lane and merged CI |
| No solver semantics contract delta and no trust-lane regression introduced | required | `pass` | v41 scope is `V32-D` surface-governance/codegen + deterministic guards; `SEMANTICS_v3` runtime authority retained |

Summary:

- `schema = "stop_gate_metrics@1"`
- `valid = true`
- `all_passed = true`
- `issues = []`

## Metric-Key Continuity Assertion

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v40_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v41_closeout.json",
  "expected_relation": "exact_keyset_equality"
}
```

## Runtime Observability Comparison (v40 Baseline vs v41 Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+40",
  "current_arc": "vNext+41",
  "baseline_source": "artifacts/stop_gate/report_v40_closeout.md",
  "current_source": "artifacts/stop_gate/report_v41_closeout.md",
  "baseline_elapsed_ms": 87,
  "current_elapsed_ms": 90,
  "delta_ms": 3,
  "notes": "Fixture/replay volume and hashed-byte footprint remain stable; elapsed_ms increased by 3ms under fixed deterministic inputs. This row remains informational-only in v41."
}
```

| Arc | Source | total_fixtures | total_replays | elapsed_ms | bytes_hashed_per_replay | bytes_hashed_total | valid | all_passed |
|---|---|---:|---:|---:|---:|---:|---|---|
| `vNext+40` baseline | `artifacts/stop_gate/metrics_v40_closeout.json` | `21` | `75` | `87` | `67236` | `201708` | `true` | `true` |
| `vNext+41` closeout | `artifacts/stop_gate/metrics_v41_closeout.json` | `21` | `75` | `90` | `67236` | `201708` | `true` | `true` |

## Surface-Governance/Codegen Artifact Evidence

```json
{
  "schema": "v32d_surface_codegen_evidence@1",
  "surface_snapshot_artifact": "artifacts/semantic_compiler/v41/surface_snapshot.json",
  "surface_diff_artifact": "artifacts/semantic_compiler/v41/surface_diff.json",
  "evidence_manifest_artifact": "artifacts/semantic_compiler/v41/evidence_manifest.json",
  "pr_splits_artifact": "docs/generated/semantic_compiler/v41/PR_SPLITS.md",
  "surface_snapshot_sha256": "cc25b38b18ce8c5aac27ac9498b30724ab5dd969071e9c54d27f6caaa86d5e87",
  "surface_diff_sha256": "c688d46c9b2fbd1c05a40e1f75acee2427d767691d838dd535ea070698e0e033",
  "evidence_manifest_sha256": "6cedc0711eb1e4bafa4432eaf549ba64db7a51dcd7ef7a7f4480c6ebc6ea4aab",
  "pr_splits_sha256": "9dc6d2f042202d5e99462e7a5d2d13eab50eef957e808a8596b2eb05672e6f0c",
  "delta_eval_mode": "no_baseline",
  "byte_replay_equal": true,
  "notes": "Artifacts are produced by the single authoritative entrypoint (`python -m adeu_semantic_compiler.compile`) from v40 compiler-core artifacts; reruns are byte-identical and v41 delta mode remains deterministic `no_baseline` under current baseline availability."
}
```

## P-Track Result Summary

- `P1` surface snapshot/delta + PR/evidence codegen MVP (`V32-D`):
  - status: `done`
  - evidence: PR `#228`
- `P2` surface governance determinism/fail-closed guard suite (`V32-D`):
  - status: `done`
  - evidence: PR `#229`

## Recommendation (`vNext+42` Planning Gate)

- gate decision:
  - `GO_VNEXT_PLUS42_PLANNING_DRAFT`
- rationale:
  - all frozen v41 criteria are satisfied with deterministic closeout evidence.
  - merged CI on `main` is green at arc completion.

## Suggested Next Artifacts

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS42.md` scoped to `V32-E` while preserving v36/v37/v38/v39/v40/v41 continuity locks.
2. Preserve v41 surface-governance/codegen contract/guard locks as mandatory continuity gates for v42+.
3. Keep `stop_gate_metrics@1` schema-family continuity unless an explicit future lock authorizes keyset expansion.
