# Draft Stop-Gate Decision (Post vNext+40)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS40.md`

Status: draft decision note (interim closeout update, March 3, 2026 UTC).

## Decision Guardrail (Frozen)

- This draft records `vNext+40` closeout evidence only.
- It must not redefine semantics, locks, or scope from `docs/LOCKED_CONTINUATION_vNEXT_PLUS40.md`.
- Any `vNext+41` lock/release decision remains a separate follow-on artifact and is not pre-committed by this note.
- Runtime-observability comparison row is required closeout evidence and is informational-only in v40 (no new timing threshold gate in this arc).
- `semantic_source_collection@0.1` and `adeu_commitments_ir@0.1` remain authoritative continuity contracts consumed by v40 compiler-core work.
- Pass-manifest hash evidence in v40 is interpreted using lock-frozen canonical JSON pass-value hash subject and read-only/mutating pass partition semantics.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `7685b6633a248451f19658d48a1d47ba79422d33`
- arc-completion CI run:
  - Run ID: `22640056293`
  - URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22640056293`
  - conclusion: `success`
- merged implementation PR sequence:
  - `#226` (`O1`) merge commit `c6a1b96c5eccd428d4ffe305326ad4ca4eaf5016`
  - `#227` (`O2`) merge commit `7685b6633a248451f19658d48a1d47ba79422d33`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v40_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v40_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v40_closeout.md`
  - compiler commitments IR output: `artifacts/semantic_compiler/v40/commitments_ir.json`
  - compiler diagnostics output: `artifacts/semantic_compiler/v40/semantic_compiler.diagnostics.json`
  - compiler pass manifest output: `artifacts/semantic_compiler/v40/pass_manifest.json`
- closeout commands:
  - `TZ=UTC LC_ALL=C PYTHONWARNINGS=ignore PYTHONPATH=packages/adeu_semantic_compiler/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_ir/src:packages/urm_runtime/src .venv/bin/python -m adeu_semantic_compiler.compile`
  - `TZ=UTC LC_ALL=C PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src .venv/bin/python apps/api/scripts/build_quality_dashboard.py --out artifacts/quality_dashboard_v40_closeout.json`
  - `TZ=UTC LC_ALL=C PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src .venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --quality-current artifacts/quality_dashboard_v40_closeout.json --quality-baseline artifacts/quality_dashboard_v39_closeout.json --out-json artifacts/stop_gate/metrics_v40_closeout.json --out-md artifacts/stop_gate/report_v40_closeout.md`

## Exit-Criteria Check (vNext+40)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| `O1`-`O2` merged with green CI | required | `pass` | PRs `#226`-`#227` merged; arc-completion merge CI run `22640056293` is `success` |
| No new stop-gate metric keys introduced | required | `pass` | metric key set in `artifacts/stop_gate/metrics_v40_closeout.json` equals v39 key set exactly; derived cardinality remains `79` |
| No stop-gate schema-family fork | required | `pass` | `schema = "stop_gate_metrics@1"` in `artifacts/stop_gate/metrics_v40_closeout.json` |
| Deterministic compiler core pass pipeline MVP (`V32-C`) closed and test-covered | required | `pass` | O1/O2 merged in PRs `#226` and `#227` with passing `python` lane at arc closeout |
| Compiler-core artifact evidence block included | required | `pass` | machine-checkable JSON block in this note (`v32c_compiler_core_evidence@1`) |
| Existing continuity thresholds remain at required values | required | `pass` | continuity metrics in `artifacts/stop_gate/metrics_v40_closeout.json` pass with `issues = []` |
| Runtime observability comparison row vs v39 baseline included | required | `pass` | machine-checkable JSON block in this note (`runtime_observability_comparison@1`) |
| v36 governance, v37 persistence, v38 commitments, and v39 semantic-source continuity remain green and unreverted | required | `pass` | v36/v37/v38/v39 continuity guard coverage remains green under v40 closeout test lane and merged CI |
| No solver semantics contract delta and no trust-lane regression introduced | required | `pass` | v40 scope is `V32-C` compiler-core pipeline + deterministic guards; `SEMANTICS_v3` runtime authority retained |

Summary:

- `schema = "stop_gate_metrics@1"`
- `valid = true`
- `all_passed = true`
- `issues = []`

## Metric-Key Continuity Assertion

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v39_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v40_closeout.json",
  "expected_relation": "exact_keyset_equality"
}
```

## Runtime Observability Comparison (v39 Baseline vs v40 Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+39",
  "current_arc": "vNext+40",
  "baseline_source": "artifacts/stop_gate/report_v39_closeout.md",
  "current_source": "artifacts/stop_gate/report_v40_closeout.md",
  "baseline_elapsed_ms": 102,
  "current_elapsed_ms": 87,
  "delta_ms": -15,
  "baseline_total_fixtures": 21,
  "current_total_fixtures": 21,
  "baseline_total_replays": 75,
  "current_total_replays": 75,
  "baseline_bytes_hashed_per_replay": 67236,
  "current_bytes_hashed_per_replay": 67236,
  "baseline_bytes_hashed_total": 201708,
  "current_bytes_hashed_total": 201708,
  "notes": "Fixture/replay volume and hashed-byte footprint remain stable; elapsed_ms decreased by 15ms under fixed deterministic inputs. This row remains informational-only in v40."
}
```

| Arc | Source | total_fixtures | total_replays | elapsed_ms | bytes_hashed_per_replay | bytes_hashed_total | valid | all_passed |
|---|---|---:|---:|---:|---:|---:|---|---|
| `vNext+39` baseline | `artifacts/stop_gate/metrics_v39_closeout.json` | `21` | `75` | `102` | `67236` | `201708` | `true` | `true` |
| `vNext+40` closeout | `artifacts/stop_gate/metrics_v40_closeout.json` | `21` | `75` | `87` | `67236` | `201708` | `true` | `true` |

## Compiler-Core Artifact Evidence

```json
{
  "schema": "v32c_compiler_core_evidence@1",
  "commitments_ir_artifact": "artifacts/semantic_compiler/v40/commitments_ir.json",
  "diagnostics_artifact": "artifacts/semantic_compiler/v40/semantic_compiler.diagnostics.json",
  "pass_manifest_artifact": "artifacts/semantic_compiler/v40/pass_manifest.json",
  "commitments_ir_sha256": "9a2bb34282bd1b54d41df8d96aaf0c1e3d0821d1e92a8fed39c4ddd5e36f1b3b",
  "diagnostics_sha256": "c9b195d98e152f6574bef04a9a02f0974c65b285b392412c4beeb23a4d8b6bae",
  "pass_manifest_sha256": "8280b26d394a4683f74d69bc3a8daf60a155fc7deea18dba98f19a908162a277",
  "pass_manifest_chain_complete": true,
  "byte_replay_equal": true,
  "notes": "Artifacts are produced by the single authoritative entrypoint (`python -m adeu_semantic_compiler.compile`) from v39 semantic-source closeout artifacts; reruns are byte-identical and pass-manifest hash chain fields are complete."
}
```

## O-Track Result Summary

- `O1` compiler core pass pipeline MVP (`V32-C`):
  - status: `done`
  - evidence: PR `#226`
- `O2` compiler core determinism/fail-closed guard suite (`V32-C`):
  - status: `done`
  - evidence: PR `#227`

## Recommendation (`vNext+41` Planning Gate)

- gate decision:
  - `GO_VNEXT_PLUS41_PLANNING_DRAFT`
- rationale:
  - all frozen v40 criteria are satisfied with deterministic closeout evidence.
  - merged CI on `main` is green at arc completion.

## Suggested Next Artifacts

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS41.md` scoped to `V32-D` while preserving v36/v37/v38/v39/v40 continuity locks.
2. Preserve v40 compiler-core contract/guard locks as mandatory continuity gates for v41+.
3. Keep `stop_gate_metrics@1` schema-family continuity unless an explicit future lock authorizes keyset expansion.
