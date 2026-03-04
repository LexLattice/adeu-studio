# Draft Stop-Gate Decision (Post vNext+43)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS43.md`

Status: draft decision note (post-hoc closeout capture, March 4, 2026 UTC).

## Decision Guardrail (Frozen)

- This draft records `vNext+43` closeout evidence only.
- It must not redefine semantics, locks, or scope from `docs/LOCKED_CONTINUATION_vNEXT_PLUS43.md`.
- This note captures the additive metric-key continuity pivot for `V32-F`; it does not authorize unrestricted future key expansion.
- Runtime-observability comparison row is required evidence and remains informational-only in this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `8a8a3236476ab29d55cd7d25199a34a5c46decaa`
- arc-completion CI run:
  - Run ID: `22673860683`
  - URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22673860683`
  - conclusion: `success`
- merged implementation PR:
  - `#233` (`metrics: add V32-F semantic-compiler stop-gate extension`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v43_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v43_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v43_closeout.md`
  - v43 semantic-compiler metric manifest: `apps/api/fixtures/stop_gate/vnext_plus27_manifest.json`

- closeout commands:
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src .venv/bin/python apps/api/scripts/build_quality_dashboard.py --out artifacts/quality_dashboard_v43_closeout.json --baseline artifacts/quality_dashboard_v42_closeout.json`
  - `TZ=UTC LC_ALL=C PYTHONHASHSEED=0 PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src:packages/adeu_commitments_ir/src:packages/adeu_semantic_source/src:packages/adeu_semantic_compiler/src:packages/adeu_ir/src .venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --quality-current artifacts/quality_dashboard_v43_closeout.json --quality-baseline artifacts/quality_dashboard_v42_closeout.json --out-json artifacts/stop_gate/metrics_v43_closeout.json --out-md artifacts/stop_gate/report_v43_closeout.md`

## Exit-Criteria Check (vNext+43)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| `V32-F` merged with green CI | required | `pass` | PR `#233` merged; arc-completion CI run `22673860683` is `success` |
| Stop-gate schema family continuity retained | required | `pass` | `schema = "stop_gate_metrics@1"` in v42 and v43 closeout metrics |
| Additive key migration is explicit and deterministic | required | `pass` | v42 keyset is strict subset of v43 keyset; required additive key set matches exactly |
| No key removals in v43 migration | required | `pass` | `removed_keys = []` in v42->v43 keyset comparison |
| v43 semantic-compiler parity metric and gate pass | required | `pass` | `artifact_semantic_compiler_evidence_hash_parity_pct = 100.0`; gate evaluates `true` |
| Historical continuity posture remains green | required | `pass` | legacy keyset preserved; v43 `issues = []`, `all_passed = true` |
| No boundary-release expansion introduced | required | `pass` | v43 scope is stop-gate metric extension only (`V32-F`) |

Summary:

- `schema = "stop_gate_metrics@1"`
- `valid = true`
- `all_passed = true`
- `issues = []`
- `derived_cardinality = 80`

## Metric-Key Continuity Assertion

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v42_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v43_closeout.json",
  "expected_relation": "baseline_subset_with_required_additions",
  "required_additive_keys": [
    "artifact_semantic_compiler_evidence_hash_parity_pct"
  ]
}
```

## Runtime Observability Comparison (v42 Baseline vs v43 Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+42",
  "current_arc": "vNext+43",
  "baseline_source": "artifacts/stop_gate/report_v42_closeout.md",
  "current_source": "artifacts/stop_gate/report_v43_closeout.md",
  "baseline_elapsed_ms": 79,
  "current_elapsed_ms": 91,
  "delta_ms": 12,
  "notes": "v43 adds semantic-compiler hash parity replay workload (vnext+27 fixtures), increasing total fixture/replay and hashed-byte counts. Informational-only in this arc."
}
```

| Arc | Source | total_fixtures | total_replays | elapsed_ms | bytes_hashed_per_replay | bytes_hashed_total | valid | all_passed |
|---|---|---:|---:|---:|---:|---:|---|---|
| `vNext+42` baseline | `artifacts/stop_gate/metrics_v42_closeout.json` | `21` | `75` | `79` | `67236` | `201708` | `true` | `true` |
| `vNext+43` closeout | `artifacts/stop_gate/metrics_v43_closeout.json` | `22` | `78` | `91` | `68230` | `204690` | `true` | `true` |

## V32-F Semantic-Compiler Metric Extension Evidence

```json
{
  "schema": "v32f_semantic_compiler_metric_extension_evidence@1",
  "new_metric_key": "artifact_semantic_compiler_evidence_hash_parity_pct",
  "new_gate_key": "artifact_semantic_compiler_evidence_hash_parity",
  "metric_value": 100.0,
  "gate_value": true,
  "baseline_cardinality": 79,
  "current_cardinality": 80,
  "added_keys": [
    "artifact_semantic_compiler_evidence_hash_parity_pct"
  ],
  "removed_keys": [],
  "vnext_plus27_manifest_path": "apps/api/fixtures/stop_gate/vnext_plus27_manifest.json",
  "vnext_plus27_manifest_hash": "dbb58a6c4948bcb9d7cf9802a855a02231a85ee8caeb0ba684bfd03704e29a99",
  "quality_dashboard_v43_sha256": "691416cd75f5a246fd9049de4f2fe2630f614a2eadf6e36ae853eae78698102d",
  "metrics_v43_sha256": "94112c9e0570b5dacc81a62a38aafd22e7f36b0c4d4ea24077f17c34d27599c7",
  "report_v43_sha256": "76e8e6a067c6e0c36a211fbbdfeff56ef8dba80ffcbd390ddd32b425882e2914",
  "notes": "Additive key migration only; schema-family continuity preserved."
}
```

## Post-Hoc Reviewer Findings (Non-Blocking for v43 Closeout)

1. The current v43 parity fixtures validate deterministic baseline/candidate equivalence, but do not yet include a deliberate negative-parity candidate case.
2. The current parity check confirms fixture-to-fixture consistency and does not yet independently recompute fixture claims from committed semantic-compiler source artifacts.
3. v43 fixture coverage is intentionally narrow (single fixture id / single surface id) for the first additive migration.
4. Closeout command examples include `PYTHONWARNINGS=ignore` as operational convenience, while deterministic lock env contract remains keyed to `TZ`, `LC_ALL`, and `PYTHONHASHSEED`.

## Recommendation (Post v43)

- gate decision:
  - `GO_VNEXT_PLUS44_PLANNING_DRAFT`
- rationale:
  - v43 closes `V32-F` with deterministic additive key migration and green CI.
  - no continuity or boundary regressions were observed in closeout evidence.

## Suggested Next Artifacts

1. Keep v43 post-hoc lock and assessment docs aligned with merged implementation details.
2. Run a post-hoc feedback pass on v43 implementation and capture remediation deltas in a focused follow-on PR:
   - add negative-parity guard-inversion fixture/test,
   - add authenticity recompute guard from committed artifacts,
   - decide/document `PYTHONWARNINGS=ignore` contract posture.
3. Start v44 planning only after the post-hoc feedback loop outcome is recorded (no implicit carryover of key-expansion authority).
