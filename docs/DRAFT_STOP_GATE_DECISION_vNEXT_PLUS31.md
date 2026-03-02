# Draft Stop-Gate Decision (Post vNext+31)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS31.md`

Status: draft decision note (interim closeout update, March 2, 2026 UTC).

## Decision Guardrail (Frozen)

- This draft records `vNext+31` closeout evidence only.
- Any `vNext+32` lock remains a separate follow-on artifact and is not pre-committed by this note.

## Evidence Source

- CI workflow: `ci` on `main`
- Arc-completion merge commit: `da9d3554232ee27adc8b5b80cf5a14d926bd061c`
- Arc-completion CI run:
  - Run ID: `22573118781`
  - URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22573118781`
  - conclusion: `success`
- merged implementation PR sequence:
  - `#208` (`E1`) merge commit `4177334f73b6336da11b705b70298251b2e5287c` (CI run `22572304290`)
  - `#209` (`E2`) merge commit `da9d3554232ee27adc8b5b80cf5a14d926bd061c` (CI run `22573118781`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v31_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v31_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v31_closeout.md`
- closeout commands:
  - `TZ=UTC LC_ALL=C PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src .venv/bin/python apps/api/scripts/build_quality_dashboard.py --out artifacts/quality_dashboard_v31_closeout.json`
  - `TZ=UTC LC_ALL=C PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src .venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --quality-current artifacts/quality_dashboard_v31_closeout.json --quality-baseline artifacts/quality_dashboard_v30_closeout.json --out-json artifacts/stop_gate/metrics_v31_closeout.json --out-md artifacts/stop_gate/report_v31_closeout.md`

## Exit-Criteria Check (vNext+31)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| `E1`-`E2` merged with green CI | required | `pass` | PRs `#208`-`#209` merged; merge CI runs `22572304290` and `22573118781` both `success` |
| No new stop-gate metric keys introduced | required | `pass` | metric key set in `artifacts/stop_gate/metrics_v31_closeout.json` equals v30 key set exactly; derived cardinality remains `79` |
| No stop-gate schema-family fork | required | `pass` | `schema = "stop_gate_metrics@1"` in `artifacts/stop_gate/metrics_v31_closeout.json` |
| Evidence Explorer API/web template contract mismatch is resolved under frozen rules | required | `pass` | E1 implementation merged in PR `#208`; web validator enforces template-path contract and deterministic fail-closed branches |
| Closeout consistency lint/backfill guard executes deterministically and fails closed | required | `pass` | E2 implementation merged in PR `#209`; CI `python` job includes `Lint closeout consistency` step and passes in arc-completion run |
| Existing continuity thresholds remain at required values | required | `pass` | continuity metrics in `artifacts/stop_gate/metrics_v31_closeout.json` pass with `issues = []` |
| Runtime observability comparison row vs v30 baseline included | required | `pass` | machine-checkable JSON block in this note (`runtime_observability_comparison@1`) |
| no solver semantics contract delta and no trust-lane regression introduced | required | `pass` | v31 scope is E1/E2 deterministic hardening only; `SEMANTICS_v3` runtime authority and trust-lane continuity retained |

Summary:

- `schema = "stop_gate_metrics@1"`
- `valid = true`
- `all_passed = true`
- `issues = []`
- `vnext_plus26_manifest_hash = b842bb583f951321178f228f017240c269f5d8259adc40004a2ff3294d2bc120`

## Metric-Key Continuity Assertion

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v30_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v31_closeout.json",
  "expected_relation": "exact_keyset_equality"
}
```

## Runtime Observability Comparison (v30 Baseline vs v31 Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+30",
  "current_arc": "vNext+31",
  "baseline_source": "artifacts/stop_gate/metrics_v30_closeout.json",
  "current_source": "artifacts/stop_gate/metrics_v31_closeout.json",
  "baseline_elapsed_ms": 88,
  "current_elapsed_ms": 140,
  "delta_ms": 52,
  "baseline_total_fixtures": 21,
  "current_total_fixtures": 21,
  "baseline_total_replays": 75,
  "current_total_replays": 75,
  "baseline_bytes_hashed_per_replay": 67236,
  "current_bytes_hashed_per_replay": 67236,
  "baseline_bytes_hashed_total": 201708,
  "current_bytes_hashed_total": 201708,
  "notes": "Fixture/replay volume and hashed-byte footprint remain stable; elapsed_ms increased under fixed deterministic inputs."
}
```

| Arc | Source | total_fixtures | total_replays | elapsed_ms | bytes_hashed_per_replay | bytes_hashed_total | valid | all_passed |
|---|---|---:|---:|---:|---:|---:|---|---|
| `vNext+30` baseline | `artifacts/stop_gate/metrics_v30_closeout.json` | `21` | `75` | `88` | `67236` | `201708` | `true` | `true` |
| `vNext+31` closeout | `artifacts/stop_gate/metrics_v31_closeout.json` | `21` | `75` | `140` | `67236` | `201708` | `true` | `true` |

## E-Track Result Summary

- `E1` Evidence Explorer template-contract closure:
  - status: `done`
  - evidence: PR `#208`
- `E2` closeout consistency guard rail and v29/v30 normalization:
  - status: `done`
  - evidence: PR `#209`

## Recommendation (`vNext+32` Planning Gate)

- gate decision:
  - `GO_VNEXT_PLUS32_PLANNING_DRAFT`
- rationale:
  - all frozen v31 criteria are satisfied with deterministic closeout evidence.
  - merged CI on `main` is green through `E1`-`E2` sequence.

## Suggested Next Artifacts

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS32.md` thin-slice scope from post-v31 baseline evidence.
2. Keep `docs/DRAFT_NEXT_ARC_OPTIONS_v5.md` execution checkpoint synchronized with v31 closeout and v32 selection state.
3. Preserve v31 template-contract and closeout-consistency fail-closed guarantees as explicit continuity gates in early v32 PRs.
