# Draft Stop-Gate Decision (Post vNext+28)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS28.md`

Status: draft decision note (interim closeout update, March 1, 2026 UTC).

## Decision Guardrail (Frozen)

- This draft records `vNext+28` closeout evidence only.
- Any `vNext+29` lock remains a separate follow-on artifact and is not pre-committed by this note.

## Evidence Source

- CI workflow: `ci` on `main`
- Arc-completion merge commit: `d66c3b98ce44e1753fc17e9bf835236a9addd76b`
- Arc-completion CI run:
  - Run ID: `22540874433`
  - URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22540874433`
  - conclusion: `success`
- merged implementation PR sequence:
  - `#196` (`B1`) merge commit `43856a8ccd26b47e62480739abea5560ceb57a84` (CI run `22526213363`)
  - `#197` (`B2`) merge commit `d13ba83b64eeb88403010f2c2ca778091a971eb4` (CI run `22540014355`)
  - `#198` (`B3`) merge commit `1617ddf4dcb78ff0e33dad2319803151dbbeb9fa` (CI run `22540586947`)
  - `#199` (`B4`) merge commit `d66c3b98ce44e1753fc17e9bf835236a9addd76b` (CI run `22540874433`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v28_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v28_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v28_closeout.md`
- closeout commands:
  - `TZ=UTC LC_ALL=C PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src .venv/bin/python apps/api/scripts/build_quality_dashboard.py --out artifacts/quality_dashboard_v28_closeout.json`
  - `TZ=UTC LC_ALL=C PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src .venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --quality-current artifacts/quality_dashboard_v28_closeout.json --quality-baseline artifacts/quality_dashboard_v27_closeout.json --out-json artifacts/stop_gate/metrics_v28_closeout.json --out-md artifacts/stop_gate/report_v28_closeout.md`
  - `TZ=UTC LC_ALL=C PYTHONWARNINGS=ignore PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src .venv/bin/python apps/api/scripts/build_tooling_transfer_report_vnext_plus26.py`

## Exit-Criteria Check (vNext+28)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| `B1`-`B4` merged with green CI | required | `pass` | PRs `#196`-`#199` merged; merge CI runs `22526213363`, `22540014355`, `22540586947`, `22540874433` all `success` |
| No new stop-gate metric keys introduced | required | `pass` | metric key set in `artifacts/stop_gate/metrics_v28_closeout.json` matches v27 exactly |
| Locked fixture parity outputs remain unchanged | required | `pass` | `artifact_stop_gate_input_model_parity_pct = 100.0`, `artifact_transfer_report_builder_parity_pct = 100.0` |
| v26 tooling transfer-report payload regeneration is canonical-hash identical to locked baseline payload | required | `pass` | check-only `apps/api/scripts/build_tooling_transfer_report_vnext_plus26.py` exits `0` with parity enforced before any write |
| Existing continuity thresholds remain at required values | required | `pass` | continuity metrics in `artifacts/stop_gate/metrics_v28_closeout.json` remain at threshold (`100.0` where applicable) |
| Runtime observability comparison row vs v27 baseline included | required | `pass` | machine-checkable JSON block in this note (`runtime_observability_comparison@1`) |
| no solver semantics contract delta and no trust-lane regression introduced | required | `pass` | B-track scope is tooling sustainability consolidation only; v3 default semantics and trust-lane continuity retained |

Summary:

- `schema = "stop_gate_metrics@1"`
- `valid = true`
- `all_passed = true`
- `issues = []`
- `vnext_plus26_manifest_hash = b842bb583f951321178f228f017240c269f5d8259adc40004a2ff3294d2bc120`

## Runtime Observability Comparison (v27 Baseline vs v28 Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+27",
  "current_arc": "vNext+28",
  "baseline_source": "artifacts/stop_gate/metrics_v27_closeout.json",
  "current_source": "artifacts/stop_gate/metrics_v28_closeout.json",
  "baseline_elapsed_ms": 83,
  "current_elapsed_ms": 81,
  "delta_ms": -2,
  "baseline_total_fixtures": 21,
  "current_total_fixtures": 21,
  "baseline_total_replays": 75,
  "current_total_replays": 75,
  "baseline_bytes_hashed_per_replay": 67236,
  "current_bytes_hashed_per_replay": 67236,
  "baseline_bytes_hashed_total": 201708,
  "current_bytes_hashed_total": 201708,
  "notes": "Fixture/replay volume and hashed bytes remain stable; elapsed_ms decreased under fixed deterministic inputs."
}
```

| Arc | Source | total_fixtures | total_replays | elapsed_ms | bytes_hashed_per_replay | bytes_hashed_total | valid | all_passed |
|---|---|---:|---:|---:|---:|---:|---|---|
| `vNext+27` baseline | `artifacts/stop_gate/metrics_v27_closeout.json` | `21` | `75` | `83` | `67236` | `201708` | `true` | `true` |
| `vNext+28` closeout | `artifacts/stop_gate/metrics_v28_closeout.json` | `21` | `75` | `81` | `67236` | `201708` | `true` | `true` |

## B-Track Result Summary

- `B1` active stop-gate manifest registry consolidation:
  - status: `done`
  - evidence: PR `#196`
- `B2` stop-gate modularization with compatibility facade:
  - status: `done`
  - evidence: PR `#197`
- `B3` deterministic v26 tooling transfer-report regeneration formalization:
  - status: `done`
  - evidence: PR `#198`
- `B4` parity/regression guard suite for `B1`-`B3` continuity proof:
  - status: `done`
  - evidence: PR `#199`

## Recommendation (`vNext+29` Planning Gate)

- gate decision:
  - `GO_VNEXT_PLUS29_PLANNING_DRAFT`
- rationale:
  - all frozen v28 criteria are satisfied with deterministic closeout evidence.
  - merged CI on `main` is green through the full `B1`-`B4` sequence.

## Suggested Next Artifacts

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS29.md` thin-slice scope using post-v28 baseline evidence.
2. Keep `docs/DRAFT_NEXT_ARC_OPTIONS_v4.md` execution checkpoint synchronized with v28 closeout and v29 selection state.
3. Preserve v28 registry/modularization/parity guard contracts as explicit continuity gates in early v29 PRs.
