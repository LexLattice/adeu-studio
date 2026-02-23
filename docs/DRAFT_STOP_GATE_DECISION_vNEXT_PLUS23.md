# Draft Stop-Gate Decision (Post vNext+23)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS23.md`

Status: draft decision note (arc closeout update, February 23, 2026 UTC).

## Decision Guardrail (Frozen)

- This draft records `vNext+23` closeout evidence only.
- Any `vNext+24` lock remains a separate follow-on artifact and is not pre-committed by this note.

## Evidence Source

- CI workflow: `ci` on `main`
- Arc-completion merge commit: `7d8838bf9f7df489f3fbeb08477fe3f3d6522a56`
- Arc-completion CI run:
  - Run ID: `22320265085`
  - URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22320265085`
  - conclusion: `success`
- merged implementation PR sequence:
  - `#176` (`V1`) merge commit `f3eec9d8bc1fe17c02226029948478eee8a40873`
  - `#177` (`V2`) merge commit `73ce66c85317400bb91e68a8012cfe2f7d9c7294`
  - `#178` (`V3`) merge commit `d0f4991c486413cb8799432678a825c45c090814`
  - `#179` (`V4`) merge commit `7d8838bf9f7df489f3fbeb08477fe3f3d6522a56`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v23_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v23_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v23_closeout.md`
  - semantics-v4 transfer report: `docs/SEMANTICS_V4_TRANSFER_REPORT_vNEXT_PLUS23.md`
- closeout commands:
  - `TZ=UTC LC_ALL=C PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src .venv/bin/python apps/api/scripts/build_quality_dashboard.py --out artifacts/quality_dashboard_v23_closeout.json`
  - `TZ=UTC LC_ALL=C PYTHONPATH=apps/api/src:packages/urm_runtime/src:packages/adeu_core_ir/src .venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --quality-current artifacts/quality_dashboard_v23_closeout.json --quality-baseline artifacts/quality_dashboard_v22_closeout.json --out-json artifacts/stop_gate/metrics_v23_closeout.json --out-md artifacts/stop_gate/report_v23_closeout.md`

## Exit-Criteria Check (vNext+23)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| `V1`-`V4` merged with green CI | required | `pass` | PRs `#176`-`#179` merged; merge CI runs `22304127177`, `22304747724`, `22305634336`, `22320265085` all `success` |
| `artifact_semantics_v4_candidate_packet_determinism_pct` | `100.0` | `pass` | `100.0` |
| `artifact_semantics_v4_candidate_projection_determinism_pct` | `100.0` | `pass` | `100.0` |
| `vNext+23 -> vNext+24` frozen thresholds all pass | required | `pass` | closeout stop-gate `all_passed = true` |
| v16/v17/v18/v19/v20/v21/v22 continuity metrics remain present and at threshold | `100.0` each | `pass` | continuity metrics in `artifacts/stop_gate/metrics_v23_closeout.json` remain at threshold |
| v18 tooling continuity | `artifact_stop_gate_ci_budget_within_ceiling_pct == 100.0` | `pass` | `100.0` |
| v23 closeout includes runtime-observability comparison vs v22 baseline | required | `pass` | comparison row included in this note |
| default runtime semantics remains v3 and unchanged | required | `pass` | `V4` regression coverage and v3 diagnostics continuity checks merged in PR `#179` |
| no trust-lane regression introduced | required | `pass` | trust taxonomy unchanged (`mapping_trust`, `solver_trust`, `proof_trust`) |
| provider continuity unchanged | required | `pass` | no proposer/provider surface expansion in `V1`-`V4` scope |
| all tracked `vNext+6` through `vNext+22` gates remain at threshold | required | `pass` | `gates` set in closeout JSON has no `false` entries |

Summary:

- `schema = "stop_gate_metrics@1"`
- `valid = true`
- `all_passed = true`
- `issues = []`
- `vnext_plus23_manifest_hash = 6ae645e5ce18e62d3a7bde3329eabbced786cdf1d789461e73c6af3a6e3a7ef2`

## Runtime Observability Comparison (v22 Baseline vs v23 Closeout)

| Arc | Source | total_fixtures | total_replays | elapsed_ms | bytes_hashed_per_replay | bytes_hashed_total | valid | all_passed |
|---|---|---:|---:|---:|---:|---:|---|---|
| `vNext+22` baseline | `artifacts/stop_gate/metrics_v22_closeout.json` | `12` | `36` | `45` | `5463` | `16389` | `true` | `true` |
| `vNext+23` closeout | `artifacts/stop_gate/metrics_v23_closeout.json` | `14` | `42` | `60` | `9260` | `27780` | `true` | `true` |

Interpretation:

- Replay volume increased by `+16.7%` (`36` -> `42`) with additive semantics-v4 candidate packet/projection determinism surfaces.
- Replay-byte observability increased (`5463` -> `9260` bytes per replay) and remained deterministic under frozen v23 hashing rules.
- Runtime remains within frozen tooling continuity budget constraints with `artifact_stop_gate_ci_budget_within_ceiling_pct = 100.0`.

## V-Track Result Summary

- `V1` deterministic semantics-v4 candidate comparison packet contract freeze:
  - status: `done`
  - evidence: PR `#176`
- `V2` deterministic semantics-v4 candidate projection + transfer report artifact family:
  - status: `done`
  - evidence: PR `#177`, `docs/SEMANTICS_V4_TRANSFER_REPORT_vNEXT_PLUS23.md`
- `V3` additive stop-gate determinism metrics for semantics-v4 candidate payload stability:
  - status: `done`
  - evidence: PR `#178`, v23 metrics in closeout stop-gate report
- `V4` non-enforcement and no-mutation/no-provider-expansion continuity:
  - status: `done`
  - evidence: PR `#179`, guard/non-enforcement/no-mutation/default-v3 continuity tests merged

## Recommendation (`vNext+24` Gate)

- gate decision:
  - `GO_VNEXT_PLUS24_DRAFT`
- rationale:
  - all frozen v23 criteria are satisfied with deterministic closeout evidence.
  - merged CI on `main` is green through the full `V1`-`V4` sequence.

## Suggested Next Artifacts

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS24.md` with explicit post-v23 scope and continuity constraints.
2. Refresh the next-arc options document for post-v23 sequencing and lock selection.
3. Reuse the v23 deterministic closeout command path as continuity checks in early v24 PRs.
