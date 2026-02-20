# Draft Stop-Gate Decision (Post vNext+15)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS15.md`

Status: draft decision note.

## Decision Guardrail (Frozen)

- This draft cannot pre-commit `vNext+16` implementation scope before all `vNext+15` exit criteria are measured and evidenced.
- Any `vNext+16` recommendation in this document is non-binding until `all_passed = true` for the `vNext+15` exit criteria.

## Evidence Source

- CI workflow: `ci` on `main`
- Run ID: `22221271880`
- Run URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22221271880`
- Head SHA: `e7944c2bc20dcae45050e84b8f9b87f7c9b62895`
- CI result timestamp window: merge on February 20, 2026 (UTC)
- Deterministic closeout artifact outputs (reproducible):
  - stop-gate JSON: `artifacts/stop_gate/metrics_v15_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v15_closeout.md`
  - core-ir depth transfer report: `docs/CORE_IR_DEPTH_TRANSFER_REPORT_vNEXT_PLUS15.md`
  - closeout commands:
    - `PYTHONPATH=apps/api/src:packages/urm_runtime/src .venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --out-json artifacts/stop_gate/metrics_v15_closeout.json --out-md artifacts/stop_gate/report_v15_closeout.md`
    - `PYTHONPATH=apps/api/src:packages/urm_runtime/src .venv/bin/python apps/api/scripts/build_core_ir_depth_transfer_report_vnext_plus15.py --out docs/CORE_IR_DEPTH_TRANSFER_REPORT_vNEXT_PLUS15.md`
- Arc diff evidence (mechanically reproducible):
  - commit range: `487cb7d..e7944c2`
  - diff command:
    - `git diff --name-status 487cb7d..e7944c2`
- Key artifacts:
  - C1 deterministic lane reporting contract:
    - `packages/adeu_core_ir/src/adeu_core_ir/lane_report.py`
    - `packages/adeu_core_ir/schema/adeu_lane_report.v0_1.json`
    - `spec/adeu_lane_report.schema.json`
    - `packages/adeu_core_ir/tests/test_core_ir_lane_report.py`
  - C2 projection/extraction alignment diagnostics:
    - `packages/adeu_core_ir/src/adeu_core_ir/projection_alignment.py`
    - `packages/adeu_core_ir/schema/adeu_projection_alignment.v0_1.json`
    - `spec/adeu_projection_alignment.schema.json`
    - `packages/adeu_core_ir/tests/test_core_ir_projection_alignment.py`
  - C3 coverage accountability + transfer report:
    - `apps/api/fixtures/stop_gate/vnext_plus15_manifest.json`
    - `apps/api/src/adeu_api/core_ir_depth_transfer_report_vnext_plus15.py`
    - `apps/api/scripts/build_core_ir_depth_transfer_report_vnext_plus15.py`
    - `apps/api/tests/test_core_ir_depth_transfer_report_vnext_plus15.py`
    - `docs/CORE_IR_DEPTH_TRANSFER_REPORT_vNEXT_PLUS15.md`
  - C4 stop-gate additive metrics + deterministic closeout:
    - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
    - `apps/api/scripts/build_stop_gate_metrics.py`
    - `apps/api/tests/test_urm_stop_gate_tools.py`
- Merge PRs:
  - `#142` (C1), `#143` (C2), `#144` (C3), `#145` (C4)

## Exit-Criteria Check (vNext+15)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| C1-C4 merged with green CI | required | `pass` | CI run `22221271880` (`python=success`, `web=success`) |
| lane report replay determinism | `100.0` | `pass` | stop-gate metric `adeu_lane_report_replay_determinism_pct = 100.0` |
| projection alignment determinism | `100.0` | `pass` | stop-gate metric `adeu_projection_alignment_determinism_pct = 100.0` |
| depth report replay determinism | `100.0` | `pass` | stop-gate metric `adeu_depth_report_replay_determinism_pct = 100.0` |
| transfer-report coverage validity | required | `pass` | `docs/CORE_IR_DEPTH_TRANSFER_REPORT_vNEXT_PLUS15.md` shows `coverage_summary.valid=true`, `coverage_pct=100.0` |
| transfer-report replay validity | required | `pass` | report JSON shows `replay_summary.valid=true`, `replay_count=3` |
| transfer-report alignment determinism validity | required | `pass` | report JSON shows `alignment_summary.valid=true`, deterministic issue counts |
| `vNext+15 -> vNext+16` thresholds all pass | required | `pass` | closeout output includes all frozen v15 metrics at threshold with stable `vnext_plus15_manifest_hash` |
| no solver semantics contract delta | required | `pass` | Arc diff is lane-report/alignment/coverage/metrics/tests/docs hardening only |
| no trust-lane regression | required | `pass` | trust-lane taxonomy unchanged (`mapping_trust`, `solver_trust`, `proof_trust`) |
| all existing stop-gate tracked `vNext+6` through `vNext+14` metrics remain at threshold | required | `pass` | v15 closeout metrics preserve prior tracked gates at threshold |
| `vNext+12`, `vNext+13`, and `vNext+14` closeout evidence remains green and reproducible | required | `pass` | prior closeout decision docs remain `valid=true`, `all_passed=true` |

Summary:

- `valid = true`
- `all_passed = true`
- `issues = []`

## C-Track Result Summary

- C1 deterministic lane reporting contract:
  - status: `done`
  - evidence: merged in `#142`; frozen `adeu_lane_report@0.1` contract + deterministic ordering.
- C2 projection/extraction alignment diagnostics:
  - status: `done`
  - evidence: merged in `#143`; deterministic evidence-only alignment diagnostics with fixed issue taxonomy/order.
- C3 deterministic coverage accountability + transfer report:
  - status: `done`
  - evidence: merged in `#144`; v15 manifest coverage + transfer-report payload with stable `vnext_plus15_manifest_hash`.
- C4 stop-gate additive metrics and deterministic closeout:
  - status: `done`
  - evidence: merged in `#145`; v15 depth-report metrics + replay determinism + strict fixture validation.

## Open Issues / Residual Risks

- none blocking `vNext+15` closeout.
- residual process risk:
  - severity: low
  - owner: integrity/runtime maintainers
  - mitigation: keep `vNext+16` scoped to additive integrity checks without solver semantics or provider-surface expansion.

## Recommendation (`vNext+16` Gate)

- gate decision:
  - `GO_VNEXT_PLUS16_DRAFT`
- rationale:
  - all `vNext+15` frozen scope items (C1-C4) are merged.
  - merge CI is green on `main` for the closeout commit.
  - deterministic closeout checks pass with `all_passed = true`.
- explicit guard:
  - if `all_passed != true`, decision is `HOLD_VNEXT_PLUS16`.
  - no implementation scope for `vNext+16` is authorized from this note while held.

## Suggested Next Artifacts

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS16.md` for Path 9 thin slice (`9a`) formal integrity checks.
2. Refresh `docs/DRAFT_NEXT_ARC_OPTIONS_v3.md` baseline snapshot to post-`vNext+15` state.
3. Start `vNext+16` PR1 only after the v16 lock draft is approved.
