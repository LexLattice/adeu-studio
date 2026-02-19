# Draft Stop-Gate Decision (Post vNext+13)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS13.md`

Status: draft decision note.

## Decision Guardrail (Frozen)

- This draft cannot pre-commit `vNext+14` implementation scope before all `vNext+13` thresholds are measured and evidenced.
- Any `vNext+14` recommendation in this document is non-binding until `all_passed = true` for the `vNext+13` exit criteria.

## Evidence Source

- CI workflow: `ci` on `main`
- Run ID: `22181276189`
- Run URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22181276189`
- Head SHA: `fa60993a4f819beb3bd45a25a41c51bb908abcc8`
- CI result timestamp window: merge on February 19, 2026 (UTC)
- Deterministic closeout artifact outputs (reproducible):
  - stop-gate JSON: `artifacts/stop_gate/metrics_v13_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v13_closeout.md`
  - closeout command:
    - `.venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --out-json artifacts/stop_gate/metrics_v13_closeout.json --out-md artifacts/stop_gate/report_v13_closeout.md`
- Arc diff evidence (mechanically reproducible):
  - commit range: `340fd22..fa60993`
  - diff command:
    - `git diff --name-status 340fd22..fa60993`
- Key artifacts:
  - A1 core IR contract freeze:
    - `packages/adeu_core_ir/src/adeu_core_ir/models.py`
    - `packages/adeu_core_ir/schema/adeu_core_ir.v0_1.json`
    - `packages/adeu_core_ir/tests/test_core_ir_models.py`
  - A2 deterministic extraction/canonicalization:
    - `packages/adeu_core_ir/src/adeu_core_ir/pipeline.py`
    - `packages/adeu_core_ir/tests/test_core_ir_pipeline.py`
  - A3 deterministic claim ledger:
    - `packages/adeu_core_ir/src/adeu_core_ir/ledger.py`
    - `packages/adeu_core_ir/tests/test_core_ir_ledger.py`
  - A4 fixture/stop-gate closeout:
    - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
    - `apps/api/fixtures/stop_gate/vnext_plus13_manifest.json`
    - `examples/eval/stop_gate/adeu_core_ir_case_a_1.json`
    - `examples/eval/stop_gate/adeu_core_ir_case_a_2.json`
    - `examples/eval/stop_gate/adeu_core_ir_case_a_3.json`
    - `apps/api/tests/test_urm_stop_gate_tools.py`
- Merge PRs:
  - `#133` (A1), `#134` (A2), `#135` (A3), `#136` (A4)

## Exit-Criteria Check (vNext+13)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| A1-A4 merged with green CI | required | `pass` | CI run `22181276189` (`python=success`, `web=success`) |
| `adeu_core_ir` replay determinism | `100.0` | `pass` | stop-gate metric `adeu_core_ir_replay_determinism_pct = 100.0` |
| claim-ledger recomputation match | `100.0` | `pass` | stop-gate metric `adeu_claim_ledger_recompute_match_pct = 100.0` |
| lane projection determinism | `100.0` | `pass` | stop-gate metric `adeu_lane_projection_determinism_pct = 100.0` |
| `vNext+13 -> vNext+14` thresholds all pass | required | `pass` | closeout output includes all frozen v13 metrics at threshold with stable `vnext_plus13_manifest_hash` |
| no solver semantics contract delta | required | `pass` | Arc diff is core-ir/extraction/ledger/metrics/tests/docs hardening only |
| no trust-lane regression | required | `pass` | trust-lane taxonomy unchanged (`mapping_trust`, `solver_trust`, `proof_trust`) |
| all existing stop-gate tracked `vNext+6` through `vNext+11` metrics remain at threshold | required | `pass` | v13 closeout metrics preserve prior tracked gates at threshold |
| `vNext+12` closeout evidence remains green and reproducible | required | `pass` | `docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS12.md` (`valid=true`, `all_passed=true`) |

Summary:

- `valid = true`
- `all_passed = true`
- `issues = []`

## A-Track Result Summary

- A1 `adeu_core_ir@0.1` contract freeze:
  - status: `done`
  - evidence: merged in `#133`; schema + deterministic ordering/edge-typing validation contracts.
- A2 deterministic extraction/canonicalization:
  - status: `done`
  - evidence: merged in `#134`; deterministic normalization/candidate merge and canonical output path.
- A3 claim-ledger scoring contract (`S/B/R`):
  - status: `done`
  - evidence: merged in `#135`; deterministic milli scoring and recomputation checks.
- A4 fixture + stop-gate closeout:
  - status: `done`
  - evidence: merged in `#136`; v13 manifest-driven metrics, fail-closed hash checks, and replay drift tests.

## Open Issues / Residual Risks

- none blocking `vNext+13` closeout.
- residual process risk:
  - severity: low
  - owner: provider/runtime maintainers
  - mitigation: keep `vNext+14` tightly scoped to provider parity/reliability and fixture-driven deterministic closeout.

## Recommendation (`vNext+14` Gate)

- gate decision:
  - `GO_VNEXT_PLUS14_DRAFT`
- rationale:
  - all `vNext+13` frozen scope items (A1-A4) are merged.
  - merge CI is green on `main` for the closeout commit.
  - deterministic closeout checks pass with `all_passed = true`.
- explicit guard:
  - if `all_passed != true`, decision is `HOLD_VNEXT_PLUS14`.
  - no implementation scope for `vNext+14` is authorized from this note while held.

## Suggested Next Artifacts

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS14.md` for Path 8 thin slice (`8a`) codex provider reliability + module parity closeout.
2. Refresh `docs/DRAFT_NEXT_ARC_OPTIONS_v3.md` baseline snapshot to post-`vNext+13` state.
3. Start `vNext+14` PR1 only after the v14 lock draft is approved.
