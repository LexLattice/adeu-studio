# Draft Stop-Gate Decision (Post vNext+12)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS12.md`

Status: draft decision note.

## Decision Guardrail (Frozen)

- This draft cannot pre-commit `vNext+13` implementation scope before all `vNext+12` exit criteria are measured and evidenced.
- Any `vNext+13` recommendation in this document is non-binding until `all_passed = true` for the `vNext+12` exit criteria.

## Evidence Source

- CI workflow: `ci` on `main`
- Run ID: `22081264162`
- Run URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22081264162`
- Head SHA: `340fd229d14f8fefb23abc4023fdd93fee24aa24`
- CI result timestamp window: merge on February 17, 2026 (UTC)
- Deterministic closeout artifact outputs (reproducible):
  - stop-gate JSON: `artifacts/stop_gate/metrics_v12_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v12_closeout.md`
  - paper practical summary: `artifacts/manual_runs/paper_pipeline_v12_closeout/summary.json`
  - closeout commands:
    - `.venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --out-json artifacts/stop_gate/metrics_v12_closeout.json --out-md artifacts/stop_gate/report_v12_closeout.md`
    - `.venv/bin/python apps/api/scripts/run_paper_pipeline.py --pdf examples/2602.11865v1.pdf --out artifacts/manual_runs/paper_pipeline_v12_closeout/summary.json`
- Arc diff evidence (mechanically reproducible):
  - commit range: `082bcb6..340fd22`
  - diff command:
    - `git diff --name-status 082bcb6..340fd22`
- Key artifacts:
  - P1 extraction robustness:
    - `packages/urm_domain_paper/src/urm_domain_paper/adapters.py`
    - `apps/api/tests/test_urm_domain_tools.py`
  - P2 deterministic selection/summary:
    - `apps/api/src/adeu_api/paper_pipeline.py`
    - `apps/api/scripts/run_paper_pipeline.py`
    - `apps/api/tests/test_paper_pipeline.py`
  - P3 worker log normalization:
    - `packages/urm_runtime/src/urm_runtime/normalization.py`
    - `apps/api/tests/fixtures/codex_exec/rollout_missing_path_noise.jsonl`
    - `apps/api/tests/test_urm_worker_runner.py`
  - P4 fixture/test closeout:
    - `apps/api/tests/test_urm_domain_tools.py`
    - `apps/api/tests/test_urm_worker_runner.py`
    - `apps/api/tests/test_paper_pipeline.py`
  - Merge PR:
    - `#130` (`vNext+12: harden real-PDF paper pipeline + close v11`)

## Exit-Criteria Check (vNext+12)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| P1-P4 merged with green CI | required | `pass` | CI run `22081264162` (`python=success`, `web=success`) |
| raw-paper extraction avoids date/header false selection on locked practical run | required | `pass` | `summary.json`: `selected_flow=raw_pdf_text`, `selected_word_count=141`, `parse_degraded_raw=false`, both flows `candidate_date_like=false` |
| selected flow/candidate reporting deterministic across replay reruns | required | `pass` | repeat run preserves stable selection fields (`selected_flow`, `selected_candidate_hash`, `selected_artifact_id`, `selection_reason`, `final_parse_quality`) |
| known rollout provider-log noise no longer causes false parse degradation | required | `pass` | `test_worker_runner_tolerates_known_rollout_log_without_parse_degraded` + `test_normalize_exec_line_tolerates_unknown_and_parse_errors` in `apps/api/tests/test_urm_worker_runner.py` |
| no solver semantics contract delta | required | `pass` | Arc diff touches paper adapter / runtime normalization / pipeline scripts/tests only |
| no trust-lane regression introduced | required | `pass` | trust taxonomy unchanged (`mapping_trust`, `solver_trust`, `proof_trust`) |
| all existing `vNext+6` through `vNext+11` determinism metrics remain at threshold | required | `pass` | stop-gate closeout output: `all_passed=true` with v6-v11 gates at threshold in `metrics_v12_closeout.json` |

Summary:

- `valid = true`
- `all_passed = true`
- `issues = []`

## P-Track Result Summary

- P1 raw-PDF extraction robustness:
  - status: `done`
  - evidence: date/header guard + structural paragraph fallback + extraction strategy/sentence-count fields.
- P2 deterministic selection summary contract:
  - status: `done`
  - evidence: `paper_pipeline_summary@1` contract emitted with explicit winner/selection diagnostics.
- P3 worker log normalization quality signaling:
  - status: `done`
  - evidence: known `codex_core::rollout::list` noise classified as `provider_log` and excluded from false parse degradation.
- P4 deterministic fixture/test closeout:
  - status: `done`
  - evidence: targeted test suite green (`test_urm_domain_tools.py`, `test_urm_worker_runner.py`, `test_paper_pipeline.py`).

## Open Issues / Residual Risks

- none blocking `vNext+12` closeout.
- residual process risk:
  - severity: low
  - owner: paper/runtime maintainers
  - mitigation: keep `vNext+13` scoped to core O/E/D/U projection IR and deterministic extraction/ledger fixtures.

## Recommendation (`vNext+13` Gate)

- gate decision:
  - `GO_VNEXT_PLUS13_DRAFT`
- rationale:
  - all `vNext+12` frozen scope items (P1-P4) are merged.
  - merge CI is green on `main` for the closeout commit.
  - deterministic closeout checks pass with `all_passed = true`.
- explicit guard:
  - if `all_passed != true`, decision is `HOLD_VNEXT_PLUS13`.
  - no implementation scope for `vNext+13` is authorized from this note while held.

## Suggested Next Artifacts

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS13.md` for core O/E/D/U projection IR (`adeu_core_ir@0.1`) and deterministic extraction/ledger thin slice.
2. Keep stop-gate schema continuity additive on `stop_gate_metrics@1`.
3. Open `vNext+13` PR1 only after the lock is approved and scoped.
