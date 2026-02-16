# Draft Stop-Gate Decision (Post vNext+9)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS9.md`

Status: draft decision note.

## Decision Guardrail (Frozen)

- This draft cannot pre-commit `vNext+10` implementation scope before all `vNext+9` thresholds are measured and evidenced.
- Any `vNext+10` recommendation in this document is non-binding until `all_passed = true` for the `vNext+9` exit criteria.

## Evidence Source

- CI workflow: `ci` on `main`
- Run ID: `22064405138`
- Run URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22064405138`
- Head SHA: `38d3d0cc065126594772b51121301f5c713d566c`
- CI result timestamp window: merge on February 16, 2026 (UTC)
- Deterministic stop-gate artifact outputs (reproducible):
  - JSON: `artifacts/stop_gate/metrics.json`
  - Markdown: `artifacts/stop_gate/report.md`
  - closeout command:
    - `.venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --out-json artifacts/stop_gate/metrics.json --out-md artifacts/stop_gate/report.md`
- Arc diff evidence (mechanically reproducible):
  - commit range: `33cdda0..38d3d0c`
  - diff command:
    - `git diff --name-status 33cdda0..38d3d0c`
- Key artifacts:
  - R1 scheduler token + concurrency thin slice:
    - `packages/urm_runtime/src/urm_runtime/storage.py`
    - `packages/urm_runtime/src/urm_runtime/copilot.py`
    - `apps/api/tests/test_urm_copilot_routes.py`
  - R2 restart recovery + orphan lease split-path:
    - `packages/urm_runtime/src/urm_runtime/copilot.py`
    - `apps/api/tests/test_urm_copilot_routes.py`
  - R3 running-total budget + cancel determinism:
    - `packages/urm_runtime/src/urm_runtime/storage.py`
    - `packages/urm_runtime/src/urm_runtime/copilot.py`
    - `apps/api/tests/test_urm_copilot_routes.py`
  - R4 runtime decomposition + stop-gate hardening:
    - `packages/urm_runtime/src/urm_runtime/child_dispatch.py`
    - `packages/urm_runtime/src/urm_runtime/child_workflow.py`
    - `packages/urm_runtime/src/urm_runtime/child_recovery.py`
    - `packages/urm_runtime/src/urm_runtime/child_budget.py`
    - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
    - `apps/api/scripts/build_stop_gate_metrics.py`
    - `apps/api/fixtures/stop_gate/vnext_plus9_manifest.json`
    - `spec/scheduler_dispatch_token.schema.json`
    - `apps/api/tests/test_urm_stop_gate_tools.py`
  - Merge PRs:
    - `#117` (R1), `#118` (R2), `#119` (R3), `#120` (R4)

## Exit-Criteria Check (vNext+9)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| R1-R4 merged with green CI | required | `pass` | CI run `22064405138` (`python=success`, `web=success`) |
| scheduler dispatch replay determinism | `100%` | `pass` | stop-gate metric `scheduler_dispatch_replay_determinism_pct = 100.0`; frozen fixtures in `apps/api/fixtures/stop_gate/vnext_plus9_manifest.json` |
| orphan lease recovery determinism | `100%` | `pass` | stop-gate metric `orphan_lease_recovery_determinism_pct = 100.0`; orphan fixtures in `examples/eval/stop_gate/orphan_lease_recovery_events_case_a_*.ndjson` |
| concurrent budget/cancel stability | `100%` | `pass` | stop-gate metric `concurrent_budget_cancel_stability_pct = 100.0`; fixtures in `examples/eval/stop_gate/concurrent_budget_cancel_events_case_a_*.ndjson` |
| `vNext+9 -> vNext+10` thresholds all pass | required | `pass` | closeout output has all three frozen `vNext+9` metrics at `100.0` and `all_passed = true` |
| no solver semantics contract delta | required | `pass` | Arc diff `33cdda0..38d3d0c` is runtime orchestration/recovery/metrics hardening only; no intentional solver semantics drift |
| no trust-lane regression | required | `pass` | changes remain runtime-policy-proof-explain operational hardening; trust lane taxonomy unchanged |
| all existing `vNext+6`, `vNext+7`, and `vNext+8` determinism metrics remain at threshold | required | `pass` | closeout output retains `validator_packet_determinism_pct`, `witness_reconstruction_determinism_pct`, `semantics_diagnostics_determinism_pct`, `policy_lint_determinism_pct`, `proof_replay_determinism_pct`, `policy_proof_packet_hash_stability_pct`, `explain_diff_determinism_pct`, `explain_api_cli_parity_pct`, `explain_hash_stability_pct` at threshold |

Summary:

- `valid = true`
- `all_passed = true`
- `issues = []`

## R-Track Result Summary

- R1 scheduler token persistence + controlled concurrency rollout:
  - status: `done`
  - evidence: merged in `#117`; deterministic token persistence + concurrency fixtures in `apps/api/tests/test_urm_copilot_routes.py`.
- R2 restart recovery + orphan lease deterministic handling:
  - status: `done`
  - evidence: merged in `#118`; deterministic started/orphan split-path recovery and linkage fixtures.
- R3 concurrent cancellation/termination + budget determinism:
  - status: `done`
  - evidence: merged in `#119`; running-total budget accounting and cancel lineage fixtures.
- R4 runtime decomposition + stop-gate hardening:
  - status: `done`
  - evidence: merged in `#120`; extracted runtime modules + manifest-driven vNext+9 stop-gate metrics and drift/hash-mismatch tests.

## Open Issues / Residual Risks

- none blocking `vNext+9` closeout.
- residual process risk:
  - severity: low
  - owner: runtime/semantics maintainers
  - mitigation: keep `vNext+10` thin-slice focused on pairwise semantic-depth quality with frozen fixture gates before broader depth expansion.

## Recommendation (`vNext+10` Gate)

- gate decision:
  - `GO_VNEXT_PLUS10_DRAFT`
- rationale:
  - all `vNext+9` frozen scope items (R1-R4) are merged.
  - merge CI is green on `main` for the closeout commit.
  - deterministic stop-gate thresholds pass with `all_passed = true` in closeout metrics output.
- explicit guard:
  - if `all_passed != true`, decision is `HOLD_VNEXT_PLUS10`.
  - no implementation scope for `vNext+10` is authorized from this note while held.

## Suggested Next Artifacts

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS10.md` for Path 5 semantic-depth v3.1 thin slice.
2. Refresh `docs/DRAFT_NEXT_ARC_OPTIONS_v2.md` baseline snapshot to post-`vNext+9`.
3. Start `vNext+10` PR1 once the `vNext+10` lock is approved.
