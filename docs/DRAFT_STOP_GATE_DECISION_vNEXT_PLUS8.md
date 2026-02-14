# Draft Stop-Gate Decision (Post vNext+8)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS8.md`

Status: draft decision note.

## Decision Guardrail (Frozen)

- This draft cannot pre-commit `vNext+9` implementation scope before all `vNext+8` thresholds are measured and evidenced.
- Any `vNext+9` recommendation in this document is non-binding until `all_passed = true` for the `vNext+8` exit criteria.

## Evidence Source

- CI workflow: `ci` on `main`
- Run ID: `22021818145`
- Run URL: `https://github.com/LexLattice/adeu-studio/actions/runs/22021818145`
- Head SHA: `971227fbd47f5a2efdd92cad99a21d36978e8f54`
- CI result timestamp window: merge on February 14, 2026 (UTC)
- Deterministic stop-gate artifact outputs (reproducible):
  - JSON: `artifacts/stop_gate/metrics.json`
  - Markdown: `artifacts/stop_gate/report.md`
  - closeout command:
    - `.venv/bin/python apps/api/scripts/build_stop_gate_metrics.py --out-json artifacts/stop_gate/metrics.json --out-md artifacts/stop_gate/report.md`
- Arc diff evidence (mechanically reproducible):
  - commit range: `78cfaa7..971227f`
  - diff command:
    - `git diff --name-status 78cfaa7..971227f`
- Key artifacts:
  - E1 explain contract normalization + schema/materialization:
    - `spec/explain_diff.schema.json`
    - `apps/api/src/adeu_api/explain_builder.py`
    - `apps/api/src/adeu_api/main.py`
    - `apps/api/src/adeu_api/storage.py`
    - `apps/api/tests/test_explain_e1_endpoints.py`
    - `apps/api/tests/test_explain_diff_packet_schema.py`
  - E2 API/CLI parity + hash stability:
    - `apps/api/src/adeu_api/explain_tools.py`
    - `packages/adeu_explain/src/adeu_explain/explain_diff.py`
    - `apps/api/tests/test_explain_cli_parity.py`
    - `apps/api/tests/fixtures/explain_parity/semantic_diff_golden_v1.json`
    - `apps/api/tests/fixtures/explain_parity/concepts_diff_golden_v1.json`
    - `apps/api/tests/fixtures/explain_parity/puzzles_diff_golden_v1.json`
    - `apps/api/tests/fixtures/explain_parity/flip_explain_golden_v1.json`
  - E3 minimal read-only UI evidence views:
    - `apps/web/src/app/explain/page.tsx`
    - `apps/web/tests/routes.smoke.test.mjs`
  - E4 replay metrics + stop-gate hardening:
    - `apps/api/fixtures/stop_gate/vnext_plus8_manifest.json`
    - `examples/eval/stop_gate/explain_diff_case_a_1.json`
    - `examples/eval/stop_gate/explain_api_case_a_1.json`
    - `examples/eval/stop_gate/explain_cli_case_a_1.json`
    - `packages/urm_runtime/src/urm_runtime/stop_gate_tools.py`
    - `apps/api/scripts/build_stop_gate_metrics.py`
    - `apps/api/tests/test_urm_stop_gate_tools.py`
  - Merge PRs:
    - `#112` (E1), `#113` (E2), `#114` (E3), `#115` (E4)

## Exit-Criteria Check (vNext+8)

| Criterion | Threshold | Result | Evidence |
|---|---|---|---|
| E1-E4 merged with green CI | required | `pass` | CI run `22021818145` (`python=success`, `web=success`) |
| explain replay determinism | `100%` | `pass` | stop-gate metric `explain_diff_determinism_pct = 100.0`; fixtures in `apps/api/fixtures/stop_gate/vnext_plus8_manifest.json` |
| explain API/CLI parity | `100%` | `pass` | stop-gate metric `explain_api_cli_parity_pct = 100.0`; parity fixtures in `apps/api/tests/test_explain_cli_parity.py` |
| explain packet hash stability | `100%` | `pass` | stop-gate metric `explain_hash_stability_pct = 100.0`; schema/hash fixtures in `apps/api/tests/test_explain_diff_packet_schema.py` |
| `vNext+8 -> vNext+9` thresholds all pass | required | `pass` | `build_stop_gate_metrics.py` closeout output has all three frozen `vNext+8` metrics at `100.0` and `all_passed = true` |
| no solver semantics contract delta | required | `pass` | Arc diff `78cfaa7..971227f` is explain contract/API/CLI/UI/metrics hardening only; no intentional solver semantics drift |
| no trust-lane regression | required | `pass` | explain outputs remain informational-only; trust lanes unchanged by E1-E4 |
| all existing `vNext+6` and `vNext+7` determinism metrics remain at threshold | required | `pass` | closeout stop-gate output retains `validator_packet_determinism_pct`, `witness_reconstruction_determinism_pct`, `semantics_diagnostics_determinism_pct`, `policy_lint_determinism_pct`, `proof_replay_determinism_pct`, `policy_proof_packet_hash_stability_pct` at `100.0` |

Summary:

- `valid = true`
- `all_passed = true`
- `issues = []`

## E-Track Result Summary

- E1 explain contract normalization:
  - status: `done`
  - evidence: merged in `#112`; `explain_diff@1` schema + deterministic endpoint/materialization fixtures.
- E2 explain API/CLI parity:
  - status: `done`
  - evidence: merged in `#113`; shared builder parity and frozen golden fixtures.
- E3 minimal read-only UI evidence views:
  - status: `done`
  - evidence: merged in `#114`; explain route + smoke coverage.
- E4 explain replay metrics + stop-gate hardening:
  - status: `done`
  - evidence: merged in `#115`; manifest-driven vNext+8 explain metrics/gates + drift/hash-mismatch tests.

## Open Issues / Residual Risks

- none blocking `vNext+8` closeout.
- residual process risk:
  - severity: low
  - owner: explain/runtime maintainers
  - mitigation: keep `vNext+9` scope focused on deterministic scheduler/recovery fixtures before throughput expansion.

## Recommendation (`vNext+9` Gate)

- gate decision:
  - `GO_VNEXT_PLUS9_DRAFT`
- rationale:
  - all `vNext+8` frozen scope items (E1-E4) are merged.
  - merge CI is green on `main` for the closeout commit.
  - deterministic stop-gate thresholds pass with `all_passed = true` in closeout metrics output.
- explicit guard:
  - if `all_passed != true`, decision is `HOLD_VNEXT_PLUS9`.
  - no implementation scope for `vNext+9` is authorized from this note while held.

## Suggested Next Artifacts

1. Draft `docs/LOCKED_CONTINUATION_vNEXT_PLUS9.md` for Path 4 controlled scale/recovery thin slice.
2. Keep `docs/DRAFT_NEXT_ARC_OPTIONS_v2.md` synchronized with post-`vNext+8` baseline context.
3. Start `vNext+9` PR1 after the `vNext+9` lock is approved.
