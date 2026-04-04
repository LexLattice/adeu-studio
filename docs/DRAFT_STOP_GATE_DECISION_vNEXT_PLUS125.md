# Draft Stop-Gate Decision (Post vNext+125)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS125.md`

Status: draft decision note (post-hoc closeout capture, April 4, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS125.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v125_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+125` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS125.md`.
- This note captures bounded `V51-B` API evidence only; it does not authorize the
  later `V51-C` UI seam, any persistent session surface, any reset/step/state control
  surface, any product-wide routing entitlement, or imported-bundle precedent by
  itself.
- Canonical `V51-B` release in `v125` is carried by the shipped `adeu_api`
  `odeu_sim.py` route/module pair, committed deterministic `v51b` fixtures, targeted
  API tests, the `apps/api` dependency and anti-coupling guard updates, and the
  canonical `v51b_odeu_sim_api_evidence@1` evidence input under
  `artifacts/agent_harness/v125/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v34.md` now marks `V51-B`
  closed on `main` and advances the branch-local default next path to `V51-C`; it
  does not select the `V51-C` UI contract by itself.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#347` (`feat(v125): add ODEU sim run API`)
- arc-completion merge commit: `16c50769352776d974635839d815a5006a41e680`
- merged-at timestamp: `2026-04-04T13:23:30Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v125_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v125_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v125_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v125/evidence_inputs/metric_key_continuity_assertion_v125.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v125/evidence_inputs/runtime_observability_comparison_v125.json`
  - `V51-B` release evidence input:
    `artifacts/agent_harness/v125/evidence_inputs/v51b_odeu_sim_api_evidence_v125.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v125/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS125_EDGES.md`

## Exit-Criteria Check (vNext+125)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V51-B` merged with green CI | required | `pass` | PR `#347`, merge commit `16c50769352776d974635839d815a5006a41e680`, checks `python/web/lean-formal = pass` |
| One bounded stateless route only ships | required | `pass` | `apps/api/src/adeu_api/odeu_sim.py`, `apps/api/src/adeu_api/main.py`, and absence of reset/step/state or session-token surfaces |
| The route consumes the released stateless kernel helper path and released summary helpers rather than instantiating a long-lived simulation object | required | `pass` | `run_canonical_scenario(...)`, `summarize_lane_state(...)`, `summarize_action_counts(...)`, and `test_build_odeu_run_response_uses_released_stateless_kernel_helper` |
| Request validation is typed and fail-closed for unsupported scenario names, negative seeds, invalid step ranges, and malformed request shape | required | `pass` | `OdeuRunRequestArtifact` strict validation, route-side invalid-request artifacts, and committed invalid-request fixtures/tests |
| Response projection law remains frozen to full released metric payload, exact three-key lane summary, sparse observed-only action counts, and event/evidence/sanction counts | required | `pass` | `OdeuRunSummary`, `OdeuRunLaneSummary`, committed `v51b` fixtures, and `test_build_odeu_run_response_matches_*_fixture` |
| Kernel-stack incompatibility fails closed instead of silently repairing projection drift | required | `pass` | typed `fail_closed_kernel_mismatch` posture and `test_build_odeu_run_response_fails_closed_on_kernel_projection_mismatch` |
| Request/response hashing remains deterministic and frozen to the admitted hash subjects only | required | `pass` | `compute_odeu_run_request_hash(...)`, `compute_odeu_run_response_hash(...)`, and typed model validation of `request_hash` / `response_hash` |
| The `apps/api` lane remains package-subordinate and imported cleanly in full-suite CI | required | `pass` | `apps/api/pyproject.toml` runtime dependency on `adeu-odeu-sim`, anti-coupling guard update, local `make check` before merge, and green merged `python` CI |
| No browser/UI/static surface or persistent storage ships in this slice | required | `pass` | shipped scope limited to `apps/api` route/tests/fixtures and closeout artifacts only |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v125_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v125/evidence_inputs/metric_key_continuity_assertion_v125.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v125/evidence_inputs/runtime_observability_comparison_v125.json` |

## Stop-Gate Summary

```json
{
  "schema": "v125_closeout_stop_gate_summary@1",
  "arc": "vNext+125",
  "target_path": "V51-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v124": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 143,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v124_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v125_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+124","current_arc":"vNext+125","baseline_source":"artifacts/stop_gate/report_v124_closeout.md","current_source":"artifacts/stop_gate/report_v125_closeout.md","baseline_elapsed_ms":143,"current_elapsed_ms":143,"delta_ms":0,"notes":"v125 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V51-B ODEU simulation API lane: one bounded POST /odeu-sim/run route over the released V51-A kernel, one stateless non-persistent execution posture, one full released metric projection plus exact three-key lane summary and sparse observed-only action counts, strict non-negative seed and bounded step validation, typed fail-closed invalid-request and kernel-mismatch artifacts, request/response hash determinism, runtime dependency wiring for adeu-odeu-sim inside apps/api, anti-coupling guard alignment for main router registration, and no reset/step/state session, browser UI, static surface, persistent storage, or product-surface widening."}
```

## V51B ODEU Sim API Evidence

```json
{"schema":"v51b_odeu_sim_api_evidence@1","evidence_input_path":"artifacts/agent_harness/v125/evidence_inputs/v51b_odeu_sim_api_evidence_v125.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS125.md#v125-continuation-contract-machine-checkable","merged_pr":"#347","merge_commit":"16c50769352776d974635839d815a5006a41e680","implementation_packages":["adeu_odeu_sim","adeu_api"],"adeu_api_root":"apps/api","adeu_api_pyproject_path":"apps/api/pyproject.toml","odeu_sim_route_source_path":"apps/api/src/adeu_api/odeu_sim.py","adeu_api_main_source_path":"apps/api/src/adeu_api/main.py","anti_coupling_guard_test_path":"apps/api/tests/test_worker_governance_j2_guards_vnext_plus36.py","canonical_replay_seed":7,"canonical_replay_horizon":25,"test_reference_paths":["apps/api/tests/test_odeu_sim_vnext_plus125.py"],"reference_healthy_baseline_fixture_path":"apps/api/tests/fixtures/v51b/reference_odeu_run_response_healthy_baseline.json","reference_weak_d_fixture_path":"apps/api/tests/fixtures/v51b/reference_odeu_run_response_weak_d.json","reference_invalid_request_fixture_path":"apps/api/tests/fixtures/v51b/reference_odeu_run_response_invalid_negative_seed.json","reference_kernel_mismatch_fixture_path":"apps/api/tests/fixtures/v51b/reference_odeu_run_response_kernel_mismatch.json","metric_key_continuity_assertion_path":"artifacts/agent_harness/v125/evidence_inputs/metric_key_continuity_assertion_v125.json","runtime_observability_comparison_path":"artifacts/agent_harness/v125/evidence_inputs/runtime_observability_comparison_v125.json","runtime_event_stream_path":"artifacts/agent_harness/v125/runtime/evidence/local/urm_events.ndjson","notes":"v125 evidence pins the released V51-B ODEU simulation API lane on main: one repo-owned adeu_api route over the released adeu_odeu_sim kernel, one bounded POST /odeu-sim/run surface only, stateless helper-path execution through run_canonical_scenario, released summary-helper projection through summarize_lane_state and summarize_action_counts, strict typed request validation with non-negative seed and bounded steps, full released metric payload plus exact three-key lane summary and sparse observed-only action counts, typed fail-closed invalid-request and kernel-mismatch responses, request/response hash determinism, runtime dependency wiring for adeu-odeu-sim, anti-coupling guard alignment for main router registration, deterministic v51b fixtures, and no reset/step/state session, browser UI, static surface, or persistent storage."}
```

## Recommendation (Post v125)

- gate decision:
  - `V51B_ODEU_SIM_API_COMPLETE_ON_MAIN`
  - `V51_ODEU_SIM_FAMILY_ACTIVE_ON_MAIN`
- rationale:
  - `v125` closes the bounded `V51-B` API seam on `main` by shipping the first
    repo-owned `POST /odeu-sim/run` route over the released `V51-A` kernel, without
    promoting the prototype's mutable reset/step/state API as live authority.
  - the shipped slice remains narrow and subordinate: one route, one summary-only JSON
    mode, released-kernel scenarios only, stateless helper-path execution, full
    released metric payload plus frozen lane-summary and action-count projections, and
    no browser/UI or persistent state widening.
  - review and CI hardening landed in the release rather than staying in commentary:
    request validation is centralized in typed route artifacts, kernel-mismatch
    projection drift fails closed through typed kernel-mismatch artifacts, `apps/api`
    now depends on `adeu-odeu-sim` in the package metadata, and the main-router
    anti-coupling guard explicitly admits this bounded consumer seam.
  - the imported sandbox bundle remains support-only and non-precedent; the release
    re-authors the live route in repo-owned `apps/api` paths rather than importing the
    prototype API wholesale.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`+0 ms` vs `v124` baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v34.md` should now be read with `V51-B` closed on
    `main` and the branch-local default next path advanced to `V51-C` / `vNext+126`.
