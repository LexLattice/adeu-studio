# Draft Stop-Gate Decision (Post vNext+126)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS126.md`

Status: draft decision note (post-hoc closeout capture, April 4, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS126.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v126_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+126` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS126.md`.
- This note captures bounded `V51-C` web evidence only; it does not authorize any
  later persistent browser/session surface, prototype-style control widening,
  broader product entitlement, or imported-bundle precedent by itself.
- Canonical `V51-C` release in `v126` is carried by the shipped `apps/web`
  `/odeu-sim` route surface, committed deterministic contract/smoke tests, and the
  canonical `v51c_odeu_sim_web_evidence@1` evidence input under
  `artifacts/agent_harness/v126/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v34.md` now marks
  `V51-A` through `V51-C` closed on `main` with no further internal `V51` path
  selected; it does not pick a later family by itself.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#348` (`feat(v126): add ODEU sim summary web route`)
- arc-completion merge commit: `db17dadcde902abed740e63a82cc4f9b430d1fd5`
- merged-at timestamp: `2026-04-04T14:13:21Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v126_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v126_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v126_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v126/evidence_inputs/metric_key_continuity_assertion_v126.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v126/evidence_inputs/runtime_observability_comparison_v126.json`
  - `V51-C` release evidence input:
    `artifacts/agent_harness/v126/evidence_inputs/v51c_odeu_sim_web_evidence_v126.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v126/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS126_EDGES.md`

## Exit-Criteria Check (vNext+126)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V51-C` merged with green CI | required | `pass` | PR `#348`, merge commit `db17dadcde902abed740e63a82cc4f9b430d1fd5`, checks `python/web/lean-formal = pass` |
| One bounded `/odeu-sim` route only ships | required | `pass` | `apps/web/src/app/odeu-sim/page.tsx` plus route-local support modules/tests and absence of broader browser-control surfaces |
| The web route remains subordinate to the released `POST /odeu-sim/run` API rather than importing kernel law directly | required | `pass` | `apps/web/src/app/odeu-sim/odeu-sim-client.tsx`, `apps/web/src/app/odeu-sim/view-model.ts`, and `test("odeu sim route: no direct kernel import ...")` |
| Initial interaction remains idle-first with defaults prefilled and user-triggered run only | required | `pass` | `INITIAL_ROUTE_STATUS = "idle"`, default config builders in `view-model.ts`, and the absence of auto-run behavior in `OdeuSimClient` |
| Route-status mapping remains exact: `idle`/`loading` added locally, completed statuses carried directly from released API `request_status` | required | `pass` | `mapApiRequestStatusToRouteStatus(...)`, `createViewModelFromApiResponse(...)`, and `test("odeu sim view-model: API status maps directly after completion")` |
| The web view model preserves full released `config_snapshot`, full released `current_metric`, exact three-key `lane_summary`, sparse observed-only `action_counts`, and released count fields | required | `pass` | `OdeuRunViewModel`, `createViewModelFromApiResponse(...)`, and committed contract/smoke tests over `/odeu-sim` |
| `response_hash` is retained in the bounded web view model | required | `pass` | `response_hash` carriage in `view-model.ts` and `test("completed response preserves full released objects and response_hash")` |
| Invalid-request and kernel-mismatch responses render explicit fail-closed browser posture instead of being normalized away | required | `pass` | `failureMessageForStatus(...)`, failure-banner rendering in `OdeuSimClient`, and failure-path contract coverage |
| No direct kernel imports, persistent browser state, or prototype control-surface widening ship in this slice | required | `pass` | route-local `apps/web/src/app/odeu-sim/*`, contract import-ban test, and absence of reset/step/state, sliders, network graph, or event-trace surfaces |
| Deterministic route smoke covers the released route and bounded web surface | required | `pass` | `apps/web/tests/routes.smoke.test.mjs` including `/odeu-sim` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v126_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v126/evidence_inputs/metric_key_continuity_assertion_v126.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v126/evidence_inputs/runtime_observability_comparison_v126.json` |

## Stop-Gate Summary

```json
{
  "schema": "v126_closeout_stop_gate_summary@1",
  "arc": "vNext+126",
  "target_path": "V51-C",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v125": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 119,
  "runtime_observability_delta_ms": -24
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v125_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v126_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+125","current_arc":"vNext+126","baseline_source":"artifacts/stop_gate/report_v125_closeout.md","current_source":"artifacts/stop_gate/report_v126_closeout.md","baseline_elapsed_ms":143,"current_elapsed_ms":119,"delta_ms":-24,"notes":"v126 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V51-C ODEU simulation web lane: one bounded /odeu-sim browser route over the released V51-B POST /odeu-sim/run API, idle-first defaults with user-triggered run only, exact API-to-UI status mapping with loading and idle added locally, full released config_snapshot and current_metric carriage plus exact three-key lane summary and sparse observed-only action counts, response_hash preservation in the bounded view model, route smoke and contract checks for the released route shape, hardened no-kernel-import enforcement inside apps/web, and no reset/step/state controls, override sliders, persistent browser state, or prototype static-surface widening."}
```

## V51C ODEU Sim Web Evidence

```json
{"schema":"v51c_odeu_sim_web_evidence@1","evidence_input_path":"artifacts/agent_harness/v126/evidence_inputs/v51c_odeu_sim_web_evidence_v126.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS126.md#v126-continuation-contract-machine-checkable","merged_pr":"#348","merge_commit":"db17dadcde902abed740e63a82cc4f9b430d1fd5","implementation_packages":["adeu_odeu_sim","adeu_api","adeu-web"],"adeu_web_root":"apps/web","odeu_sim_page_source_path":"apps/web/src/app/odeu-sim/page.tsx","odeu_sim_client_source_path":"apps/web/src/app/odeu-sim/odeu-sim-client.tsx","odeu_sim_view_model_source_path":"apps/web/src/app/odeu-sim/view-model.ts","odeu_sim_styles_source_path":"apps/web/src/app/odeu-sim/page.module.css","api_base_helper_path":"apps/web/src/app/lib/api-base.ts","route_contract_test_path":"apps/web/tests/odeu-sim-contract.test.ts","route_smoke_test_path":"apps/web/tests/routes.smoke.test.mjs","released_api_fixture_root":"apps/api/tests/fixtures/v51b","released_api_route":"POST /odeu-sim/run","browser_route_path":"/odeu-sim","canonical_replay_seed":7,"canonical_replay_horizon":25,"initial_interaction_law":"idle_first_render_with_defaults_prefilled_and_user_triggered_run_only","response_hash_preserved":true,"no_kernel_import_boundary_enforced":true,"metric_key_continuity_assertion_path":"artifacts/agent_harness/v126/evidence_inputs/metric_key_continuity_assertion_v126.json","runtime_observability_comparison_path":"artifacts/agent_harness/v126/evidence_inputs/runtime_observability_comparison_v126.json","runtime_event_stream_path":"artifacts/agent_harness/v126/runtime/evidence/local/urm_events.ndjson","notes":"v126 evidence pins the released V51-C ODEU simulation browser lane on main: one repo-owned Next.js route under apps/web over the released V51-B API only, idle-first defaults with user-triggered run, direct API request-status carriage into bounded route_status with loading and idle added locally, full released config_snapshot and current_metric payload preservation, exact three-key lane summary, sparse observed-only action counts, explicit fail-closed invalid-request and kernel-mismatch banners, response_hash carriage in the bounded view model, route smoke coverage for /odeu-sim, contract checks for direct status mapping and no direct adeu_odeu_sim imports under apps/web/src/app/odeu-sim, and no reset/step/state controls, override sliders, network graph, event trace, persistent browser state, or prototype static-surface widening."}
```

## Recommendation (Post v126)

- gate decision:
  - `V51C_ODEU_SIM_WEB_COMPLETE_ON_MAIN`
  - `V51_ODEU_SIM_FAMILY_COMPLETE_ON_MAIN`
- rationale:
  - `v126` closes the bounded `V51-C` browser seam on `main` by shipping the first
    repo-owned `apps/web` route over the released `V51-B` API, without promoting the
    imported sandbox UI into live authority.
  - the shipped slice remains narrow and subordinate: one `/odeu-sim` route, idle
    defaults with user-triggered run only, exact API-to-UI status mapping, full
    released `config_snapshot` and `current_metric` carriage, exact three-key
    `lane_summary`, sparse observed-only `action_counts`, typed fail-closed banners,
    and no reset/step/state controls, network graph, event trace, or persistent
    browser state.
  - review hardening landed in the release rather than staying in commentary: the
    idle panel now renders only in true idle posture, repo-root discovery in the web
    contract test fails closed, and the no-kernel-import matcher now catches
    side-effect and subpath imports.
  - the imported sandbox bundle remains support-only and non-precedent; the release
    re-authors the live browser consumer in repo-owned Next.js paths rather than
    copying the prototype static surface wholesale.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`-24 ms` vs `v125`
    baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v34.md` should now be read with `V51-A` through
    `V51-C` closed on `main` and no further internal `V51` path selected.
