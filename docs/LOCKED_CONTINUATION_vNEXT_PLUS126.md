# Locked Continuation vNext+126

Status: `V51-C` implementation contract.

## V126 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v51c_odeu_sim_ui_contract@1",
  "target_arc": "vNext+126",
  "target_path": "V51-C",
  "target_scope": "bounded_browser_ui_consumer_over_released_v51a_kernel_and_released_v51b_api",
  "implementation_packages": [
    "adeu_odeu_sim",
    "adeu_api",
    "adeu-web"
  ],
  "governing_released_stack": "V51-A_kernel_plus_V51-B_api_on_main",
  "source_intake_bundle": "examples/external_prototypes/odeu-sandbox-app",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "selected_schema_ids": [
    "adeu_odeu_run_view_config@1",
    "adeu_odeu_run_view_model@1"
  ],
  "admitted_route_surface": [
    "/odeu-sim"
  ],
  "released_v51b_api_route_required": "POST /odeu-sim/run",
  "released_v51b_output_mode_required": "summary_only_json",
  "released_v51b_scenarios_only": [
    "healthy_baseline",
    "weak_d"
  ],
  "admitted_ui_inputs_only": [
    "scenario_name",
    "seed",
    "steps"
  ],
  "default_scenario_name": "healthy_baseline",
  "default_seed": 7,
  "default_steps": 25,
  "initial_interaction_law": "idle_first_render_with_defaults_prefilled_and_user_triggered_run_only",
  "seed_minimum": 0,
  "steps_maximum": 25,
  "direct_kernel_import_in_web_forbidden": true,
  "persistent_client_state_forbidden": true,
  "prototype_stepwise_controls_forbidden": true,
  "prototype_parameter_override_controls_forbidden": true,
  "prototype_network_graph_and_event_trace_surfaces_forbidden": true,
  "api_contract_semantics_reinterpretation_forbidden": true,
  "route_status_vocabulary_frozen": [
    "idle",
    "loading",
    "completed_clean",
    "fail_closed_invalid_request",
    "fail_closed_kernel_mismatch"
  ],
  "route_status_mapping_law": {
    "before_request": "idle",
    "in_flight_request": "loading",
    "api_completed_clean": "completed_clean",
    "api_fail_closed_invalid_request": "fail_closed_invalid_request",
    "api_fail_closed_kernel_mismatch": "fail_closed_kernel_mismatch"
  },
  "rendered_sections_required": [
    "meta",
    "config_snapshot",
    "current_metric",
    "lane_summary",
    "action_counts",
    "event_record_count",
    "evidence_record_count",
    "sanction_event_count",
    "failure_banner"
  ],
  "config_snapshot_projection_posture": "full_released_scenario_config_payload",
  "current_metric_projection_posture": "full_released_metric_point_payload",
  "lane_summary_projection_shape": [
    "mean_legitimacy_belief",
    "mean_uncertainty",
    "mean_resources"
  ],
  "action_counts_projection_posture": "sparse_sorted_dict_of_observed_action_types_only",
  "deterministic_route_smoke_required": true,
  "minimal_interaction_suite_required": true,
  "closeout_artifacts_required": [
    "artifacts/quality_dashboard_v126_closeout.json",
    "artifacts/stop_gate/metrics_v126_closeout.json",
    "artifacts/stop_gate/report_v126_closeout.md"
  ]
}
```

## Objective

Release the bounded `V51-C` browser seam by adding one repo-owned `apps/web` route
over the released `V51-B` API only, while keeping the web layer strictly subordinate
to the released kernel/API contracts and refusing the prototype's stepwise controls,
override sliders, network graph, and event-trace sprawl.

## Required Deliverables

The first `V51-C` release should add exactly these live implementation surfaces:

- `apps/web/src/app/odeu-sim/page.tsx`
- one route-local helper or view-model module under:
  - `apps/web/src/app/odeu-sim/`
- one route-local style/module surface under:
  - `apps/web/src/app/odeu-sim/`
- route smoke coverage in:
  - `apps/web/tests/routes.smoke.test.mjs`
- one minimal interaction test under:
  - `apps/web/tests/`

This slice should not add:

- a broad `apps/web` route retrofit
- persistent browser state or storage adapters
- any direct import of prototype static assets into live route paths

## Frozen Implementation Decisions

1. Ownership

- `packages/adeu_odeu_sim` and `apps/api` remain the sole owners of simulation and API
  semantics.
- `apps/web` is a consumer only in this slice.
- the imported prototype remains shaping evidence only.

2. Consumer posture

- ship exactly one bounded route:
  - `/odeu-sim`
- the route must consume the released `POST /odeu-sim/run` API only
- the route must use `apps/web/src/app/lib/api-base.ts` or one route-local helper
  layered over that released API base
- the route must not import kernel helpers or simulation models directly into
  `apps/web`
- the route must remain non-persistent:
  - no `localStorage`
  - no `sessionStorage`
  - no long-lived browser session model
  - no polling or websocket loop

3. Input posture

- admit exactly the released API inputs:
  - `scenario_name`
  - `seed`
  - `steps`
- keep `output_mode` fixed to the released `summary_only_json` posture and do not
  surface it as a user-controlled toggle
- admit only the released starter scenarios:
  - `healthy_baseline`
  - `weak_d`
- require non-negative `seed` and `steps` bounded to `1..25`
- default the first route render to:
  - `healthy_baseline`
  - `seed = 7`
  - `steps = 25`
- initial render must remain:
  - `idle`
  - defaults prefilled only
  - user-triggered run only
- the route must not auto-run the default scenario on first page load

4. Rendering posture

- render released `V51-B` response facts only:
  - meta
  - config snapshot
  - full current metric payload
  - exact three-key lane summary
  - sparse observed-only action counts
  - event/evidence/sanction counts
- allow one bounded failure banner for:
  - `fail_closed_invalid_request`
  - `fail_closed_kernel_mismatch`
- preserve released `response_hash` in the bounded view model rather than dropping it
- do not mint new semantic judgments, regime meanings, or lane interpretations in the
  renderer
- keep the UI summary posture deterministic over the same released response payload

5. Status-mapping posture

- map route status exactly as follows:
  - before any request:
    - `idle`
  - request in flight:
    - `loading`
  - completed API response:
    - carry `completed_clean` through unchanged
    - carry `fail_closed_invalid_request` through unchanged
    - carry `fail_closed_kernel_mismatch` through unchanged

6. Forbidden widening

- no reset/step/start/pause controls
- no parameter slider or override grid
- no network graph visualization
- no public-report / evidence / action trace panels
- no event-log streaming surface
- no persistent browser state
- no product-wide navigation or broader app entitlement

## Bounded Starter Vocabularies

The first `V51-C` release should freeze:

- `route_status`:
  - `idle`
  - `loading`
  - `completed_clean`
  - `fail_closed_invalid_request`
  - `fail_closed_kernel_mismatch`
- admitted scenario names:
  - `healthy_baseline`
  - `weak_d`
- lane-summary keys:
  - `mean_legitimacy_belief`
  - `mean_uncertainty`
  - `mean_resources`

## Selected Schema Anchors

The first `V51-C` release should freeze the following contract anchors.

### `adeu_odeu_run_view_config@1`

- `schema`
- `route_id`
- `scenario_name`
- `seed`
- `steps`
- fixed `output_mode`

### `adeu_odeu_run_view_model@1`

- `schema`
- `route_status`
- `request_ref`
- `kernel_contract_ref`
- `response_hash`
- `meta`
- `config_snapshot`
- `current_metric`
- `lane_summary`
- `action_counts`
- `event_record_count`
- `evidence_record_count`
- `sanction_event_count`
- `failure_code`

## Accepted And Reject Fixtures

The first `V51-C` release should include:

- accepted route-smoke fixture:
  - `/odeu-sim` renders on the bounded route
- accepted summary render fixture:
  - `healthy_baseline`
- accepted summary render fixture:
  - `weak_d`
- typed failure render fixture:
  - `fail_closed_invalid_request`
- typed failure render fixture:
  - `fail_closed_kernel_mismatch`
- typed reject fixture:
  - reset/step/start/pause controls absent
- typed reject fixture:
  - parameter override sliders absent

## Acceptance

`V51-C` is acceptable only if:

- the new route renders and passes route-smoke coverage;
- the route consumes the released `V51-B` API only and does not import the kernel into
  `apps/web`;
- `config_snapshot` and `current_metric` remain the full released API objects rather
  than narrowed local projections;
- `response_hash` is retained in the emitted view-model surface;
- no direct import from `adeu_odeu_sim` appears anywhere under
  `apps/web/src/app/odeu-sim/`;
- the same mocked released response produces the same rendered summary markers on
  repeat runs;
- success and fail-closed UI postures are both rendered explicitly;
- stepwise sandbox controls, override sliders, network graph, event trace, and
  persistent client state remain absent.

## Local Gate

Before merge, the bounded `V51-C` slice should pass:

- `make check`
- relevant web-only focused checks while iterating, such as:
  - `npm --prefix apps/web run test:smoke`
  - one targeted minimal interaction test under `apps/web/tests/`

## Hard Constraints

- no direct import of the prototype `static/index.html`, `static/app.js`, or
  `static/style.css` into live `apps/web` route paths
- no direct import from `adeu_odeu_sim` into `apps/web/src/app/odeu-sim/`
- no browser entitlement to run the kernel without the released API seam
- no route-local mutation of the released `V51-B` request/response law
- no persistence, streaming, or full sandbox-control posture in this slice

## PR Shape

The first `V51-C` implementation PR should stay bounded to:

- `apps/web/src/app/odeu-sim/`
- minimal `apps/web` route registration and support wiring
- targeted web tests
- deterministic fixtures only if needed for the bounded route

It should not widen into:

- unrelated `apps/web` routes
- `apps/api` contract changes
- `packages/adeu_odeu_sim` kernel changes
- persistent storage or browser session infrastructure

## Non-Goals

This slice does not authorize:

- the prototype's full sandbox-control surface
- stepwise simulation playback
- scenario parameter override sliders
- network graph or trace-heavy visualization
- product-wide simulation workbench status
- reopening `V51-A` kernel law or `V51-B` API law
