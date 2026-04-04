# Locked Continuation vNext+125

Status: `V51-B` implementation contract.

## V125 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v51b_odeu_sim_api_contract@1",
  "target_arc": "vNext+125",
  "target_path": "V51-B",
  "target_scope": "bounded_non_persistent_odeu_scenario_execution_api_consumer_over_released_v51a_kernel",
  "implementation_packages": [
    "adeu_odeu_sim",
    "adeu_api"
  ],
  "governing_released_stack": "V51-A_kernel_on_main",
  "source_intake_bundle": "examples/external_prototypes/odeu-sandbox-app",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "api_route_module_required": true,
  "selected_schema_ids": [
    "adeu_odeu_run_request@1",
    "adeu_odeu_run_summary@1",
    "adeu_odeu_run_response@1"
  ],
  "admitted_route_surface": [
    "POST /odeu-sim/run"
  ],
  "admitted_output_modes": [
    "summary_only_json"
  ],
  "released_v51a_kernel_required": true,
  "released_v51a_scenarios_only": [
    "healthy_baseline",
    "weak_d"
  ],
  "persistent_session_state_forbidden": true,
  "prototype_reset_step_state_surface_forbidden": true,
  "browser_ui_and_static_surface_forbidden": true,
  "kernel_semantics_redefinition_forbidden": true,
  "response_projection_semantics_reinterpretation_forbidden": true,
  "admitted_request_fields_only": [
    "scenario_name",
    "seed",
    "steps",
    "output_mode"
  ],
  "released_stateless_kernel_helper_required": "run_canonical_scenario",
  "released_summary_helpers_required": [
    "summarize_lane_state",
    "summarize_action_counts"
  ],
  "scenario_overrides_forbidden": true,
  "seed_minimum": 0,
  "steps_maximum": 25,
  "request_status_vocabulary_frozen": [
    "completed_clean",
    "fail_closed_invalid_request",
    "fail_closed_kernel_mismatch"
  ],
  "lane_summary_projection_shape": [
    "mean_legitimacy_belief",
    "mean_uncertainty",
    "mean_resources"
  ],
  "action_counts_projection_posture": "sparse_sorted_dict_of_observed_action_types_only",
  "current_metric_projection_posture": "full_released_adeu_odeu_metric_point_payload",
  "request_hash_subject": [
    "scenario_name",
    "seed",
    "steps",
    "output_mode"
  ],
  "response_hash_subject": [
    "request_status",
    "request_ref",
    "kernel_contract_ref",
    "run_summary",
    "failure_code"
  ],
  "deterministic_route_replay_required": true,
  "closeout_artifacts_required": [
    "artifacts/quality_dashboard_v125_closeout.json",
    "artifacts/stop_gate/metrics_v125_closeout.json",
    "artifacts/stop_gate/report_v125_closeout.md"
  ]
}
```

## Objective

Release the bounded `V51-B` API seam by adding one repo-owned non-persistent
scenario-execution route over the released `V51-A` kernel, while keeping the route
strictly subordinate to the released kernel contracts and refusing the prototype's
mutable reset/step/state surface.

## Frozen Implementation Decisions

1. Ownership

- `packages/adeu_odeu_sim` remains the sole owner of simulation semantics.
- `apps/api` is a consumer only in this slice.
- the imported prototype remains shaping evidence only.

2. Route posture

- ship exactly one bounded route:
  - `POST /odeu-sim/run`
- the route is stateless and non-persistent:
  - no `app.state.sim`
  - no reset/step/state trilogy
  - no session token
- the route must consume the released stateless kernel helper path only:
  - `run_canonical_scenario(...)`
- released summary projection helpers must remain explicit:
  - `summarize_lane_state(...)`
  - `summarize_action_counts(...)`
- the route must not instantiate or retain a long-lived `ODEUSimulation` object

3. Request posture

- accept exactly one released-kernel scenario name:
  - `healthy_baseline`
  - `weak_d`
- accept one explicit `seed`
- `seed` must be a non-negative integer
- accept one explicit `steps`
- accept one output mode only:
  - `summary_only_json`
- forbid scenario override dictionaries, mutable patch inputs, or ambient config repair

4. Response posture

- emit one summary-only JSON response over the released kernel run
- project released kernel facts only:
  - meta
  - config snapshot
  - current metric
  - lane summary
  - action counts
  - event/evidence/sanction counts
- do not emit a second semantic layer or reinterpret regime labels, lane contracts, or
  deontic posture in the route
- `current_metric` must be the full released `adeu_odeu_metric_point@1` payload
- `lane_summary` must be exactly:
  - `mean_legitimacy_belief`
  - `mean_uncertainty`
  - `mean_resources`
- `action_counts` must remain the sparse sorted dict of observed action types only,
  with zero-count action types omitted
- `request_hash` and `response_hash` must be derived only from their frozen hash
  subjects and not from ambient route metadata

5. Forbidden widening

- no browser/UI or static-file surface
- no persistent storage
- no streaming / websocket surface
- no repo-wide orchestration surface
- no redefinition of kernel semantics in route code

## Bounded Starter Vocabularies

The first `V51-B` release should freeze:

- `request_status`:
  - `completed_clean`
  - `fail_closed_invalid_request`
  - `fail_closed_kernel_mismatch`
- `output_mode`:
  - `summary_only_json`
- admitted scenario names:
  - `healthy_baseline`
  - `weak_d`
- lane-summary keys:
  - `mean_legitimacy_belief`
  - `mean_uncertainty`
  - `mean_resources`

## Selected Schema Anchors

The first `V51-B` release should freeze the following contract anchors.

### `adeu_odeu_run_request@1`

- `schema`
- `scenario_name`
- `seed`
- `steps`
- `output_mode`
- `request_hash`

### `adeu_odeu_run_summary@1`

- `schema`
- `meta`
- `config_snapshot`
- `scenario`
- `seed`
- `turn`
- `current_metric`
- `lane_summary`
- `action_counts`
- `event_record_count`
- `evidence_record_count`
- `sanction_event_count`

### `adeu_odeu_run_response@1`

- `schema`
- `request_status`
- `request_ref`
- `kernel_contract_ref`
- `run_summary` when completed
- `failure_code` when fail closed
- `response_hash`

## Projection And Hash Law

The first `V51-B` release should freeze:

- `current_metric` as the full released `adeu_odeu_metric_point@1` payload
- `lane_summary` as exactly:
  - `mean_legitimacy_belief`
  - `mean_uncertainty`
  - `mean_resources`
- `action_counts` as the sparse sorted dict returned by the released helper, with
  zero-count action types omitted
- `request_hash` over exactly:
  - `scenario_name`
  - `seed`
  - `steps`
  - `output_mode`
- `response_hash` over exactly:
  - `request_status`
  - `request_ref`
  - `kernel_contract_ref`
  - `run_summary`
  - `failure_code`

## Accepted And Reject Fixtures

The first `V51-B` release should include:

- accepted deterministic response fixture:
  - `healthy_baseline`
- accepted deterministic response fixture:
  - `weak_d`
- typed invalid-request fixture:
  - unsupported scenario name
- typed invalid-request fixture:
  - negative seed
- typed invalid-request fixture:
  - `steps < 1` or `steps > 25`
- typed kernel-mismatch fixture:
  - route/kernel stack incompatibility
- typed reject fixture:
  - attempted scenario overrides or mutable session fields

## Required Deliverables

The first `V51-B` release should add:

- `apps/api/src/adeu_api/odeu_sim.py` or one equivalent bounded route module
- route-local request/response helpers only if needed for the bounded surface
- targeted API tests under `apps/api/tests/`
- committed `v51b` fixtures under `apps/api/fixtures/` or equivalent bounded fixture root

It should not add:

- `apps/web` UI work
- persistent session/state management
- static-file serving for the sandbox UI
- broader product routing

## Acceptance

The first `V51-B` release should be accepted only if:

- the route consumes the released `V51-A` kernel unchanged rather than re-implementing
  engine behavior in `apps/api`
- the route uses `run_canonical_scenario(...)` and the released summary helpers rather
  than a long-lived mutable simulation object
- same request over same released kernel yields byte-identical response fixtures
- unsupported scenario names, negative seeds, and invalid step counts fail closed with
  typed invalid-request results
- stack mismatch against the released kernel fails closed with typed
  kernel-mismatch results
- route code does not synthesize semantic summaries beyond the released kernel output
- no persistent reset/step/state route surface ships in this slice

## Local Gate

Before merge, the implementation should pass:

- relevant API lint
- targeted `apps/api` tests for the new bounded route
- targeted `packages/adeu_odeu_sim` regression coverage needed by the route seam
