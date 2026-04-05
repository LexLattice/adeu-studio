# Locked Continuation vNext+130

Status: `V52-D` implementation contract.

## V130 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v52d_paper_semantic_advanced_visualization_contract@1",
  "target_arc": "vNext+130",
  "target_path": "V52-D",
  "target_scope": "bounded_repo_owned_spatial_morphic_visualization_extension_over_released_v52a_v52b_surfaces",
  "implementation_packages": [
    "adeu_paper_semantics",
    "adeu-web"
  ],
  "governing_released_stack": "V49_semantic_forms_plus_V52-A_paper_semantics_plus_V52-B_mock_workbench_plus_V52-C_worker_bridge_on_main",
  "governing_stack_consumption_mode": "released_v52a_artifact_consumption_and_v52b_route_local_view_extension_only_v52c_bridge_not_browser_authoritative_no_parallel_paper_substrate",
  "source_intake_bundle": "examples/external_prototypes/adeu-paper-semantic-workbench-poc",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "selected_schema_ids": [
    "adeu_paper_semantic_visualization_view_config@1",
    "adeu_paper_semantic_spatial_scene_model@1",
    "adeu_paper_semantic_visualization_view_model@1"
  ],
  "admitted_route_surface": [
    "/papers/semantic-workbench"
  ],
  "released_v52a_artifact_required": true,
  "released_v52b_route_context_required": true,
  "released_v52c_bridge_browser_trigger_forbidden": true,
  "spatial_surface_route_local_derived": true,
  "released_projection_surfaces_authoritative_for_ordering_anchors": [
    "artifact",
    "local"
  ],
  "released_projection_surface_spatial_required": false,
  "selected_surface_vocabulary_frozen": [
    "artifact",
    "local",
    "spatial"
  ],
  "visible_lane_vocabulary_frozen": [
    "O",
    "E",
    "D",
    "U"
  ],
  "spatial_node_kind_vocabulary_frozen": [
    "claim",
    "lane_fragment"
  ],
  "spatial_edge_kind_vocabulary_frozen": [
    "claim_to_fragment",
    "inference_bridge"
  ],
  "initial_route_status": "ready_clean",
  "initial_surface_posture": "artifact_default_spatial_user_selected_only",
  "morphic_transition_posture_frozen": "same_object_route_local_transition_only",
  "three_d_posture_frozen": "spatial_surface_only_artifact_and_local_remain_2d",
  "fail_closed_invalid_fixture_stack_meaning_frozen": "malformed_released_artifact_or_invalid_route_local_spatial_projection_or_unsupported_scene_vocabulary",
  "spatial_layout_law_frozen": "deterministic_lane_columns_and_claim_order_rows_no_physics_no_randomness",
  "api_fetch_forbidden": true,
  "live_worker_browser_trigger_forbidden": true,
  "new_dedicated_api_route_forbidden": true,
  "prototype_spatial_scene_import_forbidden": true,
  "renderer_semantic_reinterpretation_forbidden": true,
  "view_hash_subject": [
    "route_status",
    "selected_sample_artifact_ref",
    "artifact_ref",
    "selected_surface",
    "focus_claim_id",
    "visible_lane_ids",
    "ordered_claim_ids",
    "scene_hash",
    "failure_code"
  ],
  "deterministic_route_smoke_required": true,
  "deterministic_spatial_projection_required": true,
  "closeout_artifacts_required": [
    "artifacts/quality_dashboard_v130_closeout.json",
    "artifacts/stop_gate/metrics_v130_closeout.json",
    "artifacts/stop_gate/report_v130_closeout.md"
  ]
}
```

## Objective

Release the bounded `V52-D` advanced-visualization seam by extending the existing
`/papers/semantic-workbench` route with one route-local spatial-lane scene and one
same-object morphic transition posture over released paper-semantic artifacts only.

This slice must make explicit:

- one bounded route surface only:
  - `/papers/semantic-workbench`
- one advanced surface addition only:
  - `spatial`
- one explicit derived-surface posture only:
  - `spatial` is route-local only
  - released `artifact` / `local` projections remain authoritative ordering anchors
  - no released `projection.surface = spatial` is required
- one route-local typed scene-model posture only:
  - claims
  - lane fragments
  - inference bridges
- one same-object morphic transition posture only:
  - `artifact`
  - `local`
  - `spatial`
- one explicit 3D restraint posture only:
  - spatial surface only
  - artifact/local remain 2D and operator-legible
- one fail-closed posture for:
  - malformed released artifact inputs
  - invalid spatial-projection mismatch
  - unsupported scene vocabularies.

This slice is visualization-first and still bounded. It does not authorize new
semantic authority, browser-triggered worker execution, API fetch widening, prototype
scene import, or broader product-surface redesign.

## Required Deliverables

The first `V52-D` release should add exactly these live implementation surfaces:

- `apps/web/src/app/papers/semantic-workbench/spatial-lane-scene.tsx`
- one route-local projection helper surface under:
  - `apps/web/src/app/papers/semantic-workbench/`
- bounded updates to existing route-local sources under:
  - `apps/web/src/app/papers/semantic-workbench/`
- route smoke coverage in:
  - `apps/web/tests/routes.smoke.test.mjs`
- one bounded route-contract / visualization test under:
  - `apps/web/tests/`

This slice should not add:

- `apps/api` route work;
- browser-triggered calls into `paper.run_semantic_decomposition`;
- new `packages/urm_domain_paper` or `packages/urm_domain_adeu` ownership changes;
- prototype overlay files copied wholesale into live route paths;
- broader `/papers` navigation redesign or product-surface retrofits.

## Frozen Implementation Decisions

1. Ownership

- `packages/adeu_paper_semantics` remains the sole owner of paper semantic authority.
- `apps/web` remains a consumer only in this slice.
- the already released `V52-C` bridge remains non-authoritative for browser triggering
  in this slice.
- the imported prototype remains shaping evidence only.

2. Route posture

- ship exactly one bounded route:
  - `/papers/semantic-workbench`
- extend the released route rather than creating a second paper-semantics route
- keep initial render:
  - `ready_clean`
  - committed abstract artifact selected first
  - `artifact` surface selected first
- permit `spatial` only as a user-selected local surface transition
- do not add `fetch`, `apiBase()`, worker-trigger calls, or resident session state

3. Scene projection posture

- derive spatial scene data only from released `adeu_paper_semantic_artifact@1`
  fields already consumed by `V52-B`
- treat `spatial` as a route-local derived surface only:
  - do not require released `projection.surface = spatial`
  - preserve released `artifact` / `local` projections as authoritative ordering
    anchors when they exist
- admit exactly these node kinds:
  - `claim`
  - `lane_fragment`
- admit exactly these edge kinds:
  - `claim_to_fragment`
  - `inference_bridge`
- use released `projection.claim_order` when present
- use released `projection.lane_order` when present, otherwise fallback to frozen
  `O/E/D/U`
- do not synthesize:
  - new claims
  - new diagnostics
  - new inference-bridge meanings
  - new semantic identifiers
- scene layout must be deterministic:
  - lane columns derived from released lane order
  - claim/lane-fragment row order derived from released `projection.claim_order`
    with claim-id fallback only
  - no physics simulation
  - no randomness
  - no implementation-defined force layout

4. Morphic and interaction posture

- transitions across `artifact`, `local`, and `spatial` must remain same-object,
  route-local transitions only
- the scene may add only bounded presentation helpers:
  - spatial node positions
  - bounded camera preset selection
  - deterministic scene ordering
- no local storage, session memory, or route-param persistence is selected

5. Forbidden widening

- no live worker/browser trigger wiring
- no new dedicated API route
- no upload or pasted-source execution surface
- no prototype `spatial-lane-scene.tsx` import into live code
- no new semantic authority in the renderer
- no broader product/navigation redesign

6. Determinism and hash posture

- repeated scene projection over the same released artifact and the same local view
  config must produce byte-identical route-local scene-model output
- `view_hash` must be derived only from the frozen `view_hash_subject`
- `scene_hash` must be derived only from released artifact identities, released claim /
  lane ordering anchors, and the route-local selected surface/focus/lane state
- `fail_closed_invalid_fixture_stack` must cover exactly:
  - malformed released artifact payload
  - invalid route-local spatial projection mismatch
  - unsupported node/edge vocabulary
  - missing released ordering anchors required by the deterministic scene law
- invalid scene-projection mismatch must fail closed rather than silently falling back

## Bounded Starter Vocabularies

The first `V52-D` release should freeze:

- `route_status`:
  - `ready_clean`
  - `fail_closed_invalid_fixture_stack`
- `selected_surface`:
  - `artifact`
  - `local`
  - `spatial`
- `visible_lane_ids`:
  - `O`
  - `E`
  - `D`
  - `U`
- `node_kind`:
  - `claim`
  - `lane_fragment`
- `edge_kind`:
  - `claim_to_fragment`
  - `inference_bridge`

Out-of-scope constructs in this slice are:

- live worker execution from the browser
- API-backed refresh loops
- freeform text entry or upload processing
- full-paper widening beyond released abstract/paragraph artifacts
- imported prototype scene modules as live authority
- renderer-minted semantic claims or diagnostics

## Selected Schema Anchors

The first `V52-D` release should freeze these route-local view-config anchors:

- `adeu_paper_semantic_visualization_view_config@1`
  - `route_id`
  - `selected_sample_artifact_ref`
  - `selected_surface`
  - `focus_claim_id`
  - `visible_lane_ids`

The first `V52-D` release should freeze these route-local scene-model anchors:

- `adeu_paper_semantic_spatial_scene_model@1`
  - `artifact_ref`
  - `semantic_hash`
  - `recommended_focus_claim_id`
  - `node_order`
  - `nodes`
  - `edges`
  - `scene_hash`

- `adeu_paper_semantic_spatial_scene_node@1`
  - `node_id`
  - `node_kind`
  - `claim_id`
  - `lane_id`
  - `label`
  - `position`

- `adeu_paper_semantic_spatial_scene_edge@1`
  - `edge_id`
  - `edge_kind`
  - `from_node_id`
  - `to_node_id`
  - `bridge_id`

The first `V52-D` release should freeze these route-local view-model anchors:

- `adeu_paper_semantic_visualization_view_model@1`
  - `route_status`
  - `route_contract_ref`
  - `selected_sample_artifact_ref`
  - `available_sample_artifact_refs`
  - `artifact_ref`
  - `artifact`
  - `selected_surface`
  - `focus_claim_id`
  - `visible_lane_ids`
  - `semantic_hash`
  - `identity_field_names`
  - `projection_field_names`
  - `ordered_claim_ids`
  - `spatial_scene`
  - `view_hash`
  - `failure_code`

## Fixtures

Accepted fixtures for this slice should include:

- one abstract-artifact spatial projection fixture
- one paragraph-artifact spatial projection fixture
- one deterministic focus-claim transition fixture

Reject fixtures for this slice should include:

- missing lane-fragment target required by the scene projection
- unsupported `node_kind` or `edge_kind`
- invalid route-local spatial projection mismatch

## Acceptance Criteria

The slice is acceptable when:

- the shipped route remains exactly `/papers/semantic-workbench`
- the spatial scene is derived only from released `V52-A` artifact data already
  admitted through `V52-B`
- `spatial` is implemented as a route-local derived surface only and does not require
  a released `projection.surface = spatial`
- `artifact` remains the default initial surface and `spatial` is user-selected only
- no `fetch`, live-worker import, or browser trigger path is added
- no prototype spatial-scene module is imported into live route code
- deterministic route smoke plus bounded visualization contract tests pass

## Local Gate

- docs-only starter validation:
  - `make arc-start-check ARC=130`
- once implementation starts:
  - run the relevant `apps/web` lint/tests/build for the bounded `V52-D`
    visualization surface.
