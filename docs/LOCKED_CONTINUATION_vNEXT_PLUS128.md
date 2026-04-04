# Locked Continuation vNext+128

Status: `V52-B` implementation contract.

## V128 Continuation Contract (Machine-Checkable)

```json
{
  "schema": "v52b_paper_semantic_mock_workbench_contract@1",
  "target_arc": "vNext+128",
  "target_path": "V52-B",
  "target_scope": "bounded_repo_owned_read_only_mock_workbench_route_over_released_v52a_artifacts",
  "implementation_packages": [
    "adeu_paper_semantics",
    "adeu-web"
  ],
  "governing_released_stack": "V49_semantic_forms_plus_V52-A_paper_semantics_on_main",
  "governing_stack_consumption_mode": "released_v52a_artifact_consumption_only_v49_not_reopened_no_parallel_paper_substrate",
  "source_intake_bundle": "examples/external_prototypes/adeu-paper-semantic-workbench-poc",
  "imported_bundle_authority_status": "support_only_non_precedent",
  "selected_schema_ids": [
    "adeu_paper_semantic_workbench_view_config@1",
    "adeu_paper_semantic_workbench_view_model@1"
  ],
  "admitted_route_surface": [
    "/papers/semantic-workbench"
  ],
  "released_v52a_artifact_required": true,
  "released_v52a_route_subordinate_to_package_contracts": true,
  "committed_sample_artifact_paths": [
    "packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_artifact_abstract.json",
    "packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_artifact_paragraph.json"
  ],
  "default_sample_artifact_path": "packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_artifact_abstract.json",
  "initial_route_status": "ready_clean",
  "initial_interaction_law": "ready_on_first_render_with_default_committed_sample_selected_and_user_local_navigation_only",
  "released_v52a_fixture_validation_required_before_render": true,
  "route_status_vocabulary_frozen": [
    "ready_clean",
    "fail_closed_invalid_fixture_stack"
  ],
  "fail_closed_invalid_fixture_stack_meaning_frozen": "malformed_committed_fixture_or_missing_required_v52a_fields_or_invalid_route_view_projection_config",
  "selected_surface_vocabulary_frozen": [
    "artifact",
    "local"
  ],
  "visible_lane_vocabulary_frozen": [
    "O",
    "E",
    "D",
    "U"
  ],
  "claim_ordering_law_frozen": "use_released_projection_claim_order_when_present_else_fallback_to_deterministic_claim_id_order",
  "api_fetch_forbidden": true,
  "live_worker_bridge_forbidden": true,
  "domain_harness_registration_forbidden": true,
  "direct_prototype_overlay_import_forbidden": true,
  "prototype_spatial_scene_forbidden": true,
  "text_entry_or_upload_surface_forbidden": true,
  "renderer_semantic_reinterpretation_forbidden": true,
  "view_hash_subject": [
    "route_status",
    "selected_sample_artifact_ref",
    "artifact_ref",
    "selected_surface",
    "focus_claim_id",
    "visible_lane_ids",
    "ordered_claim_ids",
    "failure_code"
  ],
  "deterministic_route_smoke_required": true,
  "minimal_interaction_suite_required": true,
  "closeout_artifacts_required": [
    "artifacts/quality_dashboard_v128_closeout.json",
    "artifacts/stop_gate/metrics_v128_closeout.json",
    "artifacts/stop_gate/report_v128_closeout.md"
  ]
}
```

## Objective

Release the bounded `V52-B` mock-workbench seam by adding one repo-owned
`/papers/semantic-workbench` browser route that consumes committed released `V52-A`
artifacts only, renders one deterministic read-only workbench projection over those
artifacts, and keeps the browser layer strictly subordinate to the released paper
semantic contract family.

This slice must make explicit:

- one bounded route surface only;
- one committed-sample artifact registry only;
- one read-only view-model layer only;
- one deterministic initial render with a default committed sample only;
- one explicit sample-ref mapping posture only:
  - `selected_sample_artifact_ref` = committed fixture path
  - `artifact_ref` = released artifact identity from consumed `adeu_paper_semantic_artifact@1`
- one bounded rendering posture for:
  - source metadata;
  - source-authority posture;
  - anchored spans;
  - claims;
  - lane fragments;
  - inference bridges;
  - diagnostics;
  - projections;
- one fail-closed posture for:
  - malformed committed sample artifacts;
  - route/view-model projection mismatch;
  - missing required released `V52-A` fields.

This slice is consumer-first and still bounded. It does not authorize live worker
execution, API fetches, domain/harness registration, text-entry processing, advanced
visualization, or direct import of the prototype overlay into live repo paths.

## Required Deliverables

The first `V52-B` release should add exactly these live implementation surfaces:

- `apps/web/src/app/papers/semantic-workbench/page.tsx`
- one route-local client and/or view-model helper surface under:
  - `apps/web/src/app/papers/semantic-workbench/`
- one route-local committed-sample registry/helper under:
  - `apps/web/src/app/papers/semantic-workbench/`
- route smoke coverage in:
  - `apps/web/tests/routes.smoke.test.mjs`
- one bounded route-contract or interaction test under:
  - `apps/web/tests/`

This slice should not add:

- `apps/api` route work;
- `packages/urm_domain_paper` or `packages/urm_domain_adeu` registration work;
- live worker bridge modules;
- spatial scene or advanced visualization modules;
- prototype overlay files copied into live route paths.

## Frozen Implementation Decisions

1. Ownership

- `packages/adeu_paper_semantics` remains the sole owner of paper semantic authority.
- `apps/web` is a consumer only in this slice.
- the imported prototype remains shaping evidence only.

2. Route posture

- ship exactly one bounded route:
  - `/papers/semantic-workbench`
- the route must consume committed released `V52-A` artifacts only
- the route must not call `fetch`, `apiBase()`, or any live worker/domain surface
- the route must not import prototype overlay modules directly into live repo paths
- the route may remain direct-entry and does not require wider `/papers` navigation
  expansion in this slice

3. Sample posture

- admit exactly these committed sample artifacts:
  - `reference_paper_semantic_artifact_abstract.json`
  - `reference_paper_semantic_artifact_paragraph.json`
- validate every committed JSON sample against the released `V52-A`
  `adeu_paper_semantic_artifact@1` shape before any route-local view-model projection
  occurs
- default first render to the committed abstract artifact
- permit only bounded local navigation across the admitted committed samples
- do not admit freeform text entry, uploads, or runtime semantic processing

4. Rendering posture

- preserve the full released `adeu_paper_semantic_artifact@1` payload in route-local
  view construction
- render released artifact facts only:
  - source metadata
  - source-authority posture
  - interpretation-authority posture
  - semantic hash
  - identity field names
  - projection field names
  - anchored spans
  - claims
  - lane fragments
  - inference bridges
  - diagnostics
  - projections
- local route derivation may add only bounded presentation helpers:
  - selected sample ref as committed fixture-path identity
  - artifact ref as released artifact-id identity
  - selected surface
  - focus claim id
  - visible lane ids
  - deterministic claim ordering
- the renderer may not mint a second semantic layer, reinterpret diagnostic meaning,
  or add worker-authority claims

5. Surface and interaction posture

- admitted surface views are exactly:
  - `artifact`
  - `local`
- admitted visible lanes are exactly:
  - `O`
  - `E`
  - `D`
  - `U`
- initial render must be:
  - `ready_clean`
  - default committed sample selected
  - user local navigation only
- no idle/loading/request loop is selected in this slice because the route is backed
  by committed local artifacts only

6. Forbidden widening

- no live worker helper or resident-codex surface
- no API bridge or harness status polling
- no text-entry processing, upload flow, or pasted-source execution surface
- no spatial lane scene, 3D surface, or advanced morphic visualization
- no persistent browser state or local storage
- no direct prototype overlay import into live route code

7. Determinism and hash posture

- repeated route rendering over the same committed sample artifact and the same local
  view config must produce byte-identical view-model output
- `view_hash` must be derived only from the frozen `view_hash_subject`
- deterministic claim ordering must be:
  - released `projection.claim_order` when present on the consumed artifact
  - otherwise deterministic claim-id order only
- `fail_closed_invalid_fixture_stack` must cover exactly:
  - malformed committed fixture payload
  - missing required released `V52-A` fields
  - invalid route-local view/config projection mismatch

## Bounded Starter Vocabularies

The first `V52-B` release should freeze:

- `route_status`:
  - `ready_clean`
  - `fail_closed_invalid_fixture_stack`
- `selected_surface`:
  - `artifact`
  - `local`
- `visible_lane_ids`:
  - `O`
  - `E`
  - `D`
  - `U`
- admitted sample source-artifact kinds:
  - `paper.abstract`
  - `pasted.paragraph`

Out-of-scope constructs in this slice are:

- live worker execution;
- API-backed workbench refresh or fetch loop;
- freeform text entry or upload-driven processing;
- `paper.abstract_digest` or full-paper widening;
- advanced spatial visualization;
- silent semantic reinterpretation in the renderer.

## Selected Schema Anchors

The first `V52-B` release should freeze the following contract anchors.

### Consumed `adeu_paper_semantic_artifact@1`

- `artifact_id`
- `source`
- `spans`
- `claims`
- `lane_fragments`
- `inference_bridges`
- `diagnostics`
- `projections`
- `source_authority_posture`
- `interpretation_authority_posture`
- `semantic_identity_mode`
- `identity_field_names`
- `projection_field_names`
- `semantic_hash`

### `adeu_paper_semantic_workbench_view_config@1`

- `schema`
- `route_id`
- `selected_sample_artifact_ref`
- `selected_surface`
- `focus_claim_id`
- `visible_lane_ids`

### `adeu_paper_semantic_workbench_view_model@1`

- `schema`
- `route_status`
- `route_contract_ref`
- `selected_sample_artifact_ref`
- `available_sample_artifact_refs`
- `artifact_ref`
- `artifact`
- `semantic_hash`
- `identity_field_names`
- `projection_field_names`
- `selected_surface`
- `focus_claim_id`
- `visible_lane_ids`
- `ordered_claim_ids`
- `failure_code`
- `view_hash`

## Accepted And Reject Fixtures

The first `V52-B` release should include:

- accepted route-smoke fixture:
  - `/papers/semantic-workbench` renders
- accepted default-sample fixture:
  - committed abstract artifact renders as `ready_clean`
- accepted sample-switch fixture:
  - committed paragraph artifact renders deterministically
- accepted validation fixture:
  - committed JSON sample is validated against released `PaperSemanticArtifact` before
    rendering
- accepted local-view fixture:
  - toggling `artifact` / `local` surface does not alter the consumed released
    artifact payload
- typed reject fixture:
  - malformed committed sample artifact
- typed reject fixture:
  - attempted API/live-worker dependency under
    `apps/web/src/app/papers/semantic-workbench`
- typed reject fixture:
  - attempted spatial-scene or advanced-visualization import in this slice

## Acceptance

Accept `V52-B` when:

- the route consumes only committed released `V52-A` artifacts;
- each committed sample artifact is explicitly validated against the released
  `adeu_paper_semantic_artifact@1` shape before rendering;
- the default first render selects the committed abstract artifact and reaches
  `ready_clean`;
- the route renders released paper-semantic contract fields including
  `semantic_hash`, `identity_field_names`, and `projection_field_names`, plus bounded
  local ordering/focus helpers;
- no direct API/live-worker/domain bridge is present under the route surface;
- no direct prototype overlay modules are imported into the live route;
- route smoke and bounded interaction/contract tests pass deterministically.

Do not accept `V52-B` if:

- the route becomes a second owner of paper semantic law;
- the route fetches live worker or API data;
- the route admits freeform text input or upload-driven semantic processing;
- the route imports the prototype spatial scene or live-worker helpers;
- the route silently widens beyond the released `V52-A` artifact family.

## Local Gate

- docs-only starter validation:
  - `make arc-start-check ARC=128`
- once source code exists, do not treat this starter bundle as a substitute for the
  relevant `apps/web` lint, smoke, and route-contract lanes for the bounded
  implementation surface.
