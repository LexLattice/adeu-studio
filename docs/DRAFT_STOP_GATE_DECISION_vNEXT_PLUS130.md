# Draft Stop-Gate Decision (Post vNext+130)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS130.md`

Status: draft decision note (post-hoc closeout capture, April 5, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS130.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v130_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+130` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS130.md`.
- This note captures bounded `V52-D` advanced-visualization evidence only; it does not
  authorize new paper-domain semantic authority, browser-triggered worker execution,
  or imported-prototype precedent by itself.
- Canonical `V52-D` release in `v130` is carried by the shipped route-local
  `apps/web/src/app/papers/semantic-workbench/` spatial scene, deterministic
  view-model extension, committed route contract/smoke tests, and the canonical
  `v52d_paper_semantic_advanced_visualization_evidence@1` evidence input under
  `artifacts/agent_harness/v130/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md` now marks
  `V52-A` through `V52-D` closed on `main` with no further internal `V52` path
  selected; it does not select a later family by itself.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#352` (`feat(v130): add paper semantic spatial visualization`)
- arc-completion merge commit: `9408051813ff8b51e1d7b02d13086f6dc61b366a`
- merged-at timestamp: `2026-04-05T00:21:08Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v130_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v130_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v130_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v130/evidence_inputs/metric_key_continuity_assertion_v130.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v130/evidence_inputs/runtime_observability_comparison_v130.json`
  - `V52-D` release evidence input:
    `artifacts/agent_harness/v130/evidence_inputs/v52d_paper_semantic_advanced_visualization_evidence_v130.json`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS130_EDGES.md`

## Exit-Criteria Check (vNext+130)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V52-D` merged with green CI | required | `pass` | PR `#352`, merge commit `9408051813ff8b51e1d7b02d13086f6dc61b366a`, checks `python/web/lean-formal = pass` |
| The live route remains exactly `/papers/semantic-workbench` | required | `pass` | `apps/web/src/app/papers/semantic-workbench/page.tsx`, route smoke coverage in `apps/web/tests/routes.smoke.test.mjs` |
| The slice consumes only released `V52-A` artifact data already admitted by the released `V52-B` route seam | required | `pass` | `sample-artifacts.ts`, `view-model.ts`, and committed `v52a` fixture consumption only |
| `spatial` ships as a route-local derived surface only, with released `artifact` / `local` projections remaining authoritative ordering anchors | required | `pass` | `selectSpatialOrderingProjection(...)`, `createViewModel(...)`, and failure code `INVALID_SPATIAL_ORDERING_PROJECTION` in `view-model.ts` |
| No released `projection.surface = spatial` contract is required | required | `pass` | released projection parsing still admits only `artifact` / `local`, while route-selected surfaces widen locally to include `spatial` |
| Scene node/edge vocabularies remain bounded and deterministic | required | `pass` | `SPATIAL_NODE_KIND_VALUES`, `SPATIAL_EDGE_KIND_VALUES`, deterministic `buildSpatialScene(...)`, and scene assertions in `apps/web/tests/paper-semantic-workbench-contract.test.ts` |
| Layout law and `scene_hash` remain deterministic over the same released artifact and local view config | required | `pass` | deterministic lane-column / claim-row positioning in `view-model.ts`, stable `scene_hash`, and repeated-view-model regression coverage |
| Route-local config stays minimal and user-driven | required | `pass` | `buildDefaultViewConfig(...)` plus config-key regression in `apps/web/tests/paper-semantic-workbench-contract.test.ts` |
| Semantic-law fields remain visible rather than being hidden behind scene-only state | required | `pass` | released `semantic_hash`, `identity_field_names`, and `projection_field_names` remain in the route-local view model and client panels |
| No browser-triggered live worker execution, no `fetch`, and no dedicated API route ship in this slice | required | `pass` | import/fetch guard in `apps/web/tests/paper-semantic-workbench-contract.test.ts`, no `apps/api` diff in the merged implementation PR |
| No prototype spatial scene is imported wholesale into live route code | required | `pass` | route import guard plus live implementation under `apps/web/src/app/papers/semantic-workbench/spatial-lane-scene.tsx` |
| Review hardening for 3D posture and scene-construction efficiency landed without widening authority | required | `pass` | follow-up commit `02fd0e4`, CSS `perspective` / `transform-style`, and lookup-map scene construction in `view-model.ts` |
| Targeted bounded web lint/tests/build passed locally and merged repo CI stayed green | required | `pass` | bounded `apps/web` lint, contract test, route smoke, `next build`, plus merged GitHub checks |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v130_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v130/evidence_inputs/metric_key_continuity_assertion_v130.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v130/evidence_inputs/runtime_observability_comparison_v130.json` |

## Stop-Gate Summary

```json
{
  "schema": "v130_closeout_stop_gate_summary@1",
  "arc": "vNext+130",
  "target_path": "V52-D",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v129": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 107,
  "runtime_observability_delta_ms": -12
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v129_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v130_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+129","current_arc":"vNext+130","baseline_source":"artifacts/stop_gate/report_v129_closeout.md","current_source":"artifacts/stop_gate/report_v130_closeout.md","baseline_elapsed_ms":119,"current_elapsed_ms":107,"delta_ms":-12,"notes":"v130 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V52-D paper semantic advanced-visualization lane: one bounded spatial surface added inside the existing /papers/semantic-workbench route only, route-local spatial scene derivation from released artifact/local ordering anchors only, preserved semantic_hash plus identity/projection field visibility, deterministic scene_hash and node ordering, explicit spatial node/edge vocabularies, no fetch and no browser-triggered worker execution, no new dedicated API route, no prototype spatial-scene import, review-driven hardening for CSS perspective/preserve-3d, and route-local scene construction tightened with lookup maps rather than repeated scans."}
```

## V52D Paper Semantic Advanced Visualization Evidence

```json
{"schema":"v52d_paper_semantic_advanced_visualization_evidence@1","evidence_input_path":"artifacts/agent_harness/v130/evidence_inputs/v52d_paper_semantic_advanced_visualization_evidence_v130.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS130.md#v130-continuation-contract-machine-checkable","merged_pr":"#352","merge_commit":"9408051813ff8b51e1d7b02d13086f6dc61b366a","implementation_packages":["adeu_paper_semantics","adeu-web"],"route_contract_ref":"v52b_paper_semantic_mock_workbench_contract","adeu_web_root":"apps/web","browser_route_path":"/papers/semantic-workbench","route_source_paths":["apps/web/src/app/papers/semantic-workbench/page.tsx","apps/web/src/app/papers/semantic-workbench/paper-semantic-workbench-client.tsx","apps/web/src/app/papers/semantic-workbench/sample-artifacts.ts","apps/web/src/app/papers/semantic-workbench/view-model.ts","apps/web/src/app/papers/semantic-workbench/spatial-lane-scene.tsx","apps/web/src/app/papers/semantic-workbench/page.module.css"],"route_test_reference_paths":["apps/web/tests/paper-semantic-workbench-contract.test.ts","apps/web/tests/routes.smoke.test.mjs"],"committed_sample_artifact_paths":["packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_artifact_abstract.json","packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_artifact_paragraph.json"],"selected_surface_vocabulary":["artifact","local","spatial"],"spatial_surface_route_local_derived":true,"released_projection_ordering_anchors":["artifact","local"],"released_projection_surface_spatial_required":false,"semantic_hash_visibility_preserved":true,"identity_projection_field_visibility_preserved":true,"claim_ordering_law":"released_projection_claim_order_then_claim_id_fallback","spatial_layout_law":"deterministic_lane_columns_and_claim_rows_no_physics_no_randomness","scene_hash_required":true,"scene_node_kind_vocabulary":["claim","lane_fragment"],"scene_edge_kind_vocabulary":["claim_to_fragment","inference_bridge"],"same_object_transition_only":true,"no_api_fetch_boundary_enforced":true,"no_live_worker_boundary_enforced":true,"no_new_dedicated_api_route_boundary_enforced":true,"no_direct_prototype_overlay_import_boundary_enforced":true,"metric_key_continuity_assertion_path":"artifacts/agent_harness/v130/evidence_inputs/metric_key_continuity_assertion_v130.json","runtime_observability_comparison_path":"artifacts/agent_harness/v130/evidence_inputs/runtime_observability_comparison_v130.json","runtime_event_stream_path":"artifacts/agent_harness/v130/runtime/evidence/local/urm_events.ndjson","notes":"v130 evidence pins the released V52-D advanced-visualization lane on main: one bounded spatial extension inside the existing /papers/semantic-workbench route only, one route-local spatial scene derived from released claims, lane fragments, inference bridges, and released artifact/local ordering anchors only, preserved semantic_hash plus identity/projection field visibility, deterministic scene_hash and node ordering, explicit claim/lane_fragment node vocabulary and claim_to_fragment/inference_bridge edge vocabulary, same-object transitions across artifact/local/spatial only, no fetch or browser-triggered live worker execution, no dedicated API route, no direct prototype spatial-scene import, CSS perspective plus preserve-3d hardening for the scene viewport, and route-local scene construction tightened with lookup maps without changing the deterministic layout law."}
```

## Recommendation (Post v130)

- gate decision:
  - `V52D_PAPER_SEMANTIC_ADVANCED_VISUALIZATION_COMPLETE_ON_MAIN`
  - `V52_PAPER_SEMANTICS_FAMILY_COMPLETE_ON_MAIN`
- rationale:
  - `v130` closes the bounded `V52-D` advanced-visualization seam on `main` by
    extending the existing `/papers/semantic-workbench` route rather than minting a
    second paper route or laundering browser authority into the already released
    worker bridge.
  - the shipped slice stays narrow and additive: one route-local `spatial` surface,
    one deterministic spatial scene model, one route-local scene component, one
    same-object transition posture across `artifact` / `local` / `spatial`, and no
    live fetch, worker trigger, or API widening.
  - released paper-semantic authority remains upstream and visible: the route still
    surfaces `semantic_hash`, identity/projection field names, and released authority
    postures instead of hiding them behind a scene-only frontend model.
  - the spatial scene remains subordinate to released ordering anchors and released
    artifact data; no released `projection.surface = spatial` contract was minted.
  - review hardening improved the actual route-local implementation without changing
    scope: `translateZ(...)` now has real perspective/preserve-3d support, and
    scene-construction efficiency was tightened with lookup maps.
  - the imported bundle remains support-only and non-precedent; the release re-authors
    live ownership entirely in repo-native `apps/web` route-local code.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability improved informationally (`-12 ms` vs `v129` baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md` should now be read with `V52-A` through
    `V52-D` closed on `main` and no further internal `V52` path currently selected.
