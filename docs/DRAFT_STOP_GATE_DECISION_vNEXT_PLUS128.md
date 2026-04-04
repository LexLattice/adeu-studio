# Draft Stop-Gate Decision (Post vNext+128)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS128.md`

Status: draft decision note (post-hoc closeout capture, April 4, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS128.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v128_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+128` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS128.md`.
- This note captures bounded `V52-B` browser-route evidence only; it does not
  authorize the later live worker bridge, advanced visualization seam, or imported
  overlay precedent by itself.
- Canonical `V52-B` release in `v128` is carried by the shipped `apps/web`
  route-local source, committed deterministic route tests, and the canonical
  `v52b_paper_semantic_mock_workbench_evidence@1` evidence input under
  `artifacts/agent_harness/v128/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md` now marks
  `V52-A` and `V52-B` closed on `main` and advances the branch-local default next
  path to `V52-C`; it does not select the `V52-C` worker bridge by itself.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#350` (`feat(v128): add paper semantic mock workbench`)
- arc-completion merge commit: `e1a66ebe71068cf3fa85fd297eb9869c0eae707a`
- merged-at timestamp: `2026-04-04T16:55:59Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v128_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v128_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v128_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v128/evidence_inputs/metric_key_continuity_assertion_v128.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v128/evidence_inputs/runtime_observability_comparison_v128.json`
  - `V52-B` release evidence input:
    `artifacts/agent_harness/v128/evidence_inputs/v52b_paper_semantic_mock_workbench_evidence_v128.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v128/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS128_EDGES.md`

## Exit-Criteria Check (vNext+128)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V52-B` merged with green CI | required | `pass` | PR `#350`, merge commit `e1a66ebe71068cf3fa85fd297eb9869c0eae707a`, checks `python/web/lean-formal = pass` |
| The shipped route is exactly `/papers/semantic-workbench` and remains bounded to `apps/web` only | required | `pass` | `apps/web/src/app/papers/semantic-workbench/page.tsx`, route smoke test, and absence of API/domain/worker widening in the merged diff |
| The route consumes only committed released `V52-A` abstract/paragraph fixtures and validates them before render | required | `pass` | `sample-artifacts.ts`, `parsePaperSemanticArtifact(...)`, committed `packages/adeu_paper_semantics/tests/fixtures/v52a/*.json`, and `paper-semantic-workbench-contract.test.ts` |
| First render defaults to the committed abstract fixture and preserves the sample-ref vs artifact-id split | required | `pass` | `buildDefaultViewConfig(...)`, `selected_sample_artifact_ref`, `artifact_ref`, and route contract test coverage |
| The workbench preserves released semantic-law visibility instead of hiding it in the browser layer | required | `pass` | route-local view model retains `semantic_hash`, `identity_field_names`, and `projection_field_names` from the released artifact |
| Deterministic claim ordering remains subordinate to the released artifact projection | required | `pass` | `projection.claim_order` first, deterministic claim-id fallback second, asserted in route-local view construction and contract tests |
| Fixture-stack and projection mismatches fail closed instead of silently falling back | required | `pass` | `fail_closed_invalid_fixture_stack`, `INVALID_SELECTED_SURFACE_PROJECTION`, malformed-fixture coverage, and invalid local projection handling |
| Unsupported diagnostic enums fail closed before rendering | required | `pass` | parser validation of `diagnostic_kind` / `severity` plus `reject_invalid_diagnostic_kind.json` route-test coverage |
| No direct API fetch, live-worker import, prototype overlay import, or spatial scene widening ships in this slice | required | `pass` | route import guard in `paper-semantic-workbench-contract.test.ts` and bounded route source set under `apps/web/src/app/papers/semantic-workbench/` |
| The bounded route passes local web gate plus production build | required | `pass` | route lint, route contract test, route smoke test, and local `npm run build` in `apps/web` from the merged PR validation |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v128_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v128/evidence_inputs/metric_key_continuity_assertion_v128.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v128/evidence_inputs/runtime_observability_comparison_v128.json` |

## Stop-Gate Summary

```json
{
  "schema": "v128_closeout_stop_gate_summary@1",
  "arc": "vNext+128",
  "target_path": "V52-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v127": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 119,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v127_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v128_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+127","current_arc":"vNext+128","baseline_source":"artifacts/stop_gate/report_v127_closeout.md","current_source":"artifacts/stop_gate/report_v128_closeout.md","baseline_elapsed_ms":119,"current_elapsed_ms":119,"delta_ms":0,"notes":"v128 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V52-B paper semantic mock-workbench lane: one bounded /papers/semantic-workbench route in apps/web, one committed-sample registry over the released abstract and paragraph V52-A fixtures, explicit selected_sample_artifact_ref versus artifact_ref identity split, pre-render validation of committed samples against the released artifact contract, preservation of semantic_hash plus identity/projection field visibility in the browser model, deterministic claim ordering from released projection.claim_order with claim-id fallback only, fail-closed handling for malformed fixture stacks and invalid local projection mismatch, invalid diagnostic-enum rejection before render, no fetch or live-worker/domain bridge imports, no direct prototype overlay imports, and no advanced visualization widening."}
```

## V52B Paper Semantic Mock Workbench Evidence

```json
{"schema":"v52b_paper_semantic_mock_workbench_evidence@1","evidence_input_path":"artifacts/agent_harness/v128/evidence_inputs/v52b_paper_semantic_mock_workbench_evidence_v128.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS128.md#v128-continuation-contract-machine-checkable","merged_pr":"#350","merge_commit":"e1a66ebe71068cf3fa85fd297eb9869c0eae707a","implementation_packages":["adeu_paper_semantics","adeu-web"],"route_contract_ref":"v52b_paper_semantic_mock_workbench_contract","adeu_web_root":"apps/web","browser_route_path":"/papers/semantic-workbench","route_source_paths":["apps/web/src/app/papers/semantic-workbench/page.tsx","apps/web/src/app/papers/semantic-workbench/paper-semantic-workbench-client.tsx","apps/web/src/app/papers/semantic-workbench/sample-artifacts.ts","apps/web/src/app/papers/semantic-workbench/view-model.ts","apps/web/src/app/papers/semantic-workbench/page.module.css"],"route_test_reference_paths":["apps/web/tests/paper-semantic-workbench-contract.test.ts","apps/web/tests/routes.smoke.test.mjs"],"committed_sample_artifact_paths":["packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_artifact_abstract.json","packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_artifact_paragraph.json"],"default_sample_artifact_path":"packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_artifact_abstract.json","selected_sample_artifact_ref_vs_artifact_ref_explicit":true,"released_fixture_validation_before_render":true,"semantic_hash_visibility_preserved":true,"identity_projection_field_visibility_preserved":true,"claim_ordering_law":"released_projection_claim_order_then_claim_id_fallback","no_api_fetch_boundary_enforced":true,"no_live_worker_boundary_enforced":true,"no_direct_prototype_overlay_import_boundary_enforced":true,"metric_key_continuity_assertion_path":"artifacts/agent_harness/v128/evidence_inputs/metric_key_continuity_assertion_v128.json","runtime_observability_comparison_path":"artifacts/agent_harness/v128/evidence_inputs/runtime_observability_comparison_v128.json","runtime_event_stream_path":"artifacts/agent_harness/v128/runtime/evidence/local/urm_events.ndjson","notes":"v128 evidence pins the released V52-B mock-workbench lane on main: one bounded apps/web route only, one deterministic committed-sample registry over the released V52-A abstract and paragraph fixtures, route-local validation against the released paper semantic artifact contract before render, preserved semantic_hash plus identity/projection field visibility, explicit selected_sample_artifact_ref versus artifact_ref split, deterministic claim ordering subordinate to released projection data, fail-closed fixture-stack and projection mismatch handling, invalid diagnostic-enum rejection, no fetch or live worker/domain bridge imports, no direct prototype overlay imports, and no advanced visualization widening."}
```

## Recommendation (Post v128)

- gate decision:
  - `V52B_PAPER_SEMANTIC_MOCK_WORKBENCH_COMPLETE_ON_MAIN`
  - `V52_PAPER_SEMANTICS_FAMILY_ACTIVE_ON_MAIN`
- rationale:
  - `v128` closes the bounded `V52-B` read-only browser seam on `main` by shipping
    one repo-owned `/papers/semantic-workbench` route that remains subordinate to
    released `V52-A` artifacts instead of laundering the imported overlay into live
    route authority.
  - the shipped slice stays narrow and artifact-disciplined: committed sample inputs
    only, explicit sample-ref versus artifact-id identity split, pre-render released
    artifact validation, preserved semantic-law visibility, deterministic local claim
    ordering, and no live worker/API/prototype-sprawl widening.
  - review hardening materially improved the release: the route now fails closed on
    invalid selected-surface projection, rejects unsupported diagnostic enums before
    render, uses build-safe route-local imports, and keeps the route-import guard wide
    enough to catch side-effect and subpath drift.
  - the imported bundle remains support-only and non-precedent; the release re-authors
    live ownership entirely in repo-native `apps/web` paths over released
    `adeu_paper_semantics` artifacts.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`0 ms` vs `v127`
    baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md` should now be read with `V52-A` and `V52-B`
    closed on `main` and the branch-local default next path advanced to `V52-C` /
    `vNext+129`.
