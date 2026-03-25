# Assessment vNext+83 Edges (Post Closeout)

This document records edge disposition for `vNext+83` (`V41-A` practical analysis
request and deterministic `source_set` capture baseline) after arc closeout.

Status: post-closeout assessment (March 25, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS83_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "authoritative_scope": "v83_closeout_edge_disposition",
  "required_in_decision": true,
  "notes": "Pre-lock edge planning is superseded by post-closeout edge disposition in this document."
}
```

## Scope

- In scope: bounded `V41-A` practical analysis request baseline; deterministic
  materialization of canonical `adeu_architecture_analysis_request@1`; exact
  repo-root-relative scope selection; `committed_tree` / `materialized_snapshot`
  discipline; per-item plus aggregate source hashing; exact brief/doc reference
  closure; authority-boundary policy pinning; explicit settlement deferral; committed
  reference fixture replay; authoritative/mirrored schema parity; and review-driven
  hardening for `tests.py` artifact-kind inference.
- Out of scope: `adeu_architecture_analysis_settlement_frame@1`,
  `adeu_architecture_observation_frame@1`, repo-grounded intended
  `adeu_architecture_semantic_ir@1` compile, `adeu_architecture_alignment_report@1`,
  CLI runner release, API/web inspection routes, automatic repo mutation, and any
  settlement, drift, or impossibility authority beyond request capture.

## Inputs

- `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md`
- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v23.md`
- `docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS83.md`
- `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py`
- `packages/adeu_architecture_ir/src/adeu_architecture_ir/__init__.py`
- `packages/adeu_architecture_ir/src/adeu_architecture_ir/export_schema.py`
- `packages/adeu_architecture_ir/tests/test_analysis_request.py`
- `packages/adeu_architecture_ir/tests/test_architecture_ir_export_schema.py`
- `packages/adeu_architecture_ir/schema/adeu_architecture_analysis_request.v1.json`
- `spec/adeu_architecture_analysis_request.schema.json`
- `apps/api/fixtures/architecture/vnext_plus83/`
- `artifacts/quality_dashboard_v83_closeout.json`
- `artifacts/stop_gate/metrics_v83_closeout.json`
- `artifacts/agent_harness/v83/evidence_inputs/metric_key_continuity_assertion_v83.json`
- `artifacts/agent_harness/v83/evidence_inputs/runtime_observability_comparison_v83.json`
- `artifacts/agent_harness/v83/evidence_inputs/v41a_architecture_analysis_request_evidence_v83.json`
- merged PR: `#305`

## Pre-Lock Edge Set Outcome (v83 Closeout)

1. Working-tree determinism drift: `resolved`.
   - the released lane accepts only `committed_tree` and explicit
     `materialized_snapshot` modes and requires immutable snapshot identity for the
     chosen mode, so ambient working-tree state is not laundered into deterministic
     request input.
2. Scope laundering through vague selection: `resolved`.
   - the released request binds one subtree anchor plus explicit additions,
     exclusions, and artifact-kind policy instead of free-form prose.
3. Source-set provenance underspecification: `resolved`.
   - every released source item now carries repo-relative path, artifact kind, and
     per-item hash plus one aggregate `source_set_hash`, with canonical ordering fixed
     to normalized repo-relative path order.
4. Brief-world drift outside the frozen repo world: `resolved`.
   - `maintainer_brief_refs` and `accepted_doc_refs` now fail closed unless they
     resolve either to frozen `source_set` content or to separately materialized and
     hashed captured artifacts.
5. Authority-policy drift at request time: `resolved`.
   - the released request binds exact authority-boundary policy input and rejects
     missing policy pinning.
6. Settlement leak into request capture: `resolved`.
   - the released lane keeps only a settlement hook and rejects settlement, drift, or
     impossibility authority claims inside the request artifact itself.
7. Observation creep: `resolved`.
   - the released `V41-A` surface remains strictly request and `source_set`
     materialization only; observation, intended compile, alignment, and runner work
     did not ship in this arc.
8. Repo-scale overreach: `resolved`.
   - the committed fixture remains tied to one bounded internal subtree plus four
     explicit additions, which keeps replay stable and cheap enough for first-lane
     exercise.

## Guard Coverage Outcome

- merged implementation files:
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_request.py`
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/__init__.py`
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/export_schema.py`
- committed reference fixture under
  `apps/api/fixtures/architecture/vnext_plus83/adeu_architecture_analysis_request_v83_reference.json`
- authoritative and mirrored schema files:
  - `packages/adeu_architecture_ir/schema/adeu_architecture_analysis_request.v1.json`
  - `spec/adeu_architecture_analysis_request.schema.json`
- merged guard files:
  - `packages/adeu_architecture_ir/tests/test_analysis_request.py`
  - `packages/adeu_architecture_ir/tests/test_architecture_ir_export_schema.py`
- v83 closeout artifact regeneration on `main` emitted:
  - canonical `metric_key_continuity_assertion@1`
  - canonical `runtime_observability_comparison@1`
  - canonical `v41a_architecture_analysis_request_evidence@1`
  - committed parent-session closeout raw/event stream fixture under
    `artifacts/agent_harness/v83/runtime/evidence/codex/copilot/v83-closeout-main-1/`
- merged guard coverage now proves:
  - exact repo-scope replay over one bounded internal subtree plus explicit additions,
  - committed-tree snapshot identity capture and fail-closed missing-identity rejection,
  - deterministic per-item and aggregate source hashing,
  - exact brief/doc reference closure and policy pinning,
  - rejection of unsupported snapshot modes, path escape, duplicate paths,
    out-of-scope inclusions, and unsupported artifact kinds,
  - explicit settlement/drift/impossibility deferral inside the request lane,
  - preserved `tests.py` classification as a `test` artifact after review hardening.

## Stop-Gate Continuity Outcome

```json
{
  "schema": "v83_edge_closeout_summary@1",
  "arc": "vNext+83",
  "target_path": "V41-A",
  "prelock_edge_count": 8,
  "resolved_edge_count": 8,
  "open_blocking_edges": 0,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v82": true,
  "all_passed": true,
  "blocking_issues": []
}
```

## Residual Risks (Post v83)

1. The released lane remains intentionally bounded to request/world binding only and
   not settlement, observation, intended compile, alignment, or runner behavior.
2. `materialized_snapshot` remains supported by contract shape, but the committed
   reference fixture in v83 exercises the `committed_tree` baseline only.
3. The practical loop still lacks the explicit settlement/entitlement seam, which is
   why `V41-B` remains the immediate next default candidate.
4. Runtime observability remains informational only in `V41-A`; later practical-loop
   widening still requires its own explicit lock and closeout evidence.

## Recommendation (Post Closeout)

1. Mark the v83 edge set as closed with no blocking issues.
2. Treat `adeu_architecture_analysis_request@1` as the canonical world-binding
   artifact for practical repo analysis going forward.
3. Treat `V41-A` as complete at its bounded baseline on `main`; any request-lane
   widening should be justified as exceptional rather than assumed.
4. Move the next default candidate to the settlement/entitlement seam explicitly,
   without reopening the released request, snapshot, or `source_set` boundaries.
