# Assessment vNext+85 Edges (Post Closeout)

This document records edge disposition for `vNext+85` (`V41-C` practical observed
implementation frame baseline) after arc closeout.

Status: post-closeout assessment (March 26, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS85_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "authoritative_scope": "v85_closeout_edge_disposition",
  "required_in_decision": true,
  "notes": "Pre-lock edge planning is superseded by post-closeout edge disposition in this document."
}
```

## Scope

- In scope: bounded `V41-C` practical observed-implementation baseline;
  deterministic materialization of canonical
  `adeu_architecture_observation_frame@1`; exact consumption of the released `V41-A`
  request / `source_set` boundary and `V41-B` settlement carry-through; facts-only
  observation entries; explicit `fact_kind` plus `observation_mode = direct |
  derived`; grounded provenance closure; in-frame cross-entry grounding; explicit
  `upstream_compile_entitlement` plus `upstream_blocking_refs`; unresolved
  observations with bounded reason typing; committed reference fixture replay;
  authoritative/mirrored schema parity; and stop-gate/evidence continuity for the
  released observation lane.
- Out of scope: repo-grounded intended
  `adeu_architecture_semantic_ir@1` compile,
  `adeu_architecture_alignment_report@1`, CLI runner release, API/web inspection
  routes, automatic repo mutation, remediation planning, and any intended,
  settlement, or alignment authority beyond the released observation frame.

## Inputs

- `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v23.md`
- `docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS85.md`
- `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/observation.py`
- `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/__init__.py`
- `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/export_schema.py`
- `packages/adeu_architecture_compiler/tests/test_architecture_compiler_v41c.py`
- `packages/adeu_architecture_compiler/tests/test_architecture_compiler_export_schema.py`
- `packages/adeu_architecture_compiler/schema/adeu_architecture_observation_frame.v1.json`
- `spec/adeu_architecture_observation_frame.schema.json`
- `apps/api/fixtures/architecture/vnext_plus85/`
- `artifacts/quality_dashboard_v85_closeout.json`
- `artifacts/stop_gate/metrics_v85_closeout.json`
- `artifacts/agent_harness/v85/evidence_inputs/metric_key_continuity_assertion_v85.json`
- `artifacts/agent_harness/v85/evidence_inputs/runtime_observability_comparison_v85.json`
- `artifacts/agent_harness/v85/evidence_inputs/v41c_architecture_observation_frame_evidence_v85.json`
- merged PR: `#307`

## Pre-Lock Edge Set Outcome (v85 Closeout)

1. Ambient repo read drift: `resolved`.
   - the released frame binds exact request/`source_set` lineage and rejects observed
     provenance outside the released `V41-A` world.
2. Observation / intended collapse: `resolved`.
   - the released frame remains facts-only and rejects intended semantics, settlement
     deontics, alignment verdicts, and remediation payloads inside the observed lane.
3. Settlement posture laundering: `resolved`.
   - the released frame carries forward `upstream_compile_entitlement` plus exact
     `upstream_blocking_refs` and rejects any drift from the released `V41-B`
     settlement frame.
4. Provenance-light / mushy observation entries: `resolved`.
   - every observed entry remains explicitly addressable with ids, `fact_kind`,
     `observation_mode`, concrete source refs, and typed entry-local fields rather
     than floating provenance-linked prose.
5. Silent invention instead of unresolved observation: `resolved`.
   - the released frame preserves explicit `unresolved_observations` with bounded
     `unresolved_reason_kind` rather than defaulting or inventing implementation
     structure.
6. Alignment / remediation creep: `resolved`.
   - the released lane stays observation-only and rejects alignment, severity, and
     repair-plan surfaces outright.
7. Direct vs derived extraction blur: `resolved`.
   - every resolved observed entry now declares `observation_mode = direct | derived`,
     keeping raw source facts distinct from bounded structural extraction.
8. Settlement carry-through drift: `resolved`.
   - downstream consumers no longer need to reopen settlement artifacts just to know
     observation posture, because the released frame carries the blocked state
     forward explicitly.
9. Floating cross-entry structure: `resolved`.
   - workflow `step_refs` and boundary `crossing_refs` must resolve to typed in-frame
     entries and stay anchored to concrete source refs instead of floating as an
     internally referential graph.
10. Duplicate or ambiguous observation identity: `resolved`.
    - root-local observation ids remain globally unique across the frame and fail
      closed on collisions.

## Guard Coverage Outcome

- merged implementation files:
  - `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/observation.py`
  - `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/__init__.py`
  - `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/export_schema.py`
- committed reference fixture under
  `apps/api/fixtures/architecture/vnext_plus85/adeu_architecture_observation_frame_v85_reference.json`
- authoritative and mirrored schema files:
  - `packages/adeu_architecture_compiler/schema/adeu_architecture_observation_frame.v1.json`
  - `spec/adeu_architecture_observation_frame.schema.json`
- merged guard files:
  - `packages/adeu_architecture_compiler/tests/test_architecture_compiler_v41c.py`
  - `packages/adeu_architecture_compiler/tests/test_architecture_compiler_export_schema.py`
- v85 closeout artifact regeneration on `main` emitted:
  - canonical `metric_key_continuity_assertion@1`
  - canonical `runtime_observability_comparison@1`
  - canonical `v41c_architecture_observation_frame_evidence@1`
  - committed parent-session closeout raw/event stream fixture under
    `artifacts/agent_harness/v85/runtime/evidence/codex/copilot/v85-closeout-main-1/`
- merged guard coverage now proves:
  - exact request-bound and settlement-bound replay over the released v85 world,
  - facts-only observation with rejection of intended/alignment/remediation creep,
  - direct-vs-derived marking across all resolved observed entry families,
  - explicit blocked settlement carry-through without entitlement laundering,
  - request-bound provenance closure and rejection of documentation items as
    observed implementation facts,
  - in-frame grounding for workflow and boundary cross-entry references,
  - explicit unresolved observation preservation and bounded reason typing,
  - structured observability-hook reasoning keyed on `observable_kind` instead of
    brittle filename substring heuristics,
  - schema export parity and deterministic fixture replay.

## Stop-Gate Continuity Outcome

```json
{
  "schema": "v85_edge_closeout_summary@1",
  "arc": "vNext+85",
  "target_path": "V41-C",
  "prelock_edge_count": 10,
  "resolved_edge_count": 10,
  "open_blocking_edges": 0,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v84": true,
  "all_passed": true,
  "blocking_issues": []
}
```

## Residual Risks (Post v85)

1. The released lane remains intentionally bounded to observed implementation only
   and not intended compile, alignment, runner behavior, or remediation.
2. The committed reference fixture in v85 exercises a blocked settlement carry-through
   posture only; an observation frame sourced from `compile_entitlement = entitled`
   remains intentionally deferred until a later slice consumes settlement honestly.
3. `observation_mode = derived` remains bounded structural extraction over the
   released repo world, not proof that the derived structure is itself intended or
   semantically final.
4. Runtime observability remains informational only in `V41-C`; later practical-loop
   widening still requires its own explicit lock and closeout evidence.

## Recommendation (Post Closeout)

1. Mark the v85 edge set as closed with no blocking issues.
2. Treat `adeu_architecture_observation_frame@1` as the canonical observed
   implementation artifact for practical repo analysis going forward.
3. Treat `V41-C` as complete at its bounded baseline on `main`; any observation-lane
   widening should be justified as exceptional rather than assumed.
4. Move the next default candidate to repo-grounded intended compile explicitly,
   without reopening the released request or settlement boundaries and without
   collapsing intended and observed lanes.
