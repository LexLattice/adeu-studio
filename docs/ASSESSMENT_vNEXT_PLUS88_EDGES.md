# Assessment vNext+88 Edges (Post Closeout)

This document records edge disposition for `vNext+88` (`V41-F` practical runner /
habitual orchestration baseline) after arc closeout.

Status: post-closeout assessment (March 26, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS88_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "authoritative_scope": "v88_closeout_edge_disposition",
  "required_in_decision": true,
  "notes": "Pre-lock edge planning is superseded by post-closeout edge disposition in this document."
}
```

## Scope

- In scope: bounded `V41-F` practical runner baseline; canonical
  `adeu_architecture_analysis_run_manifest@1`; exact sequencing over the released
  `V41-A` request boundary, `V41-B` settlement frame, `V41-C` observation frame,
  `V41-D` intended semantic IR, and `V41-E` alignment report; deterministic
  `run_id`; canonical `stage_statuses`; deterministic output/runtime-evidence
  placement; authoritative blocked-run manifest emission; explicit
  `terminal_alignment_posture = none` for blocked runs; committed reference fixture
  replay; authoritative/mirrored schema parity; and stop-gate/evidence continuity
  for the released runner lane.
- Out of scope: remediation or repo-mutation planning, merged-truth reconciliation,
  checkpoint/projection/UX practical reruns, API/web inspection routes, multi-repo
  orchestration, and any mutation authority beyond the released run manifest.

## Inputs

- `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v23.md`
- `docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS88.md`
- `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/runner.py`
- `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/__init__.py`
- `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/export_schema.py`
- `packages/adeu_architecture_compiler/tests/test_architecture_compiler_v41f.py`
- `packages/adeu_architecture_compiler/tests/test_architecture_compiler_export_schema.py`
- `packages/adeu_architecture_compiler/schema/adeu_architecture_analysis_run_manifest.v1.json`
- `spec/adeu_architecture_analysis_run_manifest.schema.json`
- `apps/api/fixtures/architecture/vnext_plus88/`
- `artifacts/quality_dashboard_v88_closeout.json`
- `artifacts/stop_gate/metrics_v88_closeout.json`
- `artifacts/agent_harness/v88/evidence_inputs/metric_key_continuity_assertion_v88.json`
- `artifacts/agent_harness/v88/evidence_inputs/runtime_observability_comparison_v88.json`
- `artifacts/agent_harness/v88/evidence_inputs/v41f_architecture_analysis_run_manifest_evidence_v88.json`
- merged PR: `#310`

## Pre-Lock Edge Set Outcome (v88 Closeout)

1. Runner as hidden reconciler: `resolved`.
   - the released lane keeps request plus settlement as the normative driver for
     intended truth, uses observation only as constraining companion evidence, and
     keeps the run manifest strictly lineage-only rather than a merged-truth surface.
2. Settlement-blocked stop laundering: `resolved`.
   - settlement-blocked runs stop after observation, emit one authoritative manifest
     stop witness, and emit no `semantic_ir_*`, no `alignment_report_*`, and no
     artifact-shaped shadows under the released intended/alignment family names.
3. Runner blocked vs alignment blocked confusion: `resolved`.
   - the released lane freezes `run_outcome` / `stop_reason_kind` separately from
     consumed alignment posture and proves that a completed run may still consume an
     emitted alignment report whose posture is `blocked`.
4. Non-deterministic run identity or placement: `resolved`.
   - `run_id`, `output_root_ref`, and `runtime_evidence_root_ref` derive only from
     canonical run inputs plus frozen runner configuration and are replay-stable.
5. Stage-ledger drift: `resolved`.
   - the released lane carries canonical `stage_statuses` over request, settlement,
     observation, intended, alignment, and manifest, and blocked runs mark
     intended/alignment as `not_run`.
6. Upstream seam recomputation inside the runner: `resolved`.
   - the released lane consumes request, settlement, observation, intended, and
     alignment artifacts as released seams and rejects local recomputation of
     settlement entitlement or alignment posture.
7. Repo-mutation or remediation creep: `resolved`.
   - the released lane keeps the run manifest lineage-only and rejects remediation,
     repo-mutation, and merged-truth fields outright.
8. Runtime evidence overclaim: `resolved`.
   - runtime evidence remains required but informational-only, while gate-relevant
     truth stays with typed artifacts, fixture replay, and stop-gate continuity.
9. Orchestration widening beyond one bounded repo scope: `resolved`.
   - the first runner baseline stays on one bounded repo scope only and does not
     widen into fleet or multi-repo orchestration.

## Guard Coverage Outcome

- merged implementation files:
  - `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/runner.py`
  - `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/__init__.py`
  - `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/export_schema.py`
- committed reference fixture ladder under `apps/api/fixtures/architecture/vnext_plus88/`:
  - `blocked_run_outputs/adeu_architecture_analysis_request.json`
  - `blocked_run_outputs/adeu_architecture_analysis_settlement_frame.json`
  - `blocked_run_outputs/adeu_architecture_observation_frame.json`
  - `adeu_architecture_analysis_run_manifest_v88_blocked_reference.json`
  - `completed_run_outputs/adeu_architecture_analysis_request.json`
  - `completed_run_outputs/adeu_architecture_analysis_settlement_frame.json`
  - `completed_run_outputs/adeu_architecture_observation_frame.json`
  - `completed_run_outputs/adeu_architecture_semantic_ir.json`
  - `completed_run_outputs/adeu_architecture_alignment_report.json`
  - `adeu_architecture_analysis_run_manifest_v88_completed_reference.json`
- authoritative and mirrored schema files:
  - `packages/adeu_architecture_compiler/schema/adeu_architecture_analysis_run_manifest.v1.json`
  - `spec/adeu_architecture_analysis_run_manifest.schema.json`
- merged guard files:
  - `packages/adeu_architecture_compiler/tests/test_architecture_compiler_v41f.py`
  - `packages/adeu_architecture_compiler/tests/test_architecture_compiler_export_schema.py`
- v88 closeout artifact regeneration on `main` emitted:
  - canonical `metric_key_continuity_assertion@1`
  - canonical `runtime_observability_comparison@1`
  - canonical `v41f_architecture_analysis_run_manifest_evidence@1`
  - committed parent-session closeout raw/event stream fixture under
    `artifacts/agent_harness/v88/runtime/evidence/codex/copilot/v88-closeout-main-1/`
- merged guard coverage now proves:
  - exact replay over the released request, settlement, observation, intended, and
    alignment world when settlement remains entitled,
  - exact replay over the released request, settlement, and observation world when
    settlement blocks intended/alignment emission,
  - deterministic `run_id` derivation and canonical stage-ledger replay,
  - authoritative blocked-run manifest emission with
    `terminal_alignment_posture = none`,
  - explicit distinction between runner-level blocked stop and alignment-level
    blocked posture in a completed run,
  - rejection of blocked-run shadow intended/alignment refs,
  - schema export parity and deterministic fixture replay,
  - replay-preserving maintenance refreshes for affected `v79`, `v82`, `v86`, and
    `v87` fixtures.

## Stop-Gate Continuity Outcome

```json
{
  "schema": "v88_edge_closeout_summary@1",
  "arc": "vNext+88",
  "target_path": "V41-F",
  "prelock_edge_count": 9,
  "resolved_edge_count": 9,
  "open_blocking_edges": 0,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v87": true,
  "all_passed": true,
  "blocking_issues": []
}
```

## Residual Risks (Post v88)

1. The released lane remains intentionally bounded to orchestration only and not
   remediation planning, repo mutation, merged-truth reconciliation, API/web
   inspection routes, or multi-repo execution.
2. The accepted v88 ladder is intentionally narrow and exercises one completed run
   plus one settlement-blocked stop, not future multi-run scheduling or fleet
   management semantics.
3. Runner completion remains an execution posture only; it does not imply alignment
   success or auto-acceptance of drift.
4. No default `V41` slices remain; any further widening now belongs to next-family
   selection rather than another `V41-*` continuation.

## Recommendation (Post Closeout)

1. Mark the v88 edge set as closed with no blocking issues.
2. Treat `adeu_architecture_analysis_run_manifest@1` as the canonical practical
   runner stop-witness/orchestration artifact for practical repo analysis going
   forward.
3. Treat `V41-F` as complete at its bounded baseline on `main`; any attempt to turn
   the runner into remediation, repo-mutation, or merged-truth authority should be
   treated as a regression.
4. Mark the bounded `V41` practical-analysis family as complete on `main`; further
   work should start with a new family-selection step rather than an additional
   `V41-*` slice.
