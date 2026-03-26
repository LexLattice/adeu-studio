# Assessment vNext+87 Edges (Post Closeout)

This document records edge disposition for `vNext+87` (`V41-E` practical
deterministic alignment baseline) after arc closeout.

Status: post-closeout assessment (March 26, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS87_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "authoritative_scope": "v87_closeout_edge_disposition",
  "required_in_decision": true,
  "notes": "Pre-lock edge planning is superseded by post-closeout edge disposition in this document."
}
```

## Scope

- In scope: bounded `V41-E` practical deterministic alignment baseline; canonical
  `adeu_architecture_alignment_report@1`; exact consumption of the released `V41-A`
  request boundary, `V41-B` settlement frame, `V41-C` observation frame, and `V41-D`
  intended semantic IR; stable finding-id derivation; canonical dedup/order;
  authoritative comparison against released `adeu_architecture_semantic_ir@1`;
  explicit severity and blocking posture; explicit unresolved-unknown carry-through;
  committed reference fixture replay; authoritative/mirrored schema parity; and
  stop-gate/evidence continuity for the released alignment lane.
- Out of scope: CLI runner release, remediation or repo-mutation planning,
  checkpoint/projection/UX practical outputs, merged-truth reconciliation, API/web
  inspection routes, and any orchestration or mutation authority beyond the released
  alignment report.

## Inputs

- `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v23.md`
- `docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS87.md`
- `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/alignment.py`
- `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/__init__.py`
- `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/export_schema.py`
- `packages/adeu_architecture_compiler/tests/test_architecture_compiler_v41e.py`
- `packages/adeu_architecture_compiler/tests/test_architecture_compiler_export_schema.py`
- `packages/adeu_architecture_compiler/schema/adeu_architecture_alignment_report.v1.json`
- `spec/adeu_architecture_alignment_report.schema.json`
- `apps/api/fixtures/architecture/vnext_plus87/`
- `artifacts/quality_dashboard_v87_closeout.json`
- `artifacts/stop_gate/metrics_v87_closeout.json`
- `artifacts/agent_harness/v87/evidence_inputs/metric_key_continuity_assertion_v87.json`
- `artifacts/agent_harness/v87/evidence_inputs/runtime_observability_comparison_v87.json`
- `artifacts/agent_harness/v87/evidence_inputs/v41e_architecture_alignment_report_evidence_v87.json`
- merged PR: `#309`

## Pre-Lock Edge Set Outcome (v87 Closeout)

1. Intended / observed collapse: `resolved`.
   - the released lane keeps request plus settlement as the normative driver for
     intended truth and uses observation only as a constraining companion input, not
     as a hidden source of intended architecture.
2. Lineage drift across the four upstream artifacts: `resolved`.
   - the released lane binds exact request id/ref, settlement id/ref, observation
     id/ref, intended architecture id, `semantic_hash`, `source_set_hash`, and
     `authority_boundary_policy`, and rejects drift from that released comparison
     world.
3. Severity / blocking laundering: `resolved`.
   - the released lane freezes exact severity and posture enums, derives blocking
     posture from explicit blocking findings, and distinguishes alignment
     `blocked` from upstream settlement `compile_entitlement = blocked`.
4. Unresolved-unknown disappearance: `resolved`.
   - the released lane preserves at least one upstream unresolved observation as an
     explicit `unresolved_unknown` alignment finding instead of silently normalizing
     it away.
5. Provenance-light findings: `resolved`.
   - every released finding carries stable id, `basis_kind`, typed support refs, and
     explicit intended/observed/request/settlement grounding rather than prose-only
     judgment.
6. Non-deterministic finding replay: `resolved`.
   - duplicate findings collapse on one canonical typed support tuple, ids are
     derived from its hash, findings emit in ascending canonical order, and
     `severity_counts` is derived from the deduplicated canonical set.
7. Remediation / runner creep: `resolved`.
   - the released lane stays comparison-only and rejects remediation, runner,
     repo-mutation, and merged-truth surfaces outright.
8. Silent settlement reinterpretation: `resolved`.
   - the released lane consumes entitled settlement posture as-is from `V41-B` and
     rejects local recomputation of settlement authority.
9. Prose-only support laundering: `resolved`.
   - the released lane rejects findings supported solely by notes, free text, or
     advisory-only upstream fields and keeps typed artifact refs as the only
     grounding surface.

## Guard Coverage Outcome

- merged implementation files:
  - `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/alignment.py`
  - `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/__init__.py`
  - `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/export_schema.py`
- committed reference fixture ladder under `apps/api/fixtures/architecture/vnext_plus87/`:
  - `adeu_architecture_analysis_request_v87_alignment_derivative.json`
  - `adeu_architecture_analysis_settlement_frame_v87_alignment_derivative.json`
  - `adeu_architecture_observation_frame_v87_alignment_derivative.json`
  - `adeu_architecture_semantic_ir_v87_alignment_derivative.json`
  - `adeu_architecture_alignment_report_v87_reference.json`
- authoritative and mirrored schema files:
  - `packages/adeu_architecture_compiler/schema/adeu_architecture_alignment_report.v1.json`
  - `spec/adeu_architecture_alignment_report.schema.json`
- merged guard files:
  - `packages/adeu_architecture_compiler/tests/test_architecture_compiler_v41e.py`
  - `packages/adeu_architecture_compiler/tests/test_architecture_compiler_export_schema.py`
- v87 closeout artifact regeneration on `main` emitted:
  - canonical `metric_key_continuity_assertion@1`
  - canonical `runtime_observability_comparison@1`
  - canonical `v41e_architecture_alignment_report_evidence@1`
  - committed parent-session closeout raw/event stream fixture under
    `artifacts/agent_harness/v87/runtime/evidence/codex/copilot/v87-closeout-main-1/`
- merged guard coverage now proves:
  - exact replay over the released request, settlement, observation, and intended
    comparison world,
  - authoritative comparison against released `adeu_architecture_semantic_ir@1`
    without reopening or redefining intended schemas,
  - stable finding-id derivation, deterministic dedup/order, and severity-count
    derivation from the canonicalized finding set,
  - explicit unresolved-unknown carry-through into a blocking alignment finding,
  - rejection of prose-only finding support and blocked-settlement worlds,
  - preservation of intended/observed lane separation with observation constraining
    but not minting intended truth,
  - schema export parity and deterministic fixture replay,
  - replay-preserving maintenance refreshes for affected `v79`, `v82`, and `v86`
    fixtures.

## Stop-Gate Continuity Outcome

```json
{
  "schema": "v87_edge_closeout_summary@1",
  "arc": "vNext+87",
  "target_path": "V41-E",
  "prelock_edge_count": 9,
  "resolved_edge_count": 9,
  "open_blocking_edges": 0,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v86": true,
  "all_passed": true,
  "blocking_issues": []
}
```

## Residual Risks (Post v87)

1. The released lane remains intentionally bounded to diagnostics only and not
   runner orchestration, remediation, repo mutation, or merged-truth reconciliation.
2. The accepted v87 ladder is intentionally narrow and exercises a blocking
   unresolved-unknown case plus a warning-only observability-gap case, not the full
   future ontology of drift.
3. Report-level `alignment_posture = blocked` remains a diagnostic posture over an
   already entitled comparison world, not a replacement for upstream settlement
   authority.
4. Habitual orchestration remains intentionally deferred to the single remaining
   `V41-F` slice.

## Recommendation (Post Closeout)

1. Mark the v87 edge set as closed with no blocking issues.
2. Treat `adeu_architecture_alignment_report@1` as the canonical alignment artifact
   for practical repo analysis going forward.
3. Treat `V41-E` as complete at its bounded baseline on `main`; any attempt to
   merge intended and observed into one truth surface should be treated as a
   regression.
4. Move the next default candidate to `V41-F` practical runner orchestration
   without reopening the released request, settlement, observation, intended, or
   alignment seams.
