# Assessment vNext+78 Edges (Post Closeout)

This document records edge disposition for `vNext+78` (`V40-B` architecture
deterministic assembly, conformance, and gating baseline) after arc closeout.

Status: post-closeout assessment (March 24, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS78_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "authoritative_scope": "v78_closeout_edge_disposition",
  "required_in_decision": true,
  "notes": "Pre-lock edge planning is superseded by post-closeout edge disposition in this document."
}
```

## Scope

- In scope: bounded `V40-B` deterministic compiler baseline; activated
  `packages/adeu_architecture_compiler`; canonical
  `adeu_architecture_conformance_report@1`; deterministic consumed-root lineage;
  section-local validators; whole-ASIR integrity; stable `ASIR-O`, `ASIR-E`, `ASIR-D`,
  `ASIR-U`, and `ASIR-P` check families; required-check profile coverage;
  deterministic blocked/ready gating; static deterministic human-escalation lineage;
  committed blocked/ready reference fixtures; authoritative and mirrored schema
  exports; and review-driven fail-closed hardening.
- Out of scope: reopening `V40-A` root-family semantics, checkpoint/oracle execution,
  `adeu_architecture_checkpoint_trace@1`, `adeu_architecture_oracle_request@1`,
  `adeu_architecture_oracle_resolution@1`, projection bundle or manifest release,
  `adeu_core_ir` lowering, UX lowering, API/workbench surfaces, direct prompt-to-code
  generation, and any broader post-`V40-B` widening.

## Inputs

- `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md`
- `docs/DRAFT_ASIR_ARC_DECOMPOSITION_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v18.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS78.md`
- `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/conformance.py`
- `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/export_schema.py`
- `packages/adeu_architecture_compiler/tests/test_architecture_compiler_v40b.py`
- `packages/adeu_architecture_compiler/tests/test_architecture_compiler_export_schema.py`
- `apps/api/fixtures/architecture/vnext_plus78/`
- `artifacts/quality_dashboard_v78_closeout.json`
- `artifacts/stop_gate/metrics_v78_closeout.json`
- `artifacts/agent_harness/v78/evidence_inputs/metric_key_continuity_assertion_v78.json`
- `artifacts/agent_harness/v78/evidence_inputs/runtime_observability_comparison_v78.json`
- `artifacts/agent_harness/v78/evidence_inputs/v40b_architecture_compiler_evidence_v78.json`
- merged PR: `#300`

## Pre-Lock Edge Set Outcome (v78 Closeout)

1. Root-redefinition drift: `resolved`.
   - the compiler consumes the released `V40-A` root family as authoritative input and
     does not mint replacement root semantics.
2. Conformance / hybrid collapse: `resolved`.
   - the released conformance report remains deterministic only and does not embed
     checkpoint, oracle, or hybrid-state surfaces.
3. Gating without honest lineage: `resolved`.
   - blocked vs ready output now carries explicit `failed_check_ids`,
     `blocking_ambiguity_refs`, `human_escalation_refs`, and consumed-root replay
     lineage.
4. Check-id instability: `resolved`.
   - stable deterministic `ASIR-O`, `ASIR-E`, `ASIR-D`, `ASIR-U`, and `ASIR-P`
     families are now emitted from the released compiler profile.
5. Whole-ASIR integrity underreach: `resolved`.
   - the shipped compiler path includes both section-local validators and a whole-ASIR
     integrity pass.
6. Premature projection leakage: `resolved`.
   - `emitted_artifact_refs` remains structurally present but empty and no projection
     artifact family is released in v78.
7. Static escalation vs hybrid drift: `resolved`.
   - `human_escalation_refs` is now tied to static deterministic escalation lineage and
     no longer relies on hybrid-lane semantics.
8. Pre-projection check-family overreach: `resolved`.
   - `ASIR-P-xxx` remains bounded to pre-projection readiness honesty, blocked/ready
     correctness, and empty emitted-artifact posture only.

## Guard Coverage Outcome

- merged implementation files:
  - `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/conformance.py`
  - `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/export_schema.py`
  - `packages/adeu_architecture_compiler/src/adeu_architecture_compiler/__init__.py`
  - `packages/adeu_architecture_compiler/schema/adeu_architecture_conformance_report.v1.json`
  - `spec/adeu_architecture_conformance_report.schema.json`
  - `apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_blocked_reference.json`
  - `apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_conformance_report_v78_ready_reference.json`
  - `apps/api/fixtures/architecture/vnext_plus78/adeu_architecture_semantic_ir_v78_ready_derivative.json`
- merged guard files:
  - `packages/adeu_architecture_compiler/tests/test_architecture_compiler_v40b.py`
  - `packages/adeu_architecture_compiler/tests/test_architecture_compiler_export_schema.py`
- v78 closeout artifact regeneration on `main` emitted:
  - canonical `metric_key_continuity_assertion@1`
  - canonical `runtime_observability_comparison@1`
  - canonical `v40b_architecture_compiler_evidence@1`
  - committed parent-session closeout raw/event stream fixture under
    `artifacts/agent_harness/v78/runtime/evidence/codex/copilot/v78-closeout-main-1/`
- review-driven hardening now includes:
  - fixed compiler config-hash validation against the released `V40-B` profile,
  - exact required-check profile coverage for imported/validated reports,
  - static human-escalation lineage sourced from deontic escalation rules,
  - ready-fixture derivative tightening that clears deterministic escalation before
    claiming `projection_readiness = ready`.

## Stop-Gate Continuity Outcome

```json
{
  "schema": "v78_edge_closeout_summary@1",
  "arc": "vNext+78",
  "target_path": "V40-B",
  "prelock_edge_count": 8,
  "resolved_edge_count": 8,
  "open_blocking_edges": 0,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v77": true,
  "all_passed": true,
  "blocking_issues": []
}
```

## Residual Risks (Post v78)

1. The released lane remains intentionally bounded to deterministic conformance only
   and not hybrid checkpoint/oracle behavior.
2. `ASIR-H-xxx`, checkpoint traces, oracle request/resolution artifacts, and hybrid
   adjudication remain deferred by design to `V40-C`.
3. Projection bundles/manifests, `adeu_core_ir` lowering, and UX compatibility remain
   excluded from the released baseline.
4. The Lean sidecar remains optional and proof-mirror-only until a later explicit lock
   promotes any finite-law subset further.

## Recommendation (Post Closeout)

1. Mark the v78 edge set as closed with no blocking issues.
2. Treat canonical `adeu_architecture_conformance_report@1` plus its authoritative and
   mirrored schema exports and v78 reference fixtures as the released `V40-B`
   deterministic compiler substrate going forward.
3. Treat `V40-B` as complete at its bounded baseline on `main`; any additional
   deterministic-compiler-only hardening should be justified as exceptional rather than
   assumed.
4. Move the next default candidate to `V40-C`, where bounded hybrid ambiguity handling
   can be introduced without reopening the released deterministic compiler boundary.
