# Assessment vNext+84 Edges (Post Closeout)

This document records edge disposition for `vNext+84` (`V41-B` practical analysis
settlement, deontic typing, and compile-entitlement baseline) after arc closeout.

Status: post-closeout assessment (March 26, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS84_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "authoritative_scope": "v84_closeout_edge_disposition",
  "required_in_decision": true,
  "notes": "Pre-lock edge planning is superseded by post-closeout edge disposition in this document."
}
```

## Scope

- In scope: bounded `V41-B` practical settlement baseline; deterministic materialization
  of canonical `adeu_architecture_analysis_settlement_frame@1`; exact consumption of
  the released `V41-A` request / `source_set` boundary; grounded interpretation,
  deontic, affordance, claim-posture, escalation, and blocking-lineage registers;
  explicit `compile_entitlement`; advisory-only `advisory_notes`; committed reference
  fixture replay; authoritative/mirrored schema parity; and stop-gate/evidence
  continuity for the released settlement lane.
- Out of scope: `adeu_architecture_observation_frame@1`, repo-grounded intended
  `adeu_architecture_semantic_ir@1` compile,
  `adeu_architecture_alignment_report@1`, CLI runner release, API/web inspection
  routes, automatic repo mutation, and any observation, compile, or drift authority
  beyond the released settlement frame.

## Inputs

- `docs/ARCHITECTURE_ADEU_ARCHITECTURE_IR_v0.md`
- `docs/DRAFT_NEXT_ARC_OPTIONS_v23.md`
- `docs/DRAFT_V41_PRACTICAL_REPO_ANALYSIS_DECOMPOSITION_v0.md`
- `docs/LOCKED_CONTINUATION_vNEXT_PLUS84.md`
- `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_settlement.py`
- `packages/adeu_architecture_ir/src/adeu_architecture_ir/__init__.py`
- `packages/adeu_architecture_ir/src/adeu_architecture_ir/export_schema.py`
- `packages/adeu_architecture_ir/tests/test_analysis_settlement.py`
- `packages/adeu_architecture_ir/tests/test_architecture_ir_export_schema.py`
- `packages/adeu_architecture_ir/schema/adeu_architecture_analysis_settlement_frame.v1.json`
- `spec/adeu_architecture_analysis_settlement_frame.schema.json`
- `apps/api/fixtures/architecture/vnext_plus83/`
- `apps/api/fixtures/architecture/vnext_plus84/`
- `artifacts/quality_dashboard_v84_closeout.json`
- `artifacts/stop_gate/metrics_v84_closeout.json`
- `artifacts/agent_harness/v84/evidence_inputs/metric_key_continuity_assertion_v84.json`
- `artifacts/agent_harness/v84/evidence_inputs/runtime_observability_comparison_v84.json`
- `artifacts/agent_harness/v84/evidence_inputs/v41b_architecture_analysis_settlement_evidence_v84.json`
- merged PR: `#306`

## Pre-Lock Edge Set Outcome (v84 Closeout)

1. Silent interpretation branch choice: `resolved`.
   - the released frame now requires `interpretation_register` plus
     `chosen_interpretation_id`, and fails closed when the chosen reading is missing
     or unresolved.
2. Request / `source_set` drift during settlement: `resolved`.
   - the released frame binds `analysis_request_id`, `analysis_request_ref`,
     `source_set_hash`, and `authority_boundary_policy` exactly back to the released
     `V41-A` request boundary and rejects internal refs that fall outside that world.
3. Typed-top / mushy-inside register drift: `resolved`.
   - every interpretation, deontic, affordance, claim-posture, escalation, and
     blocking entry remains explicitly addressable and grounded instead of hiding real
     semantics inside semi-structured prose.
4. Permission-to-obligation drift and affordance disappearance: `resolved`.
   - the released frame freezes the starter deontic vocabulary, freezes affordance
     decision classes, requires explicit rationale for deferred/declined affordances,
     and requires decision coverage for any request-bound surface typed as
     `permitted`, `optional_hint`, or `fallback_affordance`.
5. Negative-claim overreach: `resolved`.
   - `unentitled_negative_claim` remains explicit, requires rationale plus bounded
     support marker, and blocks compile entitlement while active; bounded search
     absence is not laundered into proved impossibility.
6. Hidden escalation trigger drift: `resolved`.
   - the released frame freezes `escalation_trigger_policy`, requires grounded
     `active_escalation_records`, and makes `compile_entitlement = entitled` illegal
     while any active trigger remains.
7. Entitlement fail-open: `resolved`.
   - `compile_entitlement` is frozen to `entitled` / `blocked` only, and the released
     reference fixture remains honestly `blocked` with explicit `blocking_lineage`.
8. Prose escape hatch / observation / alignment creep: `resolved`.
   - the released lane stays bounded to settlement and entitlement only, and
     `advisory_notes` is non-authoritative so it cannot become a semantic backchannel.

## Guard Coverage Outcome

- merged implementation files:
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/analysis_settlement.py`
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/__init__.py`
  - `packages/adeu_architecture_ir/src/adeu_architecture_ir/export_schema.py`
- committed reference fixture under
  `apps/api/fixtures/architecture/vnext_plus84/adeu_architecture_analysis_settlement_frame_v84_reference.json`
- authoritative and mirrored schema files:
  - `packages/adeu_architecture_ir/schema/adeu_architecture_analysis_settlement_frame.v1.json`
  - `spec/adeu_architecture_analysis_settlement_frame.schema.json`
- merged guard files:
  - `packages/adeu_architecture_ir/tests/test_analysis_settlement.py`
  - `packages/adeu_architecture_ir/tests/test_architecture_ir_export_schema.py`
- v84 closeout artifact regeneration on `main` emitted:
  - canonical `metric_key_continuity_assertion@1`
  - canonical `runtime_observability_comparison@1`
  - canonical `v41b_architecture_analysis_settlement_evidence@1`
  - committed parent-session closeout raw/event stream fixture under
    `artifacts/agent_harness/v84/runtime/evidence/codex/copilot/v84-closeout-main-1/`
- merged guard coverage now proves:
  - exact request-bound settlement replay over the released v83 world,
  - chosen-interpretation resolution and rejection of missing/invalid branch choice,
  - fail-closed deontic, affordance, and claim-posture vocabulary enforcement,
  - affordance coverage over surfaced permissions and fallback hints,
  - explicit rationale and bounded-support requirements on negative claims,
  - exact request/ref closure for interpretation support, claims, escalation, and
    blocking lineage,
  - blocked entitlement while ambiguity, escalation, or unentitled negative-claim
    posture remains active,
  - advisory prose staying non-authoritative,
  - rejection of observation/alignment payload creep in the settlement lane.

## Stop-Gate Continuity Outcome

```json
{
  "schema": "v84_edge_closeout_summary@1",
  "arc": "vNext+84",
  "target_path": "V41-B",
  "prelock_edge_count": 8,
  "resolved_edge_count": 8,
  "open_blocking_edges": 0,
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v83": true,
  "all_passed": true,
  "blocking_issues": []
}
```

## Residual Risks (Post v84)

1. The released lane remains intentionally bounded to settlement and entitlement only
   and not observation, intended compile, alignment, or runner behavior.
2. The committed reference fixture in v84 exercises the `blocked` entitlement posture
   only; an `entitled` example remains intentionally deferred until a later slice can
   consume settlement honestly.
3. `compile_entitlement = entitled` is defined as permission to proceed to downstream
   compile, not a guarantee that later compile lanes will succeed.
4. Runtime observability remains informational only in `V41-B`; later practical-loop
   widening still requires its own explicit lock and closeout evidence.

## Recommendation (Post Closeout)

1. Mark the v84 edge set as closed with no blocking issues.
2. Treat `adeu_architecture_analysis_settlement_frame@1` as the canonical pre-compile
   governance artifact for practical repo analysis going forward.
3. Treat `V41-B` as complete at its bounded baseline on `main`; any settlement-lane
   widening should be justified as exceptional rather than assumed.
4. Move the next default candidate to observed implementation extraction explicitly,
   without reopening the released `V41-A` request or `V41-B` settlement boundaries.
