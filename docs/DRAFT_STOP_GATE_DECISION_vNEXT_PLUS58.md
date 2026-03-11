# Draft Stop-Gate Decision (Pre-Start Scaffold vNext+58)

This note scaffolds the future arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS58.md`

Status: draft decision scaffold (pre-start, March 11, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS58.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "authoritative_scope": "v58_start_scaffold_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "This pre-start scaffold must be replaced by post-closeout evidence and final decision values before v58 is considered closed."
}
```

## Decision Guardrail (Draft)

- This draft is a planning scaffold only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS58.md`.
- This note scaffolds `V35-C` worker transcript/progress visibility closeout evidence
  only; it does not authorize `V35-D` through `V35-E`, topology UX, runtime enforcement
  promotion, closeout-hardening execution, multi-writer release, or direct worker/user
  interaction by itself.
- Until closeout, every CI run id, merge commit, artifact hash, and evidence payload in
  this file is provisional or intentionally absent.
- Runtime-observability comparison remains required evidence and informational-only in this
  arc.

## Planned Evidence Source

- CI workflow: `ci` on `main`
- anticipated implementation PRs:
  - `C1` (`contracts: add v35c transcript visibility baseline`)
  - `C2` (`tests: add v35c transcript visibility evidence and guard suite`)
- expected closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v58_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v58_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v58_closeout.md`
  - runtime observability evidence input:
    `artifacts/agent_harness/v58/evidence_inputs/runtime_observability_comparison_v58.json`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v58/evidence_inputs/metric_key_continuity_assertion_v58.json`
  - transcript visibility evidence input:
    `artifacts/agent_harness/v58/evidence_inputs/v35c_transcript_visibility_evidence_v58.json`
- expected supporting deterministic runtime closeout artifacts:
  - committed runtime evidence root: `artifacts/agent_harness/v58/runtime/evidence/codex/`
  - worker visibility state:
    `artifacts/agent_harness/v58/runtime/evidence/codex/visibility/v58-closeout-main-1/worker_visibility_state.json`
  - orchestration-state snapshot:
    `artifacts/agent_harness/v58/runtime/evidence/codex/orchestration_state/v58-closeout-main-1/orchestration_state_snapshot.json`
  - role handoff envelope:
    `artifacts/agent_harness/v58/runtime/evidence/codex/orchestration_state/v58-closeout-main-1/role_handoff_envelope.json`
  - parent session raw/event streams:
    `artifacts/agent_harness/v58/runtime/evidence/codex/copilot/v58-closeout-main-1/`
  - child raw/event streams:
    `artifacts/agent_harness/v58/runtime/evidence/codex/agent/`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS58_EDGES.md`

## Planned Exit-Criteria Check (vNext+58)

| Criterion | Threshold | Current State | Planned Evidence |
|---|---|---|---|
| `C1` merged with green CI | required | `pending` | final merge commit and CI run ids |
| `C2` merged with green CI | required | `pending` | final merge commit and CI run ids |
| Stop-gate schema-family continuity retained | required | `pending` | `artifacts/stop_gate/metrics_v58_closeout.json` |
| Stop-gate metric-key continuity retained | required | `pending` | `artifacts/agent_harness/v58/evidence_inputs/metric_key_continuity_assertion_v58.json` |
| Deterministic cardinality continuity retained (`80`) | required | `pending` | v57/v58 stop-gate metrics comparison |
| Canonical transcript visibility evidence emitted and hash-bound | required | `pending` | `artifacts/agent_harness/v58/evidence_inputs/v35c_transcript_visibility_evidence_v58.json` |
| Read-only visibility posture preserved | required | `pending` | `worker_visibility_state.json` plus v35c evidence booleans |
| Epistemic lane labels and explicit lane absence/divergence states materialized | required | `pending` | committed v58 visibility fixture |
| Continuation/compaction visibility remains explicit where present | required | `pending` | committed v58 visibility fixture |
| Progress visibility remains sourced from canonical state/event surfaces | required | `pending` | v35c evidence proves no ad hoc progress-summary bypass |
| Raw transcript and worker self-report remain non-authoritative | required | `pending` | closeout evidence plus guard coverage |
| Worker direct user-boundary remains forbidden | required | `pending` | guard coverage plus committed v58 fixture |
| Runtime observability comparison captured | required | `pending` | `artifacts/agent_harness/v58/evidence_inputs/runtime_observability_comparison_v58.json` |

Summary:

- expected stop-gate schema: `stop_gate_metrics@1`
- expected derived metric-key cardinality: `80`
- current decision status: `pending_closeout_evidence`

## Planned Metric-Key Continuity Assertion (Populate At Closeout)

```json
{
  "schema": "metric_key_continuity_assertion@1",
  "baseline_metrics_path": "artifacts/stop_gate/metrics_v57_closeout.json",
  "current_metrics_path": "artifacts/stop_gate/metrics_v58_closeout.json",
  "expected_relation": "exact_keyset_equality"
}
```

## Planned Runtime Observability Comparison (Populate At Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+57",
  "baseline_source": "artifacts/stop_gate/report_v57_closeout.md",
  "current_arc": "vNext+58",
  "current_source": "artifacts/stop_gate/report_v58_closeout.md",
  "notes": "Populate elapsed_ms values at closeout; v58 observability remains informational-only under frozen stop-gate semantics."
}
```

## Planned V35-C Transcript Visibility Evidence Shape

```json
{
  "schema": "v35c_transcript_visibility_evidence@1",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS58.md#v35c_transcript_visibility_contract@1",
  "evidence_input_path": "artifacts/agent_harness/v58/evidence_inputs/v35c_transcript_visibility_evidence_v58.json",
  "worker_visibility_state_path": "evidence/codex/visibility/v58-closeout-main-1/worker_visibility_state.json",
  "orchestration_state_snapshot_path": "evidence/codex/orchestration_state/v58-closeout-main-1/orchestration_state_snapshot.json",
  "role_handoff_envelope_path": "evidence/codex/orchestration_state/v58-closeout-main-1/role_handoff_envelope.json",
  "required_booleans": [
    "read_only_visibility_preserved",
    "epistemic_lane_labels_present",
    "explicit_lane_absence_materialized",
    "explicit_divergence_state_materialized",
    "continuation_bridge_visibility_present_when_available",
    "no_ad_hoc_progress_summary_bypass",
    "raw_transcript_non_authoritative",
    "worker_self_report_non_authoritative_until_reconciled",
    "worker_direct_user_boundary_forbidden",
    "verification_passed"
  ],
  "metric_key_cardinality_expected": 80,
  "metric_key_exact_set_equal_v57_expected": true
}
```

## Recommendation (Pre v58)

- gate decision:
  - `PENDING_VNEXT_PLUS58_IMPLEMENTATION`
- rationale:
  - v57 closed `V35-B` and restored eligibility for a fresh `V35-C` planning/lock pass.
  - v58 should stay a read-only transcript/progress visibility slice over the frozen
    v56/v57 substrate rather than widening into topology UX or runtime enforcement.
  - final go/no-go depends on `C1`/`C2` landing with green CI and deterministic closeout
    evidence.
