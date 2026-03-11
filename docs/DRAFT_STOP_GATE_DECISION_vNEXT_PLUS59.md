# Draft Stop-Gate Decision (Pre-Start Scaffold vNext+59)

This note scaffolds the future arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS59.md`

Status: draft decision scaffold (pre-start, March 11, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS59.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "authoritative_scope": "v59_start_scaffold_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "This pre-start scaffold must be replaced by post-closeout evidence and final decision values before v59 is considered closed."
}
```

## Decision Guardrail (Draft)

- This draft is a planning scaffold only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS59.md`.
- This note scaffolds `V35-D` topology/duty map closeout evidence only; it does not
  authorize `V35-E`, runtime enforcement promotion, closeout-hardening execution,
  multi-writer release, or direct worker/user interaction by itself.
- Until closeout, every CI run id, merge commit, artifact hash, and evidence payload in
  this file is provisional or intentionally absent.
- Runtime-observability comparison remains required evidence and informational-only in this
  arc.

## Planned Evidence Source

- CI workflow: `ci` on `main`
- anticipated implementation PRs:
  - `D1` (`runtime: add v35d topology duty map baseline`)
  - `D2` (`runtime: add v35d topology duty map evidence guards`)
- expected closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v59_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v59_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v59_closeout.md`
  - runtime observability evidence input:
    `artifacts/agent_harness/v59/evidence_inputs/runtime_observability_comparison_v59.json`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v59/evidence_inputs/metric_key_continuity_assertion_v59.json`
  - topology/duty evidence input:
    `artifacts/agent_harness/v59/evidence_inputs/v35d_topology_duty_map_evidence_v59.json`
- expected supporting deterministic runtime closeout artifacts:
  - committed runtime evidence root: `artifacts/agent_harness/v59/runtime/evidence/codex/`
  - topology duty map state:
    `artifacts/agent_harness/v59/runtime/evidence/codex/topology/v59-closeout-main-1/topology_duty_map_state.json`
  - worker visibility state:
    `artifacts/agent_harness/v59/runtime/evidence/codex/visibility/v59-closeout-main-1/worker_visibility_state.json`
  - execution topology state:
    `artifacts/agent_harness/v59/runtime/evidence/codex/orchestration_state/v59-closeout-main-1/execution_topology_state.json`
  - write lease state:
    `artifacts/agent_harness/v59/runtime/evidence/codex/orchestration_state/v59-closeout-main-1/write_lease_state.json`
  - role handoff envelope:
    `artifacts/agent_harness/v59/runtime/evidence/codex/orchestration_state/v59-closeout-main-1/role_handoff_envelope.json`
  - parent session raw/event streams:
    `artifacts/agent_harness/v59/runtime/evidence/codex/copilot/v59-closeout-main-1/`
  - child raw/event streams:
    `artifacts/agent_harness/v59/runtime/evidence/codex/agent/`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS59_EDGES.md`

## Planned Exit-Criteria Check (vNext+59)

| Criterion | Threshold | Current State | Planned Evidence |
|---|---|---|---|
| `D1` merged with green CI | required | `pending` | final merge commit and CI run ids |
| `D2` merged with green CI | required | `pending` | final merge commit and CI run ids |
| Stop-gate schema-family continuity retained | required | `pending` | `artifacts/stop_gate/metrics_v59_closeout.json` |
| Stop-gate metric-key continuity retained | required | `pending` | `artifacts/agent_harness/v59/evidence_inputs/metric_key_continuity_assertion_v59.json` |
| Deterministic cardinality continuity retained (`80`) | required | `pending` | v58/v59 stop-gate metrics comparison |
| Canonical topology/duty evidence emitted and hash-bound | required | `pending` | `artifacts/agent_harness/v59/evidence_inputs/v35d_topology_duty_map_evidence_v59.json` |
| Topology/duty view remains derived from canonical execution state only | required | `pending` | `topology_duty_map_state.json` plus v35d evidence booleans |
| Current write-lease holder and explanatory duties are projected correctly without authority inflation | required | `pending` | committed v59 topology fixture plus evidence booleans |
| Node and edge provenance markers plus artifact/event-stream provenance refs are materialized | required | `pending` | committed v59 topology fixture |
| Advisory blockers remain non-governance in topology rendering | required | `pending` | v35d evidence plus guard coverage |
| Continuation/compaction visibility remains explicit where present | required | `pending` | committed v59 topology fixture |
| Runtime observability comparison captured | required | `pending` | `artifacts/agent_harness/v59/evidence_inputs/runtime_observability_comparison_v59.json` |

Summary:

- expected stop-gate schema: `stop_gate_metrics@1`
- expected derived metric-key cardinality: `80`
- current decision status: `pending_closeout_evidence`

## Planned Runtime Observability Comparison (Populate At Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+58",
  "baseline_source": "artifacts/stop_gate/report_v58_closeout.md",
  "current_arc": "vNext+59",
  "current_source": "artifacts/stop_gate/report_v59_closeout.md",
  "notes": "Populate elapsed_ms values at closeout; v59 observability remains informational-only under frozen stop-gate semantics."
}
```

## Planned V35-D Topology/Duty Evidence Shape

```json
{
  "schema": "v35d_topology_duty_map_evidence@1",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS59.md#v35d_topology_duty_map_contract@1",
  "evidence_input_path": "artifacts/agent_harness/v59/evidence_inputs/v35d_topology_duty_map_evidence_v59.json",
  "topology_duty_map_state_path": "evidence/codex/topology/v59-closeout-main-1/topology_duty_map_state.json",
  "execution_topology_state_path": "evidence/codex/orchestration_state/v59-closeout-main-1/execution_topology_state.json",
  "worker_visibility_state_path": "evidence/codex/visibility/v59-closeout-main-1/worker_visibility_state.json",
  "required_booleans": [
    "derived_from_canonical_execution_state_only",
    "current_write_lease_holder_projected",
    "current_duty_not_authority_inflating",
    "provenance_markers_materialized",
    "artifact_and_event_stream_provenance_refs_resolve",
    "advisory_blockers_not_rendered_as_governance_blockers",
    "continuation_bridge_and_compaction_visibility_preserved",
    "non_authoritative_topology_surface_preserved",
    "verification_passed"
  ],
  "metric_key_cardinality_expected": 80,
  "metric_key_exact_set_equal_v58_expected": true
}
```

## Recommendation (Pre v59)

- gate decision:
  - `PENDING_VNEXT_PLUS59_IMPLEMENTATION`
- rationale:
  - v58 closed `V35-C` and restored eligibility for a fresh `V35-D` planning/lock pass.
  - v59 should stay a read-only topology/duty map slice over the frozen v56/v57/v58
    substrate rather than widening into runtime enforcement or direct worker/user
    interaction.
  - final go/no-go depends on `D1`/`D2` landing with green CI and deterministic closeout
    evidence.
