# Draft Stop-Gate Decision (Pre-Start Scaffold vNext+60)

This note scaffolds the future arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md`

Status: draft decision scaffold (pre-start, March 12, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS60.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "authoritative_scope": "v60_start_scaffold_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "This pre-start scaffold must be replaced by post-closeout evidence and final decision values before v60 is considered closed."
}
```

## Decision Guardrail (Draft)

- This draft is a planning scaffold only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md`.
- This note scaffolds `V35-E` bounded runtime-enforcement closeout evidence only; it does
  not authorize multi-writer release, closeout-hardening execution, topology editing, or
  direct worker/user interaction by itself.
- Until closeout, every CI run id, merge commit, artifact hash, and evidence payload in
  this file is provisional or intentionally absent.
- Runtime-observability comparison remains required evidence and informational-only in this
  arc.

## Planned Evidence Source

- CI workflow: `ci` on `main`
- anticipated implementation PRs:
  - `E1` (`runtime: add v60 e1 bounded runtime enforcement`)
  - `E2` (`runtime: add v60 e2 enforcement evidence guards`)
- expected closeout artifacts:
  - quality dashboard JSON: `artifacts/quality_dashboard_v60_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v60_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v60_closeout.md`
  - runtime observability evidence input:
    `artifacts/agent_harness/v60/evidence_inputs/runtime_observability_comparison_v60.json`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v60/evidence_inputs/metric_key_continuity_assertion_v60.json`
  - runtime-enforcement evidence input:
    `artifacts/agent_harness/v60/evidence_inputs/v35e_runtime_enforcement_evidence_v60.json`
- expected supporting deterministic runtime closeout artifacts:
  - committed runtime evidence root: `artifacts/agent_harness/v60/runtime/evidence/codex/`
  - topology duty map state:
    `artifacts/agent_harness/v60/runtime/evidence/codex/topology/v60-closeout-main-1/topology_duty_map_state.json`
  - worker visibility state:
    `artifacts/agent_harness/v60/runtime/evidence/codex/visibility/v60-closeout-main-1/worker_visibility_state.json`
  - orchestration-state snapshot:
    `artifacts/agent_harness/v60/runtime/evidence/codex/orchestration_state/v60-closeout-main-1/orchestration_state_snapshot.json`
  - write lease state:
    `artifacts/agent_harness/v60/runtime/evidence/codex/orchestration_state/v60-closeout-main-1/write_lease_state.json`
  - role transition record:
    `artifacts/agent_harness/v60/runtime/evidence/codex/orchestration_state/v60-closeout-main-1/role_transition_record.json`
  - role handoff envelope:
    `artifacts/agent_harness/v60/runtime/evidence/codex/orchestration_state/v60-closeout-main-1/role_handoff_envelope.json`
  - parent session raw/event streams:
    `artifacts/agent_harness/v60/runtime/evidence/codex/copilot/v60-closeout-main-1/`
  - child raw/event streams:
    `artifacts/agent_harness/v60/runtime/evidence/codex/agent/`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS60_EDGES.md`

## Planned Exit-Criteria Check (vNext+60)

| Criterion | Threshold | Current State | Planned Evidence |
|---|---|---|---|
| `E1` merged with green CI | required | `pending` | final merge commit and CI run ids |
| `E2` merged with green CI | required | `pending` | final merge commit and CI run ids |
| Stop-gate schema-family continuity retained | required | `pending` | `artifacts/stop_gate/metrics_v60_closeout.json` |
| Stop-gate metric-key continuity retained | required | `pending` | `artifacts/agent_harness/v60/evidence_inputs/metric_key_continuity_assertion_v60.json` |
| Deterministic cardinality continuity retained (`80`) | required | `pending` | v59/v60 stop-gate metrics comparison |
| Canonical runtime-enforcement evidence emitted and hash-bound | required | `pending` | `artifacts/agent_harness/v60/evidence_inputs/v35e_runtime_enforcement_evidence_v60.json` |
| Invalid spawn role/task/scope/lease combinations are denied deterministically | required | `pending` | enforcement evidence booleans plus merged E2 guards |
| Support-role proxy authority attempts are denied | required | `pending` | enforcement evidence booleans plus merged E2 guards |
| Claimed-work handoff required-field gaps are denied | required | `pending` | enforcement evidence booleans plus merged E2 guards |
| Observability surfaces remain read-only and non-authoritative | required | `pending` | committed v60 topology/visibility fixtures plus enforcement evidence booleans |
| Acceptance and closeout authority remain preserved | required | `pending` | committed v60 artifacts plus enforcement evidence booleans |
| Runtime observability comparison captured | required | `pending` | `artifacts/agent_harness/v60/evidence_inputs/runtime_observability_comparison_v60.json` |

Summary:

- expected stop-gate schema: `stop_gate_metrics@1`
- expected derived metric-key cardinality: `80`
- current decision status: `pending_closeout_evidence`

## Planned Runtime Observability Comparison (Populate At Closeout)

```json
{
  "schema": "runtime_observability_comparison@1",
  "baseline_arc": "vNext+59",
  "baseline_source": "artifacts/stop_gate/report_v59_closeout.md",
  "current_arc": "vNext+60",
  "current_source": "artifacts/stop_gate/report_v60_closeout.md",
  "notes": "Populate elapsed_ms values at closeout; v60 observability remains informational-only under frozen stop-gate semantics."
}
```

## Planned V35-E Runtime-Enforcement Evidence Shape

```json
{
  "schema": "v35e_runtime_enforcement_evidence@1",
  "contract_source": "docs/LOCKED_CONTINUATION_vNEXT_PLUS60.md#v35e_runtime_enforcement_contract@1",
  "evidence_input_path": "artifacts/agent_harness/v60/evidence_inputs/v35e_runtime_enforcement_evidence_v60.json",
  "orchestration_state_snapshot_path": "evidence/codex/orchestration_state/v60-closeout-main-1/orchestration_state_snapshot.json",
  "write_lease_state_path": "evidence/codex/orchestration_state/v60-closeout-main-1/write_lease_state.json",
  "role_transition_record_path": "evidence/codex/orchestration_state/v60-closeout-main-1/role_transition_record.json",
  "role_handoff_envelope_path": "evidence/codex/orchestration_state/v60-closeout-main-1/role_handoff_envelope.json",
  "worker_visibility_state_path": "evidence/codex/visibility/v60-closeout-main-1/worker_visibility_state.json",
  "topology_duty_map_state_path": "evidence/codex/topology/v60-closeout-main-1/topology_duty_map_state.json",
  "required_booleans": [
    "required_enforcement_surfaces_active",
    "single_builder_default_enforced_at_runtime",
    "support_role_proxy_authority_blocked",
    "claimed_work_handoff_validation_enforced",
    "scope_kind_validation_enforced",
    "deterministic_denial_surfaces_recorded",
    "released_happy_path_preserved_under_runtime_enforcement",
    "observability_surfaces_remain_read_only",
    "acceptance_and_closeout_authority_preserved",
    "worker_direct_user_boundary_forbidden",
    "verification_passed"
  ],
  "metric_key_cardinality_expected": 80,
  "metric_key_exact_set_equal_v59_expected": true
}
```

## Recommendation (Pre v60)

- gate decision:
  - `PENDING_VNEXT_PLUS60_IMPLEMENTATION`
- rationale:
  - v59 closed `V35-D` and restored eligibility for a fresh `V35-E` planning/lock pass.
  - v60 should stay a bounded runtime-enforcement slice over the frozen v56-v59
    substrate rather than widening into multi-writer execution, closeout automation, or
    direct worker/user interaction.
  - final go/no-go depends on `E1`/`E2` landing with green CI and deterministic closeout
    evidence.
