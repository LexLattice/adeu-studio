# Draft Stop-Gate Decision (Pre vNext+68)

This note records the pre-start decision scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS68.md`

Status: draft decision note (pre-start scaffold, March 17, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS68.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "authoritative_scope": "v68_start_stop_gate_scaffold",
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "This is a pre-start scaffold only. Closeout evidence and final decision values must replace this state after v68 implementation completes."
}
```

## Decision Guardrail (Frozen)

- This draft is a pre-start scaffold only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS68.md`.
- This note does not claim `C1` or `C2` are complete.
- This note does not authorize `V37-D` or `V37-E` by itself.
- Runtime-observability comparison remains required evidence at closeout and
  informational-only in this family.

## Planned Evidence Source

- expected CI workflow: `ci` on `main`
- planned implementation PRs:
  - `C1` executable reference loop + checkpoint-result-manifest baseline
  - `C2` executable reference-loop evidence + determinism/guard suite
- expected closeout artifacts:
  - `artifacts/quality_dashboard_v68_closeout.json`
  - `artifacts/stop_gate/metrics_v68_closeout.json`
  - `artifacts/stop_gate/report_v68_closeout.md`
  - `artifacts/agent_harness/v68/evidence_inputs/metric_key_continuity_assertion_v68.json`
  - `artifacts/agent_harness/v68/evidence_inputs/runtime_observability_comparison_v68.json`
  - `artifacts/agent_harness/v68/evidence_inputs/v37c_reference_loop_evidence_v68.json`

## Planned Exit-Criteria Check (vNext+68)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `C1` merged with green CI | required | `pending` | implementation not started |
| `C2` merged with green CI | required | `pending` | implementation not started |
| Stop-gate schema-family continuity retained | required | `pending` | closeout artifacts not generated |
| Stop-gate metric-key continuity retained | required | `pending` | closeout artifacts not generated |
| Canonical `meta_loop_checkpoint_result_manifest@1` and one accepted executable reference run emitted and hash-bound | required | `pending` | implementation not started |
| Accepted executable reference run binds exactly to the released `V37-A` and `V37-B` reference pairs | required | `pending` | implementation not started |
| Actual hard checkpoint outputs are captured from real executor bindings under the shared tuple | required | `pending` | implementation not started |
| Executed hard-checkpoint subset is explicit and intentional for the first accepted run | required | `pending` | implementation not started |
| The authoritative stop-gate executor surface is frozen and verified | required | `pending` | implementation not started |
| The accepted executed trace is distinct from the frozen `V37-B` reference trace and records realized branch/retry outcomes when exercised | required | `pending` | implementation not started |
| Attempted failed checkpoint steps still emit normalized manifest rows | required | `pending` | implementation not started |
| Observed gate truth remains derived from actual checkpoint outputs rather than from reasoning prose | required | `pending` | implementation not started |
| No diagnostics, conformance, or control-update export is released | required | `pending` | implementation not started |
| Runtime observability comparison captured | required | `pending` | closeout artifacts not generated |

## Pre-Start Recommendation

- gate decision:
  - `GO_VNEXT_PLUS68_IMPLEMENTATION_DRAFT`
- rationale:
  - `V37-A` and `V37-B` are now closed and provide the minimum stable substrate
    required before any executable recursive-compilation loop can be governed cleanly.
  - current repo hard checkpoint surfaces, typed module ontology, and typed
    sequence/trace substrate now exist, but no released executable reference loop or
    checkpoint-result-manifest surface yet exists on `main`.
