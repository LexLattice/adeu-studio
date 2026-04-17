# Draft Stop-Gate Decision (Post vNext+171)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS171.md`

Status: draft decision note (post-closeout capture, April 17, 2026 UTC).

Authority layer: closeout evidence on `main` only.

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS171.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v171_closeout_stop_gate_decision_on_main",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+171` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS171.md`.
- This note captures bounded `V62-B` external-assistant egress bridge evidence
  only on `main`; it does not by itself authorize connector hardening law,
  human-via-connector law, remote-operator law, bridge-office mutation,
  rewitness mutation, advisory-to-live promotion, repo-bound writable authority
  widening, replay/resume widening, execute widening, dispatch widening,
  product/UI rollout as authority, or hidden-cognition governance.
- Canonical `V62-B` shipment in `v171` is carried by reused
  `packages/adeu_agentic_de` package surfaces, one thin
  `apps/api/scripts/run_agentic_de_external_assistant_egress_bridge_v62b.py`
  seam, authoritative and mirrored `V62-B` schema export, deterministic `v62b`
  fixtures, and canonical `v62b_external_assistant_egress_bridge_evidence@1`
  evidence input under `artifacts/agent_harness/v171/evidence_inputs/`.
- Runtime observability comparison remains required evidence and
  informational-only in this arc.

## Evidence Source

- merged implementation PR:
  - `#398` (`feat: implement V62-B egress bridge`)
- arc-completion merge commit:
  - `857a7f907562c83a7f5a34b0b2ce747829ac7f4a`
- merged-at timestamp:
  - `2026-04-17T03:15:10+03:00`
- implementation commits integrated by the merge:
  - `267e5438b6cf8eec7f673faa2a3064a2dd4a8ee3`
    (`feat: implement V62-B egress bridge`)
  - `c1e6f5ed4f9f47c9f5d6422984abf57fd99dc311`
    (`fix: tighten V62-B egress lineage checks`)
- docs/artifacts-only closeout verification for this closeout bundle:
  - `make arc-closeout-check ARC=171`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v171_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v171_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v171_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v171/evidence_inputs/metric_key_continuity_assertion_v171.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v171/evidence_inputs/runtime_observability_comparison_v171.json`
  - `V62-B` egress bridge evidence input:
    `artifacts/agent_harness/v171/evidence_inputs/v62b_external_assistant_egress_bridge_evidence_v171.json`
  - committed runtime event-stream witness:
    `artifacts/agent_harness/v171/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS171_EDGES.md`

## Exit-Criteria Check (vNext+171)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V62-B` merged on `main` | required | `pass` | PR `#398`, merge commit `857a7f907562c83a7f5a34b0b2ce747829ac7f4a` |
| Existing package surfaces remained bounded to `adeu_agentic_de` with one thin `v62b` script seam | required | `pass` | merged diff stayed in that package surface plus schema/fixture/test and one CLI runner |
| Slice remained egress-only follow-on over shipped `V62-A` admission and ingress bridge bases | required | `pass` | shipped checker/tests enforce consumed `V62-A` refs and egress-only `V62-B` posture |
| Selected connector principal remained `external_assistant` only | required | `pass` | shipped checker/tests keep principal typing explicit and fail closed on other classes |
| Positive rewitness basis remained explicit and fail-closed | required | `pass` | shipped checker/tests require witness basis or certificate for positive rewitness posture |
| Egress bridge stayed transport-bounded and non-authorizing | required | `pass` | non-equivalence law remains explicit and enforced by shipped tests |
| `V61-A`/`V61-B` lineage consumption remained shipped and non-ambient | required | `pass` | shipped checker/tests pin bridge binding and rewitness lineage to shipped surfaces only |
| Path-level non-generalization posture remained intact | required | `pass` | merged slice does not generalize into human-via-connector, remote, repo, or execute law |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v171_closeout.json` has `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v171/evidence_inputs/metric_key_continuity_assertion_v171.json` records exact keyset equality versus `v170` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v171/evidence_inputs/runtime_observability_comparison_v171.json` records `90 ms` current elapsed, `136 ms` baseline elapsed, `-46 ms` delta |

## Stop-Gate Summary

```json
{
  "schema": "v171_closeout_stop_gate_summary@1",
  "arc": "vNext+171",
  "target_path": "V62-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v170": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 90,
  "runtime_observability_delta_ms": -46
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v170_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v171_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+170","current_arc":"vNext+171","baseline_source":"artifacts/stop_gate/report_v170_closeout.md","current_source":"artifacts/stop_gate/report_v171_closeout.md","baseline_elapsed_ms":136,"current_elapsed_ms":90,"delta_ms":-46,"notes":"v171 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the bounded V62-B external-assistant egress bridge on main: one typed, replayable egress bridge packet over one admitted codex live connector path, explicit external-assistant principal posture only, explicit consumed bridge-office and rewitness basis carry-through with fail-closed positive rewitness basis requirements, explicit path-level non-generalization, and no human-via-connector/connector-hardening/remote/repo/replay/execute/dispatch widening."}
```

## V62B External Assistant Egress Bridge Evidence

```json
{"schema":"v62b_external_assistant_egress_bridge_evidence@1","evidence_input_path":"artifacts/agent_harness/v171/evidence_inputs/v62b_external_assistant_egress_bridge_evidence_v171.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS171.md#machine-checkable-contract","merged_pr":"#398","merge_commit":"857a7f907562c83a7f5a34b0b2ce747829ac7f4a","implementation_commit":"267e5438b6cf8eec7f673faa2a3064a2dd4a8ee3","review_hardening_commit":"c1e6f5e83b7968e9de7f89075da0d375f76c359d"}
```

## Recommendation (Post v171)

- gate decision:
  - `V62B_EXTERNAL_ASSISTANT_EGRESS_BRIDGE_COMPLETE_ON_MAIN`
- rationale:
  - `v171` closes the bounded `V62-B` egress bridge follow-on seam on `main`.
  - the shipped slice stayed properly bounded:
    - same existing repo-owned package surface
    - one thin runner seam
    - one exact admitted connector path only
    - one explicit `external_assistant` principal only
    - one typed external-assistant egress bridge packet
    - consumed shipped `V62-A` admission and ingress bridge lineage
    - consumed shipped `V61-A` egress and shipped `V61-B` office/rewitness lineage
    - explicit positive rewitness basis carry-through and fail-closed enforcement
    - no human-via-connector semantics
    - no connector hardening, remote, repo, replay/resume, execute, or dispatch widening
  - stop-gate schema-family and metric-key continuity stayed intact.
  - runtime observability remained informational-only.
  - `V62-B` is now closed on `main`; the next move should be `V62-C` rather than
    widening `V62-B` in place.
