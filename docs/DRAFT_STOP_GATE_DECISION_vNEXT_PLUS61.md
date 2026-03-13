# Draft Stop-Gate Decision (Pre vNext+61)

This note records the pre-start stop-gate scaffold for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md`

Status: draft decision scaffold (pre-start, March 14, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS61.md",
  "phase": "pre_start_scaffold",
  "authoritative": false,
  "authoritative_scope": "v61_pre_start_stop_gate_scaffold",
  "required_in_closeout": true,
  "all_passed": false,
  "notes": "Pre-start scaffold only. Closeout evidence and final decision values must replace these placeholders after v61 implementation closes."
}
```

## Decision Guardrail (Frozen)

- This draft records pre-start planning intent only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS61.md`.
- This scaffold does not authorize `V36-B`, `V36-C`, `V36-D`, `V36-E`, any rendered
  route, any generic design-system release, any broad `apps/web` retrofit, or any
  `O1`/`O2`/`O3` closeout-hardening execution by itself.
- Canonical `V36-A` release in v61 is planned as a typed UX-governance artifact baseline
  only; no stop-gate schema-family fork or metric-key expansion is authorized here.

## Planned Evidence Sources

- CI workflow: `ci` on `main`
- intended implementation PRs:
  - `A1` canonical UX domain packet + morph IR baseline
  - `A2` domain/morph evidence + determinism/guard suite
- expected deterministic closeout artifacts (if v61 merges):
  - quality dashboard JSON: `artifacts/quality_dashboard_v61_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v61_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v61_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v61/evidence_inputs/metric_key_continuity_assertion_v61.json`
  - domain/morph evidence input:
    `artifacts/agent_harness/v61/evidence_inputs/v36a_ux_domain_morph_ir_evidence_v61.json`
  - committed runtime/evidence root:
    `artifacts/agent_harness/v61/`

## Planned Exit-Criteria Check (vNext+61)

| Criterion | Threshold | Current State | Planned Evidence |
|---|---|---|---|
| `A1` merged with green CI | required | `pending` | implementation PR / Actions run |
| `A2` merged with green CI | required | `pending` | implementation PR / Actions run |
| Stop-gate schema-family continuity retained | required | `pending` | `artifacts/stop_gate/metrics_v61_closeout.json` |
| Deterministic cardinality continuity retained (`80`) | required | `pending` | `metrics_v61_closeout.json` plus `metric_key_continuity_assertion_v61.json` |
| Canonical `ux_domain_packet@1` / `ux_morph_ir@1` schemas and reference instances emitted and hash-bound | required | `pending` | `v36a_ux_domain_morph_ir_evidence_v61.json` |
| Reference instances are coherently bound as one pair | required | `pending` | `v36a_ux_domain_morph_ir_evidence_v61.json` |
| Approved profile table contains exactly two explicit approved profiles and rejects out-of-table combinations | required | `pending` | `v36a_ux_domain_morph_ir_evidence_v61.json` |
| Same-context reachability glossary remains frozen in substrate terms only | required | `pending` | `v36a_ux_domain_morph_ir_evidence_v61.json` |
| No free-form brief-to-code bypass or authority-minting drift released | required | `pending` | `v36a_ux_domain_morph_ir_evidence_v61.json` plus tests |
| No projection/interaction/rendered-surface/compiler widening released | required | `pending` | lock-scope conformance + merged PR scope |

## Planned Stop-Gate Summary

- `schema = "stop_gate_metrics@1"` is expected to remain unchanged.
- `valid = true` is required at closeout.
- `all_passed = true` is required at closeout.
- `issues = []` is required at closeout.
- `derived_cardinality = 80` must remain unchanged at closeout.

## Recommendation (Pre-Start)

- gate decision:
  - `GO_VNEXT_PLUS61_IMPLEMENTATION_DRAFT`
- rationale:
  - `V35` is closed and `docs/DRAFT_NEXT_ARC_OPTIONS_v10.md` now selects `V36-A` as the
    next default candidate.
  - v61 is scoped as the minimum viable typed UX-governance substrate:
    schemas, reference instances, approved profiles, glossary, and evidence/guards only.
  - no rendered surface, projection layer, diagnostics engine, compiler export, or broad
    UX retrofit is authorized in this arc.
