# Draft Stop-Gate Decision (Post vNext+104)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS104.md`

Status: draft decision note (post-hoc closeout capture, April 1, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS104.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v104_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+104` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS104.md`.
- This note captures bounded `V45-E` release evidence only; it does not authorize
  `V45-F`, recursive-governance widening, amendment entitlement, automatic scheduling,
  automatic repo mutation, or normative binding promotion.
- Canonical `V45-E` release in v104 is carried by the
  `packages/adeu_repo_description` optimization-register schema/model/extraction
  surfaces, deterministic fixture replay under
  `apps/api/fixtures/repo_description/vnext_plus104/`, and the canonical
  `v45e_repo_optimization_register_evidence@1` evidence input under
  `artifacts/agent_harness/v104/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#326` (`V45-E: implement v104 repo optimization register`)
- arc-completion merge commit: `864df1c0a1ac675becade0906c6ea16622050513`
- merged-at timestamp: `2026-04-01T06:48:20Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v104_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v104_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v104_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v104/evidence_inputs/metric_key_continuity_assertion_v104.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v104/evidence_inputs/runtime_observability_comparison_v104.json`
  - `V45-E` release evidence input:
    `artifacts/agent_harness/v104/evidence_inputs/v45e_repo_optimization_register_evidence_v104.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v104/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS104_EDGES.md`

## Exit-Criteria Check (vNext+104)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V45-E` merged with green CI | required | `pass` | PR `#326`, merge commit `864df1c0a1ac675becade0906c6ea16622050513`, checks `python/web/lean-formal = pass` |
| Canonical `repo_optimization_register@1` shipped with authoritative/mirror schema parity | required | `pass` | `packages/adeu_repo_description/schema/repo_optimization_register.v1.json`, `spec/repo_optimization_register.schema.json` |
| Deterministic replay over the accepted v104 fixture is stable | required | `pass` | replay check in `packages/adeu_repo_description/tests/test_repo_description_v45e.py` and accepted fixture `apps/api/fixtures/repo_description/vnext_plus104/repo_optimization_register_v104_reference.json` |
| Explicit snapshot identity/hash, explicit bounded source-set binding, and explicit `source_set_hash` are present | required | `pass` | accepted fixture replay plus required-field enforcement in `packages/adeu_repo_description/src/adeu_repo_description/models.py` |
| Explicit `V45-A` through `V45-D` binding is enforced with shared snapshot identity and artifact-local source-scope compatibility | required | `pass` | `validate_repo_optimization_register_against_v45_baseline` in `packages/adeu_repo_description/src/adeu_repo_description/models.py` and baseline-binding coverage in `packages/adeu_repo_description/tests/test_repo_description_v45e.py` |
| Each optimization row preserves explicit distinction between descriptive finding, optimization candidate, and amendment entitlement | required | `pass` | row-model anchors in `models.py` and accepted fixture replay in `test_repo_description_v45e.py` |
| `cross_surface_cluster` rows carry explicit member carriers and bounded secondary tags preserve mixed findings without flattening | required | `pass` | accepted fixture replay and row-shape assertions in `packages/adeu_repo_description/tests/test_repo_description_v45e.py` |
| `source_artifact_refs` membership is constrained to the declared source set and internal finding scopes fail closed when unresolved | required | `pass` | membership/scope validation in `models.py` and reject fixtures `repo_optimization_register_v104_reject_source_artifact_ref_outside_source_set.json` plus `repo_optimization_register_v104_reject_unresolved_finding_scope.json` |
| Unsupported optimization claims, missing support basis, malformed cluster carriers, and amendment-entitlement laundering fail closed | required | `pass` | reject fixtures under `apps/api/fixtures/repo_description/vnext_plus104/` and rejection assertions in `packages/adeu_repo_description/tests/test_repo_description_v45e.py` |
| Historical `V45-C` baseline context remains explicit and planning-stable rather than silently re-derived from current branch state | required | `pass` | `_load_historical_v45c_v102_reference` in `packages/adeu_repo_description/src/adeu_repo_description/extract.py` and accepted fixture replay in `test_repo_description_v45e.py` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v104_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v104/evidence_inputs/metric_key_continuity_assertion_v104.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v104/evidence_inputs/runtime_observability_comparison_v104.json` |

## Stop-Gate Summary

```json
{
  "schema": "v104_closeout_stop_gate_summary@1",
  "arc": "vNext+104",
  "target_path": "V45-E",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v103": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 96,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v103_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v104_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+103","current_arc":"vNext+104","baseline_source":"artifacts/stop_gate/report_v103_closeout.md","current_source":"artifacts/stop_gate/report_v104_closeout.md","baseline_elapsed_ms":96,"current_elapsed_ms":96,"delta_ms":0,"notes":"v104 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V45-E repo_optimization_register@1 surface with explicit descriptive-finding versus optimization-candidate separation, explicit negative amendment-entitlement posture, bounded cross-surface-cluster carriers, source-set membership enforcement, and explicit historical V45-C baseline loading."}
```

## V45E Repo Optimization Register Evidence

```json
{"schema":"v45e_repo_optimization_register_evidence@1","evidence_input_path":"artifacts/agent_harness/v104/evidence_inputs/v45e_repo_optimization_register_evidence_v104.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS104.md#v104-continuation-contract-machine-checkable","merged_pr":"#326","merge_commit":"864df1c0a1ac675becade0906c6ea16622050513","repo_optimization_register_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_optimization_register.v1.json","repo_optimization_register_mirror_schema_path":"spec/repo_optimization_register.schema.json","accepted_optimization_register_fixture_path":"apps/api/fixtures/repo_description/vnext_plus104/repo_optimization_register_v104_reference.json"}
```

## Recommendation (Post v104)

- gate decision:
  - `V45E_REPO_OPTIMIZATION_REGISTER_COMPLETE_ON_MAIN`
- rationale:
  - v104 closes the bounded `V45-E` widening seam on `main` by shipping a
    deterministic `repo_optimization_register@1` surface with explicit descriptive
    finding versus optimization candidate versus amendment entitlement separation,
    explicit bounded compression/support vocabularies, and explicit binding back to
    the released `V45-A` through `V45-D` descriptive baseline.
  - the shipped slice remains descriptive-first and non-promotional: hotspot and
    consolidation findings do not become scheduling, mutation, or amendment
    entitlement.
  - review hardening closed a concrete implementation brittleness risk by centralizing
    historical `V45-C` baseline loading instead of leaving that fixture coupling
    inline in the main derivation body.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`0 ms` vs v103 baseline).
  - broader widening into `V45-F` remains a planning selection beyond this decision
    note.
