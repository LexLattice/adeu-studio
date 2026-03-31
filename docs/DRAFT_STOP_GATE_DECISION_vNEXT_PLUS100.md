# Draft Stop-Gate Decision (Post vNext+100)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS100.md`

Status: draft decision note (post-hoc closeout capture, March 31, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS100.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v100_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+100` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS100.md`.
- This note captures `V45-C` closeout evidence only; it does not authorize symbol-catalog
  release, test-intent matrix release, optimization-register release,
  descriptive-to-normative binding, scheduler automation, or mutation entitlement.
- Canonical `V45-C` release in v100 is carried by the
  `packages/adeu_repo_description` dependency-register schema/model/extraction surfaces,
  deterministic fixture replay under `apps/api/fixtures/repo_description/vnext_plus100/`,
  and the canonical `v45c_repo_arc_dependency_register_evidence@1` evidence input under
  `artifacts/agent_harness/v100/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#322` (`V45-C: implement v100 repo arc dependency register`)
- arc-completion merge commit: `a22d0642d9f3e562d3152245a92c5298d9ccab74`
- merged-at timestamp: `2026-03-31T04:15:10Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v100_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v100_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v100_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v100/evidence_inputs/metric_key_continuity_assertion_v100.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v100/evidence_inputs/runtime_observability_comparison_v100.json`
  - `V45-C` dependency-register evidence input:
    `artifacts/agent_harness/v100/evidence_inputs/v45c_repo_arc_dependency_register_evidence_v100.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v100/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS100_EDGES.md`

## Exit-Criteria Check (vNext+100)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V45-C` merged with green CI | required | `pass` | PR `#322`, merge commit `a22d0642d9f3e562d3152245a92c5298d9ccab74`, checks `python/web/lean-formal = pass` |
| Canonical `repo_arc_dependency_register@1` shipped with authoritative/mirror schema parity | required | `pass` | `packages/adeu_repo_description/schema/repo_arc_dependency_register.v1.json`, `spec/repo_arc_dependency_register.schema.json` |
| Deterministic dependency-register replay over accepted fixture is stable | required | `pass` | replay check in `packages/adeu_repo_description/tests/test_repo_description_v45c.py` and accepted fixture `apps/api/fixtures/repo_description/vnext_plus100/repo_arc_dependency_register_v100_reference.json` |
| Snapshot identity/hash + stale-snapshot posture are bound in emitted artifacts | required | `pass` | accepted fixture replay + required-field enforcement in `packages/adeu_repo_description/src/adeu_repo_description/models.py` |
| Dependency-policy binding remains explicit and immutable (`dependency_policy_ref` + hash) | required | `pass` | policy-hash computation and validation in `models.py` |
| Fail-closed rejection of dangling/duplicate/status/authority contradictions is shipped | required | `pass` | rejected fixtures under `apps/api/fixtures/repo_description/vnext_plus100/` plus rejection assertions in `test_repo_description_v45c.py` |
| Dependency cycles are rejected across all edge types, not only unresolved hard blockers | required | `pass` | cycle validation in `models.py` and `test_v100_rejects_dependency_cycles_even_when_edges_are_non_blocking` |
| Authority-laundering guard rejects normalized natural-language separators | required | `pass` | normalization guard in `models.py` and `test_v100_rejects_authority_terms_with_natural_language_separators` |
| Selected-path extraction no longer depends on one exact planning phrase | required | `pass` | multi-signal extraction in `packages/adeu_repo_description/src/adeu_repo_description/extract.py` and `test_v100_selected_path_extraction_accepts_consistent_non_phrase_markers` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v100_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v100/evidence_inputs/metric_key_continuity_assertion_v100.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v100/evidence_inputs/runtime_observability_comparison_v100.json` |

## Stop-Gate Summary

```json
{
  "schema": "v100_closeout_stop_gate_summary@1",
  "arc": "vNext+100",
  "target_path": "V45-C",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v99": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 96,
  "runtime_observability_delta_ms": -4
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v99_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v100_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+99","baseline_elapsed_ms":100,"baseline_source":"artifacts/stop_gate/report_v99_closeout.md","current_arc":"vNext+100","current_elapsed_ms":96,"current_source":"artifacts/stop_gate/report_v100_closeout.md","delta_ms":-4,"notes":"v100 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while adding the bounded V45-C open arc dependency-register baseline on main, including cycle rejection across all dependency edge types and normalized authority-laundering guards.","schema":"runtime_observability_comparison@1"}
```

## V45C Repo Arc Dependency Register Evidence

```json
{"schema":"v45c_repo_arc_dependency_register_evidence@1","evidence_input_path":"artifacts/agent_harness/v100/evidence_inputs/v45c_repo_arc_dependency_register_evidence_v100.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS100.md#v100-continuation-contract-machine-checkable","merged_pr":"#322","merge_commit":"a22d0642d9f3e562d3152245a92c5298d9ccab74","repo_arc_dependency_register_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_arc_dependency_register.v1.json","repo_arc_dependency_register_mirror_schema_path":"spec/repo_arc_dependency_register.schema.json","accepted_dependency_register_fixture_path":"apps/api/fixtures/repo_description/vnext_plus100/repo_arc_dependency_register_v100_reference.json"}
```

## Recommendation (Post v100)

- gate decision:
  - `V45C_REPO_ARC_DEPENDENCY_REGISTER_COMPLETE_ON_MAIN`
- rationale:
  - v100 closes the bounded `V45-C` descriptive seam on `main` with deterministic
    extraction of `repo_arc_dependency_register@1`, explicit snapshot/policy binding,
    fail-closed rejection of dangling/duplicate/status/authority contradictions, and
    merged review hardening for multi-signal planning extraction plus full-edge cycle
    rejection.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`-4 ms` vs v99 baseline).
  - widening into later `V45` lanes remains a planning selection beyond this decision
    note.
