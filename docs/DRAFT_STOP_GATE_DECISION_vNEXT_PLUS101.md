# Draft Stop-Gate Decision (Post vNext+101)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS101.md`

Status: draft decision note (post-hoc closeout capture, March 31, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS101.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v101_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+101` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS101.md`.
- This note captures bounded `V45-B` release evidence only; it does not authorize
  test-intent matrix release, optimization-register release, descriptive-to-normative
  binding, scheduler automation, mutation entitlement, or recursive-governance
  widening.
- Canonical `V45-B` release in v101 is carried by the
  `packages/adeu_repo_description` symbol-catalog and dependency-graph
  schema/model/extraction surfaces, deterministic fixture replay under
  `apps/api/fixtures/repo_description/vnext_plus101/`, and the canonical
  `v45b_repo_symbol_catalog_dependency_graph_evidence@1` evidence input under
  `artifacts/agent_harness/v101/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#324` (`V45-B: implement v101 repo symbol catalog and dependency graph`)
- arc-completion merge commit: `0eee0354867c1959f0d34cc8134d283369f99d96`
- merged-at timestamp: `2026-03-31T16:46:54Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v101_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v101_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v101_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v101/evidence_inputs/metric_key_continuity_assertion_v101.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v101/evidence_inputs/runtime_observability_comparison_v101.json`
  - `V45-B` release evidence input:
    `artifacts/agent_harness/v101/evidence_inputs/v45b_repo_symbol_catalog_dependency_graph_evidence_v101.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v101/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS101_EDGES.md`

## Exit-Criteria Check (vNext+101)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V45-B` merged with green CI | required | `pass` | PR `#324`, merge commit `0eee0354867c1959f0d34cc8134d283369f99d96`, checks `python/web/lean-formal = pass` |
| Canonical `repo_symbol_catalog@1` and `repo_dependency_graph@1` shipped with authoritative/mirror schema parity | required | `pass` | `packages/adeu_repo_description/schema/repo_symbol_catalog.v1.json`, `spec/repo_symbol_catalog.schema.json`, `packages/adeu_repo_description/schema/repo_dependency_graph.v1.json`, `spec/repo_dependency_graph.schema.json` |
| Deterministic replay over accepted v101 fixtures is stable | required | `pass` | replay checks in `packages/adeu_repo_description/tests/test_repo_description_v45b.py` and accepted fixtures under `apps/api/fixtures/repo_description/vnext_plus101/` |
| Explicit snapshot identity/hash, explicit source-set binding, and explicit `source_set_hash` are present | required | `pass` | accepted fixture replay plus required-field enforcement in `packages/adeu_repo_description/src/adeu_repo_description/models.py` |
| Typed symbol entries carry explicit identity/module/qualname/kind/classification posture plus source artifact refs | required | `pass` | symbol-catalog schema/model anchors in `models.py` and accepted fixture `repo_symbol_catalog_v101_reference.json` |
| Typed dependency edges carry endpoint kinds, dependency posture, and derivation posture/method | required | `pass` | dependency-graph schema/model anchors in `models.py` and accepted fixture `repo_dependency_graph_v101_reference.json` |
| Accepted catalog/graph fixtures reconcile over one shared snapshot/source-set identity | required | `pass` | pair validation in `validate_repo_symbol_catalog_dependency_graph_pair` and acceptance tests in `test_repo_description_v45b.py` |
| Fail-closed rejection covers dangling refs, untyped out-of-scope endpoints, duplicate identities, pair drift, and authority laundering | required | `pass` | reject fixtures under `apps/api/fixtures/repo_description/vnext_plus101/` and rejection assertions in `test_repo_description_v45b.py` |
| Nested control-flow symbol and import extraction gaps are closed | required | `pass` | recursive statement-body traversal in `packages/adeu_repo_description/src/adeu_repo_description/extract.py` and tests `test_v45b_collects_unpacking_targets_and_control_flow_symbols` plus `test_v45b_collects_nested_control_flow_imports` |
| Duplicate normalized module import paths are rejected fail-closed | required | `pass` | duplicate-module-path guard in `extract.py` and test `test_v45b_rejects_duplicate_normalized_module_import_paths` |
| External dotted refs do not duplicate path segments | required | `pass` | `_merge_external_dependency_suffix` in `extract.py` and test `test_v45b_external_dotted_refs_do_not_duplicate_segments` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v101_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v101/evidence_inputs/metric_key_continuity_assertion_v101.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v101/evidence_inputs/runtime_observability_comparison_v101.json` |

## Stop-Gate Summary

```json
{
  "schema": "v101_closeout_stop_gate_summary@1",
  "arc": "vNext+101",
  "target_path": "V45-B",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v102": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 96,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v102_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v101_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+102","current_arc":"vNext+101","baseline_source":"artifacts/stop_gate/report_v102_closeout.md","current_source":"artifacts/stop_gate/report_v101_closeout.md","baseline_elapsed_ms":96,"current_elapsed_ms":96,"delta_ms":0,"notes":"v101 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V45-B repo_symbol_catalog@1 and repo_dependency_graph@1 surfaces with explicit endpoint ontology, bounded provenance, and pair-consistency guards."}
```

## V45B Repo Symbol Catalog Dependency Graph Evidence

```json
{"schema":"v45b_repo_symbol_catalog_dependency_graph_evidence@1","evidence_input_path":"artifacts/agent_harness/v101/evidence_inputs/v45b_repo_symbol_catalog_dependency_graph_evidence_v101.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS101.md#v101-continuation-contract-machine-checkable","merged_pr":"#324","merge_commit":"0eee0354867c1959f0d34cc8134d283369f99d96","repo_symbol_catalog_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_symbol_catalog.v1.json","repo_symbol_catalog_mirror_schema_path":"spec/repo_symbol_catalog.schema.json","repo_dependency_graph_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_dependency_graph.v1.json","repo_dependency_graph_mirror_schema_path":"spec/repo_dependency_graph.schema.json","accepted_symbol_catalog_fixture_path":"apps/api/fixtures/repo_description/vnext_plus101/repo_symbol_catalog_v101_reference.json","accepted_dependency_graph_fixture_path":"apps/api/fixtures/repo_description/vnext_plus101/repo_dependency_graph_v101_reference.json"}
```

## Recommendation (Post v101)

- gate decision:
  - `V45B_REPO_SYMBOL_CATALOG_AND_DEPENDENCY_GRAPH_COMPLETE_ON_MAIN`
- rationale:
  - v101 closes the bounded `V45-B` widening seam on `main` by shipping
    deterministic `repo_symbol_catalog@1` and `repo_dependency_graph@1` surfaces with
    explicit snapshot/source-set binding, explicit endpoint kinds, explicit
    provenance/derivation fields, and fail-closed pair-consistency guards.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`0 ms` vs v102 baseline).
  - broader widening into `V45-D` and later lanes remains a planning selection beyond
    this decision note.
