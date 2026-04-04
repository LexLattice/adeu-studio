# Draft Stop-Gate Decision (Post vNext+129)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS129.md`

Status: draft decision note (post-hoc closeout capture, April 4, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS129.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v129_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+129` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS129.md`.
- This note captures bounded `V52-C` live worker-bridge evidence only; it does not
  authorize the later advanced-visualization seam or imported overlay precedent by
  itself.
- Canonical `V52-C` release in `v129` is carried by the shipped
  `packages/urm_domain_paper` domain-pack extension, the bounded `apps/api` URM
  tool-call surface integration, committed deterministic bridge/domain tests, the
  explicit capability-lattice entry, and the canonical
  `v52c_paper_semantic_worker_bridge_evidence@1` evidence input under
  `artifacts/agent_harness/v129/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md` now marks
  `V52-A` through `V52-C` closed on `main` and advances the branch-local default next
  path to `V52-D`; it does not select the `V52-D` visualization seam by itself.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#351` (`feat(v129): add paper semantic worker bridge`)
- arc-completion merge commit: `73984233e995cae3561c116af14dbb7aee7db9ea`
- merged-at timestamp: `2026-04-04T17:59:04Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v129_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v129_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v129_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v129/evidence_inputs/metric_key_continuity_assertion_v129.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v129/evidence_inputs/runtime_observability_comparison_v129.json`
  - `V52-C` release evidence input:
    `artifacts/agent_harness/v129/evidence_inputs/v52c_paper_semantic_worker_bridge_evidence_v129.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v129/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS129_EDGES.md`

## Exit-Criteria Check (vNext+129)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V52-C` merged with green CI | required | `pass` | PR `#351`, merge commit `73984233e995cae3561c116af14dbb7aee7db9ea`, checks `python/web/lean-formal = pass` |
| The live bridge extends the existing `urm_domain_paper` domain pack additively rather than instantiating a new owner surface or laundering ownership into `urm_domain_adeu` | required | `pass` | `packages/urm_domain_paper/src/urm_domain_paper/adapters.py`, `models.py`, and absence of live bridge ownership in `urm_domain_adeu` |
| The new tool is exposed only as `paper.run_semantic_decomposition` over the existing URM tool-call surface | required | `pass` | `PaperDomainTools.call_tool(...)`, `apps/api/src/adeu_api/urm_routes.py`, and no dedicated paper-semantics API route in the merged diff |
| Existing paper-domain tools and the existing default template remain additive and unchanged | required | `pass` | preserved `paper.ingest_text` / `paper.extract_abstract_candidate` / `paper.check_constraints` / `paper.emit_artifact` flow, retained `paper.abstract.pipeline.v0`, and regression coverage in `apps/api/tests/test_urm_domain_tools.py` |
| The bridge consumes only released `adeu_paper_semantic_worker_request@1` inputs and keeps `V52-B` route-local state non-authoritative | required | `pass` | `RunSemanticDecompositionArgs`, direct `PaperSemanticWorkerRequest` validation, and no browser-local view state admitted in bridge arguments |
| Capability-lattice / policy mapping for `paper.run_semantic_decomposition` is explicit and tested | required | `pass` | `policy/urm.capability.lattice.v1.json`, packaged lattice copy under `packages/urm_runtime`, and `apps/api/tests/test_urm_capability_policy.py` |
| Bridge results remain refs-only and evidence-bearing, with `warrant_tag`, `artifact_ref`, and no embedded live semantic artifact payload | required | `pass` | `PaperSemanticWorkerBridgeResult`, result serialization by alias, and success-path tool-call regression coverage |
| Invalid request, invalid returned artifact payload, and runtime bridge/config mismatch all fail closed | required | `pass` | `fail_closed_invalid_request`, `fail_closed_bridge_config_mismatch`, worker-result validation in `adapters.py`, and dedicated failure regressions in `apps/api/tests/test_urm_domain_tools.py` |
| The bridge is additive and does not destabilize the existing paper-domain tool flow | required | `pass` | existing paper-tool tests remain green alongside the new semantic-decomposition tool regressions in `apps/api/tests/test_urm_domain_tools.py` |
| No `apps/web` fetch wiring, dedicated API route, or prototype workflow-overlay import ships in this slice | required | `pass` | merged diff bounded to `urm_domain_paper`, `apps/api`, capability-policy files, and no live route changes under `apps/web` |
| The bounded bridge/domain lane passed targeted local validation and green repo CI | required | `pass` | targeted Ruff/pytest lane in the implementation PR plus merged `python/web/lean-formal` GitHub checks |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v129_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v129/evidence_inputs/metric_key_continuity_assertion_v129.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v129/evidence_inputs/runtime_observability_comparison_v129.json` |

## Stop-Gate Summary

```json
{
  "schema": "v129_closeout_stop_gate_summary@1",
  "arc": "vNext+129",
  "target_path": "V52-C",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v128": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 119,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v128_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v129_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+128","current_arc":"vNext+129","baseline_source":"artifacts/stop_gate/report_v128_closeout.md","current_source":"artifacts/stop_gate/report_v129_closeout.md","baseline_elapsed_ms":119,"current_elapsed_ms":119,"delta_ms":0,"notes":"v129 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V52-C paper semantic worker-bridge lane: one additive extension of the existing urm_domain_paper domain pack, one bounded paper.run_semantic_decomposition tool over the existing URM tool-call surface, direct consumption of released adeu_paper_semantic_worker_request@1 inputs, explicit capability-lattice coverage for the new tool, typed refs-only bridge results carrying bridge_status plus warrant_tag and artifact_ref, fail-closed handling for invalid requests and invalid worker artifact payloads, preserved paper.abstract.pipeline.v0 and existing paper-domain tool flow, no apps/web widening, and no prototype workflow-overlay laundering."}
```

## V52C Paper Semantic Worker Bridge Evidence

```json
{"schema":"v52c_paper_semantic_worker_bridge_evidence@1","evidence_input_path":"artifacts/agent_harness/v129/evidence_inputs/v52c_paper_semantic_worker_bridge_evidence_v129.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS129.md#v129-continuation-contract-machine-checkable","merged_pr":"#351","merge_commit":"73984233e995cae3561c116af14dbb7aee7db9ea","implementation_packages":["adeu_paper_semantics","urm_domain_paper","urm_runtime","adeu_api"],"domain_pack_root":"packages/urm_domain_paper","domain_models_source_path":"packages/urm_domain_paper/src/urm_domain_paper/models.py","domain_adapters_source_path":"packages/urm_domain_paper/src/urm_domain_paper/adapters.py","domain_package_init_source_path":"packages/urm_domain_paper/src/urm_domain_paper/__init__.py","domain_pyproject_path":"packages/urm_domain_paper/pyproject.toml","api_route_source_path":"apps/api/src/adeu_api/urm_routes.py","policy_lattice_paths":["policy/urm.capability.lattice.v1.json","packages/urm_runtime/src/urm_runtime/policy/urm.capability.lattice.v1.json"],"tool_name":"paper.run_semantic_decomposition","template_id":"paper.semantic_decomposition.v0","existing_default_template_id_retained":"paper.abstract.pipeline.v0","bridge_owner_surface":"urm_domain_paper","bridge_api_surface":"urm_tool_call_endpoint","released_worker_request_fixture_paths":["packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_worker_request_abstract.json","packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_worker_request_paragraph.json"],"returned_artifact_fixture_paths":["packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_artifact_abstract.json","packages/adeu_paper_semantics/tests/fixtures/v52a/reference_paper_semantic_artifact_paragraph.json"],"route_test_reference_paths":["apps/api/tests/test_urm_domain_tools.py","apps/api/tests/test_urm_capability_policy.py"],"bridge_status_vocabulary":["completed_checked","completed_checked_idempotent_replay","fail_closed_invalid_request","fail_closed_bridge_config_mismatch"],"warrant_tag_frozen":"checked","artifact_ref_only_result":true,"embedded_artifact_payload_forbidden":true,"existing_paper_tool_regression_required":true,"metric_key_continuity_assertion_path":"artifacts/agent_harness/v129/evidence_inputs/metric_key_continuity_assertion_v129.json","runtime_observability_comparison_path":"artifacts/agent_harness/v129/evidence_inputs/runtime_observability_comparison_v129.json","runtime_event_stream_path":"artifacts/agent_harness/v129/runtime/evidence/local/urm_events.ndjson","notes":"v129 evidence pins the released V52-C paper semantic worker-bridge lane on main: one additive extension of the existing urm_domain_paper domain pack only, one bounded paper.run_semantic_decomposition tool only, retained paper.abstract.pipeline.v0 default template, direct consumption of released adeu_paper_semantic_worker_request@1 inputs, explicit capability-lattice and policy coverage for the new tool, typed refs-only bridge results carrying request lineage plus bridge_status, warrant_tag, artifact_ref, worker_id, evidence_id, worker_status, and replay metadata, fail-closed handling for invalid requests, invalid returned artifact payloads, and bridge/runtime mismatch, regression coverage proving the existing paper-domain tool flow remains unchanged, and no apps/web widening or prototype workflow-overlay import."}
```

## Recommendation (Post v129)

- gate decision:
  - `V52C_PAPER_SEMANTIC_WORKER_BRIDGE_COMPLETE_ON_MAIN`
  - `V52_PAPER_SEMANTICS_FAMILY_ACTIVE_ON_MAIN`
- rationale:
  - `v129` closes the bounded `V52-C` live worker-bridge seam on `main` by
    extending the existing `urm_domain_paper` domain pack rather than laundering
    paper-semantic bridge ownership into `urm_domain_adeu` or a prototype overlay.
  - the shipped slice stays narrow and additive: one explicit
    `paper.run_semantic_decomposition` tool, one retained default abstract template,
    one released worker-request contract, one refs-only bridge result, and no new
    dedicated API route or browser-trigger surface.
  - explicit capability-policy wiring now matches the live tool surface, and the
    bridge fails closed on invalid request, invalid returned artifact payload, and
    runtime/config mismatch instead of silently repairing those cases.
  - the existing closed-world `paper.abstract` tool lane remains intact and regression
    covered; `v129` adds a bridge seam without superseding prior paper-domain tools.
  - the imported bundle remains support-only and non-precedent; the release re-authors
    live ownership entirely in repo-native `urm_domain_paper` plus existing `apps/api`
    integration paths.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`0 ms` vs `v128`
    baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v35.md` should now be read with `V52-A` through
    `V52-C` closed on `main` and the branch-local default next path advanced to
    `V52-D` / `vNext+130`.
