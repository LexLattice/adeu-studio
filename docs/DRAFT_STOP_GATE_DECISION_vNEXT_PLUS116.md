# Draft Stop-Gate Decision (Post vNext+116)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS116.md`

Status: draft decision note (post-hoc closeout capture, April 3, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS116.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v116_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+116` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS116.md`.
- This note captures bounded `V48-E` worker-delegation topology evidence only; it
  does not authorize worker/worker delegation, recursive topology, repo-wide
  orchestration, binding or compiled-boundary redefinition, worker-envelope
  redefinition, conformance redefinition, execution authority expansion, approval
  posture, waiver issuance, or deferral issuance by itself.
- Canonical `V48-E` release in `v116` is carried by the shipped
  `adeu_agent_harness` source, schema-export, deterministic fixtures, and targeted
  test surfaces plus the canonical
  `v48e_worker_delegation_topology_evidence@1` evidence input under
  `artifacts/agent_harness/v116/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v31.md` now marks
  `V48-A` through `V48-E` closed on `main`; it does not select any post-`V48`
  family by itself.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#338` (`[codex] feat(v116): add worker delegation topology`)
- arc-completion merge commit: `098b5eb1b31d264beb8f07e5dd272cb571ed1352`
- merged-at timestamp: `2026-04-03T01:14:27Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v116_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v116_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v116_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v116/evidence_inputs/metric_key_continuity_assertion_v116.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v116/evidence_inputs/runtime_observability_comparison_v116.json`
  - `V48-E` release evidence input:
    `artifacts/agent_harness/v116/evidence_inputs/v48e_worker_delegation_topology_evidence_v116.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v116/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS116_EDGES.md`

## Exit-Criteria Check (vNext+116)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V48-E` merged with green CI | required | `pass` | PR `#338`, merge commit `098b5eb1b31d264beb8f07e5dd272cb571ed1352`, checks `python/web/lean-formal = pass` |
| Released `worker_delegation_topology@1` ships with authoritative/mirror schema parity | required | `pass` | `packages/adeu_agent_harness/schema/worker_delegation_topology.v1.json`, mirrored `spec/worker_delegation_topology.schema.json`, and parity coverage in `packages/adeu_agent_harness/tests/test_worker_delegation_topology_export_schema.py` |
| Accepted completed and typed rejected/incomplete reference fixtures replay deterministically | required | `pass` | committed fixtures under `packages/adeu_agent_harness/tests/fixtures/v48e/` and tests `test_v48e_reference_worker_delegation_topology_replays_deterministically`, `test_v48e_reference_rejected_compiled_boundary_mismatch_fixture_replays`, and `test_v48e_reference_incomplete_lineage_fixture_replays` |
| Every accepted topology binds exactly one released parent `V48-D` report, one released child `V48-D` report, one explicit `supervisor_to_worker` edge, one explicit parent task identity, one explicit delegated task identity, and one explicit child task identity | required | `pass` | cardinality and topology validation in `packages/adeu_agent_harness/src/adeu_agent_harness/worker_delegation_topology.py`, committed reference fixtures, and tests `test_v48e_models_accept_committed_reference_payloads` plus `test_v48e_parent_and_child_reports_keep_v48d_schema` |
| Parent and child remain coherent on exact repo identity, exact snapshot identity, and exact compiled-boundary identity with no widening algebra selected | required | `pass` | authority-relation posture `same_compiled_boundary_no_widening` in the released schema and fixtures, plus rejection replay in `test_v48e_reference_rejected_compiled_boundary_mismatch_fixture_replays` |
| Raw-input bypass of released `V48-D` reports remains forbidden | required | `pass` | input-source validation in `packages/adeu_agent_harness/src/adeu_agent_harness/worker_delegation_topology.py` and test `test_v48e_rejects_raw_v48d_bypass` |
| Self-edge laundering and role ambiguity fail closed | required | `pass` | tests `test_v48e_marks_same_worker_subject_as_rejected` and `test_v48e_marks_swapped_roles_as_rejected` |
| `handoff_result`, supporting diagnostics, and topology identity remain derived from resolved lineage outcome rather than prose assertion | required | `pass` | topology-id derivation and outcome aggregation in `packages/adeu_agent_harness/src/adeu_agent_harness/worker_delegation_topology.py` and test `test_v48e_topology_id_changes_when_resolved_outcome_changes` |
| Supporting-diagnostic family vocabulary remains frozen and duplicate/misordered diagnostics fail closed | required | `pass` | schema/model validation in `packages/adeu_agent_harness/src/adeu_agent_harness/worker_delegation_topology.py` and test `test_v48e_model_rejects_out_of_order_or_duplicate_diagnostics` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v116_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v116/evidence_inputs/metric_key_continuity_assertion_v116.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v116/evidence_inputs/runtime_observability_comparison_v116.json` |

## Stop-Gate Summary

```json
{
  "schema": "v116_closeout_stop_gate_summary@1",
  "arc": "vNext+116",
  "target_path": "V48-E",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v115": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 139,
  "runtime_observability_delta_ms": 19
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v115_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v116_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+115","current_arc":"vNext+116","baseline_source":"artifacts/stop_gate/report_v115_closeout.md","current_source":"artifacts/stop_gate/report_v116_closeout.md","baseline_elapsed_ms":120,"current_elapsed_ms":139,"delta_ms":19,"notes":"v116 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V48-E worker-delegation topology lane: one canonical worker_delegation_topology@1 over one released parent V48-D report plus one released child V48-D report, one explicit supervisor_to_worker edge, exact same repo/snapshot/compiled-boundary posture, explicit parent/delegated/child task identities, typed completed/rejected/incomplete_lineage outcomes, and fail-closed handling for raw-input bypass, lineage mismatch, compiled-boundary mismatch, same-worker self-edge, role ambiguity, recursive topology, and diagnostic-order drift."}
```

## V48E Worker Delegation Topology Evidence

```json
{"schema":"v48e_worker_delegation_topology_evidence@1","evidence_input_path":"artifacts/agent_harness/v116/evidence_inputs/v48e_worker_delegation_topology_evidence_v116.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS116.md#v116-continuation-contract-machine-checkable","merged_pr":"#338","merge_commit":"098b5eb1b31d264beb8f07e5dd272cb571ed1352","implementation_packages":["adeu_agent_harness"],"worker_delegation_topology_implementation_source_path":"packages/adeu_agent_harness/src/adeu_agent_harness/worker_delegation_topology.py","worker_delegation_topology_export_source_path":"packages/adeu_agent_harness/src/adeu_agent_harness/export_schema.py","worker_delegation_topology_authoritative_schema_path":"packages/adeu_agent_harness/schema/worker_delegation_topology.v1.json","worker_delegation_topology_mirror_schema_path":"spec/worker_delegation_topology.schema.json","test_reference_paths":["packages/adeu_agent_harness/tests/test_taskpack_binding.py","packages/adeu_agent_harness/tests/test_taskpack_binding_export_schema.py","packages/adeu_agent_harness/tests/test_compiled_taskpack_binding.py","packages/adeu_agent_harness/tests/test_compiled_taskpack_binding_export_schema.py","packages/adeu_agent_harness/tests/test_worker_execution_envelope.py","packages/adeu_agent_harness/tests/test_worker_execution_envelope_export_schema.py","packages/adeu_agent_harness/tests/test_worker_boundary_conformance.py","packages/adeu_agent_harness/tests/test_worker_boundary_conformance_export_schema.py","packages/adeu_agent_harness/tests/test_worker_delegation_topology.py","packages/adeu_agent_harness/tests/test_worker_delegation_topology_export_schema.py","packages/adeu_agent_harness/tests/test_taskpack_compile.py"],"accepted_completed_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48e/reference_worker_delegation_topology.json","typed_rejected_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48e/reference_worker_delegation_topology_rejected_compiled_boundary_mismatch.json","typed_incomplete_lineage_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48e/reference_worker_delegation_topology_incomplete_lineage.json","metric_key_continuity_assertion_path":"artifacts/agent_harness/v116/evidence_inputs/metric_key_continuity_assertion_v116.json","runtime_observability_comparison_path":"artifacts/agent_harness/v116/evidence_inputs/runtime_observability_comparison_v116.json","runtime_event_stream_path":"artifacts/agent_harness/v116/runtime/evidence/local/urm_events.ndjson","notes":"v116 evidence pins the released V48-E delegated topology lane on main: one canonical worker_delegation_topology@1, one explicit supervisor_to_worker edge over one released parent V48-D report plus one released child V48-D report, exact same repo/snapshot/compiled-boundary posture, distinct worker subjects, typed completed/rejected/incomplete_lineage outcomes, starter supporting-diagnostic families, and fail-closed handling for raw V48-D bypass, lineage mismatch, compiled-boundary mismatch, self-edge laundering, role ambiguity, recursive topology, and diagnostic normalization drift."}
```

## Recommendation (Post v116)

- gate decision:
  - `V48E_WORKER_DELEGATION_TOPOLOGY_COMPLETE_ON_MAIN`
  - `V48_POLICY_TO_TASKPACK_AND_WORKER_ENFORCEMENT_BRANCH_COMPLETE_ON_MAIN`
- rationale:
  - `v116` closes the bounded `V48-E` delegated topology seam on `main` by taking
    one released parent `worker_boundary_conformance_report@1` and one released child
    `worker_boundary_conformance_report@1` as the only admitted lineage inputs and
    deterministically binding them into one canonical `worker_delegation_topology@1`.
  - the shipped slice is topology-first and still bounded: one
    `supervisor_to_worker` edge only, exact same repo/snapshot identity, exact same
    compiled-boundary posture, one explicit parent task identity, one explicit
    delegated task identity, one explicit child task identity, and distinct parent
    versus child worker subjects.
  - accepted starter topology remains `handoff_result = completed` only, while
    `rejected` and `incomplete_lineage` remain typed emitted fail-closed outcomes
    rather than accepted completion posture.
  - raw-input bypass, lineage mismatch, compiled-boundary mismatch, self-edge
    laundering, role ambiguity, recursive topology, and diagnostic-order drift fail
    closed rather than being repaired by local convention.
  - authoritative schema, mirrored export, committed reference fixtures, and targeted
    tests remain in parity for the released `V48-E` surface.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`+19 ms` vs `v115`
    baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v31.md` now records `V48-A` through `V48-E` as
    closed on `main` and records that no further internal `V48` path is currently
    selected.
