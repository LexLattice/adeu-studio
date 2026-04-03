# Draft Stop-Gate Decision (Post vNext+115)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS115.md`

Status: draft decision note (post-hoc closeout capture, April 3, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS115.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v115_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+115` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS115.md`.
- This note captures bounded `V48-D` worker-boundary conformance evidence only; it
  does not authorize delegated multi-worker topology release, repo-wide orchestration,
  supervisor/worker authority expansion, worker/worker authority expansion,
  signature-envelope redefinition, execution-result redefinition, approval posture,
  waiver issuance, or deferral issuance by itself.
- Canonical `V48-D` release in `v115` is carried by the shipped
  `adeu_agent_harness` source, schema-export, deterministic fixtures, and targeted
  test surfaces plus the canonical
  `v48d_worker_boundary_conformance_evidence@1` evidence input under
  `artifacts/agent_harness/v115/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#337` (`[codex] feat(v115): add worker boundary conformance report`)
- arc-completion merge commit: `c84b60e62a1ad1aabd99471ac5f9db132218188c`
- merged-at timestamp: `2026-04-02T23:57:55Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v115_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v115_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v115_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v115/evidence_inputs/metric_key_continuity_assertion_v115.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v115/evidence_inputs/runtime_observability_comparison_v115.json`
  - `V48-D` release evidence input:
    `artifacts/agent_harness/v115/evidence_inputs/v48d_worker_boundary_conformance_evidence_v115.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v115/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS115_EDGES.md`

## Exit-Criteria Check (vNext+115)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V48-D` merged with green CI | required | `pass` | PR `#337`, merge commit `c84b60e62a1ad1aabd99471ac5f9db132218188c`, checks `python/web/lean-formal = pass` |
| Released `worker_boundary_conformance_report@1` ships with authoritative/mirror schema parity | required | `pass` | `packages/adeu_agent_harness/schema/worker_boundary_conformance_report.v1.json`, mirrored `spec/worker_boundary_conformance_report.schema.json`, and parity coverage in `packages/adeu_agent_harness/tests/test_worker_boundary_conformance_export_schema.py` |
| Accepted conformant and bounded non-conformant reference fixtures replay deterministically | required | `pass` | committed fixtures under `packages/adeu_agent_harness/tests/fixtures/v48d/` and tests `test_v48d_reference_worker_boundary_conformance_replays_deterministically`, `test_v48d_reference_nonconformant_mutation_fixture_replays`, and `test_v48d_reference_nonconformant_command_fixture_replays` |
| Every accepted report binds exactly one released boundary instance, one released attestation, one released provenance carrier, and one explicit four-carrier observed-action set | required | `pass` | cardinality and carrier validation in `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py`, committed reference fixtures, and tests `test_v48d_models_accept_committed_reference_payloads` plus `test_v48d_rejects_missing_observed_action_carrier` |
| Hidden repo search and support/provenance substitution remain forbidden | required | `pass` | explicit carrier loading and support-only posture in `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py` and test `test_v48d_rejects_support_artifact_substitution_posture` |
| Invalid relative-path carrier refs fail closed with typed conformance error posture | required | `pass` | fail-closed path normalization in `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py` and test `test_v48d_rejects_invalid_relative_path_with_conformance_error` |
| Forbidden operation kinds and off-boundary mutation drift force non-conformant or incomplete-evidence posture rather than conformant posture | required | `pass` | filesystem mutation checks in `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py` and tests `test_v48d_reference_nonconformant_mutation_fixture_replays` plus `test_v48d_marks_forbidden_operation_kind_non_conformant` |
| Command drift and exact execution-repository identity drift replay as bounded non-conformance | required | `pass` | tests `test_v48d_reference_nonconformant_command_fixture_replays`, `test_v48d_marks_branch_identity_mismatch_non_conformant`, and `test_v48d_rejects_carrier_repo_identity_mismatch` |
| Overall judgment, starter `check_family`, and per-check `judgment` vocabularies remain frozen and are derived from typed checks rather than prose assertion | required | `pass` | frozen vocabularies and precedence in `docs/LOCKED_CONTINUATION_vNEXT_PLUS115.md`, implementation in `packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py`, and deterministic replay of committed fixtures |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v115_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v115/evidence_inputs/metric_key_continuity_assertion_v115.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v115/evidence_inputs/runtime_observability_comparison_v115.json` |

## Stop-Gate Summary

```json
{
  "schema": "v115_closeout_stop_gate_summary@1",
  "arc": "vNext+115",
  "target_path": "V48-D",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v114": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 120,
  "runtime_observability_delta_ms": 9
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v114_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v115_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+114","current_arc":"vNext+115","baseline_source":"artifacts/stop_gate/report_v114_closeout.md","current_source":"artifacts/stop_gate/report_v115_closeout.md","baseline_elapsed_ms":111,"current_elapsed_ms":120,"delta_ms":9,"notes":"v115 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V48-D worker-boundary conformance lane: one canonical worker_boundary_conformance_report@1 over one released V48-C boundary-instance/attestation/provenance chain, one frozen four-carrier observed-action set, exact conformant/non_conformant/incomplete_evidence aggregation, explicit support-vs-observation separation, and fail-closed handling for raw-input bypass, missing observed carriers, invalid relative-path carrier refs, repo-identity mismatch, support-artifact substitution, forbidden operation kinds, command drift, and branch-identity mismatch."}
```

## V48D Worker Boundary Conformance Evidence

```json
{"schema":"v48d_worker_boundary_conformance_evidence@1","evidence_input_path":"artifacts/agent_harness/v115/evidence_inputs/v48d_worker_boundary_conformance_evidence_v115.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS115.md#v115-continuation-contract-machine-checkable","merged_pr":"#337","merge_commit":"c84b60e62a1ad1aabd99471ac5f9db132218188c","implementation_packages":["adeu_agent_harness"],"worker_boundary_conformance_implementation_source_path":"packages/adeu_agent_harness/src/adeu_agent_harness/worker_boundary_conformance.py","worker_boundary_conformance_export_source_path":"packages/adeu_agent_harness/src/adeu_agent_harness/export_schema.py","worker_boundary_conformance_authoritative_schema_path":"packages/adeu_agent_harness/schema/worker_boundary_conformance_report.v1.json","worker_boundary_conformance_mirror_schema_path":"spec/worker_boundary_conformance_report.schema.json","test_reference_paths":["packages/adeu_agent_harness/tests/test_taskpack_binding.py","packages/adeu_agent_harness/tests/test_taskpack_binding_export_schema.py","packages/adeu_agent_harness/tests/test_compiled_taskpack_binding.py","packages/adeu_agent_harness/tests/test_compiled_taskpack_binding_export_schema.py","packages/adeu_agent_harness/tests/test_worker_execution_envelope.py","packages/adeu_agent_harness/tests/test_worker_execution_envelope_export_schema.py","packages/adeu_agent_harness/tests/test_worker_boundary_conformance.py","packages/adeu_agent_harness/tests/test_worker_boundary_conformance_export_schema.py","packages/adeu_agent_harness/tests/test_taskpack_compile.py"],"accepted_conformant_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48d/reference_worker_boundary_conformance_report.json","accepted_non_conformant_mutation_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48d/reference_worker_boundary_conformance_report_nonconformant_mutation.json","accepted_non_conformant_command_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48d/reference_worker_boundary_conformance_report_nonconformant_command.json","metric_key_continuity_assertion_path":"artifacts/agent_harness/v115/evidence_inputs/metric_key_continuity_assertion_v115.json","runtime_observability_comparison_path":"artifacts/agent_harness/v115/evidence_inputs/runtime_observability_comparison_v115.json","runtime_event_stream_path":"artifacts/agent_harness/v115/runtime/evidence/local/urm_events.ndjson","notes":"v115 evidence pins the released V48-D conformance lane on main: one canonical worker_boundary_conformance_report@1, one explicit four-carrier observed-action set, exact conformant/non_conformant/incomplete_evidence aggregation, support/provenance kept lineage-only rather than observational, and fail-closed handling for raw V48-B/V48-A bypass, missing observed carriers, invalid relative-path refs, repo/task/worker identity mismatch, support-artifact substitution, forbidden operation kinds, command drift, and branch-identity mismatch."}
```

## Recommendation (Post v115)

- gate decision:
  - `V48D_WORKER_BOUNDARY_CONFORMANCE_COMPLETE_ON_MAIN`
  - `V48_POLICY_TO_TASKPACK_AND_WORKER_ENFORCEMENT_BRANCH_ACTIVE_ON_MAIN`
- rationale:
  - `v115` closes the bounded `V48-D` replayable single-worker conformance seam on
    `main` by taking one released `V48-C` boundary-instance / attestation /
    provenance chain as the only admitted lineage input and deterministically binding
    it to one frozen four-carrier observed-action set and one canonical
    `worker_boundary_conformance_report@1`.
  - the shipped slice is conformance-first and still pre-topology: it does not
    reopen descriptive semantics, ANM semantics, `V48-A` binding semantics, `V48-B`
    compiler semantics, `V48-C` worker-envelope semantics, generic
    runner/verifier/attestation kernel semantics, or multi-worker topology.
  - observed-action carriers now remain explicit and non-substitutable: provenance and
    other support artifacts may support lineage, but they do not stand in for the
    filesystem mutation set, command invocation log, emitted artifact set, or exact
    execution-repository identity carrier.
  - raw `V48-B` / `V48-A` bypass, missing observed-action carriers, invalid
    relative-path refs, repo/task/worker identity mismatch, forbidden operation kinds,
    command drift, and branch-identity drift fail closed rather than being repaired
    by local convention.
  - authoritative schema, mirrored export, committed reference fixtures, and targeted
    tests remain in parity for the released `V48-D` surface.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`+9 ms` vs `v114`
    baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v31.md` now records `V48-D` as closed on `main` and
    advances the branch-local default next path to `V48-E` / `vNext+116`.
