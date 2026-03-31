# Draft Stop-Gate Decision (Post vNext+99)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS99.md`

Status: draft decision note (post-hoc closeout capture, March 31, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS99.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v99_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+99` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS99.md`.
- This note captures `V45-A` closeout evidence only; it does not authorize recursive
  governance binding, symbol-catalog release, dependency-graph release, test-intent
  matrix release, optimization-register release, or mutation entitlement.
- Canonical `V45-A` release in v99 is carried by the `packages/adeu_repo_description`
  schema-registry/entity-catalog surfaces, deterministic fixture replay under
  `apps/api/fixtures/repo_description/vnext_plus99/`, and the canonical
  `v45a_repo_self_description_evidence@1` evidence input under
  `artifacts/agent_harness/v99/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- arc-completion merge commit: `791d574ef97ca348ec7c9db88e89bb3f7e17995f`
- merged implementation PRs:
  - `#321` (`V45-A: implement v99 repo schema registry and entity catalog`)
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v99_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v99_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v99_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v99/evidence_inputs/metric_key_continuity_assertion_v99.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v99/evidence_inputs/runtime_observability_comparison_v99.json`
  - `V45-A` self-description evidence input:
    `artifacts/agent_harness/v99/evidence_inputs/v45a_repo_self_description_evidence_v99.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v99/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS99_EDGES.md`

## Exit-Criteria Check (vNext+99)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V45-A` merged with green CI | required | `pass` | PR `#321`, merge commit `791d574ef97ca348ec7c9db88e89bb3f7e17995f` |
| Canonical `repo_schema_family_registry@1` and `repo_entity_catalog@1` shipped with authoritative/mirror schema parity | required | `pass` | `packages/adeu_repo_description/schema/repo_schema_family_registry.v1.json`, `spec/repo_schema_family_registry.schema.json`, `packages/adeu_repo_description/schema/repo_entity_catalog.v1.json`, `spec/repo_entity_catalog.schema.json` |
| Deterministic registry + entity-catalog replay over accepted fixtures is stable | required | `pass` | replay checks in `packages/adeu_repo_description/tests/test_repo_description_v45a.py` and accepted fixtures `.../repo_schema_family_registry_v99_reference.json`, `.../repo_entity_catalog_v99_reference.json` |
| Snapshot identity/hash + stale-snapshot posture are bound in emitted artifacts | required | `pass` | reference fixture replay + required-field enforcement in `packages/adeu_repo_description/src/adeu_repo_description/models.py` |
| Classification-policy binding remains explicit and immutable (`classification_policy_ref` + hash) | required | `pass` | policy-hash computation and validation in `models.py` |
| Role-form precedence law is enforced fail-closed (`structural > semantic > governance > lexical`) | required | `pass` | precedence validation in `models.py` and rejected fixture `.../repo_schema_family_registry_v99_reject_precedence_contradiction.json` |
| Naming-only role-form classification is rejected fail-closed | required | `pass` | rejected fixture `.../repo_schema_family_registry_v99_reject_naming_only_role_form_classification.json` and rejection assertions in `test_repo_description_v45a.py` |
| Settled posture without adjudication support is rejected fail-closed | required | `pass` | rejected fixture `.../repo_schema_family_registry_v99_reject_settled_posture_without_adjudication_support.json` |
| Representative reconstruction subset round-trips under canonical normalized semantic equivalence | required | `pass` | reconstruction validation in `models.py` plus rejected fixture `.../repo_schema_family_registry_v99_reject_non_round_tripping_reconstruction.json` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v99_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v99/evidence_inputs/metric_key_continuity_assertion_v99.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v99/evidence_inputs/runtime_observability_comparison_v99.json` |

## Stop-Gate Summary

```json
{
  "schema": "v99_closeout_stop_gate_summary@1",
  "arc": "vNext+99",
  "target_path": "V45-A",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v98": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 100,
  "runtime_observability_delta_ms": 17
}
```

## Metric-Key Continuity Assertion

```json
{"baseline_metrics_path":"artifacts/stop_gate/metrics_v98_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v99_closeout.json","expected_relation":"exact_keyset_equality","schema":"metric_key_continuity_assertion@1"}
```

## Runtime Observability Comparison

```json
{"baseline_arc":"vNext+98","baseline_elapsed_ms":83,"baseline_source":"artifacts/stop_gate/report_v98_closeout.md","current_arc":"vNext+99","current_elapsed_ms":100,"current_source":"artifacts/stop_gate/report_v99_closeout.md","delta_ms":17,"notes":"v99 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while adding the bounded V45-A repo self-description baseline on main.","schema":"runtime_observability_comparison@1"}
```

## V45A Repo Self-Description Evidence

```json
{"schema":"v45a_repo_self_description_evidence@1","evidence_input_path":"artifacts/agent_harness/v99/evidence_inputs/v45a_repo_self_description_evidence_v99.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS99.md#v99-continuation-contract-machine-checkable","merged_pr":"#321","merge_commit":"791d574ef97ca348ec7c9db88e89bb3f7e17995f","repo_schema_family_registry_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_schema_family_registry.v1.json","repo_schema_family_registry_mirror_schema_path":"spec/repo_schema_family_registry.schema.json","repo_entity_catalog_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_entity_catalog.v1.json","repo_entity_catalog_mirror_schema_path":"spec/repo_entity_catalog.schema.json","accepted_registry_fixture_path":"apps/api/fixtures/repo_description/vnext_plus99/repo_schema_family_registry_v99_reference.json","accepted_entity_catalog_fixture_path":"apps/api/fixtures/repo_description/vnext_plus99/repo_entity_catalog_v99_reference.json"}
```

## Recommendation (Post v99)

- gate decision:
  - `V45A_REPO_SELF_DESCRIPTION_BASELINE_COMPLETE_ON_MAIN`
- rationale:
  - v99 closes the bounded `V45-A` descriptive seam on `main` with deterministic
    extraction of `repo_schema_family_registry@1` and scoped
    `repo_entity_catalog@1`, explicit snapshot/policy binding, precedence-bound
    classification posture, and fail-closed rejection of snapshot/posture/precedence/
    taxonomy/reconstruction contradictions.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`+17 ms` vs v98 baseline).
  - widening into later `V45` lanes remains a planning selection beyond this decision
    note.
