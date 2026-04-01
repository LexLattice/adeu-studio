# Draft Stop-Gate Decision (Post vNext+105)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md`

Status: draft decision note (post-hoc closeout capture, April 1, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS105.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v105_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+105` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md`.
- This note captures bounded `V45-F` release evidence only; it does not authorize
  downstream execution, mutation, scheduling, release gating, approval posture, or
  recursive-governance action by itself.
- Canonical `V45-F` release in v105 is carried by the
  `packages/adeu_repo_description` binding-frame schema/model/extraction surfaces,
  deterministic fixture replay under
  `apps/api/fixtures/repo_description/vnext_plus105/`, and the canonical
  `v45f_repo_descriptive_normative_binding_frame_evidence@1` evidence input under
  `artifacts/agent_harness/v105/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#327` (`V45-F: implement v105 descriptive normative binding frame`)
- arc-completion merge commit: `ffbf0fe8a042aa4529ef615a5ba750fd30d9124e`
- merged-at timestamp: `2026-04-01T08:34:02Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v105_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v105_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v105_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v105/evidence_inputs/metric_key_continuity_assertion_v105.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v105/evidence_inputs/runtime_observability_comparison_v105.json`
  - `V45-F` release evidence input:
    `artifacts/agent_harness/v105/evidence_inputs/v45f_repo_descriptive_normative_binding_frame_evidence_v105.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v105/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS105_EDGES.md`

## Exit-Criteria Check (vNext+105)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V45-F` merged with green CI | required | `pass` | PR `#327`, merge commit `ffbf0fe8a042aa4529ef615a5ba750fd30d9124e`, checks `python/web/lean-formal = pass` |
| Canonical `repo_descriptive_normative_binding_frame@1` shipped with authoritative/mirror schema parity | required | `pass` | `packages/adeu_repo_description/schema/repo_descriptive_normative_binding_frame.v1.json`, `spec/repo_descriptive_normative_binding_frame.schema.json` |
| Deterministic replay over the accepted v105 fixture is stable | required | `pass` | replay check in `packages/adeu_repo_description/tests/test_repo_description_v45f.py` and accepted fixture `apps/api/fixtures/repo_description/vnext_plus105/repo_descriptive_normative_binding_frame_v105_reference.json` |
| Explicit snapshot identity/hash, explicit bounded source-set binding, explicit `source_set_hash`, and explicit extraction posture/method are present | required | `pass` | accepted fixture replay plus required-field enforcement in `packages/adeu_repo_description/src/adeu_repo_description/models.py` |
| Explicit `V45-A` through `V45-E` binding is enforced with bound-baseline compatibility rules | required | `pass` | `validate_repo_descriptive_normative_binding_frame_against_v45_baseline` in `packages/adeu_repo_description/src/adeu_repo_description/models.py` and baseline-binding coverage in `packages/adeu_repo_description/tests/test_repo_description_v45f.py` |
| Each binding row preserves explicit distinction between descriptive input, consumer class, binding posture, authority source, and promotion-law posture | required | `pass` | row-model anchors in `models.py` and accepted fixture replay in `test_repo_description_v45f.py` |
| Bounded consumer-class doctrine remains explicit and non-executive | required | `pass` | bounded starter vocabularies in `models.py`, accepted fixture replay, and lock boundary in `docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md` |
| `descriptive_input_ref` and `source_artifact_refs` fail closed when unresolved or out of declared scope | required | `pass` | membership/baseline-resolution validation in `models.py` and reject fixtures `repo_descriptive_normative_binding_frame_v105_reject_descriptive_input_ref_outside_bound_baseline.json` plus `repo_descriptive_normative_binding_frame_v105_reject_source_artifact_ref_outside_source_set.json` |
| Binding-frame collapse, authority laundering, missing promotion-law posture, and recursive-governance execution entitlement fail closed | required | `pass` | reject fixtures under `apps/api/fixtures/repo_description/vnext_plus105/` and rejection assertions in `packages/adeu_repo_description/tests/test_repo_description_v45f.py` |
| Snapshot-validity posture propagates consistently through nested bound derivations, including `V45-B` surfaces | required | `pass` | `derive_v45f_repo_descriptive_normative_binding_frame` in `packages/adeu_repo_description/src/adeu_repo_description/extract.py`, baseline validation in `models.py`, and `test_v45f_propagates_historical_snapshot_validity_to_nested_derivations` in `test_repo_description_v45f.py` |
| Historical `V45-C` baseline context remains explicit rather than silently re-derived from current planning state | required | `pass` | `_load_historical_v45c_v102_reference` in `packages/adeu_repo_description/src/adeu_repo_description/extract.py` and accepted fixture replay in `test_repo_description_v45f.py` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v105_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v105/evidence_inputs/metric_key_continuity_assertion_v105.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v105/evidence_inputs/runtime_observability_comparison_v105.json` |

## Stop-Gate Summary

```json
{
  "schema": "v105_closeout_stop_gate_summary@1",
  "arc": "vNext+105",
  "target_path": "V45-F",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v104": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 96,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v104_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v105_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+104","current_arc":"vNext+105","baseline_source":"artifacts/stop_gate/report_v104_closeout.md","current_source":"artifacts/stop_gate/report_v105_closeout.md","baseline_elapsed_ms":96,"current_elapsed_ms":96,"delta_ms":0,"notes":"v105 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V45-F repo_descriptive_normative_binding_frame@1 surface with explicit consumer-class and promotion-law doctrine, explicit non-executive posture, cross-artifact baseline validation over released V45-A through V45-E surfaces, historical V45-C loading, and explicit snapshot-validity propagation across nested derivations including bound V45-B artifacts."}
```

## V45F Repo Descriptive Normative Binding Frame Evidence

```json
{"schema":"v45f_repo_descriptive_normative_binding_frame_evidence@1","evidence_input_path":"artifacts/agent_harness/v105/evidence_inputs/v45f_repo_descriptive_normative_binding_frame_evidence_v105.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS105.md#v105-continuation-contract-machine-checkable","merged_pr":"#327","merge_commit":"ffbf0fe8a042aa4529ef615a5ba750fd30d9124e","repo_descriptive_normative_binding_frame_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_descriptive_normative_binding_frame.v1.json","repo_descriptive_normative_binding_frame_mirror_schema_path":"spec/repo_descriptive_normative_binding_frame.schema.json","accepted_binding_frame_fixture_path":"apps/api/fixtures/repo_description/vnext_plus105/repo_descriptive_normative_binding_frame_v105_reference.json"}
```

## Recommendation (Post v105)

- gate decision:
  - `V45F_REPO_DESCRIPTIVE_NORMATIVE_BINDING_FRAME_COMPLETE_ON_MAIN`
- rationale:
  - v105 closes the bounded `V45-F` widening seam on `main` by shipping a
    deterministic `repo_descriptive_normative_binding_frame@1` surface with explicit
    descriptive-input versus consumer-class versus authority-source versus
    promotion-law separation.
  - the shipped slice remains non-executive and non-approving: it constrains later
    normative consumers without minting mutation, scheduling, or recursive-execution
    authority by itself.
  - review hardening closed a concrete brittleness risk by propagating requested
    snapshot-validity posture through nested `V45-A`, `V45-B`, `V45-D`, and `V45-E`
    derivations and by validating `V45-B` posture consistency explicitly in the
    bound-baseline validator.
  - historical `V45-C` context remains explicit and inspectable rather than being
    silently re-derived from current planning state.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`0 ms` vs v104 baseline).
  - the bounded `V45` family ladder through `V45-F` is now complete on `main`; later
    recursive-governance or amendment-execution consumers, if selected, should be
    treated as downstream family work rather than another implicit `V45` continuation.
