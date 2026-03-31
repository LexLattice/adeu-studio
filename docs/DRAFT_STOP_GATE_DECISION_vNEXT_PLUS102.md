# Draft Stop-Gate Decision (Post vNext+102)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS102.md`

Status: draft decision note (post-hoc closeout capture, March 31, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS102.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v102_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+102` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS102.md`.
- This note captures bounded `V45-C` corrective hardening evidence only; it does not
  authorize symbol-catalog release, code dependency-graph release, test-intent matrix
  release, optimization-register release, descriptive-to-normative binding, scheduler
  automation, or mutation entitlement.
- Canonical `V45-C` corrective release in v102 is carried by the
  `packages/adeu_repo_description` dependency-register schema/model/extraction surfaces,
  deterministic fixture replay under `apps/api/fixtures/repo_description/vnext_plus102/`,
  and the canonical `v45c_repo_arc_dependency_register_hardening_evidence@1` evidence
  input under `artifacts/agent_harness/v102/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#323` (`V45-C: implement v102 corrective hardening for dependency register`)
- arc-completion merge commit: `dc25623edc192f11ea9921f25254d4d4a8fec35e`
- merged-at timestamp: `2026-03-31T15:41:16Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v102_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v102_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v102_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v102/evidence_inputs/metric_key_continuity_assertion_v102.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v102/evidence_inputs/runtime_observability_comparison_v102.json`
  - `V45-C` corrective hardening evidence input:
    `artifacts/agent_harness/v102/evidence_inputs/v45c_repo_arc_dependency_register_hardening_evidence_v102.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v102/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS102_EDGES.md`

## Exit-Criteria Check (vNext+102)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V45-C` corrective hardening merged with green CI | required | `pass` | PR `#323`, merge commit `dc25623edc192f11ea9921f25254d4d4a8fec35e`, checks `python/web/lean-formal = pass` |
| Canonical `repo_arc_dependency_register@2` shipped with authoritative/mirror schema parity | required | `pass` | `packages/adeu_repo_description/schema/repo_arc_dependency_register.v2.json`, `spec/repo_arc_dependency_register.schema.json` |
| Deterministic dependency-register replay over accepted v102 fixture is stable | required | `pass` | replay check in `packages/adeu_repo_description/tests/test_repo_description_v45c.py` and accepted fixture `apps/api/fixtures/repo_description/vnext_plus102/repo_arc_dependency_register_v102_reference.json` |
| Source-set binding and source-set hash are explicit | required | `pass` | accepted fixture replay + required-field enforcement in `packages/adeu_repo_description/src/adeu_repo_description/models.py` |
| Artifact-level extraction posture/method and entry/edge derivation posture/method are explicit | required | `pass` | schema/model anchors plus enforcement in `packages/adeu_repo_description/src/adeu_repo_description/models.py` |
| `source_artifact_refs` membership is constrained to the declared `source_set` | required | `pass` | membership validation in `models.py` and reject fixture `repo_arc_dependency_register_v102_reject_source_artifact_ref_outside_source_set.json` |
| Blocker-list projections reconcile with unresolved hard incoming dependency edges | required | `pass` | blocker reconciliation validation in `models.py` and reject fixture `repo_arc_dependency_register_v102_reject_blocker_dependency_inconsistency.json` |
| Explicit cycle posture and cycle-detection scope are required and validated | required | `pass` | cycle posture/scope validation in `models.py` and reject fixture `repo_arc_dependency_register_v102_reject_missing_cycle_posture.json` |
| Undefined pending-list posture and undefined cross-family vocabulary are rejected | required | `pass` | reject fixtures `repo_arc_dependency_register_v102_reject_undefined_pending_list_posture.json` and `repo_arc_dependency_register_v102_reject_supports_all_three_way_claim.json` |
| Planning corrective marker is validated against lock target path | required | `pass` | `_validate_v45c_corrective_planning_markers` in `packages/adeu_repo_description/src/adeu_repo_description/extract.py` and tests `test_v102_corrective_*` |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v102_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v102/evidence_inputs/metric_key_continuity_assertion_v102.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v102/evidence_inputs/runtime_observability_comparison_v102.json` |

## Stop-Gate Summary

```json
{
  "schema": "v102_closeout_stop_gate_summary@1",
  "arc": "vNext+102",
  "target_path": "V45-C",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v100": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 96,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v100_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v102_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+100","current_arc":"vNext+102","baseline_source":"artifacts/stop_gate/report_v100_closeout.md","current_source":"artifacts/stop_gate/report_v102_closeout.md","baseline_elapsed_ms":96,"current_elapsed_ms":96,"delta_ms":0,"notes":"v102 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while hardening the released V45-C dependency register to repo_arc_dependency_register@2 with explicit provenance, bounded posture vocabularies, cycle posture scope, and corrective planning-marker consistency guards."}
```

## V45C Repo Arc Dependency Register Hardening Evidence

```json
{"schema":"v45c_repo_arc_dependency_register_hardening_evidence@1","evidence_input_path":"artifacts/agent_harness/v102/evidence_inputs/v45c_repo_arc_dependency_register_hardening_evidence_v102.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS102.md#v102-continuation-contract-machine-checkable","merged_pr":"#323","merge_commit":"dc25623edc192f11ea9921f25254d4d4a8fec35e","repo_arc_dependency_register_authoritative_schema_path":"packages/adeu_repo_description/schema/repo_arc_dependency_register.v2.json","repo_arc_dependency_register_mirror_schema_path":"spec/repo_arc_dependency_register.schema.json","accepted_dependency_register_fixture_path":"apps/api/fixtures/repo_description/vnext_plus102/repo_arc_dependency_register_v102_reference.json"}
```

## Recommendation (Post v102)

- gate decision:
  - `V45C_REPO_ARC_DEPENDENCY_REGISTER_HARDENING_COMPLETE_ON_MAIN`
- rationale:
  - v102 closes the bounded corrective `V45-C` follow-up on `main` by shipping
    deterministic `repo_arc_dependency_register@2` surfaces with explicit source-set
    provenance, bounded posture/method vocabularies, explicit cycle posture/scope,
    blocker projection consistency laws, and fail-closed rejection for undefined
    pending-list and cross-family vocabulary.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`0 ms` vs v100 baseline).
  - broader widening into `V45-B` and later lanes remains a planning selection beyond
    this decision note.
