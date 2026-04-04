# Draft Stop-Gate Decision (Post vNext+120)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS120.md`

Status: draft decision note (post-hoc closeout capture, April 4, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS120.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v120_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+120` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS120.md`.
- This note captures bounded `V49-D` bridge evidence only; it does not authorize any
  later semantic consumer family, symbol-audit lane, paper-semantic lane, simulation
  lane, runtime surface, or CLI / API / web consumer by itself.
- Canonical `V49-D` release in `v120` is carried by the shipped
  `adeu_semantic_forms` bridge source, committed deterministic `v49d` fixtures,
  package tests, and the canonical
  `v49d_semantic_forms_v48_bridge_evidence@1` evidence input under
  `artifacts/agent_harness/v120/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md` now marks `V49-D`
  closed on `main`, completing the bounded `V49` family with no further internal
  `V49` path currently selected; it does not select any later semantic consumer family
  by itself.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#342` (`[codex] feat(v120): add semantic forms V48 bridge`)
- arc-completion merge commit: `d3d26c8ae9c638960431f08136ed0587df439228`
- merged-at timestamp: `2026-04-04T00:56:04Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v120_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v120_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v120_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v120/evidence_inputs/metric_key_continuity_assertion_v120.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v120/evidence_inputs/runtime_observability_comparison_v120.json`
  - `V49-D` release evidence input:
    `artifacts/agent_harness/v120/evidence_inputs/v49d_semantic_forms_v48_bridge_evidence_v120.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v120/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS120_EDGES.md`

## Exit-Criteria Check (vNext+120)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V49-D` merged with green CI | required | `pass` | PR `#342`, merge commit `d3d26c8ae9c638960431f08136ed0587df439228`, checks `python/web/lean-formal = pass` |
| Repo-owned `adeu_semantic_forms` package remains the only live owner of the bridge lane | required | `pass` | `packages/adeu_semantic_forms/pyproject.toml`, `packages/adeu_semantic_forms/src/adeu_semantic_forms/bridge_v48.py`, and absence of prototype-tree import into live package paths |
| Bridge consumes exactly one released `adeu_taskpack_binding_spec_seed@1` plus exactly one repo-owned `adeu_semantic_seed_v48_bridge_contract@1` and emits exactly one released `anm_taskpack_binding_profile@1` | required | `pass` | `bridge_seed_to_v48a_taskpack_binding_profile(...)` in `packages/adeu_semantic_forms/src/adeu_semantic_forms/bridge_v48.py`, released bridge/seed models in `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py`, and committed `v49d` fixtures |
| Bridge output is produced only through released `build_v48a_taskpack_binding_profile(...)` semantics | required | `pass` | released-builder call in `bridge_v48.py`, plus replay against `packages/adeu_agent_harness/tests/fixtures/v48a/reference_anm_taskpack_binding_profile.json` |
| Bridge consumes only released `V49-C` seed lineage and does not recover authority from raw `V45` / `V47` / `V49-A` / `V49-B` surfaces | required | `pass` | bridge helper signature, absence of ambient recovery logic, and committed `v49d` fixture scope |
| Profile lineage, snapshot lineage, and seed-anchor mapping all fail closed on mismatch | required | `pass` | `ASF6002`, `ASF6003`, and wrapped `AHK5605` reject posture in `bridge_v48.py`, plus scope/snapshot reject fixtures and tests |
| Bridge contract task-scope, command, evidence, and prompt projections are contract-owned only and are never synthesized | required | `pass` | released bridge-contract model and builder in `models.py` / `parse_profile.py`, pass-through projection handling in `bridge_v48.py`, and prompt-authority reject fixture/test |
| `policy_authority_clause_ref` remains builder-owned through released `V47-E` / `V48-A` lineage and is never synthesized locally | required | `pass` | bridge helper delegates clause resolution to released `build_v48a_taskpack_binding_profile(...)` only |
| Seed fixed defaults may restate only the released `V48-A` postures and fail closed on conflict | required | `pass` | exact-default enforcement in `_validate_seed_defaults(...)`, fixed-default conflict fixture, and `test_fixed_default_conflict_fails_closed` |
| Empty seed projection families are rejected predictably before entering the released `V48-A` builder | required | `pass` | `_validate_seed_projections(...)` and `test_empty_seed_projection_fails_closed` |
| Emitted binding profile revalidates under the released `AnmTaskpackBindingProfile` model and recomputed `semantic_hash` matches emitted output | required | `pass` | output revalidation path in `bridge_v48.py` and reference replay tests |
| Emitted binding profile is admissible as the released `binding_profile_ref` carrier for `compile_v48b_taskpack_binding(...)`, with remaining compiler inputs supplied separately | required | `pass` | compile-compatibility proof in `packages/adeu_semantic_forms/tests/test_semantic_forms_bridge_v48.py::test_reference_bridge_output_is_compile_compatible` |
| Repeated bridge replay is byte-identical and deterministic | required | `pass` | `test_repeated_bridge_is_byte_identical` and committed `v49d` reference fixtures |
| No new compile wrapper, worker runtime, or product consumer ships in this slice | required | `pass` | implementation footprint limited to bridge/package/tests/fixtures and absence of CLI/API/web surfaces |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v120_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v120/evidence_inputs/metric_key_continuity_assertion_v120.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v120/evidence_inputs/runtime_observability_comparison_v120.json` |

## Stop-Gate Summary

```json
{
  "schema": "v120_closeout_stop_gate_summary@1",
  "arc": "vNext+120",
  "target_path": "V49-D",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v119": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 107,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v119_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v120_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+119","current_arc":"vNext+120","baseline_source":"artifacts/stop_gate/report_v119_closeout.md","current_source":"artifacts/stop_gate/report_v120_closeout.md","baseline_elapsed_ms":107,"current_elapsed_ms":107,"delta_ms":0,"notes":"v120 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V49-D semantic-seed bridge lane: one repo-owned adeu_semantic_forms bridge surface, one released V49-C seed lineage only, one repo-owned adeu_semantic_seed_v48_bridge_contract@1, one released V48-A binding-profile emission path, one released binding_profile_ref admissibility path into V48-B, fail-closed anchor and snapshot matching, exact released-posture fixed-default restatement, deterministic v49d replay fixtures, compile-compatibility proof through released V48-B, and no new compile wrapper, runtime surface, or product-surface widening."}
```

## V49D Semantic Forms V48 Bridge Evidence

```json
{"schema":"v49d_semantic_forms_v48_bridge_evidence@1","evidence_input_path":"artifacts/agent_harness/v120/evidence_inputs/v49d_semantic_forms_v48_bridge_evidence_v120.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS120.md#v120-continuation-contract-machine-checkable","merged_pr":"#342","merge_commit":"d3d26c8ae9c638960431f08136ed0587df439228","implementation_packages":["adeu_semantic_forms"],"semantic_forms_package_root":"packages/adeu_semantic_forms","semantic_forms_pyproject_path":"packages/adeu_semantic_forms/pyproject.toml","semantic_forms_models_source_path":"packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py","semantic_forms_parse_profile_source_path":"packages/adeu_semantic_forms/src/adeu_semantic_forms/parse_profile.py","semantic_forms_transform_v48_seed_source_path":"packages/adeu_semantic_forms/src/adeu_semantic_forms/transform_v48_seed.py","semantic_forms_bridge_v48_source_path":"packages/adeu_semantic_forms/src/adeu_semantic_forms/bridge_v48.py","semantic_forms_package_init_source_path":"packages/adeu_semantic_forms/src/adeu_semantic_forms/__init__.py","test_reference_paths":["packages/adeu_semantic_forms/tests/test_semantic_forms_models.py","packages/adeu_semantic_forms/tests/test_semantic_forms_parse_profile.py","packages/adeu_semantic_forms/tests/test_semantic_forms_transform_v48_seed.py","packages/adeu_semantic_forms/tests/test_semantic_forms_bridge_v48.py"],"reference_seed_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49d/reference_taskpack_binding_spec_seed.json","reference_bridge_contract_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49d/reference_semantic_seed_v48_bridge_contract.json","scope_anchor_mismatch_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49d/mutation_semantic_seed_v48_bridge_contract_scope_anchor_mismatch.json","snapshot_mismatch_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49d/mutation_semantic_seed_v48_bridge_contract_snapshot_mismatch.json","prompt_authority_drift_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49d/mutation_semantic_seed_v48_bridge_contract_prompt_authority_drift.json","fixed_default_conflict_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49d/mutation_taskpack_binding_spec_seed_fixed_default_conflict.json","reference_v48a_binding_profile_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48a/reference_anm_taskpack_binding_profile.json","reference_v48b_compiled_binding_fixture_path":"packages/adeu_agent_harness/tests/fixtures/v48b/reference_compiled_policy_taskpack_binding.json","metric_key_continuity_assertion_path":"artifacts/agent_harness/v120/evidence_inputs/metric_key_continuity_assertion_v120.json","runtime_observability_comparison_path":"artifacts/agent_harness/v120/evidence_inputs/runtime_observability_comparison_v120.json","runtime_event_stream_path":"artifacts/agent_harness/v120/runtime/evidence/local/urm_events.ndjson","notes":"v120 evidence pins the released V49-D semantic-seed bridge lane on main: one repo-owned adeu_semantic_forms bridge helper over one released V49-C seed plus one repo-owned adeu_semantic_seed_v48_bridge_contract@1, direct emission through released build_v48a_taskpack_binding_profile(...) semantics only, released binding_profile_ref admissibility into compile_v48b_taskpack_binding(...), fail-closed profile, anchor, snapshot, fixed-default, prompt-authority, and empty-seed-projection reject posture, deterministic v49d replay fixtures, compile-compatibility proof through released V48-B, and no new compile wrapper, runtime surface, or product-surface widening."}
```

## Recommendation (Post v120)

- gate decision:
  - `V49D_SEMANTIC_FORMS_V48_BRIDGE_COMPLETE_ON_MAIN`
  - `V49_SEMANTIC_FORMS_SUBSTRATE_FAMILY_COMPLETE_ON_MAIN`
- rationale:
  - `v120` closes the bounded `V49-D` bridge seam on `main` by shipping the first
    repo-owned `adeu_semantic_forms` helper from one released semantic seed plus one
    repo-owned bridge contract into one released `V48-A` binding profile.
  - the shipped slice remains bridge-first and bounded: one released seed contract,
    one repo-owned bridge contract, one starter domain, one released `V48-A` builder
    path, one released `binding_profile_ref` admissibility path into `V48-B`, and no
    worker runtime or product-surface widening.
  - admissibility is explicit and fail closed: no raw `V45` / `V47` / `V49-A` /
    `V49-B` bypass, no local synthesis of `task_scope_summary`, prompt inputs, or
    `policy_authority_clause_ref`, and exact profile / snapshot / anchor matching.
  - seed projection law is explicit and deterministic: `allow_paths`, `forbid_paths`,
    and `forbid_effects` are passed into the released `V48-A` projection families
    unchanged, but empty projection families are rejected locally before builder entry.
  - bridge defaults remain exact restatements of the released `V48-A` postures only
    and fail closed on conflict.
  - the emitted binding profile revalidates under the released
    `AnmTaskpackBindingProfile` model and is proved compile-compatible with the
    released `V48-B` compiler lane.
  - the imported prototype bundle remains support-only and non-precedent; the release
    re-authors live bridge code in repo-owned package paths rather than importing
    prototype code wholesale.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`0 ms` vs `v119` baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md` now records `V49-D` as closed on `main`,
    completing the bounded `V49` family with no further internal `V49` path selected.
