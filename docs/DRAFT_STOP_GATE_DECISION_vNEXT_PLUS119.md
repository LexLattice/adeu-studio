# Draft Stop-Gate Decision (Post vNext+119)

This note records the arc-completion decision for:

- `docs/LOCKED_CONTINUATION_vNEXT_PLUS119.md`

Status: draft decision note (post-hoc closeout capture, April 4, 2026 UTC).

## Decision-State Marker (Machine-Checkable)

```json
{
  "schema": "decision_artifact_state@1",
  "artifact": "docs/DRAFT_STOP_GATE_DECISION_vNEXT_PLUS119.md",
  "phase": "post_closeout_decision",
  "authoritative": true,
  "authoritative_scope": "v119_closeout_stop_gate_decision",
  "required_in_closeout": true,
  "all_passed": true,
  "notes": "Pre-start scaffold markers are superseded by post-closeout evidence and final decision values in this document."
}
```

## Decision Guardrail (Frozen)

- This draft records `vNext+119` closeout evidence only.
- It must not redefine semantics, locks, or scope from
  `docs/LOCKED_CONTINUATION_vNEXT_PLUS119.md`.
- This note captures bounded `V49-C` deterministic lowering evidence only; it does not
  authorize the later `V49-D` bridge, `V48-A` binding-profile emission,
  `V48-B` compiled-boundary emission, worker runtime behavior, or CLI / API / web
  consumers by itself.
- Canonical `V49-C` release in `v119` is carried by the shipped
  `adeu_semantic_forms` lowering source, committed deterministic `v49c` fixtures,
  package tests, and the canonical
  `v49c_semantic_forms_lowering_evidence@1` evidence input under
  `artifacts/agent_harness/v119/evidence_inputs/`.
- Runtime observability comparison remains required evidence and informational-only in
  this arc.
- This note also records that `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md` now marks `V49-C`
  closed on `main` and advances the branch-local default next path to `V49-D`; it
  does not select any later `V49` closeout by itself.

## Evidence Source

- CI workflow: `ci` on `main`
- merged implementation PRs:
  - `#341` (`[codex] add semantic forms deterministic lowering`)
- arc-completion merge commit: `cfb9b26aeaaea16db827af37e535a4d949036fa2`
- merged-at timestamp: `2026-04-03T23:57:19Z`
- merged PR checks:
  - `python`: `pass`
  - `web`: `pass`
  - `lean-formal`: `pass`
- deterministic closeout artifacts (reproducible):
  - quality dashboard JSON: `artifacts/quality_dashboard_v119_closeout.json`
  - stop-gate JSON: `artifacts/stop_gate/metrics_v119_closeout.json`
  - stop-gate Markdown: `artifacts/stop_gate/report_v119_closeout.md`
  - metric-key continuity evidence input:
    `artifacts/agent_harness/v119/evidence_inputs/metric_key_continuity_assertion_v119.json`
  - runtime observability evidence input:
    `artifacts/agent_harness/v119/evidence_inputs/runtime_observability_comparison_v119.json`
  - `V49-C` release evidence input:
    `artifacts/agent_harness/v119/evidence_inputs/v49c_semantic_forms_lowering_evidence_v119.json`
  - runtime event stream evidence:
    `artifacts/agent_harness/v119/runtime/evidence/local/urm_events.ndjson`
- closeout edge assessment:
  - `docs/ASSESSMENT_vNEXT_PLUS119_EDGES.md`

## Exit-Criteria Check (vNext+119)

| Criterion | Threshold | Current State | Evidence |
|---|---|---|---|
| `V49-C` merged with green CI | required | `pass` | PR `#341`, merge commit `cfb9b26aeaaea16db827af37e535a4d949036fa2`, checks `python/web/lean-formal = pass` |
| Repo-owned `adeu_semantic_forms` package remains the only live owner of the first lowering lane | required | `pass` | `packages/adeu_semantic_forms/pyproject.toml`, `packages/adeu_semantic_forms/src/adeu_semantic_forms/transform_v48_seed.py`, and absence of prototype-tree import into live package paths |
| Lowering consumes exactly one released `adeu_semantic_normal_form@1` plus exactly one released `adeu_semantic_transform_contract@1` and emits exactly one released `adeu_taskpack_binding_spec_seed@1` | required | `pass` | `lower_semantic_normal_form_to_taskpack_binding_spec_seed(...)` in `packages/adeu_semantic_forms/src/adeu_semantic_forms/transform_v48_seed.py`, released models in `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py`, and committed `v49c` fixtures |
| Lowering remains admissible only from direct released `V49-A` normal forms or released `V49-B` parse results with `parse_status = resolved_singleton` | required | `pass` | `lower_parse_result_to_taskpack_binding_spec_seed(...)` gating in `transform_v48_seed.py` and `test_typed_alternatives_parse_result_is_not_admissible_for_lowering` |
| Lowering does not silently choose one candidate out of `typed_alternatives`, and does not lower `clarification_required` or `rejected_unsupported` outputs | required | `pass` | `ASF5902` fail-closed path in `transform_v48_seed.py` and parse-result admissibility tests |
| Contract-declared required singleton relations are enforced generically and fail closed when missing or duplicated | required | `pass` | generic enforcement over `transform_contract.required_singleton_relations` in `transform_v48_seed.py`, `test_missing_required_relation_fails_closed`, `test_contract_required_singleton_relations_are_enforced_generically`, and `test_duplicate_singleton_relation_fails_closed` |
| `produce_artifact_kind` remains singleton in the starter slice and emits one canonical artifact family as a single-item deterministic set | required | `pass` | starter relation projection and artifact-kind guard in `transform_v48_seed.py`, plus `reference_taskpack_binding_spec_seed.json` |
| Transform-contract mismatch, unsupported relation kinds, and fixed-default conflicts fail closed | required | `pass` | `ASF5903`, `ASF5906`, and `ASF5907` paths in `transform_v48_seed.py`, with replay fixtures and targeted tests |
| Repeated lowering is byte-identical and deterministic multi-relation ordering is retained | required | `pass` | deterministic lowering law in `transform_v48_seed.py` and `test_repeated_lowering_is_byte_identical` |
| Emitted seed remains pre-bridge only and is not admissible as a released `V48-A` binding profile in this slice | required | `pass` | shipped scope limited to `adeu_taskpack_binding_spec_seed@1`, `transform_v48_seed.py`, and absence of `V48` bridge helper surfaces in `packages/adeu_semantic_forms` |
| Deterministic `v49c` fixtures replay exactly | required | `pass` | `packages/adeu_semantic_forms/tests/test_semantic_forms_transform_v48_seed.py` and fixtures under `packages/adeu_semantic_forms/tests/fixtures/v49c/` |
| No `V48` bridge helper, worker runtime, or product consumer ships in this slice | required | `pass` | implementation footprint limited to lowering/package/tests/fixtures and absence of CLI/API/web surfaces |
| Stop-gate schema-family continuity retained | required | `pass` | `artifacts/stop_gate/metrics_v119_closeout.json` with `schema = stop_gate_metrics@1`, `valid = true`, `all_passed = true` |
| Stop-gate metric-key continuity retained | required | `pass` | `artifacts/agent_harness/v119/evidence_inputs/metric_key_continuity_assertion_v119.json` |
| Runtime observability comparison captured | required | `pass` | `artifacts/agent_harness/v119/evidence_inputs/runtime_observability_comparison_v119.json` |

## Stop-Gate Summary

```json
{
  "schema": "v119_closeout_stop_gate_summary@1",
  "arc": "vNext+119",
  "target_path": "V49-C",
  "stop_gate_schema_family": "stop_gate_metrics@1",
  "metric_key_cardinality": 80,
  "metric_key_exact_set_equal_v118": true,
  "all_passed": true,
  "runtime_observability_elapsed_ms": 107,
  "runtime_observability_delta_ms": 0
}
```

## Metric-Key Continuity Assertion

```json
{"schema":"metric_key_continuity_assertion@1","baseline_metrics_path":"artifacts/stop_gate/metrics_v118_closeout.json","current_metrics_path":"artifacts/stop_gate/metrics_v119_closeout.json","expected_relation":"exact_keyset_equality"}
```

## Runtime Observability Comparison

```json
{"schema":"runtime_observability_comparison@1","baseline_arc":"vNext+118","current_arc":"vNext+119","baseline_source":"artifacts/stop_gate/report_v118_closeout.md","current_source":"artifacts/stop_gate/report_v119_closeout.md","baseline_elapsed_ms":107,"current_elapsed_ms":107,"delta_ms":0,"notes":"v119 closeout keeps the frozen stop-gate schema family and exact metric keyset unchanged while shipping the released V49-C semantic lowering lane: one repo-owned adeu_semantic_forms lowering surface, one released repo_policy_work normal-form domain, one released adeu_semantic_transform_contract@1 source only, direct V49-A normal-form or V49-B resolved_singleton gating only, no lowering from typed_alternatives clarification_required or rejected_unsupported, generic required-singleton enforcement, singleton produce_artifact_kind emission, fixed-default conflict fail-closed posture, deterministic v49c replay fixtures, and no V48 bridge helper, runtime, or product-surface widening."}
```

## V49C Semantic Forms Lowering Evidence

```json
{"schema":"v49c_semantic_forms_lowering_evidence@1","evidence_input_path":"artifacts/agent_harness/v119/evidence_inputs/v49c_semantic_forms_lowering_evidence_v119.json","contract_source":"docs/LOCKED_CONTINUATION_vNEXT_PLUS119.md#v119-continuation-contract-machine-checkable","merged_pr":"#341","merge_commit":"cfb9b26aeaaea16db827af37e535a4d949036fa2","implementation_packages":["adeu_semantic_forms"],"semantic_forms_package_root":"packages/adeu_semantic_forms","semantic_forms_pyproject_path":"packages/adeu_semantic_forms/pyproject.toml","semantic_forms_models_source_path":"packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py","semantic_forms_parse_profile_source_path":"packages/adeu_semantic_forms/src/adeu_semantic_forms/parse_profile.py","semantic_forms_parser_source_path":"packages/adeu_semantic_forms/src/adeu_semantic_forms/parser.py","semantic_forms_transform_v48_seed_source_path":"packages/adeu_semantic_forms/src/adeu_semantic_forms/transform_v48_seed.py","semantic_forms_package_init_source_path":"packages/adeu_semantic_forms/src/adeu_semantic_forms/__init__.py","test_reference_paths":["packages/adeu_semantic_forms/tests/test_semantic_forms_models.py","packages/adeu_semantic_forms/tests/test_semantic_forms_parse_profile.py","packages/adeu_semantic_forms/tests/test_semantic_forms_parser.py","packages/adeu_semantic_forms/tests/test_semantic_forms_transform_v48_seed.py"],"reference_seed_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49c/reference_taskpack_binding_spec_seed.json","missing_policy_anchor_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49c/mutation_semantic_normal_form_missing_policy_anchor.json","duplicate_worker_subject_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49c/mutation_semantic_normal_form_duplicate_worker_subject.json","profile_mismatch_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49c/mutation_semantic_transform_contract_profile_mismatch.json","fixed_default_conflict_fixture_path":"packages/adeu_semantic_forms/tests/fixtures/v49c/mutation_semantic_transform_contract_fixed_default_conflict.json","metric_key_continuity_assertion_path":"artifacts/agent_harness/v119/evidence_inputs/metric_key_continuity_assertion_v119.json","runtime_observability_comparison_path":"artifacts/agent_harness/v119/evidence_inputs/runtime_observability_comparison_v119.json","runtime_event_stream_path":"artifacts/agent_harness/v119/runtime/evidence/local/urm_events.ndjson","notes":"v119 evidence pins the released V49-C semantic lowering lane on main: one repo-owned adeu_semantic_forms lowering surface over released V49-A semantic normal forms and transform contracts, direct V49-A or V49-B resolved_singleton gating only, no lowering from typed_alternatives clarification_required or rejected_unsupported, generic required-singleton enforcement, singleton produce_artifact_kind projection, deterministic multi-relation ordering, fixed-default conflict fail-closed posture, deterministic v49c replay fixtures, and no V48 bridge helper, runtime surface, or product-surface widening."}
```

## Recommendation (Post v119)

- gate decision:
  - `V49C_SEMANTIC_FORMS_LOWERING_COMPLETE_ON_MAIN`
  - `V49_SEMANTIC_FORMS_SUBSTRATE_FAMILY_ACTIVE_ON_MAIN`
- rationale:
  - `v119` closes the bounded `V49-C` deterministic lowering seam on `main` by
    shipping the first repo-owned `adeu_semantic_forms` lowering surface from one
    released semantic normal form plus one released transform contract into one narrow
    `adeu_taskpack_binding_spec_seed@1`.
  - the shipped slice remains lowering-first and bounded: one released input normal
    form, one released transform contract, one starter domain, one starter target
    schema, one deterministic seed contract, and no downstream bridge, runtime, or
    product-surface widening.
  - admissibility is explicit and fail closed: direct `V49-A` normal forms are
    admitted, `V49-B` parse results are admitted only when `parse_status` is exactly
    `resolved_singleton`, and lowering never silently chooses one alternative out of
    `typed_alternatives`.
  - relation projection law is explicit and deterministic: contract-declared required
    singleton relations are enforced generically, supported multi relations remain
    ordered deterministically, and `produce_artifact_kind` stays singleton in the
    starter slice.
  - fixed defaults remain contract-declared constant projection only and fail closed
    on conflict with relation-derived values.
  - the emitted seed remains pre-bridge and non-equivalent to a released `V48-A`
    binding profile; the later `V49-D` bridge remains the only selected lane for
    handing semantic seeds into the released `V48` stack.
  - the imported prototype bundle remains support-only and non-precedent; the release
    re-authors live lowering code in repo-owned package paths rather than importing
    prototype code wholesale.
  - no stop-gate schema-family or metric-key regressions were introduced.
  - runtime observability changed only informationally (`0 ms` vs `v118` baseline).
  - `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md` now records `V49-C` as closed on `main` and
    advances the branch-local default next path to `V49-D` / `vNext+120`.
