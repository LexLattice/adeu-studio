# Assessment vNext+119 Edges

Status: post-closeout edge assessment for `V49-C` (April 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS119_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Released-Contract Bypass

- Risk:
  the lowering lane could claim `V49-C` ownership while consuming ad hoc local
  structures instead of the released `V49-A` normal-form and transform-contract
  contracts.
- Response:
  keep one released normal form plus one released transform contract in and one
  released seed contract out.
- Closeout Evidence:
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/transform_v48_seed.py`,
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py`, and committed
  `v49c` replay fixtures under `packages/adeu_semantic_forms/tests/fixtures/v49c/`.

### Edge 2: Upstream Outcome Shortcutting

- Risk:
  the lowering lane could silently choose one candidate out of
  `typed_alternatives` or otherwise lower from non-`resolved_singleton` recovery
  outputs.
- Response:
  admit lowering only from directly authored released `V49-A` normal forms or
  released `V49-B` outputs whose `parse_status` is exactly `resolved_singleton`.
- Closeout Evidence:
  `lower_parse_result_to_taskpack_binding_spec_seed(...)` in
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/transform_v48_seed.py` and
  `packages/adeu_semantic_forms/tests/test_semantic_forms_transform_v48_seed.py::test_typed_alternatives_parse_result_is_not_admissible_for_lowering`.

### Edge 3: Required-Relation Softness

- Risk:
  missing contract-declared required singleton relations could be silently repaired
  into apparent success.
- Response:
  require generic fail-closed enforcement over
  `transform_contract.required_singleton_relations`.
- Closeout Evidence:
  generic required-singleton enforcement in lowering source plus
  `test_missing_required_relation_fails_closed` and
  `test_contract_required_singleton_relations_are_enforced_generically`.

### Edge 4: Singleton Multiplicity Drift

- Risk:
  duplicate singleton relations could be tolerated inconsistently across
  implementations.
- Response:
  require duplicate singleton relations to fail closed.
- Closeout Evidence:
  `_required_singleton_value(...)` in lowering source,
  `mutation_semantic_normal_form_duplicate_worker_subject.json`, and
  `test_duplicate_singleton_relation_fails_closed`.

### Edge 5: Multi-Relation Ordering Drift

- Risk:
  emitted path/effect/artifact collections could depend on incidental iteration order.
- Response:
  require deterministic ordering from released normal-form ordering and replay
  byte-identical seed emission.
- Closeout Evidence:
  lowering projection logic and
  `packages/adeu_semantic_forms/tests/test_semantic_forms_transform_v48_seed.py::test_repeated_lowering_is_byte_identical`.

### Edge 6: `produce_artifact_kind` Multiplicity Drift

- Risk:
  the starter lowering slice could treat `produce_artifact_kind` as both singleton and
  multi-valued, leaving the multiplicity law to implementation taste.
- Response:
  freeze `produce_artifact_kind` as a required singleton relation in `V49-C` and emit
  it as one canonical artifact family represented as a single-item deterministic set.
- Closeout Evidence:
  artifact-kind guard in lowering source and
  `packages/adeu_semantic_forms/tests/fixtures/v49c/reference_taskpack_binding_spec_seed.json`.

### Edge 7: Unsupported Relation Laundering

- Risk:
  unsupported relation kinds or transform mismatches could be silently dropped while
  still producing a seed.
- Response:
  require unsupported relation kinds and contract mismatch to fail closed.
- Closeout Evidence:
  `ASF5903` and `ASF5906` fail-closed paths in lowering source plus
  `mutation_semantic_transform_contract_profile_mismatch.json` and targeted tests.

### Edge 8: Consumed Normal-Form Anchor Drift

- Risk:
  `transform_v48_seed.py` could end up defining what parts of the released normal form
  actually matter because the consumed input anchors are left implicit.
- Response:
  consume the released normal-form anchors explicitly: schema, profile/domain lineage,
  statement cores, identity-bearing per-core fields, and semantic hash.
- Closeout Evidence:
  consumed anchor checks in lowering source and released normal-form models in
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py`.

### Edge 9: Fixed-Default Overreach

- Risk:
  `fixed_defaults` could become a back door for parser heuristics or bridge semantics.
- Response:
  treat `fixed_defaults` as contract-declared constant projection only, and fail closed
  if a fixed default conflicts with a relation-derived emitted value.
- Closeout Evidence:
  fixed-default conflict handling in lowering source,
  `mutation_semantic_transform_contract_fixed_default_conflict.json`, and
  `test_fixed_default_conflict_fails_closed`.

### Edge 10: Seed Contract Overreach

- Risk:
  the first lowering slice could emit something closer to a `V48-A` binding profile or
  a compiled boundary than to a narrow seed.
- Response:
  keep the emitted contract pre-bridge and pre-runtime, with one bounded seed family
  only, and state explicitly that it is not a `V48-A` binding profile without the
  later `V49-D` bridge.
- Closeout Evidence:
  emitted contract limited to `adeu_taskpack_binding_spec_seed@1`, reference seed
  fixture, and absence of bridge outputs in shipped scope.

### Edge 11: Bridge Laundering

- Risk:
  the first lowering slice could quietly add `V48-A` / `V48-B` helper behavior.
- Response:
  defer all downstream `V48` bridge helpers to `V49-D`.
- Closeout Evidence:
  shipped scope limited to lowering/package/tests/fixtures only and no bridge helper
  implementation under `packages/adeu_semantic_forms`.

### Edge 12: Projection Leakage Into Identity

- Risk:
  notices, diagnostics, or incidental lowering explanations could quietly change seed
  identity.
- Response:
  compute deterministic seed identity from the bounded emitted seed payload only.
- Closeout Evidence:
  released `TaskpackBindingSpecSeed` identity law in models, deterministic seed replay,
  and absence of explanatory support fields in emitted seed fixtures.

### Edge 13: Consumer Prematurity

- Risk:
  symbol audit, paper semantics, simulation, or product consumers could leak into the
  first lowering release and blur ownership.
- Response:
  keep `V49-C` bounded to lowering behavior, fixtures, and targeted tests only.
- Closeout Evidence:
  shipped scope limited to `transform_v48_seed.py`, package exports, `v49c` fixtures,
  targeted tests, and support-only closeout artifacts.

## Current Judgment

- `V49-C` was the right next `V49` move because `V49-A` had already frozen the starter
  contracts and identity law, and `V49-B` had already frozen bounded recovery into
  those contracts on `main`.
- the shipped result is properly narrow: one repo-owned deterministic lowering
  surface, one released `repo_policy_work` normal-form domain, one released transform
  contract family, direct `V49-A` or `V49-B resolved_singleton` admissibility only,
  generic required-singleton enforcement, singleton `produce_artifact_kind`,
  deterministic replay, fixed-default conflict fail-closed posture, and no bridge,
  runtime, or product-surface widening.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md` should now be read with `V49-C` closed on
  `main` and the branch-local default next path advanced to `V49-D`.
