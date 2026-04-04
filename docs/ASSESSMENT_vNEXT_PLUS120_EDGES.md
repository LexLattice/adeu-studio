# Assessment vNext+120 Edges

Status: post-closeout edge assessment for `V49-D` (April 4, 2026 UTC).

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS120_EDGES.md",
  "phase": "post_closeout_assessment",
  "authoritative": true,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Released-Seed Bypass

- Risk:
  the bridge lane could claim `V49-D` ownership while rebuilding authority from raw
  earlier-family inputs instead of consuming the released `V49-C` seed contract.
- Response:
  keep one released seed plus one repo-owned bridge contract in and one released
  `V48-A` binding profile out.
- Closeout Evidence:
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/bridge_v48.py`,
  `packages/adeu_semantic_forms/src/adeu_semantic_forms/models.py`, and committed
  `v49d` replay fixtures under `packages/adeu_semantic_forms/tests/fixtures/v49d/`.

### Edge 2: Anchor-Resolution Drift

- Risk:
  `scope_anchor_ref`, `policy_anchor_ref`, or `worker_subject_ref` could be repaired
  by local convention or ambient repo search rather than explicit bridge law.
- Response:
  require the bridge contract to name expected seed anchors explicitly and fail closed
  on mismatch.
- Closeout Evidence:
  exact anchor checks in `bridge_v48.py`,
  `mutation_semantic_seed_v48_bridge_contract_scope_anchor_mismatch.json`, and
  `test_scope_anchor_mismatch_fails_closed`.

### Edge 3: Snapshot Drift

- Risk:
  the bridge could combine a released seed with a bridge contract from a different
  snapshot posture and still emit an apparently valid binding profile.
- Response:
  freeze exact snapshot-id and snapshot-sha equality through the released `V48-A`
  builder path and fail closed on mismatch.
- Closeout Evidence:
  wrapped released-builder mismatch path in `bridge_v48.py`,
  `mutation_semantic_seed_v48_bridge_contract_snapshot_mismatch.json`, and
  `test_snapshot_mismatch_fails_closed`.

### Edge 4: Released `V48-A` Redefinition

- Risk:
  the bridge helper could recreate released `V48-A` semantics locally and drift from
  the actual binding-profile authority surface.
- Response:
  require emission only through released `build_v48a_taskpack_binding_profile(...)`
  semantics.
- Closeout Evidence:
  single released-builder call in `bridge_v48.py` and exact replay against the
  committed `v48a` reference binding profile.

### Edge 5: Compile-Lane Laundering

- Risk:
  the bridge slice could quietly ship a new compile wrapper and blur the boundary with
  released `V48-B`.
- Response:
  require admissibility only as the released `binding_profile_ref` carrier for
  `compile_v48b_taskpack_binding(...)`, with remaining compiler inputs supplied
  separately and no new compile wrapper in `V49-D`.
- Closeout Evidence:
  `test_reference_bridge_output_is_compile_compatible` and absence of any new compile
  helper under `packages/adeu_semantic_forms`.

### Edge 6: Fixed-Default Overreach

- Risk:
  seed fixed defaults could become a back door for bridge heuristics or new binding
  authority.
- Response:
  allow fixed defaults only as exact restatements of released `V48-A` postures and
  fail closed on conflict.
- Closeout Evidence:
  `_validate_seed_defaults(...)`,
  `mutation_taskpack_binding_spec_seed_fixed_default_conflict.json`, and
  `test_fixed_default_conflict_fails_closed`.

### Edge 7: Empty-Projection Drift

- Risk:
  semantically admissible but structurally incomplete seeds could leak through to the
  released `V48-A` builder and surface only as generic upstream builder errors.
- Response:
  reject empty `allow_paths`, `forbid_paths`, or `forbid_effects` locally before
  builder entry.
- Closeout Evidence:
  `_validate_seed_projections(...)` and
  `test_empty_seed_projection_fails_closed`.

### Edge 8: Projection Laundering

- Risk:
  task scope, prompt, command, or evidence projections could be invented from prompt
  prose, prototype text, or local convention instead of typed bridge inputs.
- Response:
  require `task_scope_summary`, `prompt_projection_inputs`, command projections, and
  evidence projections to come only from the bridge contract and pass unchanged into
  the released builder.
- Closeout Evidence:
  released bridge-contract model, reference bridge-contract builder, and
  `mutation_semantic_seed_v48_bridge_contract_prompt_authority_drift.json`.

### Edge 9: Policy-Clause Laundering

- Risk:
  the bridge could end up synthesizing or repairing `policy_authority_clause_ref`
  lineage locally instead of letting the released `V48-A` builder resolve it from the
  admitted `V47-E` carrier.
- Response:
  require clause lineage to be resolved only through the released `V48-A` builder path
  and fail closed if the bridge would need to invent it.
- Closeout Evidence:
  bridge helper delegates clause resolution entirely to released
  `build_v48a_taskpack_binding_profile(...)` and never emits a local clause-repair
  branch.

### Edge 10: Output-Revalidation Softness

- Risk:
  emitted binding profiles could be treated as valid bridge outputs without being
  revalidated under the released `AnmTaskpackBindingProfile` model.
- Response:
  revalidate the emitted output and require semantic-hash parity.
- Closeout Evidence:
  output revalidation path in `bridge_v48.py` and exact replay tests against the
  committed `v48a` fixture.

### Edge 11: Consumer Prematurity

- Risk:
  symbol audit, paper semantics, simulation, worker runtime, or product consumers
  could leak into the bridge slice and blur ownership.
- Response:
  keep `V49-D` bounded to bridge behavior, fixtures, and targeted tests only.
- Closeout Evidence:
  shipped scope limited to `bridge_v48.py`, package exports, `v49d` fixtures, targeted
  tests, and support-only closeout artifacts.

## Current Judgment

- `V49-D` was the right final `V49` move because `V49-A` had already frozen the
  substrate contracts and identity law, `V49-B` had already frozen bounded recovery,
  and `V49-C` had already frozen deterministic seed lowering on `main`.
- the shipped result is properly narrow: one repo-owned bridge helper, one released
  `repo_policy_work` seed family, one repo-owned bridge contract family, one released
  `V48-A` binding-profile emission path, one released `binding_profile_ref`
  admissibility path into `V48-B`, exact profile/snapshot/anchor/default matching,
  deterministic replay, compile-compatibility proof, and no runtime or product-surface
  widening.
- `docs/DRAFT_NEXT_ARC_OPTIONS_v32.md` should now be read with `V49-D` closed on
  `main`, completing the bounded `V49` family with no further internal `V49` path
  currently selected.
