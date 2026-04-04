# Assessment vNext+120 Edges

Status: planning-edge assessment for `V49-D`.

## Assessment-State Marker (Machine-Checkable)

```json
{
  "schema": "assessment_artifact_state@1",
  "artifact": "docs/ASSESSMENT_vNEXT_PLUS120_EDGES.md",
  "phase": "pre_lock_assessment",
  "authoritative": false,
  "required_in_decision": true
}
```

## Open Edges

### Edge 1: Seed-Lineage Bypass

- Risk:
  the bridge lane could claim `V49-D` ownership while bypassing the released
  `V49-C` seed contract and rebuilding authority from raw earlier-family inputs.
- Response:
  require exactly one released `adeu_taskpack_binding_spec_seed@1` plus one
  bridge-contract input, with no raw `V45` / `V47` / `V49-A` / `V49-B` bypass.

### Edge 2: Anchor-Resolution Ambiguity

- Risk:
  `scope_anchor_ref`, `policy_anchor_ref`, or `worker_subject_ref` could be resolved
  by local convention or ambient repo search rather than explicit bridge law.
- Response:
  require the bridge contract to name the expected seed anchors explicitly and fail
  closed on mismatch.

### Edge 3: Snapshot Drift

- Risk:
  the bridge could combine a released seed with a bridge contract from a different
  snapshot posture and still emit an apparently valid binding profile.
- Response:
  freeze exact snapshot-id and snapshot-sha equality between seed and bridge contract.

### Edge 4: Released `V48-A` Redefinition

- Risk:
  the bridge helper could recreate released `V48-A` semantics locally and drift from
  the actual binding-profile authority surface.
- Response:
  require emission only through released `build_v48a_taskpack_binding_profile(...)`
  semantics.

### Edge 5: Compile-Lane Laundering

- Risk:
  the bridge slice could quietly ship a new compile wrapper and blur the boundary with
  released `V48-B`.
- Response:
  require admissibility only as the released `binding_profile_ref` carrier for
  `compile_v48b_taskpack_binding(...)`, with the remaining released compiler inputs
  supplied separately and no new compile wrapper in `V49-D`.

### Edge 6: Fixed-Default Overreach

- Risk:
  seed fixed defaults could become a back door for bridge heuristics or new binding
  authority.
- Response:
  allow fixed defaults only as exact restatements of released `V48-A` postures and
  fail closed on conflict.

### Edge 7: Projection Laundering

- Risk:
  task scope, prompt, command, or evidence projections could be invented from prompt
  prose, prototype text, or local convention instead of typed bridge inputs.
- Response:
  require `task_scope_summary`, `prompt_projection_inputs`, command projections, and
  evidence projections to come only from the bridge contract and pass unchanged into
  the released builder.

### Edge 8: Seed-to-Binding Mapping Drift

- Risk:
  `allow_paths`, `forbid_paths`, and `forbid_effects` could map inconsistently into
  released `V48-A` projection families across implementations.
- Response:
  freeze one deterministic seed-to-projection mapping law in the lock.

### Edge 9: Worker-Subject Drift

- Risk:
  the emitted binding profile could carry a worker subject that no longer matches the
  released seed lineage.
- Response:
  require exact worker-subject equality between seed and bridge contract.

### Edge 10: Policy-Clause Laundering

- Risk:
  the bridge could end up synthesizing or repairing `policy_authority_clause_ref`
  lineage locally instead of letting the released `V48-A` builder resolve it from the
  admitted `V47-E` carrier.
- Response:
  require clause lineage to be resolved only through the released `V48-A` builder path
  and fail closed if the bridge would need to invent it.

### Edge 11: Consumer Prematurity

- Risk:
  runtime, conformance, delegation, symbol audit, paper semantics, simulation, or
  product consumers could leak into the bridge slice and blur ownership.
- Response:
  keep `V49-D` bounded to bridge behavior, fixtures, and targeted tests only.

## Current Judgment

- `V49-D` is worth implementing next because `V49-A` through `V49-C` have already
  frozen the substrate contracts, bounded recovery, and deterministic lowering on
  `main`.
- the next move should remain narrowly operational but still non-runtime: one released
  `V49-C` seed plus one repo-owned bridge contract into one released `V48-A` binding
  profile, with released-`binding_profile_ref` admissibility into `V48-B`,
  fail-closed mapping posture, non-synthesized clause lineage and prompt/task-scope
  inputs, and no new compile wrapper or product-surface widening.
