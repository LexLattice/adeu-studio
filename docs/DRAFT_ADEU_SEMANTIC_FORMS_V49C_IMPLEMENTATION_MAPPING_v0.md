# Draft ADEU Semantic Forms V49C Implementation Mapping v0

Status: support-layer implementation mapping for `V49-C`.

Authority layer: support only.

This note does not authorize implementation by itself. It maps the imported
`adeu_semantic_forms` prototype material to the repo-owned `V49-C` lowering slice so
the implementation can stay grounded without silently importing prototype code as live
authority.

## Carry Forward Nearly As-Is

- starter downstream target posture:
  - `adeu_taskpack_binding_spec_seed@1`
- starter transform-contract posture:
  - one released normal form in
  - one released transform contract in
  - one seed out
- starter relation families used by the transform contract:
  - required singleton relations:
    - `bind_scope_anchor`
    - `bind_policy_anchor`
    - `use_worker_subject`
    - `set_mutation_posture`
    - `produce_artifact_kind`
  - supported multi relations:
    - `allow_path`
    - `forbid_path`
    - `forbid_effect`
- fixed-default posture already grounded in the released `V49-A` reference transform
  contract:
  - `lineage_resolution_posture`
  - `prompt_projection_posture`
  - `unsupported_mapping_posture`

## Re-Author With Repo Alignment

- live lowering owner:
  - `packages/adeu_semantic_forms/src/adeu_semantic_forms/transform_v48_seed.py`
- emitted seed contract shape:
  - repo-owned source of truth
  - deterministic seed hash law
  - explicit lineage fields
  - explicit non-equivalence with released `V48-A` binding profiles
- deterministic ordering law:
  - all emitted multi-value collections deduped and sorted by canonical value
- fail-closed doctrine:
  - missing required singleton relation
  - duplicate singleton relation
  - unsupported relation kind
  - transform mismatch
  - fixed-default conflict with relation-derived values
- repo-native fixtures and tests:
  - accepted lowering replay
  - missing-required reject
  - duplicate-singleton reject
  - mismatch reject
  - byte-identical replay

## Defer To Later Slice

- lowering from non-`resolved_singleton` recovery outcomes:
  - stays rejected in `V49-C`
  - no alternative selection policy here
- bridge into released `V48-A` / `V48-B`:
  - deferred to `V49-D`
- worker runtime behavior:
  - not selected here
- CLI / API / web consumers:
  - not selected here

## Do Not Import

- do not copy prototype lowering code wholesale into live package paths
- do not import any prototype-specific bridge helper as if it were a released `V48`
  surface
- do not import any prototype product or demo surface into this slice
- do not let prototype explanatory fields become seed identity fields
